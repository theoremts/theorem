import type * as tslib from 'typescript/lib/tsserverlibrary'

// ---------------------------------------------------------------------------
// Diagnostic code range — custom codes for Theorem diagnostics
// ---------------------------------------------------------------------------

const DIAG_CODE_DISPROVED  = 100_001
const DIAG_CODE_UNKNOWN    = 100_002
const DIAG_CODE_CALLSITE   = 100_003
const DIAG_CODE_ERROR      = 100_004

const SOURCE = 'theorem'

// ---------------------------------------------------------------------------
// Types for cached verification results
// ---------------------------------------------------------------------------

interface CachedDiagnostics {
  sourceHash: string
  diagnostics: tslib.Diagnostic[]
}

interface VerificationFailure {
  message: string
  start: number
  length: number
  code: number
  category: tslib.DiagnosticCategory
}

// ---------------------------------------------------------------------------
// Plugin entry point
// ---------------------------------------------------------------------------

function init(modules: { typescript: typeof tslib }): tslib.server.PluginModule {
  const ts = modules.typescript

  function create(info: tslib.server.PluginCreateInfo): tslib.LanguageService {
    const logger = info.project.projectService.logger

    function log(msg: string): void {
      logger.info(`[theorem-ts-plugin] ${msg}`)
    }

    log('plugin created')

    // -------------------------------------------------------------------
    // Z3 context — lazily initialized once
    // -------------------------------------------------------------------

    let z3Ctx: import('@theoremts/core').Z3Context | null = null
    let z3InitPromise: Promise<import('@theoremts/core').Z3Context> | null = null
    let z3Failed = false

    async function getZ3(): Promise<import('@theoremts/core').Z3Context | null> {
      if (z3Failed) return null
      if (z3Ctx !== null) return z3Ctx

      if (z3InitPromise === null) {
        z3InitPromise = (async () => {
          try {
            log('initializing Z3 WASM...')
            const core = await import('@theoremts/core')
            const ctx = await core.getContext()
            log('Z3 WASM initialized')
            return ctx
          } catch (err) {
            z3Failed = true
            log(`Z3 initialization failed: ${err}`)
            throw err
          }
        })()
      }

      try {
        z3Ctx = await z3InitPromise
        return z3Ctx
      } catch {
        return null
      }
    }

    // Kick off Z3 initialization immediately
    getZ3()

    // -------------------------------------------------------------------
    // Diagnostics cache — keyed by fileName + source hash
    // -------------------------------------------------------------------

    const cache = new Map<string, CachedDiagnostics>()
    const pendingVersions = new Map<string, string>()  // fileName → hash being verified
    let debounceTimers = new Map<string, ReturnType<typeof setTimeout>>()

    function hashSource(source: string): string {
      // Fast hash for change detection
      let h = 0
      for (let i = 0; i < source.length; i++) {
        h = ((h << 5) - h + source.charCodeAt(i)) | 0
      }
      return String(h)
    }

    // -------------------------------------------------------------------
    // Debounced background verification
    // -------------------------------------------------------------------

    function scheduleVerification(
      fileName: string,
      source: string,
      sourceFile: tslib.SourceFile,
      hash: string,
    ): void {
      // Clear existing debounce timer for this file
      const existing = debounceTimers.get(fileName)
      if (existing) clearTimeout(existing)

      // Debounce 500ms — avoids re-verifying on every keystroke
      const timer = setTimeout(() => {
        debounceTimers.delete(fileName)
        pendingVersions.set(fileName, hash)
        runVerification(fileName, source, sourceFile, hash)
      }, 500)

      debounceTimers.set(fileName, timer)
    }

    async function runVerification(
      fileName: string,
      source: string,
      sourceFile: tslib.SourceFile,
      hash: string,
    ): Promise<void> {
      try {
        const ctx = await getZ3()
        if (ctx === null) return

        // Check if a newer version was requested while we were waiting
        if (pendingVersions.get(fileName) !== hash) return

        const core = await import('@theoremts/core')
        const failures: VerificationFailure[] = []

        let irList: import('@theoremts/core').FunctionIR[]
        try {
          irList = core.extractFromSource(source, fileName)
        } catch (err) {
          log(`extraction failed for ${fileName}: ${err}`)
          return
        }

        if (irList.length === 0) {
          cache.set(fileName, { sourceHash: hash, diagnostics: [] })
          refreshProject()
          return
        }

        // Check again if source changed during extraction
        if (pendingVersions.get(fileName) !== hash) return

        const registry = core.buildRegistry(irList)

        for (const ir of irList) {
          let tasks: import('@theoremts/core').VerificationTask[]
          try {
            tasks = core.translate(ir, ctx, registry)
          } catch (err) {
            log(`translation failed for ${ir.name ?? '(anonymous)'}: ${err}`)
            continue
          }

          for (const task of tasks) {
            try {
              const result = await core.check({ ...task, timeout: 5000 })
              if (result.status === 'disproved') {
                const ceText = formatCounterexample(result.counterexample)
                const traceText = result.trace ? formatTrace(result.trace) : ''
                failures.push({
                  message: `Theorem: ${task.contractText} — counterexample: ${ceText}${traceText}`,
                  start: findContractPosition(source, ir.name, task.contractText),
                  length: estimateSpanLength(ir.name),
                  code: DIAG_CODE_DISPROVED,
                  category: ts.DiagnosticCategory.Error,
                })
              } else if (result.status === 'unknown') {
                failures.push({
                  message: `Theorem: ${task.contractText} — could not prove (${result.reason})`,
                  start: findContractPosition(source, ir.name, task.contractText),
                  length: estimateSpanLength(ir.name),
                  code: DIAG_CODE_UNKNOWN,
                  category: ts.DiagnosticCategory.Warning,
                })
              }
            } catch (err) {
              log(`check failed for task "${task.contractText}": ${err}`)
            }
          }
        }

        // Call-site obligations
        try {
          const callSiteTasks = core.extractCallSiteObligations(source, fileName, registry, ctx)
          for (const task of callSiteTasks) {
            try {
              const result = await core.check({ ...task, timeout: 5000 })
              if (result.status === 'disproved') {
                const ceText = formatCounterexample(result.counterexample)
                const callSitePos = findCallSitePosition(source, task.functionName ?? '', task.contractText)
                failures.push({
                  message: `Theorem: ${task.contractText}${ceText ? ` — ${ceText}` : ''}`,
                  start: callSitePos,
                  length: estimateCallSiteSpanLength(source, callSitePos),
                  code: DIAG_CODE_CALLSITE,
                  category: ts.DiagnosticCategory.Error,
                })
              }
            } catch (err) {
              log(`call-site check failed: ${err}`)
            }
          }
        } catch (err) {
          log(`call-site extraction failed for ${fileName}: ${err}`)
        }

        // Only cache if source hasn't changed since we started
        if (pendingVersions.get(fileName) === hash) {
          const diagnostics = failures.map(f => toDiagnostic(f, sourceFile))
          cache.set(fileName, { sourceHash: hash, diagnostics })
          pendingVersions.delete(fileName)
          refreshProject()
        }

      } catch (err) {
        log(`verification error for ${fileName}: ${err}`)
      } finally {
        pendingVersions.delete(fileName)
      }
    }

    // -------------------------------------------------------------------
    // Project refresh
    // -------------------------------------------------------------------

    function refreshProject(): void {
      try {
        info.project.refreshDiagnostics()
      } catch {
        // refreshDiagnostics may not exist on all TS server versions
        try {
          // Alternative: mark project as dirty
          (info.project as any).markAsDirty?.()
        } catch {}
      }
    }

    // -------------------------------------------------------------------
    // Convert VerificationFailure to ts.Diagnostic
    // -------------------------------------------------------------------

    function toDiagnostic(
      failure: VerificationFailure,
      sourceFile: tslib.SourceFile,
    ): tslib.Diagnostic {
      return {
        file: sourceFile,
        start: failure.start,
        length: failure.length,
        messageText: failure.message,
        category: failure.category,
        code: failure.code,
        source: SOURCE,
      }
    }

    // -------------------------------------------------------------------
    // Source position helpers
    // -------------------------------------------------------------------

    function findContractPosition(
      source: string,
      fnName: string | undefined,
      _contractText: string,
    ): number {
      if (fnName) {
        // For function declarations: highlight the name, not "function" keyword
        const fnPattern = new RegExp(`function\\s+(${escapeRegex(fnName)})\\b`)
        const fnMatch = fnPattern.exec(source)
        if (fnMatch) return fnMatch.index + fnMatch[0].indexOf(fnName)

        // For const/let declarations
        const constPattern = new RegExp(`(?:const|let|var)\\s+(${escapeRegex(fnName)})\\b`)
        const constMatch = constPattern.exec(source)
        if (constMatch) return constMatch.index + constMatch[0].indexOf(fnName)

        // For class methods
        const methodPattern = new RegExp(`\\b(${escapeRegex(fnName)})\\s*\\(`)
        const methodMatch = methodPattern.exec(source)
        if (methodMatch) return methodMatch.index
      }
      return 0
    }

    function estimateSpanLength(fnName: string | undefined): number {
      return fnName?.length ?? 20
    }

    function findCallSitePosition(
      source: string,
      functionName: string,
      contractText: string,
    ): number {
      const callee = functionName.replace(/^\(call-site\)\s*/, '')
      if (callee) {
        const callMatch = contractText.match(/^([^(]+)\(([^)]*)\)/)
        if (callMatch) {
          const argText = callMatch[2]!.trim()
          const exact = `${callee}(${argText})`
          const idx = source.indexOf(exact)
          if (idx >= 0) return idx
        }
        const pattern = new RegExp(`\\b${escapeRegex(callee)}\\s*\\(`)
        const match = pattern.exec(source)
        if (match) return match.index
      }
      return 0
    }

    function estimateCallSiteSpanLength(source: string, start: number): number {
      let depth = 0
      let i = start
      while (i < source.length) {
        if (source[i] === '(') depth++
        if (source[i] === ')') {
          depth--
          if (depth === 0) return i - start + 1
        }
        i++
      }
      return Math.min(30, source.length - start)
    }

    // -------------------------------------------------------------------
    // Formatting helpers
    // -------------------------------------------------------------------

    function formatCounterexample(ce: Record<string, unknown>): string {
      const entries = Object.entries(ce)
        .filter(([k]) => !k.startsWith('__'))
        .map(([k, v]) => `${k} = ${v}`)
      return entries.length > 0 ? entries.join(', ') : ''
    }

    function formatTrace(trace: Record<string, unknown>): string {
      const entries = Object.entries(trace)
        .filter(([, v]) => v !== '?')
        .map(([k, v]) => `${k} = ${v}`)
      return entries.length > 0 ? ` (where ${entries.join(', ')})` : ''
    }

    function escapeRegex(s: string): string {
      return s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')
    }

    // -------------------------------------------------------------------
    // Build proxy language service
    // -------------------------------------------------------------------

    const proxy = Object.create(null) as tslib.LanguageService

    for (const k of Object.keys(info.languageService) as Array<keyof tslib.LanguageService>) {
      const x = info.languageService[k]
      // eslint-disable-next-line @typescript-eslint/no-explicit-any, @typescript-eslint/no-unsafe-return
      ;(proxy as any)[k] = typeof x === 'function'
        ? (...args: any[]) => (x as any).apply(info.languageService, args)
        : x
    }

    // -------------------------------------------------------------------
    // Override getSemanticDiagnostics
    // -------------------------------------------------------------------

    proxy.getSemanticDiagnostics = (fileName: string): tslib.Diagnostic[] => {
      const original = info.languageService.getSemanticDiagnostics(fileName)

      if (!fileName.endsWith('.ts') || fileName.endsWith('.d.ts')) {
        return original
      }

      const program = info.languageService.getProgram()
      const sourceFile = program?.getSourceFile(fileName)
      if (!sourceFile) return original

      const source = sourceFile.getText()
      const hash = hashSource(source)

      // Return cached if fresh
      const cached = cache.get(fileName)
      if (cached && cached.sourceHash === hash) {
        return [...original, ...cached.diagnostics]
      }

      // Invalidate stale cache
      if (cached) cache.delete(fileName)

      // Schedule verification (debounced)
      scheduleVerification(fileName, source, sourceFile, hash)

      // Return original while verification runs
      return original
    }

    return proxy
  }

  return { create }
}

export = init
