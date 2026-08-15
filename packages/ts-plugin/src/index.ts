import type * as tslib from 'typescript/lib/tsserverlibrary'
import { spawn, type ChildProcess } from 'child_process'
import { join } from 'path'
import { writeFileSync, mkdirSync } from 'fs'

// ---------------------------------------------------------------------------
// Diagnostic code range — custom codes for Theorem diagnostics
// ---------------------------------------------------------------------------

const SOURCE = 'theorem'
const PLUGIN_VERSION = '0.7.0'
const CHILD_TIMEOUT_MS = 60_000

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

interface TheoremFix {
  start: number
  length: number
  title: string
  insertPos: number
  insertText: string
}

interface CachedDiagnostics {
  sourceHash: string
  diagnostics: tslib.Diagnostic[]
  /** Element accesses whose bounds Theorem PROVED — tsc's possibly-undefined
   *  errors at these spots are suppressed (proof beats assertion). */
  suppressions: Array<{ line: number; exprText: string }>
  /** One-click fixes: Spacer-inferred invariants inserted at the loop. */
  fixes: TheoremFix[]
}

interface ChildFailure {
  message: string
  start: number
  length: number
  code: number
  severity: 'error' | 'warning'
}

interface ChildOutput {
  failures: ChildFailure[]
  suppressions?: Array<{ line: number; exprText: string }>
  fixes?: TheoremFix[]
}

// ---------------------------------------------------------------------------
// Plugin entry point
//
// All verification (Z3 WASM included) runs in a short-lived child process —
// never inside tsserver. Z3's worker threads and memory previously starved
// the tsserver event loop and crash-looped the server, which also left the
// editor rendering diagnostics computed against stale file versions.
// ---------------------------------------------------------------------------

function init(modules: { typescript: typeof tslib }): tslib.server.PluginModule {
  const ts = modules.typescript

  function create(info: tslib.server.PluginCreateInfo): tslib.LanguageService {
    const logger = info.project.projectService.logger

    function log(msg: string): void {
      logger.info(`[theorem-ts-plugin] ${msg}`)
    }

    log(`plugin created (v${PLUGIN_VERSION} — subprocess verification)`)

    // -------------------------------------------------------------------
    // Diagnostics cache — keyed by fileName + source hash
    // -------------------------------------------------------------------

    const cache = new Map<string, CachedDiagnostics>()
    const pendingVersions = new Map<string, string>()
    const debounceTimers = new Map<string, ReturnType<typeof setTimeout>>()
    const activeChildren = new Map<string, ChildProcess>()

    function hashSource(source: string): string {
      let h = 0
      for (let i = 0; i < source.length; i++) {
        h = ((h << 5) - h + source.charCodeAt(i)) | 0
      }
      return String(h)
    }

    // -------------------------------------------------------------------
    // Debounced background verification (in a child process)
    // -------------------------------------------------------------------

    function scheduleVerification(fileName: string, source: string, hash: string): void {
      const existing = debounceTimers.get(fileName)
      if (existing) clearTimeout(existing)

      const timer = setTimeout(() => {
        debounceTimers.delete(fileName)
        pendingVersions.set(fileName, hash)
        runVerification(fileName, source, hash)
      }, 500)

      debounceTimers.set(fileName, timer)
    }

    function runVerification(fileName: string, source: string, hash: string): void {
      // A newer edit may already have superseded this run
      if (pendingVersions.get(fileName) !== hash) return

      // Kill any in-flight child for this file — it computed an older version
      const previous = activeChildren.get(fileName)
      if (previous) {
        try { previous.kill('SIGKILL') } catch { /* already dead */ }
        activeChildren.delete(fileName)
      }

      const childPath = join(__dirname, 'verifier-child.js')
      let child: ChildProcess
      try {
        child = spawn(process.execPath, [childPath], {
          env: { ...process.env, ELECTRON_RUN_AS_NODE: '1' },
          stdio: ['pipe', 'pipe', 'pipe'],
        })
      } catch (err) {
        log(`failed to spawn verifier child: ${err}`)
        return
      }

      activeChildren.set(fileName, child)

      const killTimer = setTimeout(() => {
        log(`verifier child timed out for ${fileName}`)
        try { child.kill('SIGKILL') } catch { /* already dead */ }
      }, CHILD_TIMEOUT_MS)

      const stdoutChunks: Buffer[] = []
      const stderrChunks: Buffer[] = []
      child.stdout?.on('data', (c: Buffer) => stdoutChunks.push(c))
      child.stderr?.on('data', (c: Buffer) => stderrChunks.push(c))

      child.on('error', err => {
        clearTimeout(killTimer)
        activeChildren.delete(fileName)
        log(`verifier child error for ${fileName}: ${err}`)
      })

      child.on('close', exitCode => {
        clearTimeout(killTimer)
        if (activeChildren.get(fileName) === child) activeChildren.delete(fileName)

        if (exitCode !== 0) {
          const stderr = Buffer.concat(stderrChunks).toString('utf-8').slice(0, 500)
          log(`verifier child exited ${exitCode} for ${fileName}: ${stderr}`)
          return
        }

        // Discard if the file changed while the child was running
        if (pendingVersions.get(fileName) !== hash) return

        let failures: ChildFailure[]
        let suppressions: Array<{ line: number; exprText: string }>
        let fixes: TheoremFix[]
        try {
          const parsed = JSON.parse(Buffer.concat(stdoutChunks).toString('utf-8')) as ChildOutput
          failures = parsed.failures
          suppressions = parsed.suppressions ?? []
          fixes = parsed.fixes ?? []
        } catch (err) {
          log(`failed to parse verifier output for ${fileName}: ${err}`)
          return
        }

        const diagnostics = failures.map(f => toDiagnostic(f))
        cache.set(fileName, { sourceHash: hash, diagnostics, suppressions, fixes })
        pendingVersions.delete(fileName)
        refreshDiags()
        dumpDebug(fileName, source, hash, failures)
        log(`verified ${fileName}: ${failures.length} finding(s)`)
      })

      const contractsDir = join(info.project.getCurrentDirectory(), '.theorem', 'contracts')
      try {
        child.stdin?.write(JSON.stringify({ fileName, source, contractsDir }))
        child.stdin?.end()
      } catch (err) {
        log(`failed to write to verifier child: ${err}`)
        try { child.kill('SIGKILL') } catch { /* already dead */ }
      }
    }

    // -------------------------------------------------------------------
    // Debug dump — written after every verification so diagnostics can be
    // inspected without tsserver logging (.theorem/plugin-debug.json in the
    // project directory)
    // -------------------------------------------------------------------

    function dumpDebug(fileName: string, source: string, hash: string, failures: ChildFailure[]): void {
      try {
        const dir = join(info.project.getCurrentDirectory(), '.theorem')
        mkdirSync(dir, { recursive: true })
        const lineOf = (offset: number) => source.slice(0, offset).split('\n').length
        writeFileSync(join(dir, 'plugin-debug.json'), JSON.stringify({
          pluginVersion: PLUGIN_VERSION,
          fileName,
          sourceHash: hash,
          sourceLength: source.length,
          timestamp: new Date().toISOString(),
          failures: failures.map(f => ({
            message: f.message,
            start: f.start,
            length: f.length,
            line: lineOf(f.start),
            anchoredText: source.slice(f.start, f.start + f.length),
          })),
        }, null, 2))
      } catch { /* debug only — never break diagnostics */ }
    }

    // -------------------------------------------------------------------
    // Diagnostic conversion / refresh
    // -------------------------------------------------------------------

    // tsc's possibly-undefined family: 2532 "Object is possibly 'undefined'",
    // 18048 "'x' is possibly 'undefined'", 18047 possibly 'null'. When
    // Theorem PROVED the index in bounds for that exact access, the error is
    // refuted by theorem — suppress it. Anything unproven passes through.
    const SUPPRESSIBLE = new Set([2532, 18048, 18047])

    function filterProvenBounds(
      diags: tslib.Diagnostic[],
      suppressions: Array<{ line: number; exprText: string }>,
      src: string,
    ): tslib.Diagnostic[] {
      if (suppressions.length === 0) return diags
      const lineStarts: number[] = [0]
      for (let i = 0; i < src.length; i++) if (src[i] === '\n') lineStarts.push(i + 1)
      const lineOf = (offset: number): number => {
        let lo = 0, hi = lineStarts.length - 1
        while (lo < hi) { const mid = (lo + hi + 1) >> 1; if (lineStarts[mid]! <= offset) lo = mid; else hi = mid - 1 }
        return lo + 1
      }
      return diags.filter(d => {
        if (d.code === undefined || !SUPPRESSIBLE.has(d.code) || d.start === undefined) return true
        const diagLine = lineOf(d.start)
        const lineEnd = src.indexOf('\n', lineStarts[diagLine - 1]!)
        const lineText = src.slice(lineStarts[diagLine - 1]!, lineEnd === -1 ? src.length : lineEnd)
        const hit = suppressions.some(sp =>
          sp.line === diagLine && lineText.includes(sp.exprText.split('[')[0]!))
        if (hit) log(`suppressed tsc ${d.code} at line ${diagLine} — bounds proved by theorem`)
        return !hit
      })
    }

    function toDiagnostic(failure: ChildFailure): tslib.Diagnostic {
      return {
        file: undefined,
        start: failure.start,
        length: failure.length,
        messageText: failure.message,
        category: failure.severity === 'error' ? ts.DiagnosticCategory.Error : ts.DiagnosticCategory.Warning,
        code: failure.code,
        source: SOURCE,
      } as tslib.Diagnostic
    }

    function refreshDiags(): void {
      try {
        info.project.refreshDiagnostics()
      } catch {
        try { (info.project as unknown as { markAsDirty?: () => void }).markAsDirty?.() } catch { /* best effort */ }
      }
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

      // Read from the ScriptInfo snapshot — the live editor buffer — NOT from
      // program.getSourceFile(): program snapshots can lag the buffer by many
      // edits, which anchors diagnostics against text the user no longer sees.
      const scriptInfo = info.project.getScriptInfo(fileName)
      const snapshot = scriptInfo?.getSnapshot()
      const source = snapshot !== undefined
        ? snapshot.getText(0, snapshot.getLength())
        : sourceFile.getText()
      const hash = hashSource(source)

      if (snapshot !== undefined && sourceFile.text.length !== source.length) {
        log(`stale program for ${fileName}: program=${sourceFile.text.length} chars, buffer=${source.length} chars — using buffer`)
      }

      // Return cached if fresh — re-bind sourceFile to current version
      const cached = cache.get(fileName)
      if (cached && cached.sourceHash === hash) {
        const rebound = cached.diagnostics.map(d => ({ ...d, file: sourceFile }))
        const filtered = filterProvenBounds(original, cached.suppressions, source)
        return [...filtered, ...rebound]
      }

      // Schedule verification (debounced, in a child process)
      scheduleVerification(fileName, source, hash)

      // Return original only — don't show stale diagnostics with wrong offsets
      return original
    }

    // -------------------------------------------------------------------
    // Code fixes: the lightbulb that inserts Spacer-inferred invariants
    // -------------------------------------------------------------------

    proxy.getCodeFixesAtPosition = (fileName, start, end, errorCodes, formatOptions, preferences) => {
      const original = info.languageService.getCodeFixesAtPosition(
        fileName, start, end, errorCodes, formatOptions, preferences)
      const cached = cache.get(fileName)
      if (cached === undefined || cached.fixes.length === 0) return original
      const ours: tslib.CodeFixAction[] = []
      for (const fix of cached.fixes) {
        const overlaps = start <= fix.start + fix.length && end >= fix.start
        if (!overlaps) continue
        ours.push({
          fixName: 'theorem-insert-invariants',
          description: fix.title,
          changes: [{
            fileName,
            textChanges: [{ span: { start: fix.insertPos, length: 0 }, newText: fix.insertText }],
          }],
        })
      }
      return ours.length > 0 ? [...original, ...ours] : original
    }

    return proxy
  }

  return { create }
}

export = init
