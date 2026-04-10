// Contract types double as method decorators (TS 5+ decorators)
type MethodDecorator = <T>(target: T, context: ClassMethodDecoratorContext) => T

export type PreCondition = MethodDecorator & { readonly __type: 'requires' }
export type PostCondition = MethodDecorator & { readonly __type: 'ensures' }
export type Invariant = { readonly __type: 'invariant' }
export type Decreases = { readonly __type: 'decreases' }
export type Modification = { readonly __type: 'modifies'; readonly refs: string[] }

export type Check = { readonly __type: 'check' }
export type Assume = { readonly __type: 'assume' }
export type Unreachable = { readonly __type: 'unreachable' }

export type LoopInvariant = { readonly __type: 'loop-invariant'; readonly loopIndex: number }
export type LoopDecreases = { readonly __type: 'loop-decreases'; readonly loopIndex: number }

export type Contract = PreCondition | PostCondition | Invariant | Decreases | Modification | Check | Assume | Unreachable | LoopInvariant | LoopDecreases

// ---------------------------------------------------------------------------
// Config
// ---------------------------------------------------------------------------

export interface TheoremConfig {
  include?: string[]
  exclude?: string[]
  /** Glob patterns for `.contracts.ts` files that declare contracts for external functions. */
  contracts?: string[]
  solver?: {
    timeout?: number
    maxCounterexamples?: number
    minimizeCounterexamples?: boolean
  }
  scan?: {
    skipDirs?: string[]
    risks?: Record<string, string>
  }
  reporter?: {
    format?: 'cli' | 'sarif'
    showUsedAssumptions?: boolean
  }
}
