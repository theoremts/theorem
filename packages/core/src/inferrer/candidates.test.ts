import { describe, it } from 'node:test'
import assert from 'node:assert/strict'
import { verifyCandidates } from './candidates.js'
import { getContext } from '../solver/context.js'
import type { InferredContract } from './index.js'
import type { Expr, FunctionIR } from '../parser/ir.js'

describe('verifyCandidates', () => {
  it('keeps a proven candidate (x * x >= 0)', async () => {
    const ctx = await getContext()

    const ir: FunctionIR = {
      name: 'f',
      params: [{ name: 'x', sort: 'real' }],
      returnSort: 'real',
      body: {
        kind: 'binary',
        op: '*',
        left: { kind: 'ident', name: 'x' },
        right: { kind: 'ident', name: 'x' },
      },
      contracts: [],
    }

    const candidate: InferredContract = {
      kind: 'ensures',
      text: 'output() >= 0',
      predicate: {
        kind: 'binary',
        op: '>=',
        left: { kind: 'call', callee: 'output', args: [] },
        right: { kind: 'literal', value: 0 },
      },
      confidence: 'derived',
      source: 'test',
    }

    const result = await verifyCandidates([candidate], ir, ctx, [])
    assert.equal(result.length, 1)
    assert.equal(result[0]?.confidence, 'proven')
    assert.equal(result[0]?.text, 'output() >= 0')
  })

  it('discards a disproved candidate (x + 1 >= 0 without requires)', async () => {
    const ctx = await getContext()

    const ir: FunctionIR = {
      name: 'f',
      params: [{ name: 'x', sort: 'real' }],
      returnSort: 'real',
      body: {
        kind: 'binary',
        op: '+',
        left: { kind: 'ident', name: 'x' },
        right: { kind: 'literal', value: 1 },
      },
      contracts: [],
    }

    const candidate: InferredContract = {
      kind: 'ensures',
      text: 'output() >= 0',
      predicate: {
        kind: 'binary',
        op: '>=',
        left: { kind: 'call', callee: 'output', args: [] },
        right: { kind: 'literal', value: 0 },
      },
      confidence: 'derived',
      source: 'test',
    }

    const result = await verifyCandidates([candidate], ir, ctx, [])
    assert.equal(result.length, 0)
  })

  it('proves a candidate with requires assumption (x >= 0 => x + 1 > 0)', async () => {
    const ctx = await getContext()

    const ir: FunctionIR = {
      name: 'f',
      params: [{ name: 'x', sort: 'real' }],
      returnSort: 'real',
      body: {
        kind: 'binary',
        op: '+',
        left: { kind: 'ident', name: 'x' },
        right: { kind: 'literal', value: 1 },
      },
      contracts: [],
    }

    const requiresContract: InferredContract = {
      kind: 'requires',
      text: 'x >= 0',
      predicate: {
        kind: 'binary',
        op: '>=',
        left: { kind: 'ident', name: 'x' },
        right: { kind: 'literal', value: 0 },
      },
      confidence: 'guard',
      source: 'test',
    }

    const candidate: InferredContract = {
      kind: 'ensures',
      text: 'output() > 0',
      predicate: {
        kind: 'binary',
        op: '>',
        left: { kind: 'call', callee: 'output', args: [] },
        right: { kind: 'literal', value: 0 },
      },
      confidence: 'derived',
      source: 'test',
    }

    const result = await verifyCandidates([candidate], ir, ctx, [requiresContract])
    assert.equal(result.length, 1)
    assert.equal(result[0]?.confidence, 'proven')
    assert.equal(result[0]?.text, 'output() > 0')
  })
})
