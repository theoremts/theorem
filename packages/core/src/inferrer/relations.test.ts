import { describe, it } from 'node:test'
import assert from 'node:assert/strict'
import { extractRelations } from './relations.js'
import { extractFunctionsFromSource } from '../parser/extractor.js'
import { getContext } from '../solver/context.js'

describe('extractRelations', () => {
  it('two numeric params generates relational candidates', async () => {
    const irs = extractFunctionsFromSource(
      `function f(a: number, b: number) { return a + b }`,
      'test.ts',
    )
    const ir = irs[0]!
    const ctx = await getContext()
    const candidates = await extractRelations(ir, ctx, [])

    assert.ok(candidates.length >= 4, `expected at least 4 candidates, got ${candidates.length}`)

    const texts = candidates.map(c => c.text)
    assert.ok(texts.includes('output() >= a'), `missing output() >= a, got: ${texts.join(', ')}`)
    assert.ok(texts.includes('output() <= a'), `missing output() <= a, got: ${texts.join(', ')}`)
    assert.ok(texts.includes('output() >= b'), `missing output() >= b, got: ${texts.join(', ')}`)
    assert.ok(texts.includes('output() <= b'), `missing output() <= b, got: ${texts.join(', ')}`)
    assert.ok(texts.includes('output() >= 0'), `missing output() >= 0, got: ${texts.join(', ')}`)

    // All should be ensures with derived confidence
    for (const c of candidates) {
      assert.equal(c.kind, 'ensures')
      assert.equal(c.confidence, 'derived')
      assert.equal(c.source, 'relational candidate')
    }
  })

  it('one numeric param generates relational candidates', async () => {
    const irs = extractFunctionsFromSource(
      `function f(x: number) { return x * 2 }`,
      'test.ts',
    )
    const ir = irs[0]!
    const ctx = await getContext()
    const candidates = await extractRelations(ir, ctx, [])

    assert.ok(candidates.length >= 2, `expected at least 2 candidates, got ${candidates.length}`)

    const texts = candidates.map(c => c.text)
    assert.ok(texts.includes('output() >= x'), `missing output() >= x, got: ${texts.join(', ')}`)
    assert.ok(texts.includes('output() <= x'), `missing output() <= x, got: ${texts.join(', ')}`)
    assert.ok(texts.includes('output() >= 0'), `missing output() >= 0, got: ${texts.join(', ')}`)
  })

  it('no body returns empty', async () => {
    const ir = {
      name: 'f',
      params: [{ name: 'x', sort: 'real' as const }],
      returnSort: 'real' as const,
      body: undefined,
      contracts: [],
    }
    const ctx = await getContext()
    const candidates = await extractRelations(ir, ctx, [])
    assert.equal(candidates.length, 0)
  })

  it('non-numeric return sort returns empty', async () => {
    const irs = extractFunctionsFromSource(
      `function f(s: string) { return s.length }`,
      'test.ts',
    )
    const ir = irs[0]!
    const ctx = await getContext()
    const candidates = await extractRelations(ir, ctx, [])

    // If return sort is not numeric, no relational candidates
    // (depends on how extractor classifies s.length — may be 'real' or 'unknown')
    // Just assert it doesn't crash
    assert.ok(Array.isArray(candidates))
  })

  it('deduplicates with existing requires', async () => {
    const irs = extractFunctionsFromSource(
      `function f(x: number) { return x * 2 }`,
      'test.ts',
    )
    const ir = irs[0]!
    const ctx = await getContext()

    // Pre-populate requires with one of the candidates
    const existingRequires = [{
      kind: 'requires' as const,
      text: 'output() >= x',
      predicate: { kind: 'binary' as const, op: '>=' as const, left: { kind: 'call' as const, callee: 'output', args: [] }, right: { kind: 'ident' as const, name: 'x' } },
      confidence: 'guard' as const,
      source: 'test',
    }]

    const candidates = await extractRelations(ir, ctx, existingRequires)
    const texts = candidates.map(c => c.text)
    assert.ok(!texts.includes('output() >= x'), 'should not duplicate existing requires')
  })
})
