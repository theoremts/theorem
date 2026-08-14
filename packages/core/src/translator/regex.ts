import type { Z3Context } from '../solver/context.js'

/**
 * Translates a JavaScript regex literal into a Z3 regular expression (Re).
 *
 * Supported subset: literal characters, escapes (\d \D \w \W \s \S \n \t \r
 * and escaped punctuation), character classes with ranges and negation,
 * groups (capturing and non-capturing — capture semantics are irrelevant to
 * matching), alternation, quantifiers (* + ? {n} {n,} {n,m}, lazy variants
 * match the same language), the dot, and ^/$ anchors at the pattern edges.
 *
 * JS `re.test(s)` is a SUBSTRING search: without anchors the pattern is
 * wrapped in Full (any string) on the unanchored sides, so InRe matches
 * .test() semantics exactly.
 *
 * Negated classes and the dot use AllChar.diff(...) — correct over the full
 * unicode alphabet, not an ASCII enumeration.
 *
 * Unsupported constructs (backreferences, lookaround, unicode property
 * escapes, mid-pattern anchors, the i/m/s flags) return null — the caller
 * must DROP the constraint, never approximate it.
 */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Re = any

export function jsRegexToRe(pattern: string, flags: string, ctx: Z3Context): Re | null {
  // Flags that change matching semantics in ways we don't model
  if (/[imsuy]/.test(flags)) return null

  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const anyCtx = ctx as any
  /* eslint-disable @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-assignment, @typescript-eslint/no-unsafe-return */
  const reSort = anyCtx.Re.sort(anyCtx.String.sort())
  const lit = (s: string): Re => anyCtx.Re.toRe(s)
  const range = (lo: string, hi: string): Re => anyCtx.Range(lo, hi)
  const allChar = (): Re => anyCtx.AllChar(reSort)
  const full = (): Re => anyCtx.Full(reSort)
  const union = (rs: Re[]): Re => rs.reduce((a: Re, b: Re) => a.union(b))

  const DIGIT = (): Re => range('0', '9')
  const WORD = (): Re => union([range('a', 'z'), range('A', 'Z'), range('0', '9'), lit('_')])
  const SPACE = (): Re => union([lit(' '), lit('\t'), lit('\n'), lit('\r'), lit('\f'), lit('\v')])

  let pos = 0
  let failed = false
  const fail = (): null => { failed = true; return null }
  const peek = (): string => pattern[pos] ?? ''
  const next = (): string => pattern[pos++] ?? ''

  /** One escape sequence (after the backslash) as a char-class Re, or a literal string. */
  function escapeAtom(): Re | null {
    const c = next()
    switch (c) {
      case 'd': return DIGIT()
      case 'D': return allChar().diff(DIGIT())
      case 'w': return WORD()
      case 'W': return allChar().diff(WORD())
      case 's': return SPACE()
      case 'S': return allChar().diff(SPACE())
      case 'n': return lit('\n')
      case 't': return lit('\t')
      case 'r': return lit('\r')
      case 'f': return lit('\f')
      case 'v': return lit('\v')
      case '0': return lit('\0')
      case 'b': case 'B': return fail()          // word boundaries: not a language
      case 'p': case 'P': case 'k': return fail() // property escapes, backrefs
      case '': return fail()
      default:
        if (/[1-9]/.test(c)) return fail()        // backreference
        return lit(c)                             // escaped punctuation: \. \+ \( ...
    }
  }

  /** [...] character class. */
  function charClass(): Re | null {
    const negated = peek() === '^'
    if (negated) pos++
    const members: Re[] = []
    let first = true
    while (peek() !== ']' || first) {
      if (pos >= pattern.length) return fail()
      first = false
      let ch = next()
      if (ch === '\\') {
        const e = escapeAtom()
        if (e === null) return null
        // Range endpoints must be single literals; class escapes stand alone
        if (peek() === '-' && pattern[pos + 1] !== ']') return fail()
        members.push(e)
        continue
      }
      if (peek() === '-' && pattern[pos + 1] !== ']' && pattern[pos + 1] !== undefined) {
        pos++  // consume '-'
        let hi = next()
        if (hi === '\\') {
          const e = next()
          if (!/[nrtfv]/.test(e)) {
            if (/[dDwWsS]/.test(e)) return fail()
            hi = e
          } else {
            hi = { n: '\n', r: '\r', t: '\t', f: '\f', v: '\v' }[e]!
          }
        }
        members.push(range(ch, hi))
        continue
      }
      members.push(lit(ch))
    }
    pos++  // consume ']'
    if (members.length === 0) return fail()
    const cls = union(members)
    return negated ? allChar().diff(cls) : cls
  }

  /** atom: char, dot, escape, class, or group. */
  function atom(): Re | null {
    const c = peek()
    if (c === '(') {
      pos++
      if (peek() === '?') {
        pos++
        const k = next()
        if (k !== ':') return fail()  // lookaround / named groups
      }
      const inner = alternation()
      if (inner === null || next() !== ')') return fail()
      return inner
    }
    if (c === '[') { pos++; return charClass() }
    if (c === '\\') { pos++; return escapeAtom() }
    if (c === '.') { pos++; return allChar().diff(lit('\n')) }
    if (c === '^' || c === '$') return fail()  // mid-pattern anchor
    if (c === ')' || c === '|' || c === '') return null  // end of sequence
    if (c === '*' || c === '+' || c === '?' || c === '{') return fail()
    pos++
    return lit(c)
  }

  /** atom with optional quantifier. */
  function quantified(): Re | null {
    const a = atom()
    if (a === null) return failed ? null : null
    let result: Re = a
    const q = peek()
    if (q === '*') { pos++; result = a.star() }
    else if (q === '+') { pos++; result = a.plus() }
    else if (q === '?') { pos++; result = a.option() }
    else if (q === '{') {
      const m = /^\{(\d+)(,(\d*)?)?\}/.exec(pattern.slice(pos))
      if (m === null) return fail()
      pos += m[0].length
      const lo = parseInt(m[1]!, 10)
      if (m[2] === undefined) result = a.loop(lo, lo)                        // {n}
      else if (m[3] === undefined || m[3] === '') result = a.loop(lo)         // {n,}
      else {
        const hi = parseInt(m[3], 10)
        if (hi < lo) return fail()
        result = a.loop(lo, hi)                                              // {n,m}
      }
    }
    if (peek() === '?') pos++  // lazy quantifier: same language
    return result
  }

  /** sequence of quantified atoms. */
  function sequence(): Re | null {
    const parts: Re[] = []
    for (;;) {
      const before = pos
      const item = quantified()
      if (item === null) {
        if (failed) return null
        if (pos !== before) return null
        break
      }
      parts.push(item)
    }
    if (parts.length === 0) return lit('')  // empty branch matches ε
    return parts.reduce((a: Re, b: Re) => a.concat(b))
  }

  function alternation(): Re | null {
    const branches: Re[] = []
    for (;;) {
      const b = sequence()
      if (b === null) return null
      branches.push(b)
      if (peek() === '|') { pos++; continue }
      break
    }
    return union(branches)
  }

  // Edge anchors: ^...$ = full match; missing side = substring on that side
  let anchoredStart = false
  let anchoredEnd = false
  let body = pattern
  if (body.startsWith('^')) { anchoredStart = true; body = body.slice(1) }
  if (body.endsWith('$') && !body.endsWith('\\$')) { anchoredEnd = true; body = body.slice(0, -1) }

  pattern = body
  pos = 0
  const core = alternation()
  if (core === null || failed || pos !== pattern.length) return null

  let result: Re = core
  if (!anchoredStart) result = full().concat(result)
  if (!anchoredEnd) result = result.concat(full())
  return result
  /* eslint-enable @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-assignment, @typescript-eslint/no-unsafe-return */
}
