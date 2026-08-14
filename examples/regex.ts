// Regular expressions as contracts — /re/.test(s) and z.string().regex()
// become Z3 regular-expression membership (str.in_re), integrated with
// sequence lengths.
//
//   theorem verify examples/regex.ts

import { requires, ensures, output } from 'theoremts'
import { z } from 'zod'

// ✓ PROVED — matching ^\d+$ requires at least one character
export function digitsNonEmpty(s: string): number {
  requires(/^\d+$/.test(s))
  ensures(output() >= 1)
  return s.length
}

// ✗ DISPROVED — one digit suffices: counterexample s = "0"
export function digitsTooStrong(s: string): number {
  requires(/^\d+$/.test(s))
  ensures(output() >= 2)
  return s.length
}

// ✓ PROVED — the schema's regex pins the length exactly: {5} means FIVE
const AddressSchema = z.object({
  zip: z.string().regex(/^\d{5}$/),
})
export function zipLength(input: unknown): number {
  const addr = AddressSchema.parse(input)
  ensures(output() === 5)
  return addr.zip.length
}

// JS re.test is SUBSTRING search: without anchors, /\d/ means "contains a
// digit", which still implies non-emptiness. ✓ PROVED
export function containsDigit(s: string): number {
  requires(/\d/.test(s))
  ensures(output() >= 1)
  return s.length
}
