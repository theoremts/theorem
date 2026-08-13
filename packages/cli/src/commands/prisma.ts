import { readFileSync, writeFileSync, mkdirSync } from 'fs'
import { dirname, join, resolve } from 'path'
import { parsePrismaSchema, generateTheoremSchemas } from '@theoremts/core'

const dim = '\x1b[2m'
const bold = '\x1b[1m'
const green = '\x1b[32m'
const reset = '\x1b[0m'

/**
 * `theorem prisma <schema.prisma>` — generates Theorem-consumable schemas
 * (one Zod-style schema + row type per model) from the database schema.
 * Int/BigInt columns become integer facts, nullability is preserved, and the
 * output plugs straight into verify/scan/plugin via the existing engine.
 */
export function prismaCommand(schemaPath: string, opts: Record<string, unknown>): void {
  const absPath = resolve(process.cwd(), schemaPath)
  const source = readFileSync(absPath, 'utf-8')

  const schema = parsePrismaSchema(source)
  if (schema.models.length === 0) {
    console.log('No models found in', schemaPath)
    return
  }

  const generated = generateTheoremSchemas(schema, schemaPath)

  const outPath = typeof opts['output'] === 'string'
    ? resolve(process.cwd(), opts['output'])
    : join(dirname(absPath), 'theorem-schemas.ts')

  if (opts['dryRun']) {
    console.log(generated)
    console.log(`${dim}(dry run — would write to ${outPath})${reset}`)
    return
  }

  mkdirSync(dirname(outPath), { recursive: true })
  writeFileSync(outPath, generated)

  console.log(`${green}${bold}✓${reset} Generated ${schema.models.length} model schema(s), ${schema.enums.length} enum(s)`)
  console.log(`${dim}  ${outPath}${reset}`)
  console.log(`${dim}  Use: const row = ${schema.models[0]!.name}RowSchema.parse(data)${reset}`)
}
