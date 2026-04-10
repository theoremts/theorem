# theoremts-ts-plugin

TypeScript Language Service Plugin for [Theorem](https://github.com/theoremts/theorem) — shows verification results inline in VS Code.

```bash
npm install -D theoremts-ts-plugin
```

```json
// tsconfig.json
{ "compilerOptions": { "plugins": [{ "name": "theoremts-ts-plugin" }] } }
```

Shows contract violations as squiggly lines, hover tooltips, and Problems panel entries.
