# theoremts-plugins

Bundler plugins for [Theorem](https://github.com/theoremts/theorem) — strip contracts at build time for zero runtime overhead.

```typescript
// vite.config.ts
import { theoremVite } from 'theoremts-plugins/vite'
export default { plugins: [theoremVite()] }
```

Also available: `theoremts-plugins/esbuild`, `theoremts-plugins/tsup`.
