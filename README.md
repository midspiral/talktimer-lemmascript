# Talk Timer (LemmaScript)

A verified talk-timer React app. The domain model lives in `src/domain.ts` — annotated TypeScript that is translated to Dafny by [LemmaScript](https://github.com/midspiral/LemmaScript) for formal verification.

## Setup

```sh
npm install
```

## Develop

```sh
npm run dev
```

## Build

```sh
npm run build
```

## Verify (Dafny backend)

Regenerates `src/domain.dfy.gen` from `src/domain.ts` and verifies `src/domain.dfy`:

```sh
npm run regen
npm run check
```

## Layout

| Path | Purpose |
|------|---------|
| `src/domain.ts` | TypeScript domain logic with `//@` LemmaScript annotations |
| `src/domain.dfy.gen` | Generated Dafny (regeneratable) |
| `src/domain.dfy` | Annotated Dafny (gen + proof additions) |
| `src/domain.proofs.dfy` | Hand-written induction lemmas |
| `src/App.tsx` | React UI; imports `apply`, `init`, helpers directly from `./domain` |
