# Talk Timer (LemmaScript)

[![LemmaScript verified](https://img.shields.io/github/actions/workflow/status/midspiral/talktimer-lemmascript/lemmascript.yml?branch=main&label=LemmaScript%20verified)](https://github.com/midspiral/talktimer-lemmascript/actions/workflows/lemmascript.yml)

A verified talk-timer React app. The domain model lives in `src/domain.ts` — annotated TypeScript that is translated to Dafny by [LemmaScript](https://github.com/midspiral/LemmaScript) for formal verification.
Ported from [lemmafit](https://github.com/midspiral/lemmafit) [case study](https://github.com/midspiral/talktimer-lemmafit).

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

Additionally verifies the hand-written behavioral lemmas:

```sh
npm run check:proofs
```

## What has been verified

Plain-English statements with the corresponding lemma name(s) from `src/domain.proofs.dfy` (or `src/domain.dfy` for the LS-generated `*_ensures` lemmas) in parentheses.

### The invariant

The model has an invariant `inv(m)`:
- `currentTime ≥ 0` and `lastLapTime ≥ 0` and `lastLapTime ≤ currentTime` (`ElapsedTimeNonNegative`)
- every recorded lap has `timestamp ≥ 0`, `duration ≥ 0`, `expectedDuration ≥ -1` (`LapDurationsNonNegative`)
- `activeSection` is either `-1` (no active section) or a valid index into `originalTemplate`

`inv` holds at startup (`init_ensures`) and is preserved by every one of the 17 user actions (`apply_ensures` + 17 per-case `apply*_ensures` lemmas). The full Undo/Redo history (`past` / `present` / `future`) preserves a stronger invariant `histInv` saying every snapshot in history is itself valid (`initHistory_ensures`, `doAction_ensures`, `preview_ensures`, `commitFrom_ensures`, `undo_ensures`, `redo_ensures`).

### Lap edits

- Deleting a lap shrinks the list by one (`DeleteLapReducesCount`) and leaves every *other* lap's duration unchanged (`DeletePreservesDurations`).
- Adjusting a duration to `d` sets that lap's duration to `d` and changes nothing else about it (`AdjustOnlyChangesDuration`).
- Toggling a lap's selection flips exactly that one bit (`SelectLapToggles`).
- Moving up at index `i` swaps laps `i-1` and `i` (`MoveUpSwaps`); moving down swaps `i` and `i+1` (`MoveDownSwaps`); both preserve the lap count (`MovePreservesCount`). Moving the first lap up is a no-op (`MoveUpFirstNoEffect`); same for moving the last lap down (`MoveDownLastNoEffect`).
- Adding or removing a tag preserves every other field of the lap — timestamp, duration, section, selected, expected duration (`AddTagPreservesLapData`, `RemoveTagPreservesLapData`). After adding tag `t`, `t` is in the lap's tags (`AddTagAddsTag`); after removing it, `t` is not (`RemoveTagRemovesTag`).

### Practice mode

- **Consume template** pops one entry off the queue (`ConsumeTemplateDecreasesQueue`) and on the *last* lap sets its section (`ConsumeTemplateSetsLabel`), tags (`ConsumeTemplateSetsTags`), selected flag (`ConsumeTemplateSelectsLap`), and expected duration (`ConsumeTemplateSetsExpected`) to match the entry — while leaving the lap's duration (`ConsumeTemplatePreservesDuration`) and timestamp (`ConsumeTemplatePreservesTimestamp`) untouched. Bundled together: `ConsumeTemplateRoundTrip`.
- **Jump to a section by index** sets `activeSection = idx` (`SetActiveSectionUpdatesState`).
- **Apply active section** re-labels only the last lap — section (`ApplyActiveSectionSetsLabel`), selected (`ApplyActiveSectionSelectsLap`), expected (`ApplyActiveSectionSetsExpected`), tags (`ApplyActiveSectionSetsTags`) — without consuming the queue (`ApplyActiveSectionPreservesQueue`) and without touching that lap's duration (`ApplyActiveSectionPreservesDuration`) or timestamp (`ApplyActiveSectionPreservesTimestamp`).

### Reset

- In practice mode, restores the original template back as the lap list (`ResetRestoresOriginalTemplate`), with each lap's section (`ResetRestoresCorrectSections`) and tags (`ResetRestoresCorrectTags`) matching the template entry at the same index, and clears the template queue (`ResetClearsTemplate`).

### Import

- After `ImportLaps`, the original laps are still at their original indices (`ImportPreservesExisting`), and the imported laps are appended at the end (`ImportAppendsToEnd`). Imported laps are clamped to satisfy `inv` (`clampLaps_ensures`).

### Aggregations

- `selectedTotal`, `selectedCount`, `sumByTag`, `countByTag`, `sumBySection`, `countBySection` are all `≥ 0` whenever the laps are valid (`SelectedTotalNonNegative`, `SelectedCountNonNegative`, `SumByTagNonNegative`, `CountByTagNonNegative_`, `SumBySectionNonNegative`, `countBySection_ensures`).
- `sumByTag` / `sumBySection` only ever add the duration of laps that are *both* selected *and* match the tag/section (`SumByTagOnlySelected`, `SumByTagOnlyTagged`, `SumByTagIncludesDuration`, `SumBySectionOnlySelected`, `SumBySectionOnlyMatching`).
- `runningTotals(laps)` has length equal to `laps.length` (`runningTotals_ensures`), starts at 0 (`RunningTotalsFirstIsZero`), and every entry is `≥ 0` when the laps are valid (`RunningTotalsNonNegative`).
- `minBySection` / `maxBySection` return `-1` when there is no matching lap, otherwise a non-negative duration (`minBySection_ensures`, `maxBySection_ensures`).

### Undo / Redo

- After any new action, the redo queue is empty (`DoHasNoRedoBranch`).
- `redo(undo(h)) == h` when `h.past` is non-empty (`UndoRedoRoundTrip`).
- `undo(redo(h)) == h` when `h.future` is non-empty (`RedoUndoRoundTrip`).
- Undo at the beginning of history is a no-op (`UndoAtBeginningIsNoOp`); same for redo at the end (`RedoAtEndIsNoOp`).

### Not verified

The React UI (`src/App.tsx`), time-formatting / parsing helpers (`formatTime` / `parseTime`), Markdown import/export, clipboard side effects, and the wall-clock timer itself.

## Layout

| Path | Purpose |
|------|---------|
| `src/domain.ts` | TypeScript domain logic with `//@` LemmaScript annotations |
| `src/domain.dfy.gen` | Generated Dafny (regeneratable) |
| `src/domain.dfy` | Annotated Dafny (gen + proof additions) |
| `src/domain.proofs.dfy` | Hand-written induction lemmas |
| `src/App.tsx` | React UI; imports `apply`, `init`, helpers directly from `./domain` |
