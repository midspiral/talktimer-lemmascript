// Behavioral proofs for talktimer-lemmascript
// Mirrors the lemma set from talktimer-lemmafit/lemmafit/dafny/Domain.dfy
// (which is a TalkTimer domain refining the Kernel/History abstract module).
//
// Conventions: identifiers map TS-case → original PascalCase.

include "domain.dfy"

import opened Std.Collections.Seq

// ════════════════════════════════════════════════════════════════════════════
// Core requirement lemmas (already implied by inv-preservation, but spelled
// out here as standalone facts to match the original Domain.dfy lemma set).
// ════════════════════════════════════════════════════════════════════════════

// [verified] Timer elapsed time is always non-negative
lemma ElapsedTimeNonNegative(m: Model)
  requires inv(m)
  ensures m.currentTime >= 0
{}

// [verified] All lap durations are non-negative
lemma LapDurationsNonNegative(m: Model)
  requires inv(m)
  ensures forall i | 0 <= i < |m.laps| :: m.laps[i].duration >= 0
{}

// ════════════════════════════════════════════════════════════════════════════
// Basic apply behavioral lemmas
// ════════════════════════════════════════════════════════════════════════════

// [verified] Deleting a lap reduces the count by 1
lemma DeleteLapReducesCount(m: Model, idx: int)
  requires inv(m)
  requires 0 <= idx < |m.laps|
  ensures |applyDeleteLap(m, idx).laps| == |m.laps| - 1
{}

// [verified] Deleting a lap preserves other laps' durations
lemma DeletePreservesDurations(m: Model, idx: int)
  requires inv(m)
  requires 0 <= idx < |m.laps|
  ensures forall i | 0 <= i < idx ::
    applyDeleteLap(m, idx).laps[i].duration == m.laps[i].duration
  ensures forall i | idx < i < |m.laps| ::
    applyDeleteLap(m, idx).laps[i - 1].duration == m.laps[i].duration
{}

// [verified] Adjusting duration only changes that lap (duration, section, selected unchanged in other fields)
lemma AdjustOnlyChangesDuration(m: Model, idx: int, dur: int)
  requires inv(m)
  requires 0 <= idx < |m.laps|
  requires dur >= 0
  ensures applyAdjustDuration(m, idx, dur).laps[idx].duration == dur
  ensures applyAdjustDuration(m, idx, dur).laps[idx].section == m.laps[idx].section
  ensures applyAdjustDuration(m, idx, dur).laps[idx].selected == m.laps[idx].selected
{}

// [verified] Selecting a lap toggles its selected state
lemma SelectLapToggles(m: Model, idx: int)
  requires inv(m)
  requires 0 <= idx < |m.laps|
  ensures applySelectLap(m, idx).laps[idx].selected == !m.laps[idx].selected
{}

// ════════════════════════════════════════════════════════════════════════════
// Lap reordering lemmas
// ════════════════════════════════════════════════════════════════════════════

// [verified] Moving a lap up swaps it with the previous lap
lemma MoveUpSwaps(m: Model, idx: int)
  requires inv(m)
  requires 1 <= idx < |m.laps|
  ensures applyMoveUp(m, idx).laps[idx - 1] == m.laps[idx]
  ensures applyMoveUp(m, idx).laps[idx] == m.laps[idx - 1]
{}

// [verified] Moving a lap down swaps it with the next lap
lemma MoveDownSwaps(m: Model, idx: int)
  requires inv(m)
  requires 0 <= idx < |m.laps| - 1
  ensures applyMoveDown(m, idx).laps[idx] == m.laps[idx + 1]
  ensures applyMoveDown(m, idx).laps[idx + 1] == m.laps[idx]
{}

// [verified] Moving the first lap up has no effect
lemma MoveUpFirstNoEffect(m: Model)
  requires inv(m)
  requires |m.laps| > 0
  ensures applyMoveUp(m, 0) == m
{}

// [verified] Moving the last lap down has no effect
lemma MoveDownLastNoEffect(m: Model)
  requires inv(m)
  requires |m.laps| > 0
  ensures applyMoveDown(m, |m.laps| - 1) == m
{}

// [verified] Moving preserves lap count
lemma MovePreservesCount(m: Model, idx: int)
  requires inv(m)
  ensures |applyMoveUp(m, idx).laps| == |m.laps|
  ensures |applyMoveDown(m, idx).laps| == |m.laps|
{}

// ════════════════════════════════════════════════════════════════════════════
// Tagging lemmas
// ════════════════════════════════════════════════════════════════════════════

// [verified] Adding a tag preserves other lap data
lemma AddTagPreservesLapData(m: Model, idx: int, tag: string)
  requires inv(m)
  requires 0 <= idx < |m.laps|
  ensures applyAddTag(m, idx, tag).laps[idx].timestamp == m.laps[idx].timestamp
  ensures applyAddTag(m, idx, tag).laps[idx].duration == m.laps[idx].duration
  ensures applyAddTag(m, idx, tag).laps[idx].section == m.laps[idx].section
  ensures applyAddTag(m, idx, tag).laps[idx].selected == m.laps[idx].selected
  ensures applyAddTag(m, idx, tag).laps[idx].expectedDuration == m.laps[idx].expectedDuration
{}

// [verified] Removing a tag preserves other lap data
lemma RemoveTagPreservesLapData(m: Model, idx: int, tag: string)
  requires inv(m)
  requires 0 <= idx < |m.laps|
  ensures applyRemoveTag(m, idx, tag).laps[idx].timestamp == m.laps[idx].timestamp
  ensures applyRemoveTag(m, idx, tag).laps[idx].duration == m.laps[idx].duration
  ensures applyRemoveTag(m, idx, tag).laps[idx].section == m.laps[idx].section
  ensures applyRemoveTag(m, idx, tag).laps[idx].selected == m.laps[idx].selected
  ensures applyRemoveTag(m, idx, tag).laps[idx].expectedDuration == m.laps[idx].expectedDuration
{}

// [verified] Added tag is present in the lap's tags
lemma AddTagAddsTag(m: Model, idx: int, tag: string)
  requires inv(m)
  requires 0 <= idx < |m.laps|
  ensures tag in applyAddTag(m, idx, tag).laps[idx].tags
{
  addTagToSeq_ensures(m.laps[idx].tags, tag);
}

// [verified] Removed tag is not present in the lap's tags
lemma RemoveTagRemovesTag(m: Model, idx: int, tag: string)
  requires inv(m)
  requires 0 <= idx < |m.laps|
  ensures !(tag in applyRemoveTag(m, idx, tag).laps[idx].tags)
{
  removeTagFromSeq_ensures(m.laps[idx].tags, tag);
}

// ════════════════════════════════════════════════════════════════════════════
// Practice mode lemmas
// ════════════════════════════════════════════════════════════════════════════

// [verified] Consuming template sets the lap's section label
lemma ConsumeTemplateSetsLabel(m: Model)
  requires inv(m)
  requires |m.template| > 0
  requires |m.laps| > 0
  ensures applyConsumeTemplate(m).laps[|m.laps| - 1].section == m.template[0].section
{}

// [verified] Consuming template sets the lap's expected duration (when entry has one)
lemma ConsumeTemplateSetsExpected(m: Model)
  requires inv(m)
  requires |m.template| > 0
  requires |m.laps| > 0
  requires m.template[0].expectedDuration >= 0
  ensures applyConsumeTemplate(m).laps[|m.laps| - 1].expectedDuration == m.template[0].expectedDuration
{}

// [verified] Consuming template sets the lap's tags
lemma ConsumeTemplateSetsTags(m: Model)
  requires inv(m)
  requires |m.template| > 0
  requires |m.laps| > 0
  ensures applyConsumeTemplate(m).laps[|m.laps| - 1].tags == m.template[0].tags
{}

// [verified] Consuming template selects the lap
lemma ConsumeTemplateSelectsLap(m: Model)
  requires inv(m)
  requires |m.template| > 0
  requires |m.laps| > 0
  ensures applyConsumeTemplate(m).laps[|m.laps| - 1].selected == true
{}

// [verified] Template queue length decreases by one after consumption
lemma ConsumeTemplateDecreasesQueue(m: Model)
  requires inv(m)
  requires |m.template| > 0
  requires |m.laps| > 0
  ensures |applyConsumeTemplate(m).template| == |m.template| - 1
{}

// [verified] ConsumeTemplate preserves original lap duration
lemma ConsumeTemplatePreservesDuration(m: Model)
  requires inv(m)
  requires |m.template| > 0
  requires |m.laps| > 0
  ensures applyConsumeTemplate(m).laps[|m.laps| - 1].duration == m.laps[|m.laps| - 1].duration
{}

// [verified] ConsumeTemplate preserves original lap timestamp
lemma ConsumeTemplatePreservesTimestamp(m: Model)
  requires inv(m)
  requires |m.template| > 0
  requires |m.laps| > 0
  ensures applyConsumeTemplate(m).laps[|m.laps| - 1].timestamp == m.laps[|m.laps| - 1].timestamp
{}

// [verified] ConsumeTemplate round-trip: sets all fields from template entry
lemma ConsumeTemplateRoundTrip(m: Model)
  requires inv(m)
  requires |m.template| > 0
  requires |m.laps| > 0
  ensures var result := applyConsumeTemplate(m);
          var idx := |m.laps| - 1;
          var entry := m.template[0];
          result.laps[idx].section == entry.section &&
          result.laps[idx].selected == true &&
          result.laps[idx].tags == entry.tags &&
          (entry.expectedDuration >= 0 ==> result.laps[idx].expectedDuration == entry.expectedDuration)
{}

// ════════════════════════════════════════════════════════════════════════════
// Active section lemmas
// ════════════════════════════════════════════════════════════════════════════

// [verified] SetActiveSection updates model state to selected index
lemma SetActiveSectionUpdatesState(m: Model, idx: int)
  requires inv(m)
  requires idx >= -1 && (idx == -1 || idx < |m.originalTemplate|)
  ensures applySetActiveSection(m, idx).activeSection == idx
{}

// [verified] ApplyActiveSection labels last lap from active section entry
lemma ApplyActiveSectionSetsLabel(m: Model)
  requires inv(m)
  requires m.activeSection >= 0 && m.activeSection < |m.originalTemplate|
  requires |m.laps| > 0
  ensures applyApplyActiveSection(m).laps[|m.laps| - 1].section == m.originalTemplate[m.activeSection].section
{}

// [verified] ApplyActiveSection sets the lap to selected
lemma ApplyActiveSectionSelectsLap(m: Model)
  requires inv(m)
  requires m.activeSection >= 0 && m.activeSection < |m.originalTemplate|
  requires |m.laps| > 0
  ensures applyApplyActiveSection(m).laps[|m.laps| - 1].selected == true
{}

// [verified] ApplyActiveSection sets expected duration from template
lemma ApplyActiveSectionSetsExpected(m: Model)
  requires inv(m)
  requires m.activeSection >= 0 && m.activeSection < |m.originalTemplate|
  requires |m.laps| > 0
  requires m.originalTemplate[m.activeSection].expectedDuration >= 0
  ensures applyApplyActiveSection(m).laps[|m.laps| - 1].expectedDuration == m.originalTemplate[m.activeSection].expectedDuration
{}

// [verified] ApplyActiveSection sets tags from template
lemma ApplyActiveSectionSetsTags(m: Model)
  requires inv(m)
  requires m.activeSection >= 0 && m.activeSection < |m.originalTemplate|
  requires |m.laps| > 0
  ensures applyApplyActiveSection(m).laps[|m.laps| - 1].tags == m.originalTemplate[m.activeSection].tags
{}

// [verified] ApplyActiveSection preserves original lap duration
lemma ApplyActiveSectionPreservesDuration(m: Model)
  requires inv(m)
  requires m.activeSection >= 0 && m.activeSection < |m.originalTemplate|
  requires |m.laps| > 0
  ensures applyApplyActiveSection(m).laps[|m.laps| - 1].duration == m.laps[|m.laps| - 1].duration
{}

// [verified] ApplyActiveSection preserves original lap timestamp
lemma ApplyActiveSectionPreservesTimestamp(m: Model)
  requires inv(m)
  requires m.activeSection >= 0 && m.activeSection < |m.originalTemplate|
  requires |m.laps| > 0
  ensures applyApplyActiveSection(m).laps[|m.laps| - 1].timestamp == m.laps[|m.laps| - 1].timestamp
{}

// [verified] ApplyActiveSection does not consume template queue
lemma ApplyActiveSectionPreservesQueue(m: Model)
  requires inv(m)
  requires m.activeSection >= 0 && m.activeSection < |m.originalTemplate|
  requires |m.laps| > 0
  ensures |applyApplyActiveSection(m).template| == |m.template|
{}

// ════════════════════════════════════════════════════════════════════════════
// Import lemmas
// ════════════════════════════════════════════════════════════════════════════

// [verified] Importing laps preserves existing laps
lemma ImportPreservesExisting(m: Model, laps: seq<Lap>)
  requires inv(m)
  ensures forall i | 0 <= i < |m.laps| ::
    applyImportLaps(m, laps).laps[i] == m.laps[i]
{
  forall i | 0 <= i < |m.laps|
    ensures applyImportLaps(m, laps).laps[i] == m.laps[i]
  {
    assert (m.laps + clampLaps(laps))[i] == m.laps[i];
  }
}

// [verified] Import appends laps to the end
lemma ImportAppendsToEnd(m: Model, laps: seq<Lap>)
  requires inv(m)
  ensures |applyImportLaps(m, laps).laps| == |m.laps| + |clampLaps(laps)|
{}

// ════════════════════════════════════════════════════════════════════════════
// Reset from practice mode lemmas
// ════════════════════════════════════════════════════════════════════════════

// [verified] Reset in practice mode restores original template as laps
lemma ResetRestoresOriginalTemplate(m: Model)
  requires inv(m)
  requires |m.originalTemplate| > 0
  ensures |applyReset(m).laps| == |m.originalTemplate|
  ensures applyReset(m).laps == templateToLaps(m.originalTemplate)
{
  templateToLaps_ensures(m.originalTemplate);
}

// [verified] Reset in practice mode clears template (exits practice mode)
lemma ResetClearsTemplate(m: Model)
  requires inv(m)
  requires |m.originalTemplate| > 0
  ensures |applyReset(m).template| == 0
  ensures |applyReset(m).originalTemplate| == 0
{}

// Helper: templateToLaps preserves section at each index
lemma TemplateToLapsPreservesSection(template: seq<TemplateEntry>, i: int)
  requires 0 <= i < |template|
  ensures |templateToLaps(template)| == |template|
  ensures templateToLaps(template)[i].section == template[i].section
  decreases |template|
{
  templateToLaps_ensures(template);
  if i == 0 {
  } else {
    TemplateToLapsPreservesSection(template[1..], i - 1);
  }
}

// Helper: templateToLaps preserves tags at each index
lemma TemplateToLapsPreservesTags(template: seq<TemplateEntry>, i: int)
  requires 0 <= i < |template|
  ensures |templateToLaps(template)| == |template|
  ensures templateToLaps(template)[i].tags == template[i].tags
  decreases |template|
{
  templateToLaps_ensures(template);
  if i == 0 {
  } else {
    TemplateToLapsPreservesTags(template[1..], i - 1);
  }
}

// [verified] Reset in practice mode: each restored lap has correct section from original template
lemma ResetRestoresCorrectSections(m: Model, i: int)
  requires inv(m)
  requires |m.originalTemplate| > 0
  requires 0 <= i < |m.originalTemplate|
  ensures var r := applyReset(m);
          |r.laps| == |m.originalTemplate| && r.laps[i].section == m.originalTemplate[i].section
{
  templateToLaps_ensures(m.originalTemplate);
  TemplateToLapsPreservesSection(m.originalTemplate, i);
}

// [verified] Reset in practice mode: each restored lap has correct tags from original template
lemma ResetRestoresCorrectTags(m: Model, i: int)
  requires inv(m)
  requires |m.originalTemplate| > 0
  requires 0 <= i < |m.originalTemplate|
  ensures var r := applyReset(m);
          |r.laps| == |m.originalTemplate| && r.laps[i].tags == m.originalTemplate[i].tags
{
  templateToLaps_ensures(m.originalTemplate);
  TemplateToLapsPreservesTags(m.originalTemplate, i);
}

// ════════════════════════════════════════════════════════════════════════════
// Selected total / count lemmas
// ════════════════════════════════════════════════════════════════════════════

lemma SelectedDurationsNonNegative(laps: seq<Lap>)
  requires lapsValid(laps)
  ensures forall i | 0 <= i < |selectedDurations(laps)| :: selectedDurations(laps)[i] >= 0
  decreases |laps|
{
  if |laps| == 0 {
  } else {
    SelectedDurationsNonNegative(laps[1..]);
  }
}

lemma SumFromNonNegative(s: seq<int>, i: nat)
  requires i <= |s|
  requires forall j | i <= j < |s| :: s[j] >= 0
  ensures sumFrom(s, i) >= 0
  decreases |s| - i
{
  if i == |s| {
  } else {
    SumFromNonNegative(s, i + 1);
  }
}

// [verified] Selected count is non-negative
lemma SelectedCountNonNegative(laps: seq<Lap>)
  ensures selectedCount(laps) >= 0
{}

// [verified] Selected total is non-negative when all durations are non-negative
lemma SelectedTotalNonNegative(laps: seq<Lap>)
  requires lapsValid(laps)
  ensures selectedTotal(laps) >= 0
{
  SelectedDurationsNonNegative(laps);
  SumFromNonNegative(selectedDurations(laps), 0);
}

// ════════════════════════════════════════════════════════════════════════════
// Tag total lemmas
// ════════════════════════════════════════════════════════════════════════════

// [verified] sumByTag is non-negative when all durations are non-negative
lemma SumByTagNonNegative(laps: seq<Lap>, tag: string)
  requires lapsValid(laps)
  ensures sumByTag(laps, tag) >= 0
  decreases |laps|
{
  if |laps| == 0 {
  } else {
    SumByTagNonNegative(laps[1..], tag);
  }
}

// [verified] sumByTag only counts selected laps
lemma SumByTagOnlySelected(laps: seq<Lap>, tag: string)
  requires |laps| > 0
  requires !laps[0].selected
  ensures sumByTag(laps, tag) == sumByTag(laps[1..], tag)
{}

// [verified] sumByTag only counts laps with the tag
lemma SumByTagOnlyTagged(laps: seq<Lap>, tag: string)
  requires |laps| > 0
  requires laps[0].selected
  requires !lapHasTag(laps[0], tag)
  ensures sumByTag(laps, tag) == sumByTag(laps[1..], tag)
{}

// [verified] sumByTag includes duration when lap is selected and has tag
lemma SumByTagIncludesDuration(laps: seq<Lap>, tag: string)
  requires |laps| > 0
  requires laps[0].selected
  requires lapHasTag(laps[0], tag)
  ensures sumByTag(laps, tag) == laps[0].duration + sumByTag(laps[1..], tag)
{}

// [verified] countByTag is non-negative (already in domain.dfy via _ensures, restated)
lemma CountByTagNonNegative_(laps: seq<Lap>, tag: string)
  ensures countByTag(laps, tag) >= 0
{
  countByTag_ensures(laps, tag);
}

// ════════════════════════════════════════════════════════════════════════════
// Section aggregation lemmas
// ════════════════════════════════════════════════════════════════════════════

// [verified] sumBySection is non-negative
lemma SumBySectionNonNegative(laps: seq<Lap>, section: string)
  requires lapsValid(laps)
  ensures sumBySection(laps, section) >= 0
  decreases |laps|
{
  if |laps| == 0 {
  } else {
    SumBySectionNonNegative(laps[1..], section);
  }
}

// [verified] sumBySection only counts selected laps
lemma SumBySectionOnlySelected(laps: seq<Lap>, section: string)
  requires |laps| > 0
  requires !laps[0].selected
  ensures sumBySection(laps, section) == sumBySection(laps[1..], section)
{}

// [verified] sumBySection only counts laps with the section
lemma SumBySectionOnlyMatching(laps: seq<Lap>, section: string)
  requires |laps| > 0
  requires laps[0].selected
  requires laps[0].section != section
  ensures sumBySection(laps, section) == sumBySection(laps[1..], section)
{}

// ════════════════════════════════════════════════════════════════════════════
// Running totals
// ════════════════════════════════════════════════════════════════════════════

// [verified] First running total is always zero
lemma RunningTotalsFirstIsZero(laps: seq<Lap>)
  requires |laps| > 0
  ensures runningTotals(laps)[0] == 0
{}

lemma RunningTotalsHelperNonNegative(laps: seq<Lap>, acc: int)
  requires lapsValid(laps)
  requires acc >= 0
  ensures forall i | 0 <= i < |runningTotalsHelper(laps, acc)| :: runningTotalsHelper(laps, acc)[i] >= 0
  decreases |laps|
{
  if |laps| == 0 {
  } else {
    var newAcc := if laps[0].selected then acc + laps[0].duration else acc;
    RunningTotalsHelperNonNegative(laps[1..], newAcc);
  }
}

// [verified] Running totals are non-negative when all durations are non-negative
lemma RunningTotalsNonNegative(laps: seq<Lap>)
  requires lapsValid(laps)
  ensures forall i | 0 <= i < |runningTotals(laps)| :: runningTotals(laps)[i] >= 0
{
  RunningTotalsHelperNonNegative(laps, 0);
}

// ════════════════════════════════════════════════════════════════════════════
// History / Undo / Redo (Kernel-pattern from original Replay.dfy)
//
// The `History` datatype, `histInv` predicate, and the six operations
// (`initHistory`, `doAction`, `preview`, `commitFrom`, `undo`, `redo`)
// all come from the verified `domain.dfy` (generated from `domain.ts`).
// `histInv` preservation by each op is already verified there.
// The lemmas below add behavioral / round-trip facts.
// ════════════════════════════════════════════════════════════════════════════

// [verified] InitHistory satisfies the invariant
lemma InitHistorySatisfiesInv()
  ensures histInv(initHistory())
{}

// [verified] Undo preserves the history invariant (restates initHistory_ensures from LS-gen)
lemma UndoPreservesHistInv(h: History)
  requires histInv(h)
  ensures histInv(undo(h))
{
  undo_ensures(h);
}

// [verified] Redo preserves the history invariant
lemma RedoPreservesHistInv(h: History)
  requires histInv(h)
  ensures histInv(redo(h))
{
  redo_ensures(h);
}

// [verified] Do preserves the history invariant
lemma DoPreservesHistInv(h: History, a: Action)
  requires histInv(h)
  ensures histInv(doAction(h, a))
{
  doAction_ensures(h, a);
}

// [verified] Preview preserves the history invariant
lemma PreviewPreservesHistInv(h: History, a: Action)
  requires histInv(h)
  ensures histInv(preview(h, a))
{
  preview_ensures(h, a);
}

// [verified] CommitFrom preserves the history invariant
lemma CommitFromPreservesHistInv(h: History, baseline: Model)
  requires histInv(h)
  requires inv(baseline)
  ensures histInv(commitFrom(h, baseline))
{
  commitFrom_ensures(h, baseline);
}

// [verified] After a new action, there is no redo branch (linear undo)
lemma DoHasNoRedoBranch(h: History, a: Action)
  requires histInv(h)
  ensures var h2 := doAction(h, a); histInv(h2) && redo(h2) == h2
{
  doAction_ensures(h, a);
}

// [verified] Round-trip: undo then redo restores the same history
lemma UndoRedoRoundTrip(h: History)
  requires histInv(h)
  requires |h.past| > 0
  ensures redo(undo(h)) == h
{
  undo_ensures(h);
}

// [verified] Round-trip: redo then undo restores the same history
lemma RedoUndoRoundTrip(h: History)
  requires histInv(h)
  requires |h.future| > 0
  ensures undo(redo(h)) == h
{
  redo_ensures(h);
}

// [verified] Undo at beginning is a no-op
lemma UndoAtBeginningIsNoOp(h: History)
  requires histInv(h)
  requires |h.past| == 0
  ensures undo(h) == h
{}

// [verified] Redo at end is a no-op
lemma RedoAtEndIsNoOp(h: History)
  requires histInv(h)
  requires |h.future| == 0
  ensures redo(h) == h
{}
