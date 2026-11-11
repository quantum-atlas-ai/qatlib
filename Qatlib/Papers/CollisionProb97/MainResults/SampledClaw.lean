/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.SampledTableMemory
import Qatlib.Papers.CollisionProb97.MainResults.ClawExecution
import Qatlib.Papers.CollisionProb97.MainResults.OraclePairLaw

/-!
# Claw finding with a sampled distinct-image table

This module composes distinct-image sampling for `F` with verified search for matching
`G`-values. The law `run` returns a claw and records the two oracle costs separately,
implementing the regular claw construction of [BrassardHoyerTapp1998Collision].

The results compute the expected `F` cost as a sum of sampling stage means and bound the
expected `G` cost using the exact marked-set cardinality `k * rG`.

## Main statements

* `run_correct`: Every supported output of the sampled claw algorithm is a pair `(s, x)`
  satisfying `F s = G x` [BrassardHoyerTapp1998Collision].
* `run_Fbounds`: Under the half-image constraint, the expected number of `F` evaluations lies
  between `k` and `2 * k`, as in Theorem 5 of [BrassardHoyerTapp1998Collision].
* `run_Gbound`: The expected number of `G` evaluations is at most `(1 + 4 * SourcePhaseConstant
  l) * sqrt (|X| / (k * rG))`, as in Theorem 5 of [BrassardHoyerTapp1998Collision].

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal Classical
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
namespace Qatlib.Papers.CollisionProb97.MainResults.SampledClaw
variable {S X R : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [AddCommGroup R] [Fintype R] [DecidableEq R]

omit [Fintype S] [DecidableEq S] [Nonempty S] [Nonempty X] [AddCommGroup R] in

/-- A table of `k` distinct `F`-values marks exactly `k * r` inputs for a surjective `r`-to-one
function `G`. -/
theorem marked_card (F : S → R) (G : X → R) (r : ℕ) (hG : RToOne G r)
    (honto : Finset.univ.image G = Finset.univ) {k : ℕ} (s : DistinctImageTable.Records F k) :
    (ActualSearch.marked G ∅ (ReadOnlyTable.values (SampledTableMemory.memory s))).card = k*r := by
  rw [ClawExecution.marked_card G r hG _ (by rw [honto]; exact Finset.subset_univ _),
    SampledTableMemory.memory_card]

omit [Fintype S] [DecidableEq S] [Nonempty S] [Nonempty X] [AddCommGroup R] in

/-- A positive-size distinct-image table gives a nonempty marked set for a surjective function
with positive regular fiber size. -/
theorem marked_pos (F : S → R) (G : X → R) (r : ℕ) (hr : 0 < r) (hG : RToOne G r)
    (honto : Finset.univ.image G = Finset.univ) {k : ℕ} (hk : 0 < k)
    (s : DistinctImageTable.Records F k) :
    0 < (ActualSearch.marked G ∅ (ReadOnlyTable.values (SampledTableMemory.memory s))).card := by
  rw [marked_card F G r hG honto s]
  exact Nat.mul_pos hk hr

/-- The claw-finding law that builds a sampled distinct-image table for `F` and searches `G`,
retaining the two evaluation costs separately. -/
def run (F : S → R) (rF : ℕ) (hrF : 0 < rF) (hF : RToOne F rF)
    (G : X → R) (rG : ℕ) (hrG : 0 < rG) (hG : RToOne G rG)
    (honto : Finset.univ.image G = Finset.univ)
    (k : ℕ) (hk : 0 < k) (hhalf : 2*k ≤ (Finset.univ.image F).card)
    (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) : PMF (Option (S × X) × (ℕ × ℕ)) :=
  OraclePairLaw.join (DistinctImageTable.build F rF hrF hF k hhalf) fun s =>
    ClawExecution.search G (SampledTableMemory.memory s) l hl hl4 (marked_pos F G rG hrG hG honto hk s)

/-- Every supported output of the sampled claw algorithm is a pair `(s, x)` satisfying `F s = G
x` [BrassardHoyerTapp1998Collision]. -/
theorem run_correct (F : S → R) (rF : ℕ) (hrF : 0 < rF) (hF : RToOne F rF)
    (G : X → R) (rG : ℕ) (hrG : 0 < rG) (hG : RToOne G rG)
    (honto : Finset.univ.image G = Finset.univ)
    (k : ℕ) (hk : 0 < k) (hhalf : 2*k ≤ (Finset.univ.image F).card)
    (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (out : Option (S × X)) (a b : ℕ)
    (hm : run F rF hrF hF G rG hrG hG honto k hk hhalf l hl hl4 (out,(a,b)) ≠ 0) :
    ∃ s x, out = some (s,x) ∧ F s = G x := by
  obtain ⟨s,_,hs⟩ := OraclePairLaw.support _ _ out a b hm
  exact ClawExecution.search_correct F G (SampledTableMemory.memory s)
    (SampledTableMemory.memory_accurate s) l hl hl4 _ out b hs

/-- The expected number of `F` evaluations is the sum of `DistinctImageTable.stageMean F j` over
`j < k` [BrassardHoyerTapp1998Collision]. -/
theorem run_Fmean (F : S → R) (rF : ℕ) (hrF : 0 < rF) (hF : RToOne F rF)
    (G : X → R) (rG : ℕ) (hrG : 0 < rG) (hG : RToOne G rG)
    (honto : Finset.univ.image G = Finset.univ)
    (k : ℕ) (hk : 0 < k) (hhalf : 2*k ≤ (Finset.univ.image F).card)
    (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) :
    expectation (run F rF hrF hF G rG hrG hG honto k hk hhalf l hl hl4)
      (fun z => (z.2.1 : ℝ≥0∞)) = ∑ j ∈ Finset.range k, DistinctImageTable.stageMean F j := by
  rw [run, OraclePairLaw.first_mean, DistinctImageTable.build_expected]

/-- Under the half-image constraint, the expected number of `F` evaluations lies between `k` and
`2 * k`, as in Theorem 5 of [BrassardHoyerTapp1998Collision]. -/
theorem run_Fbounds (F : S → R) (rF : ℕ) (hrF : 0 < rF) (hF : RToOne F rF)
    (G : X → R) (rG : ℕ) (hrG : 0 < rG) (hG : RToOne G rG)
    (honto : Finset.univ.image G = Finset.univ)
    (k : ℕ) (hk : 0 < k) (hhalf : 2*k ≤ (Finset.univ.image F).card)
    (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) :
    (k : ℝ≥0∞) ≤ expectation (run F rF hrF hF G rG hrG hG honto k hk hhalf l hl hl4)
      (fun z => (z.2.1 : ℝ≥0∞)) ∧
    expectation (run F rF hrF hF G rG hrG hG honto k hk hhalf l hl hl4)
      (fun z => (z.2.1 : ℝ≥0∞)) ≤ 2*k := by
  simp only [run, OraclePairLaw.first_mean]
  exact DistinctImageTable.build_query_bounds F rF hrF hF k hhalf

/-- The expected number of `G` evaluations is at most `(1 + 4 * SourcePhaseConstant l) * sqrt
(|X| / (k * rG))`, as in Theorem 5 of [BrassardHoyerTapp1998Collision]. -/
theorem run_Gbound (F : S → R) (rF : ℕ) (hrF : 0 < rF) (hF : RToOne F rF)
    (G : X → R) (rG : ℕ) (hrG : 0 < rG) (hG : RToOne G rG)
    (honto : Finset.univ.image G = Finset.univ)
    (k : ℕ) (hk : 0 < k) (hhalf : 2*k ≤ (Finset.univ.image F).card)
    (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) :
    expectation (run F rF hrF hF G rG hrG hG honto k hk hhalf l hl hl4)
      (fun z => (z.2.2 : ℝ≥0∞)) ≤
      ENNReal.ofReal ((1+4*SourcePhaseConstant l)*Real.sqrt ((Fintype.card X:ℝ)/((k*rG:ℕ):ℝ))) := by
  apply OraclePairLaw.second_bound
  intro s
  have hb := ClawExecution.search_expected G (SampledTableMemory.memory s) l hl hl4
    (marked_pos F G rG hrG hG honto hk s)
  simpa only [marked_card F G rG hG honto s] using hb

end Qatlib.Papers.CollisionProb97.MainResults.SampledClaw
