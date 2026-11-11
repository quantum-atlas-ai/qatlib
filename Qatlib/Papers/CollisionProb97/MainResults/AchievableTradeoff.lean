/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.CollisionParameters

/-!
# Achievable collision time-space tradeoff

This module chooses a finite input table for collision finding in a regular function with fiber
size at least two. Under `1 ≤ S ≤ T` and `|image F| ≤ S*T^2`, it obtains a table-size bound, an
expected-query bound proportional to `T`, and validity of every supported output, realizing the
tradeoff associated with [BrassardHoyerTapp1998Collision].

## Main statements

* `full_table_expected`: exact expected cost when the full input table is used.
* `selected_expected`: the cost bound for a table meeting the resource inequalities.
* `achievable`: existence of a table and the combined size, cost, and correctness guarantees.

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
namespace Qatlib.Papers.CollisionProb97.MainResults.AchievableTradeoff
variable {X R : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [AddCommGroup R] [Fintype R] [DecidableEq R]

omit [AddCommGroup R] [Fintype R] in

/-- For an `r`-to-one function with `r ≥ 2`, the full input table always yields an early
collision; see [BrassardHoyerTapp1998Collision]. -/
theorem full_table_early (F : X → R) (r : ℕ) (hr : 2 ≤ r) (hF : RToOne F r) :
    CollisionExecution.early F Finset.univ ≠ none := by
  intro he
  have hp := CollisionExecution.marked_pos F r hr hF Finset.univ Finset.univ_nonempty he
  simp [ActualSearch.marked] at hp

/-- For an `r`-to-one function with `r ≥ 2`, running the collision procedure with the full input
table has expected cost exactly `Fintype.card X`; see [BrassardHoyerTapp1998Collision]. -/
theorem full_table_expected (F : X → R) (r : ℕ) (hr : 2 ≤ r) (hF : RToOne F r)
    (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) :
    expectedCost (CollisionExecution.run F r hr hF Finset.univ Finset.univ_nonempty l hl hl4) =
      (Fintype.card X : ℝ≥0∞) := by
  rw [CollisionExecution.run, dif_neg (full_table_early F r hr hF),
    expectedCost_charge, expectedCost_ret, add_zero, Finset.card_univ]

/-- If `K.card ≤ T` and `|image F| ≤ K.card*T^2`, bounds the expected collision-run cost by
`(1+(1+4*SourcePhaseConstant l)*sqrt 2)*T` under the stated regularity and phase-growth
assumptions. -/
theorem selected_expected (F : X → R) (r : ℕ) (hr : 2 ≤ r) (hF : RToOne F r)
    (K : Finset X) (hK : K.Nonempty) (T : ℝ)
    (hKT : (K.card:ℝ) ≤ T) (hresource : ((Finset.univ.image F).card:ℝ) ≤ (K.card:ℝ)*T^2)
    (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) :
    expectedCost (CollisionExecution.run F r hr hF K hK l hl hl4) ≤
      ENNReal.ofReal ((1+(1+4*SourcePhaseConstant l)*Real.sqrt 2)*T) := by
  apply (CollisionParameters.run_expected_image F r hr hF K hK l hl hl4).trans
  apply ENNReal.ofReal_le_ofReal
  have hk : (0:ℝ) < K.card := by exact_mod_cast Finset.card_pos.mpr hK
  have hT : 0 ≤ T := le_trans hk.le hKT
  have hratio : ((Finset.univ.image F).card:ℝ)/K.card ≤ T^2 := by
    apply (div_le_iff₀ hk).mpr
    nlinarith
  have hs := Real.sqrt_le_sqrt hratio
  rw [Real.sqrt_sq hT] at hs
  have hg : 0 ≤ (1+4*SourcePhaseConstant l)*Real.sqrt 2 := by
    have := search_source_constant_nonneg l hl hl4
    positivity
  have hp := mul_le_mul_of_nonneg_left hs hg
  nlinarith

/-- For an `r`-to-one function with `r ≥ 2`, `1 ≤ S ≤ T`, and `|image F| ≤ S*T^2`, there exists
a nonempty table of at most `S` inputs with `K.card+1 ≤ 2*S`, the stated expected-cost
bound, and only valid collisions in its output support. This realizes the resource tradeoff
of [Brassard et al., Corollary 3][BrassardHoyerTapp1998Collision]. -/
theorem achievable (F : X → R) (r : ℕ) (hr : 2 ≤ r) (hF : RToOne F r)
    (S : ℕ) (hS : 1 ≤ S) (T : ℝ) (hST : (S:ℝ) ≤ T)
    (hresource : ((Finset.univ.image F).card:ℝ) ≤ (S:ℝ)*T^2)
    (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) :
    ∃ (K : Finset X) (hK : K.Nonempty),
      K.card ≤ S ∧ K.card+1 ≤ 2*S ∧
      expectedCost (CollisionExecution.run F r hr hF K hK l hl hl4) ≤
        ENNReal.ofReal ((1+(1+4*SourcePhaseConstant l)*Real.sqrt 2)*T) ∧
      ∀ out c, CollisionExecution.run F r hr hF K hK l hl hl4 (out,c) ≠ 0 →
        ∃ s t, out = some (s,t) ∧ s ≠ t ∧ F s = F t := by
  by_cases hSN : S ≤ Fintype.card X
  · let K := InputSelection.select (X := X) S
    have hc : K.card = S := InputSelection.select_card S hSN
    have hK : K.Nonempty := InputSelection.select_nonempty S hS hSN
    refine ⟨K,hK,by omega,by omega,?_,?_⟩
    · apply selected_expected F r hr hF K hK T (by simpa only [hc] using hST)
        (by simpa only [hc] using hresource) l hl hl4
    · exact CollisionExecution.run_correct F r hr hF K hK l hl hl4
  · refine ⟨Finset.univ,Finset.univ_nonempty,?_,?_,?_,?_⟩
    · simpa only [Finset.card_univ] using (show Fintype.card X ≤ S by omega)
    · rw [Finset.card_univ]
      omega
    · rw [full_table_expected]
      have hNS : (Fintype.card X:ℝ) ≤ S := by exact_mod_cast (show Fintype.card X ≤ S by omega)
      have hNT : (Fintype.card X:ℝ) ≤ T := hNS.trans hST
      have hT : 0 ≤ T := (Nat.cast_nonneg S).trans hST
      have hg : 0 ≤ (1+4*SourcePhaseConstant l)*Real.sqrt 2 := by
        have := search_source_constant_nonneg l hl hl4
        positivity
      have hb : (Fintype.card X:ℝ) ≤ (1+(1+4*SourcePhaseConstant l)*Real.sqrt 2)*T := by
        nlinarith [mul_nonneg hg hT]
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hb
    · exact CollisionExecution.run_correct F r hr hF Finset.univ Finset.univ_nonempty l hl hl4

end Qatlib.Papers.CollisionProb97.MainResults.AchievableTradeoff
