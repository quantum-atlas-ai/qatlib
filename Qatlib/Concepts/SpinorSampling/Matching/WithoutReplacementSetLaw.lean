/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.OrderedFiberEquiv
import Qatlib.Concepts.SpinorSampling.Matching.WithoutReplacementSupport

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Without Replacement Set Law

Without Replacement Set Law constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators

variable {S : Type} [Fintype S] [DecidableEq S]

/-- Complete original `without_replacement_constant_eq` guarantee for `WithoutReplacementSetLaw`; all source hypotheses and output obligations are retained. -/
theorem without_replacement_constant_eq (M k : ℕ) :
    withoutReplacementConstant M k = 1 / (M.descFactorial k : ℝ) := by
  induction k generalizing M with
  | zero => simp [withoutReplacementConstant]
  | succ k ih =>
    cases M with
    | zero => simp [withoutReplacementConstant]
    | succ M =>
      rw [withoutReplacementConstant, Nat.add_sub_cancel, ih,
        Nat.succ_descFactorial_succ, Nat.cast_mul]
      rw [div_div, mul_comm]

/-- Complete original `without_replacement_fiber_mass` guarantee for `WithoutReplacementSetLaw`; all source hypotheses and output obligations are retained. -/
theorem without_replacement_fiber_mass (R A : Finset S) {k : ℕ}
    (hA : A.card = k) (hsub : A ⊆ R) :
    (∑ ω ∈ (Finset.univ : Finset (Fin k → S)).filter
      (fun ω => occupiedSites ω = A), withoutReplacementMass R k ω) =
        1 / (R.card.choose k : ℝ) := by
  classical
  have hk : k ≤ R.card := hA ▸ Finset.card_le_card hsub
  let good : Finset (Fin k → S) := Finset.univ.filter
    (fun ω => Function.Injective ω ∧ occupiedSites ω = A)
  have hsupport :
      (∑ ω ∈ (Finset.univ : Finset (Fin k → S)).filter
        (fun ω => occupiedSites ω = A), withoutReplacementMass R k ω) =
      ∑ ω ∈ good, withoutReplacementMass R k ω := by
    symm
    apply Finset.sum_subset
    · intro ω hω
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hω).2.2⟩
    · intro ω hω hnot
      have hnonneg := without_replacement_mass_nonneg R k ω
      by_contra hne
      have hpos : 0 < withoutReplacementMass R k ω := lt_of_le_of_ne hnonneg (Ne.symm hne)
      have hinj := without_replacement_mass_pos_injective R k ω hpos
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinj,
        (Finset.mem_filter.mp hω).2⟩)
  have hconst (ω : Fin k → S) (hω : ω ∈ good) :
      withoutReplacementMass R k ω = withoutReplacementConstant R.card k := by
    obtain ⟨hinj,hset⟩ := (Finset.mem_filter.mp hω).2
    apply without_replacement_mass_valid_eq_constant R k hk ω _ hinj
    intro i
    apply hsub
    rw [← hset]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hcard : good.card = k.factorial := by
    have hc : Fintype.card (orderedFiber A k) = good.card := by
      exact @Fintype.card_of_subtype (Fin k → S)
        (fun ω => Function.Injective ω ∧ occupiedSites ω = A) good
        (fun _ => by simp only [good, Finset.mem_filter, Finset.mem_univ, true_and])
        (orderedFiberFintype A k)
    exact hc.symm.trans (ordered_fiber_card_factorial A hA)
  rw [hsupport]
  calc
    _ = (good.card : ℝ) * withoutReplacementConstant R.card k := by
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    _ = (k.factorial : ℝ) / (R.card.descFactorial k : ℝ) := by
      rw [hcard, without_replacement_constant_eq]
      ring
    _ = 1 / (R.card.choose k : ℝ) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
      have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      rw [← div_div, div_self hf]

/-- Complete original `without_replacement_set_expectation` guarantee for `WithoutReplacementSetLaw`; all source hypotheses and output obligations are retained. -/
theorem without_replacement_set_expectation (R : Finset S) {k : ℕ}
    (F : Finset S → ℝ) :
    (∑ ω : Fin k → S, withoutReplacementMass R k ω * F (occupiedSites ω)) =
      (1 / (R.card.choose k : ℝ)) * (∑ A ∈ R.powersetCard k, F A) := by
  classical
  let w : (Fin k → S) → ℝ := fun ω =>
    withoutReplacementMass R k ω * F (occupiedSites ω)
  have hsupport (ω : Fin k → S) (hω : occupiedSites ω ∉ R.powersetCard k) :
      withoutReplacementMass R k ω = 0 := by
    have hnonneg := without_replacement_mass_nonneg R k ω
    by_contra hne
    have hpos : 0 < withoutReplacementMass R k ω := lt_of_le_of_ne hnonneg (Ne.symm hne)
    have hinj := without_replacement_mass_pos_injective R k ω hpos
    have hmem := without_replacement_mass_pos_mem R k ω hpos
    apply hω
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hmem i
    · simpa [occupiedSites] using Finset.card_image_of_injective
        (Finset.univ : Finset (Fin k)) hinj
  have hrestrict :
      (∑ ω : Fin k → S, w ω) =
      ∑ ω ∈ (Finset.univ : Finset (Fin k → S)).filter
        (fun ω => occupiedSites ω ∈ R.powersetCard k), w ω := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro ω _ hnot
    have hnot' : occupiedSites ω ∉ R.powersetCard k := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnot
    simp [w, hsupport ω hnot']
  change (∑ ω : Fin k → S, w ω) = _
  rw [hrestrict, ← Finset.sum_fiberwise_eq_sum_filter
    (Finset.univ : Finset (Fin k → S)) (R.powersetCard k) occupiedSites w]
  calc
    _ = ∑ A ∈ R.powersetCard k,
        (1 / (R.card.choose k : ℝ)) * F A := by
      apply Finset.sum_congr rfl
      intro A hA
      have hAmem := Finset.mem_powersetCard.mp hA
      have hrow :
          (∑ ω ∈ (Finset.univ : Finset (Fin k → S)).filter
            (fun ω => occupiedSites ω = A), w ω) =
          (∑ ω ∈ (Finset.univ : Finset (Fin k → S)).filter
            (fun ω => occupiedSites ω = A), withoutReplacementMass R k ω) * F A := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ω hω
        dsimp [w]
        rw [(Finset.mem_filter.mp hω).2]
      rw [hrow, without_replacement_fiber_mass R A hAmem.2 hAmem.1]
    _ = _ := by rw [Finset.mul_sum]

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.without_replacement_constant_eq
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.without_replacement_fiber_mass

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.without_replacement_set_expectation
