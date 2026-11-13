/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.ReversibleSorter
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.QueryWordCore.Circuit
import Mathlib.Data.Fintype.Perm

/-!
# Uniform rank states and permutation relabeling

This module supplies finite-dimensional ingredients for the antisymmetrization discussion of
[AbramsLloyd1997]. The dependent rank space `rankSpace n` has n! elements, and `stepTwoState` is
its normalized uniform state with amplitude 1/√(n!).

A finite-cardinality equivalence `stepThreeEquiv` relabels ranks as permutations. Its matrix
`stepThreeMatrix` has both conjugate-transpose inverse identities and preserves the sum of
squared amplitude norms.

## Main statements

* `card_rankSpace`: The dependent rank space has n! elements.
* `stepTwoState_normalized`: The uniform rank state is normalized.
* `stepThree_preserves_norm`: Permutation relabeling preserves squared amplitude norm.

## References

* [Abrams and Lloyd, 1997][AbramsLloyd1997]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.FourStepSynthesis
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators

/-- The dependent product of the finite ranges of sizes n, n − 1, through one, indexed by `Fin
n`. -/
abbrev rankSpace (n : ℕ) : Type := (i : Fin n) → Fin (n - i.val)

/-- The product of j + 1 over j < n equals n!. -/
theorem prod_range_succ_id (n : ℕ) :
    (∏ j ∈ Finset.range n, (j + 1)) = n.factorial := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ, Nat.mul_comm]

/-- The product of n − j over j < n equals n!. -/
theorem prod_range_sub (n : ℕ) :
    (∏ j ∈ Finset.range n, (n - j)) = n.factorial := by
  have h := Finset.prod_range_reflect (fun j => j + 1) n
  rw [prod_range_succ_id] at h
  rw [← h]
  apply Finset.prod_congr rfl
  intro j hj
  have hj' : j < n := Finset.mem_range.mp hj
  omega

/-- The dependent rank space for n particles has cardinality n! [AbramsLloyd1997]. -/
theorem card_rankSpace (n : ℕ) : Fintype.card (rankSpace n) = n.factorial := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [Fin.prod_univ_eq_prod_range]
  exact prod_range_sub n

/-- The complex amplitude equal to the reciprocal of the real square root of n!. -/
def stepTwoAmp (n : ℕ) : ℂ :=
  (((Real.sqrt (n.factorial : ℝ) : ℝ)) : ℂ)⁻¹

/-- The constant-amplitude state on `rankSpace n` with amplitude `stepTwoAmp n`. -/
def stepTwoState (n : ℕ) : QState (rankSpace n) := fun _ => stepTwoAmp n

/-- The squared norm of the uniform rank amplitude equals 1/n!. -/
theorem sq_norm_stepTwoAmp (n : ℕ) :
    ‖stepTwoAmp n‖ ^ 2 = (n.factorial : ℝ)⁻¹ := by
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  unfold stepTwoAmp
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hn.le]

/-- The uniform state on the dependent rank space is normalized [AbramsLloyd1997]. -/
theorem stepTwoState_normalized (n : ℕ) : Normalized (stepTwoState n) := by
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  unfold Normalized
  simp only [stepTwoState]
  rw [Finset.sum_const, Finset.card_univ, card_rankSpace, nsmul_eq_mul,
    sq_norm_stepTwoAmp]
  exact mul_inv_cancel₀ hn.ne'

/-- An equivalence between rank records and permutations obtained from their equal finite
cardinalities. -/
def stepThreeEquiv (n : ℕ) : rankSpace n ≃ Equiv.Perm (Fin n) :=
  Fintype.equivOfCardEq (by
    rw [card_rankSpace, Fintype.card_perm, Fintype.card_fin])

/-- The zero-one matrix representing the relabeling from rank records to permutations by
`stepThreeEquiv`. -/
def stepThreeMatrix (n : ℕ) :
    Matrix (Equiv.Perm (Fin n)) (rankSpace n) ℂ :=
  Matrix.of fun σ r => if σ = stepThreeEquiv n r then (1 : ℂ) else 0

/-- Applying the relabeling matrix evaluates the input state at the inverse image of each
permutation. -/
theorem stepThreeMatrix_apply (n : ℕ) (ψ : QState (rankSpace n))
    (σ : Equiv.Perm (Fin n)) :
    (stepThreeMatrix n *ᵥ ψ) σ = ψ ((stepThreeEquiv n).symm σ) := by
  simp only [stepThreeMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single ((stepThreeEquiv n).symm σ)]
  · simp
  · intro r _ hr
    have hne : σ ≠ stepThreeEquiv n r := by
      intro h
      apply hr
      have h' : stepThreeEquiv n r =
          stepThreeEquiv n ((stepThreeEquiv n).symm σ) := by
        rw [Equiv.apply_symm_apply]
        exact h.symm
      exact (stepThreeEquiv n).injective h'
    simp [hne]
  · simp

/-- Complex conjugation fixes the zero-one indicator of a decidable proposition. -/
theorem star_ite_one (p : Prop) [Decidable p] :
    star (if p then (1 : ℂ) else 0) = (if p then 1 else 0) := by
  by_cases hp : p <;> simp [hp]

/-- The conjugate transpose of the rank-to-permutation matrix times that matrix is the identity
on rank records [AbramsLloyd1997]. -/
theorem stepThreeMatrix_isometry (n : ℕ) :
    (stepThreeMatrix n)ᴴ * stepThreeMatrix n = 1 := by
  ext r r'
  simp only [stepThreeMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (stepThreeEquiv n r)]
  · rw [star_ite_one]
    by_cases hrr : r = r'
    · subst hrr; simp
    · have hne : stepThreeEquiv n r ≠ stepThreeEquiv n r' :=
        fun h => hrr ((stepThreeEquiv n).injective h)
      simp [hne, hrr]
  · intro σ _ hσ
    simp [hσ]
  · simp

/-- The rank-to-permutation matrix times its conjugate transpose is the identity on permutations
[AbramsLloyd1997]. -/
theorem stepThreeMatrix_right_inverse (n : ℕ) :
    stepThreeMatrix n * (stepThreeMatrix n)ᴴ = 1 := by
  ext σ τ
  simp only [stepThreeMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single ((stepThreeEquiv n).symm σ)]
  · rw [Equiv.apply_symm_apply, star_ite_one]
    by_cases hστ : σ = τ
    · subst hστ; simp
    · have hτσ : ¬τ = σ := fun h => hστ h.symm
      simp [hστ, hτσ]
  · intro r _ hr
    have hne : σ ≠ stepThreeEquiv n r := by
      intro h
      apply hr
      have h' : stepThreeEquiv n r =
          stepThreeEquiv n ((stepThreeEquiv n).symm σ) := by
        rw [Equiv.apply_symm_apply]
        exact h.symm
      exact (stepThreeEquiv n).injective h'
    simp [hne]
  · simp

/-- Relabeling a rank state by `stepThreeMatrix` preserves the sum of squared amplitude norms
[AbramsLloyd1997]. -/
theorem stepThree_preserves_norm (n : ℕ) (ψ : QState (rankSpace n)) :
    (∑ σ : Equiv.Perm (Fin n), ‖(stepThreeMatrix n *ᵥ ψ) σ‖ ^ 2) =
      ∑ r : rankSpace n, ‖ψ r‖ ^ 2 := by
  simp only [stepThreeMatrix_apply]
  exact (Fintype.sum_equiv (stepThreeEquiv n)
    (fun r => ‖ψ r‖ ^ 2)
    (fun σ => ‖ψ ((stepThreeEquiv n).symm σ)‖ ^ 2)
    (fun r => by simp)).symm

end Qatlib.Papers.ManyBodyFermi97.MainResults.FourStepSynthesis
