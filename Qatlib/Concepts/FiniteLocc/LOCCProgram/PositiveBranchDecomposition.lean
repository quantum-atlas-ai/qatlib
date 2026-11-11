/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.LocalUnitaryDiscard
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Mathlib.Analysis.Matrix.Order

/-!
# Positive branch decompositions on qubits

This module proves kernel constraints for finite sums of positive semidefinite matrices and
applies them to positive complex-linear maps on qubit operators whose sum is the identity map.
Each component sends the identity operator to a scalar multiple of the identity. The
matrix-positivity background is described in [Bhatia1997].

The remaining lemmas show that relabeling respects multiplication, adjoints, and positivity, and
give a partial-trace identity for conjugation on a discarded tensor factor.

## Main statements

* `psd_family_kernel`: zero quadratic form for a positive sum forces every summand to annihilate
  the vector.
* `positive_qubit_family_scalar_one`: each positive linear component of the identity map has
  scalar value at the identity.
* `partialTrace_discard_sandwich`: moves a conjugation on the discarded factor into an
  adjoint-product factor.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1500000
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.FiniteLocc.LOCCProgram
open Matrix
open scoped Classical BigOperators ComplexOrder

/-- If the quadratic form of a finite sum of positive semidefinite matrices vanishes at a
vector, every summand annihilates that vector. -/
theorem psd_family_kernel {I : Type} [Fintype I] [DecidableEq I] (m : ℕ)
    (A : Fin m → Matrix I I ℂ) (hA : ∀ s, (A s).PosSemidef) (v : I → ℂ)
    (hz : star v ⬝ᵥ ((∑ s, A s) *ᵥ v) = 0) : ∀ s, A s *ᵥ v = 0 := by
  have hs : (∑ s, (star v ⬝ᵥ (A s *ᵥ v)).re) = 0 := by
    rw [← Complex.re_sum]
    have he : (∑ s, star v ⬝ᵥ (A s *ᵥ v)) = star v ⬝ᵥ ((∑ s, A s) *ᵥ v) := by
      simp only [Matrix.sum_mulVec, dotProduct_sum]
    rw [he, hz]
    rfl
  intro s
  have hr : (star v ⬝ᵥ (A s *ᵥ v)).re = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => (hA s).re_dotProduct_nonneg v)).mp hs s (Finset.mem_univ s)
  have hi := (Complex.nonneg_iff.mp ((hA s).dotProduct_mulVec_nonneg v)).2
  apply (hA s).dotProduct_mulVec_zero_iff.mp
  apply Complex.ext <;> simp [hr, hi]

/-- A Hermitian two-dimensional operator annihilating the vector `[1,t]`, with real `t`
satisfying `t ^ 2 = 1`, has equal diagonal entries. -/
theorem balanced_diag_of_kernel (A : Operator 2) (hA : A.IsHermitian)
    (t : ℝ) (ht : t^2 = 1) (hk : A *ᵥ ![1, (t : ℂ)] = 0) : A 0 0 = A 1 1 := by
  have h0 := congrFun hk 0
  have h1 := congrFun hk 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, Pi.zero_apply] at h0 h1
  have h10 : A 1 0 = -(t : ℂ) * A 1 1 := by linear_combination h1
  have hd := congrArg (fun M : Operator 2 => M 1 1) hA.eq
  have he := congrArg (fun M : Operator 2 => M 0 1) hA.eq
  simp only [Matrix.conjTranspose_apply] at hd he
  have htstar : star (t : ℂ) = (t : ℂ) := by simp
  rw [h10, star_mul, star_neg, htstar, hd] at he
  rw [← he] at h0
  have hc : (t : ℂ)^2 = 1 := by exact_mod_cast ht
  linear_combination h0 + (A 1 1) * hc

/-- For a finite family of positive complex-linear maps on qubit operators summing to the
identity map, each map sends the identity operator to a scalar multiple of the identity. -/
theorem positive_qubit_family_scalar_one (m : ℕ) (F : Fin m → Operator 2 → Operator 2)
    (hadd : ∀ s A B, F s (A + B) = F s A + F s B)
    (hsmul : ∀ s (c : ℂ) A, F s (c • A) = c • F s A)
    (hpos : ∀ s A, A.PosSemidef → (F s A).PosSemidef)
    (hsum : ∀ A, ∑ s, F s A = A) :
    ∀ s, ∃ a : ℂ, F s 1 = a • (1 : Operator 2) := by
  let E₀ := outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))
  let E₁ := outerProduct (Qatlib.Foundations.PureStateMath.Ket (1 : Fin 2))
  let P := outerProduct (![1, 1] : QState (Fin 2))
  let Q := outerProduct (![1, -1] : QState (Fin 2))
  have hE : E₀ + E₁ = (1 : Operator 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [E₀, E₁, outerProduct_apply, Qatlib.Foundations.PureStateMath.Ket, Matrix.one_apply]
  have hPQ : P + Q = (2 : ℂ) • (1 : Operator 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [P, Q, outerProduct_apply, Matrix.one_apply]
  have hzero (A : Operator 2) (hp : A.PosSemidef) (v : Fin 2 → ℂ)
      (hv : star v ⬝ᵥ (A *ᵥ v) = 0) : ∀ s, F s A *ᵥ v = 0 := by
    apply psd_family_kernel m (fun s => F s A) (fun s => hpos s A hp) v
    rw [hsum]
    exact hv
  have hk₀ := hzero E₀ (outerProduct_posSemidef _) (Qatlib.Foundations.PureStateMath.Ket 1)
    (by norm_num [E₀, outerProduct_apply, Qatlib.Foundations.PureStateMath.Ket, Matrix.mulVec, dotProduct, Fin.sum_univ_two])
  have hk₁ := hzero E₁ (outerProduct_posSemidef _) (Qatlib.Foundations.PureStateMath.Ket 0)
    (by norm_num [E₁, outerProduct_apply, Qatlib.Foundations.PureStateMath.Ket, Matrix.mulVec, dotProduct, Fin.sum_univ_two])
  have hkP := hzero P (outerProduct_posSemidef _) ![1, -1]
    (by norm_num [P, outerProduct_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two])
  have hkQ := hzero Q (outerProduct_posSemidef _) ![1, 1]
    (by norm_num [Q, outerProduct_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two])
  intro s
  have hP : (F s P) 0 0 = (F s P) 1 1 :=
    balanced_diag_of_kernel _ (hpos s P (outerProduct_posSemidef _)).1 (-1) (by norm_num) (by simpa using hkP s)
  have hQ : (F s Q) 0 0 = (F s Q) 1 1 :=
    balanced_diag_of_kernel _ (hpos s Q (outerProduct_posSemidef _)).1 1 (by norm_num) (hkQ s)
  have hI : F s 1 = F s E₀ + F s E₁ := by rw [← hE, hadd]
  have hI2 : (2 : ℂ) • F s 1 = F s P + F s Q := by rw [← hsmul, ← hadd, hPQ]
  have hd : (F s 1) 0 0 = (F s 1) 1 1 := by
    have h0 := congrArg (fun M : Operator 2 => M 0 0) hI2
    have h1 := congrArg (fun M : Operator 2 => M 1 1) hI2
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply] at h0 h1
    linear_combination (h0 - h1 + hP + hQ) / 2
  have h01 : (F s 1) 0 1 = 0 := by
    have h0 := congrFun (hk₀ s) 0
    have h1 := congrFun (hk₁ s) 1
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Qatlib.Foundations.PureStateMath.Ket] at h0 h1
    have hh := congrArg (fun M : Operator 2 => M 0 1) (hpos s E₁ (outerProduct_posSemidef _)).1.eq
    simp only [Matrix.conjTranspose_apply, h1, star_zero] at hh
    rw [hI]
    simp only [Matrix.add_apply, h0, hh.symm, add_zero]
  have h10 : (F s 1) 1 0 = 0 := by
    have hh :=
        congrArg (fun M : Operator 2 => M 1 0)
        (hpos s 1 (by simpa using Matrix.posSemidef_conjTranspose_mul_self (1 : Operator 2))).1.eq
    simp only [Matrix.conjTranspose_apply, h01, star_zero] at hh
    exact hh.symm
  refine ⟨(F s 1) 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, hd]

/-- Relabeling matrix indices along an equivalence preserves matrix multiplication. -/
theorem converse_relabel_mul {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A B : Matrix I I ℂ) :
    relabelGate e (A * B) = relabelGate e A * relabelGate e B :=
  (Matrix.reindexAlgEquiv ℂ ℂ e).map_mul A B

/-- Relabeling matrix indices commutes with taking the conjugate transpose. -/
theorem converse_relabel_adjoint {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A : Matrix I I ℂ) :
    relabelGate e Aᴴ = (relabelGate e A)ᴴ := by ext i j; rfl

/-- Relabeling matrix indices preserves positive semidefiniteness. -/
theorem converse_relabel_positive {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    (relabelGate e A).PosSemidef := hA.submatrix e.symm

/-- Under partial trace over the second factor, conjugating by the identity tensored with `A`
equals right multiplication by the identity tensored with `Aᴴ * A` before tracing. -/
theorem partialTrace_discard_sandwich (D E : ℕ) (A : Operator E)
    (X : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace (TensorGate (1 : Operator D) A * X * (TensorGate (1 : Operator D) A)ᴴ) =
      PartialTrace (X * TensorGate (1 : Operator D) (Aᴴ * A)) := by
  ext i j
  let B : Operator E := fun a b => X (i, a) (j, b)
  have hl : PartialTrace (TensorGate (1 : Operator D) A * X *
      (TensorGate (1 : Operator D) A)ᴴ) i j = Matrix.trace (A * B * Aᴴ) := by
    change (∑ a, (TensorGate (1 : Operator D) A * X *
      (TensorGate (1 : Operator D) A)ᴴ) (i, a) (j, a)) = _
    simp_rw [conj_tensorRight_apply]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    rfl
  have hr : PartialTrace (X * TensorGate (1 : Operator D) (Aᴴ * A)) i j =
      Matrix.trace (B * (Aᴴ * A)) := by
    simp only [PartialTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Fintype.sum_prod_type, tensorGate_apply, Matrix.one_apply, ite_mul,
      mul_ite, one_mul, mul_zero, zero_mul, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  rw [hl, hr]
  simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_cycle B Aᴴ A).symm

end Qatlib.Concepts.FiniteLocc.LOCCProgram
