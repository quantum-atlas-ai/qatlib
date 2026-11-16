/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAOABddOcc14.MainResults.StateModel
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Analysis.Complex.Trigonometric

@[expose] public section


/-! # Normalization of the explicit QAOA state
Finite tensor orthogonality and phase norm preservation establish normalization
for the actual archived amplitudes, independently of any clause formula.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QAOABddOcc14.MainResults

open scoped BigOperators
open Qatlib.Papers.QAOABddOcc14.MainResults

/-- One entry of the actual single-qubit mixer matrix. -/
def bitMixer (β : ℝ) (z w : Bool) : ℂ :=
  if z = w then (Real.cos β : ℂ)
  else -(Complex.I * (Real.sin β : ℂ))

/-- The two columns of one mixer are orthonormal by cos squared plus sin squared. -/
theorem bitOrth (β : ℝ) (w v : Bool) :
    (∑ z : Bool, (starRingEnd ℂ) (bitMixer β z w) * bitMixer β z v) =
      if w = v then (1 : ℂ) else 0 := by
  cases w <;> cases v <;> apply Complex.ext <;>
    simp [bitMixer, Complex.mul_re, Complex.mul_im,
      Complex.sin_ofReal_re, Complex.cos_ofReal_re] <;>
    nlinarith [Real.cos_sq_add_sin_sq β]

/-- Product-sum factorization lifts single-qubit column orthogonality to the register. -/
theorem mixOrth {n : ℕ} (β : ℝ) (w v : Basis n) :
    (∑ z : Basis n, (starRingEnd ℂ) (mixAmp β z w) * mixAmp β z v) =
      if w = v then (1 : ℂ) else 0 := by
  have heach : ∀ z : Basis n,
      (starRingEnd ℂ) (mixAmp β z w) * mixAmp β z v =
        ∏ a : Fin n, (starRingEnd ℂ) (bitMixer β (z a) (w a)) *
          bitMixer β (z a) (v a) := by
    intro z
    simp only [mixAmp, bitMixer, map_prod, Finset.prod_mul_distrib]
  simp_rw [heach]
  rw [← Fintype.prod_sum (fun (a : Fin n) (z : Bool) =>
    (starRingEnd ℂ) (bitMixer β z (w a)) * bitMixer β z (v a))]
  simp_rw [bitOrth]
  rw [Fintype.prod_boole]
  have hfun : (∀ a : Fin n, w a = v a) ↔ w = v :=
    ⟨fun h => funext h, fun h a => congrFun h a⟩
  simp only [hfun]

/-- Column orthogonality preserves the finite sum of squared complex amplitudes. -/
theorem normPreserved {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι → ι → ℂ)
    (hU : ∀ w v,
      (∑ z, (starRingEnd ℂ) (U z w) * U z v) = if w = v then (1 : ℂ) else 0)
    (a : ι → ℂ) :
    (∑ z, Complex.normSq (∑ w, U z w * a w)) = ∑ w, Complex.normSq (a w) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  change (∑ z, (starRingEnd ℂ) (∑ w, U z w * a w) * (∑ v, U z v * a v)) =
    ∑ w, (starRingEnd ℂ) (a w) * a w
  have hexpand : ∀ z,
      (starRingEnd ℂ) (∑ w, U z w * a w) * (∑ v, U z v * a v) =
        ∑ w, ∑ v, ((starRingEnd ℂ) (U z w) * U z v) *
          ((starRingEnd ℂ) (a w) * a v) := by
    intro z
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [map_mul]
    ring
  calc
    (∑ z, (starRingEnd ℂ) (∑ w, U z w * a w) * (∑ v, U z v * a v)) =
        ∑ z, ∑ w, ∑ v, ((starRingEnd ℂ) (U z w) * U z v) *
          ((starRingEnd ℂ) (a w) * a v) :=
      Finset.sum_congr rfl (fun z _ => hexpand z)
    _ = ∑ w, ∑ v, (∑ z, (starRingEnd ℂ) (U z w) * U z v) *
          ((starRingEnd ℂ) (a w) * a v) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_mul]
    _ = ∑ w, (starRingEnd ℂ) (a w) * a w := by
      simp_rw [hU]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true]

/-- The actual diagonal phase has squared norm one because its exponent is imaginary. -/
theorem phaseNorm {n : ℕ} (I : E3Instance n) (γ : ℝ) (z : Basis n) :
    Complex.normSq (phaseAmp I γ z) = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  simp [phaseAmp, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- The uniform-start amplitude has squared norm the reciprocal register size. -/
theorem plusNorm (n : ℕ) : Complex.normSq (plusAmp n) = ((2 : ℝ) ^ n)⁻¹ := by
  rw [plusAmp, Complex.normSq_ofReal, ← mul_inv,
    Real.mul_self_sqrt (by positivity : 0 ≤ (2 : ℝ) ^ n)]

/-- The explicit QAOA state is normalized for every instance and both real angles. -/
theorem qaoaNormalized {n : ℕ} (I : E3Instance n) (γ β : ℝ) :
    ∑ z : Basis n, measWeight I γ β z = 1 := by
  have hU := normPreserved (fun z w : Basis n => mixAmp β z w)
    (mixOrth β) (fun w => phaseAmp I γ w * plusAmp n)
  have hsum :
      (∑ z : Basis n, measWeight I γ β z) =
        ∑ w : Basis n, Complex.normSq (phaseAmp I γ w * plusAmp n) := by
    simpa only [measWeight, qaoaAmp, mul_assoc] using hU
  rw [hsum]
  simp_rw [Complex.normSq_mul, phaseNorm, one_mul, plusNorm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  exact mul_inv_cancel₀ (by positivity)

end Qatlib.Papers.QAOABddOcc14.MainResults
