/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SchattenDiamond.DiamondNorm

set_option autoImplicit false

noncomputable section
namespace Qatlib.Concepts.ReferenceError.DensityToRaw
open Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 2000000

private theorem density_bound_positive {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (T : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (δ : ℝ) (_hδ : 0 ≤ δ)
    (h : ∀ ρ, ρ.PosSemidef → Matrix.trace ρ = 1 → (T ρ).traceNorm ≤ δ)
    (X : Matrix A A ℂ) (hX : X.PosSemidef) :
    (T X).traceNorm ≤ δ * X.traceNorm := by
  let q := X.traceNorm
  have hq : 0 ≤ q := Matrix.traceNorm_nonneg X
  by_cases hz : q = 0
  · have hx0 : X = 0 := (Matrix.traceNorm_zero_iff X).mp hz
    subst X
    simp [map_zero, Matrix.traceNorm_zero]
  · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
    let ρ := ((q⁻¹ : ℝ) : ℂ) • X
    have hρ : ρ.PosSemidef := hX.smul (RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hq))
    have htr : Matrix.trace ρ = 1 := by
      rw [Matrix.trace_smul, ← hX.traceNorm_eq_trace]
      change ((q⁻¹ : ℝ) : ℂ) * (q : ℂ) = 1
      exact_mod_cast inv_mul_cancel₀ hz
    have hb := h ρ hρ htr
    have he : (q : ℂ) • ρ = X := by
      rw [smul_smul]
      have hc : (q : ℂ) * ((q⁻¹ : ℝ) : ℂ) = 1 := by
        exact_mod_cast mul_inv_cancel₀ hz
      rw [hc, one_smul]
    calc
      (T X).traceNorm = q * (T ρ).traceNorm := by
        conv_lhs => rw [← he]
        rw [map_smul, Matrix.traceNorm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hq]
      _ ≤ q * δ := mul_le_mul_of_nonneg_left hb hq
      _ = δ * X.traceNorm := mul_comm _ _

private theorem density_bound_hermitian {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (T : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ ρ, ρ.PosSemidef → Matrix.trace ρ = 1 → (T ρ).traceNorm ≤ δ)
    (X : Matrix A A ℂ) (hX : X.IsHermitian) :
    (T X).traceNorm ≤ δ * X.traceNorm := by
  have hp : (HermitianSplit.posPart hX).PosSemidef := by
    unfold HermitianSplit.posPart
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact RCLike.ofReal_nonneg.mpr (le_max_right _ _)
  have hn : (HermitianSplit.negPart hX).PosSemidef := by
    unfold HermitianSplit.negPart
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact RCLike.ofReal_nonneg.mpr (le_max_right _ _)
  have he : T X = T (HermitianSplit.posPart hX) - T (HermitianSplit.negPart hX) := by
    rw [← map_sub, HermitianSplit.sub_posPart_negPart hX]
  calc
    (T X).traceNorm ≤ (T (HermitianSplit.posPart hX)).traceNorm +
        (T (HermitianSplit.negPart hX)).traceNorm := by
      rw [he, sub_eq_add_neg]
      simpa only [Matrix.traceNorm_neg] using Matrix.traceNorm_add_le
        (T (HermitianSplit.posPart hX)) (-T (HermitianSplit.negPart hX))
    _ ≤ δ * (HermitianSplit.posPart hX).traceNorm +
        δ * (HermitianSplit.negPart hX).traceNorm :=
      add_le_add (density_bound_positive T δ hδ h _ hp)
        (density_bound_positive T δ hδ h _ hn)
    _ = δ * X.traceNorm := by
      rw [← mul_add, ← HermitianSplit.traceNorm_sub_posPart_negPart hX]

theorem finite_reference_density_error_to_raw :
  ∀ (D E : ℕ) (T : Operator D →ₗ[ℂ] Operator E) (δ : ℝ), 0 ≤ δ →
    (∀ (r : ℕ) (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
      ρ.PosSemidef → Matrix.trace ρ = 1 → Matrix.traceNorm (tensorLeft T ρ) ≤ δ) →
    ∀ (r : ℕ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
      Matrix.traceNorm (tensorLeft T X) ≤ 2 * δ * Matrix.traceNorm X := by
  intro D E T δ hδ h r X
  let S : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ →ₗ[ℂ]
      Matrix (Fin E × Fin r) (Fin E × Fin r) ℂ :=
    { toFun := tensorLeft T
      map_add' := by
        intro A B
        ext a b
        exact congrFun (congrFun (T.map_add _ _) a.1) b.1
      map_smul' := by
        intro c A
        exact diamond_tensorLeft_input_smul T c A }
  let R := (1 / 2 : ℂ) • (X + Xᴴ)
  let I := (-Complex.I / 2) • (X - Xᴴ)
  have hR : R.IsHermitian := by
    simp only [R, Matrix.IsHermitian, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
    simp [add_comm]
  have hI : I.IsHermitian := by
    simp only [I, Matrix.IsHermitian, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    ext a b
    simp [Matrix.smul_apply, Matrix.sub_apply]
    ring
  have hRI : R + Complex.I • I = X := by
    ext a b
    simp [R, I, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply]
    ring_nf
    simp [Complex.I_sq]
    ring
  have hnR : R.traceNorm ≤ X.traceNorm := by
    rw [Matrix.traceNorm_smul]
    have hc : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [hc]
    apply (mul_le_mul_of_nonneg_left (Matrix.traceNorm_add_le X Xᴴ) (by positivity)).trans
    rw [Matrix.traceNorm_conjTranspose]
    linarith
  have hnI : I.traceNorm ≤ X.traceNorm := by
    rw [Matrix.traceNorm_smul]
    have hc : ‖(-Complex.I / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
      rw [norm_div, norm_neg, Complex.norm_I]
      norm_num
    rw [hc, sub_eq_add_neg]
    apply (mul_le_mul_of_nonneg_left (Matrix.traceNorm_add_le X (-Xᴴ)) (by positivity)).trans
    rw [Matrix.traceNorm_neg, Matrix.traceNorm_conjTranspose]
    linarith
  change (S X).traceNorm ≤ _
  have he : S X = S R + Complex.I • S I := by
    rw [← S.map_smul, ← S.map_add, hRI]
  calc
    (S X).traceNorm ≤ (S R).traceNorm + (S I).traceNorm := by
      rw [he]
      simpa only [Matrix.traceNorm_smul, Complex.norm_I, one_mul] using
        Matrix.traceNorm_add_le (S R) (Complex.I • S I)
    _ ≤ δ * R.traceNorm + δ * I.traceNorm :=
      add_le_add (density_bound_hermitian S δ hδ (h r) R hR)
        (density_bound_hermitian S δ hδ (h r) I hI)
    _ ≤ δ * X.traceNorm + δ * X.traceNorm :=
      add_le_add (mul_le_mul_of_nonneg_left hnR hδ) (mul_le_mul_of_nonneg_left hnI hδ)
    _ = _ := by ring

end Qatlib.Concepts.ReferenceError.DensityToRaw
