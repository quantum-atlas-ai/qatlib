/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError
import Mathlib.Data.ENNReal.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.ReferenceError.RefTraceError

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.SchattenDiamond.DiamondNorm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def finiteDiamondNorm {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : ℝ≥0∞ :=
  ⨆ r : ℕ, ⨆ X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ,
    if Matrix.traceNorm X ≤ 1 then ENNReal.ofReal (Matrix.traceNorm (tensorLeft T X)) else 0

noncomputable def finiteDiamondDistance {D E : ℕ}
    (T S : Operator D →ₗ[ℂ] Operator E) : ℝ≥0∞ := (1/2 : ℝ≥0∞)*finiteDiamondNorm (T-S)

theorem diamond_tensorLeft_input_smul {D E r : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (c : ℂ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    tensorLeft T (c • X) = c • tensorLeft T X := by
  ext a b
  change T (c • (fun i j => X (i,a.2) (j,b.2) : Operator D)) a.1 b.1 = _
  exact congrFun (congrFun (T.map_smul c (fun i j => X (i,a.2) (j,b.2))) a.1) b.1

theorem finiteDiamondNorm_apply {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (r : ℕ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    ENNReal.ofReal (Matrix.traceNorm (tensorLeft T X)) ≤
      finiteDiamondNorm T * ENNReal.ofReal (Matrix.traceNorm X) := by
  classical
  by_cases hz : Matrix.traceNorm X = 0
  · have hX := (Matrix.traceNorm_zero_iff X).mp hz
    subst X
    have ht : tensorLeft T (0 : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) = 0 := by
      ext a b
      exact congrFun (congrFun T.map_zero a.1) b.1
    rw [ht, Matrix.traceNorm_zero]
    simp
  · let q := Matrix.traceNorm X
    have hq : 0 < q := lt_of_le_of_ne (Matrix.traceNorm_nonneg X) (Ne.symm hz)
    let Y := ((q⁻¹ : ℝ) : ℂ) • X
    have hY : Matrix.traceNorm Y = 1 := by
      rw [Matrix.traceNorm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hq)]
      exact inv_mul_cancel₀ (ne_of_gt hq)
    have hXY : X = (q : ℂ) • Y := by
      have hc : (q : ℂ)*((q⁻¹ : ℝ) : ℂ) = 1 := by
        exact_mod_cast mul_inv_cancel₀ (ne_of_gt hq)
      ext a b
      change X a b = (q : ℂ)*(((q⁻¹ : ℝ) : ℂ)*X a b)
      rw [← mul_assoc, hc, one_mul]
    have hbound : ENNReal.ofReal (Matrix.traceNorm (tensorLeft T Y)) ≤ finiteDiamondNorm T := by
      unfold finiteDiamondNorm
      exact le_iSup_of_le r (le_iSup_of_le Y (by simp [hY]))
    calc
      _ = ENNReal.ofReal q * ENNReal.ofReal (Matrix.traceNorm (tensorLeft T Y)) := by
        conv_lhs => rw [hXY]
        rw [diamond_tensorLeft_input_smul, Matrix.traceNorm_smul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hq, ENNReal.ofReal_mul hq.le]
      _ ≤ ENNReal.ofReal q * finiteDiamondNorm T := mul_le_mul_right hbound _
      _ = _ := mul_comm _ _

theorem finiteDiamondNorm_le_iff_uniform : ∀ (D E : ℕ)
    (T : Operator D →ₗ[ℂ] Operator E) (delta : ℝ), 0 ≤ delta →
    (finiteDiamondNorm T ≤ ENNReal.ofReal delta ↔
      ∀ (r : ℕ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
        Matrix.traceNorm (tensorLeft T X) ≤ delta*Matrix.traceNorm X) := by
  intro D E T delta hd
  constructor
  · intro h r X
    have he := (finiteDiamondNorm_apply T r X).trans
      (mul_le_mul_left h (ENNReal.ofReal (Matrix.traceNorm X)))
    rw [← ENNReal.ofReal_mul hd] at he
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hd (Matrix.traceNorm_nonneg X))).mp he
  · intro h
    unfold finiteDiamondNorm
    apply iSup_le
    intro r
    apply iSup_le
    intro X
    split_ifs with hx
    · exact ENNReal.ofReal_le_ofReal ((h r X).trans
        ((mul_le_mul_of_nonneg_left hx hd).trans_eq (mul_one delta)))
    · exact bot_le

theorem diamond_tensorLeft_add {D E r : ℕ} (T S : Operator D →ₗ[ℂ] Operator E)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    tensorLeft (T+S) X = tensorLeft T X + tensorLeft S X := by rfl

@[simp] theorem finiteDiamondNorm_zero (D E : ℕ) :
    finiteDiamondNorm (0 : Operator D →ₗ[ℂ] Operator E) = 0 := by
  have ht (r : ℕ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
      tensorLeft (0 : Operator D →ₗ[ℂ] Operator E) X = 0 := rfl
  simp [finiteDiamondNorm, ht, Matrix.traceNorm_zero]

theorem finiteDiamondNorm_algebra : ∀ (D E F : ℕ)
    (T S : Operator D →ₗ[ℂ] Operator E) (R : Operator E →ₗ[ℂ] Operator F),
    finiteDiamondNorm (T+S) ≤ finiteDiamondNorm T + finiteDiamondNorm S ∧
    finiteDiamondNorm (R.comp T) ≤ finiteDiamondNorm R * finiteDiamondNorm T ∧
    (finiteDiamondNorm T = 0 ↔ T = 0) := by
  intro D E F T S R
  classical
  have hunit (V : Operator D →ₗ[ℂ] Operator E) (r : ℕ)
      (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) (hx : Matrix.traceNorm X ≤ 1) :
      ENNReal.ofReal (Matrix.traceNorm (tensorLeft V X)) ≤ finiteDiamondNorm V := by
    apply (finiteDiamondNorm_apply V r X).trans
    simpa using mul_le_mul_right (show ENNReal.ofReal (Matrix.traceNorm X) ≤ 1 by
      exact (ENNReal.ofReal_le_ofReal hx).trans_eq (by norm_num)) (finiteDiamondNorm V)
  refine ⟨?_, ?_, ?_⟩
  · unfold finiteDiamondNorm at ⊢
    apply iSup_le
    intro r
    apply iSup_le
    intro X
    split_ifs with hx
    · rw [diamond_tensorLeft_add]
      calc
        _ ≤ ENNReal.ofReal (Matrix.traceNorm (tensorLeft T X)+Matrix.traceNorm (tensorLeft S X)) :=
          ENNReal.ofReal_le_ofReal (Matrix.traceNorm_add_le _ _)
        _ = _ := ENNReal.ofReal_add (Matrix.traceNorm_nonneg _) (Matrix.traceNorm_nonneg _)
        _ ≤ _ := add_le_add (hunit T r X hx) (hunit S r X hx)
    · exact bot_le
  · unfold finiteDiamondNorm at ⊢
    apply iSup_le
    intro r
    apply iSup_le
    intro X
    split_ifs with hx
    · rw [tensorLeft_comp]
      exact (finiteDiamondNorm_apply R r (tensorLeft T X)).trans
        (mul_le_mul_right (hunit T r X hx) (finiteDiamondNorm R))
    · exact bot_le
  · constructor
    · intro hz
      ext Y a b
      let X : Matrix (Fin D × Fin 1) (Fin D × Fin 1) ℂ := fun p q => Y p.1 q.1
      have h := finiteDiamondNorm_apply T 1 X
      rw [hz, zero_mul] at h
      have hzero : tensorLeft T X = 0 := (Matrix.traceNorm_zero_iff _).mp
        (le_antisymm (ENNReal.ofReal_eq_zero.mp (le_antisymm h (bot_le)))
          (Matrix.traceNorm_nonneg _))
      have he := congrFun (congrFun hzero (a,0)) (b,0)
      simpa [tensorLeft, X] using he
    · intro h; subst T; exact finiteDiamondNorm_zero D E

theorem diamond_traceNorm_reindex {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ≃ B) (X : Matrix A A ℂ) :
    Matrix.traceNorm (Matrix.reindex e e X) = Matrix.traceNorm X := by
  classical
  let u : Matrix B A ℂ := (1 : Matrix A A ℂ).submatrix e.symm id
  have hu : u.Isometry := Matrix.submatrix_one_id_left_isometry e.symm.bijective
  have he : u*X*uᴴ = Matrix.reindex e e X := by
    ext a b
    simp [u, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Matrix.reindex_apply, mul_ite, ite_mul, apply_ite]
  have hp (a b : A) : (uᴴ*u) a b = if a=b then 1 else 0 := by
    simpa only [Matrix.Isometry, Matrix.one_apply] using congrFun (congrFun hu a) b
  rw [← he]
  rw [Matrix.traceNorm_isometry_right (u := u) (by
    ext a b
    by_cases hab : a=b <;> simpa [Matrix.one_apply, hab] using hp a b)]
  rw [Matrix.traceNorm_isometry_left (u := u) (by
    ext a b
    by_cases hab : a=b <;> simpa [Matrix.one_apply, hab] using hp a b)]

theorem diamond_amplification_swap {D E r : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    ChannelAmplification T r (Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) X) =
    Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (tensorLeft T X) := by rfl

theorem finiteDiamondNorm_left_reference : ∀ (D E : ℕ) (T : Operator D →ₗ[ℂ] Operator E),
    finiteDiamondNorm T =
      ⨆ r : ℕ, ⨆ X : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ,
        if Matrix.traceNorm X ≤ 1 then
          ENNReal.ofReal (Matrix.traceNorm (ChannelAmplification T r X)) else 0 := by
  intro D E T
  classical
  apply le_antisymm
  · unfold finiteDiamondNorm
    apply iSup_le
    intro r
    apply iSup_le
    intro X
    split_ifs with hx
    · let Y := Matrix.reindex (Equiv.prodComm (Fin D) (Fin r)) (Equiv.prodComm _ _) X
      have hY : Matrix.traceNorm Y ≤ 1 := by rw [diamond_traceNorm_reindex]; exact hx
      have he : Matrix.traceNorm (ChannelAmplification T r Y) = Matrix.traceNorm (tensorLeft T X) := by
        rw [diamond_amplification_swap, diamond_traceNorm_reindex]
      rw [← he]
      exact le_iSup_of_le r (le_iSup_of_le Y (by simp [hY]))
    · exact bot_le
  · apply iSup_le
    intro r
    apply iSup_le
    intro X
    split_ifs with hx
    · let Y := Matrix.reindex (Equiv.prodComm (Fin r) (Fin D)) (Equiv.prodComm _ _) X
      have hY : Matrix.traceNorm Y ≤ 1 := by rw [diamond_traceNorm_reindex]; exact hx
      have he : Matrix.traceNorm (tensorLeft T Y) = Matrix.traceNorm (ChannelAmplification T r X) := by
        have hswap := diamond_amplification_swap T Y
        have hr : Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) Y = X := by
          ext a b; rfl
        rw [hr] at hswap
        rw [hswap, diamond_traceNorm_reindex]
      rw [← he]
      unfold finiteDiamondNorm
      exact le_iSup_of_le r (le_iSup_of_le Y (by simp [hY]))
    · exact bot_le

end Qatlib.Concepts.SchattenDiamond.DiamondNorm

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qatlib.Concepts.SchattenDiamond.DiamondNorm

theorem diamond_tensorLeft_map_sub {D E r : ℕ} (T S : Operator D →ₗ[ℂ] Operator E)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    tensorLeft (T-S) X = tensorLeft T X-tensorLeft S X := by rfl

theorem finiteDiamondDistance_le_of_uniform {D E : ℕ}
    (T S : Operator D →ₗ[ℂ] Operator E) (delta : ℝ) (hd : 0 ≤ delta)
    (h : ∀ r : ℕ, ∀ X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ,
      Matrix.traceNorm (tensorLeft T X-tensorLeft S X) ≤ delta*Matrix.traceNorm X) :
    finiteDiamondDistance T S ≤ ENNReal.ofReal (delta/2) := by
  have hn := (finiteDiamondNorm_le_iff_uniform D E (T-S) delta hd).mpr (by
    intro r X; rw [diamond_tensorLeft_map_sub]; exact h r X)
  unfold finiteDiamondDistance
  calc
    _ ≤ (1/2 : ℝ≥0∞)*ENNReal.ofReal delta := mul_le_mul_right hn _
    _ = _ := by
      rw [show (1/2 : ℝ≥0∞)=ENNReal.ofReal (1/2 : ℝ) by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
      congr 1
      ring
end Qatlib.Concepts.SchattenDiamond.DiamondNorm
