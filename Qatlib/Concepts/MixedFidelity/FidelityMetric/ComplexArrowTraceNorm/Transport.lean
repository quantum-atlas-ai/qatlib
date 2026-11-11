/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.TransportDefs
import Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.Block
import Qatlib.Concepts.BlockEncoding.EncodingCore.PrepareUnitary
import Mathlib.Tactic

/-!
# Isometric transport of arrow-block trace norms

A directional block supported on two unit vectors is an isometric conjugate of `fullBlock`. This
representation transports its trace norm to the explicit arrow-block formula, including scalar
normalization and the balanced-tail case. See [Bhatia1997].

## Main statements

* `exists_directional_isometry`: the directional block factors through an isometry.
* `normalized_directionalBlock_half_traceNorm`: the explicit normalized trace norm.
* `balanced_directionalBlock_half_traceNorm`: reduction to `errorNumerator`.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm

/-- The rectangular frame with distinguished columns `u` and `v` and remaining columns supplied
by `complexPrepare`. -/
private def directionalFrame (l n : ℕ) (u : Fin l → ℂ) (v : Fin (n + 1) → ℂ) :
    Matrix (Fin l ⊕ Fin (n + 1)) (Fin 2 ⊕ Fin n) ℂ :=
  fun a b => match a, b with
  | .inl i, .inl k => if k = 0 then u i else 0
  | .inl _, .inr _ => 0
  | .inr j, .inl k => if k = 1 then v j else 0
  | .inr j, .inr k => Qatlib.Concepts.BlockEncoding.EncodingCore.complexPrepare v 0 j k.succ

set_option maxHeartbeats 1500000 in

/-- For unit vectors `u` and `v`, a single isometry realizes every corresponding directional
block as `J * fullBlock * Jᴴ`. -/
theorem exists_directional_isometry (l n : ℕ) (u : Fin l → ℂ) (v : Fin (n + 1) → ℂ)
    (hu : ∑ i, ‖u i‖ ^ 2 = 1) (hv : ∑ j, ‖v j‖ ^ 2 = 1) :
    ∃ J : Matrix (Fin l ⊕ Fin (n + 1)) (Fin 2 ⊕ Fin n) ℂ,
      J.Isometry ∧ ∀ (ell mass tail : ℝ) (z : ℂ),
        Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.directionalBlock l (n + 1) u v ell mass tail z =
          J * Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.fullBlock n ell mass tail z * Jᴴ := by
  let U := Qatlib.Concepts.BlockEncoding.EncodingCore.complexPrepare v (0 : Fin (n + 1))
  have hU :=
      Qatlib.Concepts.BlockEncoding.EncodingCore.complexPrepare_unitary v (0 : Fin (n + 1)) hv
  have hleft : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hU)
  have hright : U * Uᴴ = 1 := mul_eq_one_comm.mp hleft
  have hcol (j : Fin (n + 1)) : U j 0 = v j := by
    have h :=
        congrFun (Qatlib.Concepts.BlockEncoding.EncodingCore.complexPrepare_mulVec_ket v 0) j
    simpa [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, mul_ite] using h
  have hgram (a b : Fin (n + 1)) :
      (∑ i, star (U i a) * U i b) = if a = b then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using
      congrFun (congrFun hleft a) b
  have hrows (a b : Fin (n + 1)) :
      (∑ i, U a i * star (U b i)) = if a = b then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using
      congrFun (congrFun hright a) b
  have hnu : (∑ i, star (u i) * u i) = 1 := by
    simpa [Qatlib.Foundations.PureStateMath.Inner, dotProduct] using
      (Qatlib.Foundations.PureStateMath.normalized_iff_inner_self u).mp hu
  have hnv : (∑ i, star (v i) * v i) = 1 := by
    simpa [Qatlib.Foundations.PureStateMath.Inner, dotProduct] using
      (Qatlib.Foundations.PureStateMath.normalized_iff_inner_self v).mp hv
  simp only [RCLike.star_def] at hnu hnv
  have hiso : (directionalFrame l n u v).Isometry := by
    ext a b
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        fin_cases a <;> fin_cases b <;>
          simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
            directionalFrame, hnu, hnv]
      | inr b =>
        fin_cases a
        · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
            directionalFrame]
        · simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
            directionalFrame, Matrix.one_apply, hcol] using! hgram 0 b.succ
    | inr a =>
      cases b with
      | inl b =>
        fin_cases b
        · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
            directionalFrame]
        · simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
            directionalFrame, Matrix.one_apply, hcol] using hgram a.succ 0
      | inr b =>
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
          directionalFrame, Matrix.one_apply] using hgram a.succ b.succ
  have htail (a b : Fin (n + 1)) :
      (∑ i : Fin n, U a i.succ * star (U b i.succ)) =
        (if a = b then 1 else 0) - v a * star (v b) := by
    have h := hrows a b
    rw [Fin.sum_univ_succ, hcol, hcol] at h
    linear_combination h
  have hweighted (a b : Fin (n + 1)) (s : ℂ) :
      (∑ i : Fin n, s * (U a i.succ * (starRingEnd ℂ) (U b i.succ))) =
        s * ((if a = b then 1 else 0) - v a * (starRingEnd ℂ) (v b)) := by
    simpa only [Finset.mul_sum, RCLike.star_def] using congrArg (s * ·) (htail a b)
  refine ⟨directionalFrame l n u v, hiso, ?_⟩
  intro ell mass tail z
  ext a b
  cases a <;> cases b <;>
    simp [Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.directionalBlock, Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.directionOuter, directionalFrame, Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.fullBlock, Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.arrow,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, mul_assoc] <;> ring_nf
  all_goals simp
  rename_i a b
  have hscaled :
      (∑ i : Fin n, (tail : ℂ) * Qatlib.Concepts.BlockEncoding.EncodingCore.complexPrepare v 0 a i.succ *
        (starRingEnd ℂ) (Qatlib.Concepts.BlockEncoding.EncodingCore.complexPrepare v 0 b i.succ)) =
      (tail : ℂ) * ((if a = b then 1 else 0) - v a * (starRingEnd ℂ) (v b)) := by
    simpa only [mul_assoc] using hweighted a b (tail : ℂ)
  rw [hscaled]
  split_ifs <;> ring

/-- For unit direction vectors and a nonempty second block, the trace norm of any complex-scaled
directional block equals that of the corresponding scaled arrow block with tail dimension `m
- 1`. -/
private theorem directional_traceNorm_scaled (l m : ℕ) (hm : 1 ≤ m)
    (u : Fin l → ℂ) (v : Fin m → ℂ)
    (hu : ∑ i, ‖u i‖ ^ 2 = 1) (hv : ∑ j, ‖v j‖ ^ 2 = 1)
    (ell mass tail : ℝ) (z scale : ℂ) :
    Matrix.traceNorm (scale • Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.directionalBlock l m u v ell mass tail z) =
      Matrix.traceNorm (scale • Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.fullBlock (m - 1) ell mass tail z) := by
  cases m with
  | zero => omega
  | succ n =>
    obtain ⟨J, hJ, htransport⟩ :=
        Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.exists_directional_isometry l n u v hu hv
    letI : DecidableEq (Fin 2 ⊕ Fin n) := Classical.decEq _
    have hJ' : J.Isometry := by
      ext i j
      have hij := congrFun (congrFun hJ i) j
      by_cases h : i = j <;> simpa [Matrix.one_apply, h] using hij
    have heq : scale • Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.directionalBlock l (n + 1) u v ell mass tail z =
        J * (scale • Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.fullBlock n ell mass tail z) * Jᴴ := by
      rw [htransport]
      simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [heq, Matrix.traceNorm_isometry_right hJ', Matrix.traceNorm_isometry_left hJ']
    simp

/-- For unit directions and positive `q`, the normalized half trace norm is the explicit arrow
norm plus `(m - 1) * |tail|`, divided by `2 * q`. -/
theorem normalized_directionalBlock_half_traceNorm (l m : ℕ) (hm : 1 ≤ m)
    (u : Fin l → ℂ) (v : Fin m → ℂ)
    (hu : ∑ i, ‖u i‖ ^ 2 = 1) (hv : ∑ j, ‖v j‖ ^ 2 = 1)
    (ell mass tail q : ℝ) (z : ℂ) (hq : 0 < q) :
    Matrix.traceNorm (((q⁻¹ : ℝ) : ℂ) • Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.directionalBlock l m u v ell mass tail z) / 2 =
      (max |mass| (Real.sqrt ((2 * ell + mass) ^ 2 + 4 * ‖z‖ ^ 2)) +
        ((m - 1 : ℕ) : ℝ) * |tail|) / (2 * q) := by
  rw [directional_traceNorm_scaled l m hm u v hu hv]
  exact Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.normalized_fullBlock_half_traceNorm (m - 1) ell mass tail q z hq

/-- For unit directions, nonnegative mass, positive normalization, and `(m - 1) * tail = mass`,
the normalized half trace norm equals `errorNumerator ell mass (‖z‖ ^ 2) / q`. -/
theorem balanced_directionalBlock_half_traceNorm (l m : ℕ) (hm : 1 ≤ m)
    (u : Fin l → ℂ) (v : Fin m → ℂ)
    (hu : ∑ i, ‖u i‖ ^ 2 = 1) (hv : ∑ j, ‖v j‖ ^ 2 = 1)
    (ell mass tail q : ℝ) (z : ℂ) (hq : 0 < q) (hmass : 0 ≤ mass)
    (hbalance : ((m - 1 : ℕ) : ℝ) * tail = mass) :
    Matrix.traceNorm (((q⁻¹ : ℝ) : ℂ) • Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.directionalBlock l m u v ell mass tail z) / 2 =
      Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.errorNumerator ell mass (‖z‖ ^ 2) / q := by
  rw [directional_traceNorm_scaled l m hm u v hu hv]
  exact Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.balanced_fullBlock_half_traceNorm (m - 1) ell mass tail q z hq hmass hbalance
end Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm
