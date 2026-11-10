/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.ReciprocalPolynomial
import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.BlockEncoding.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Polynomial Matrix Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator

noncomputable def reciprocalError (δ : ℝ) (n : ℕ) : ℝ :=
  (1 - δ ^ 2) ^ n / δ

theorem reciprocalPolynomial_error_eq (n : ℕ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) :
    |(reciprocalPolynomial n).eval x - x⁻¹| = (1 - x ^ 2) ^ n / x := by
  have hq : 0 ≤ 1 - x ^ 2 := by nlinarith
  rw [abs_sub_comm, inv_sub_reciprocalPolynomial_eval n (ne_of_gt hx0),
    abs_of_nonneg (div_nonneg (pow_nonneg hq n) hx0.le)]

theorem reciprocalPolynomial_error_le (n : ℕ) {δ x : ℝ}
    (hδ : 0 < δ) (hx : x ∈ Set.Icc δ 1) :
    |(reciprocalPolynomial n).eval x - x⁻¹| ≤ reciprocalError δ n := by
  have hx0 : 0 < x := hδ.trans_le hx.1
  have hq : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.2]
  have hqδ : 0 ≤ 1 - δ ^ 2 := by nlinarith [hx.1, hx.2]
  have hle : 1 - x ^ 2 ≤ 1 - δ ^ 2 := by
    have hs := pow_le_pow_left₀ hδ.le hx.1 2
    linarith
  rw [reciprocalPolynomial_error_eq n hx0 hx.2, reciprocalError]
  exact div_le_div₀ (pow_nonneg hqδ n) (pow_le_pow_left₀ hq hle n) hδ hx.1

theorem reciprocalError_nonneg {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (n : ℕ) : 0 ≤ reciprocalError δ n := by
  exact div_nonneg (pow_nonneg (by nlinarith : 0 ≤ 1 - δ ^ 2) n) hδ.le

theorem complexReciprocalPolynomial_error_le (n : ℕ) {δ x : ℝ}
    (hδ : 0 < δ) (hx : x ∈ Set.Icc δ 1) :
    ‖(complexReciprocalPolynomial n).eval (x : ℂ) - (x : ℂ)⁻¹‖ ≤
      reciprocalError δ n := by
  rw [complexReciprocalPolynomial_eval_real, ← Complex.ofReal_inv,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact reciprocalPolynomial_error_le n hδ hx

theorem scaledReciprocalPolynomial_error_le (n : ℕ) (c : ℝ) {δ x : ℝ}
    (hδ : 0 < δ) (hx : x ∈ Set.Icc δ 1) :
    ‖(C (c : ℂ) * complexReciprocalPolynomial n).eval (x : ℂ) -
      (c : ℂ) / (x : ℂ)‖ ≤ |c| * reciprocalError δ n := by
  rw [Polynomial.eval_mul, Polynomial.eval_C, div_eq_mul_inv, ← mul_sub,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (complexReciprocalPolynomial_error_le n hδ hx)
    (abs_nonneg c)

theorem tendsto_reciprocalError {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun n : ℕ => reciprocalError δ n) atTop (𝓝 0) := by
  have hq0 : 0 ≤ 1 - δ ^ 2 := by nlinarith
  have hq1 : 1 - δ ^ 2 < 1 := by nlinarith [sq_pos_of_pos hδ]
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).div_const δ
  simpa [reciprocalError] using h

theorem reciprocalPolynomial_eventually_error_lt {δ ε : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ Set.Icc δ 1,
      |(reciprocalPolynomial n).eval x - x⁻¹| < ε := by
  have he : ∀ᶠ n : ℕ in atTop, reciprocalError δ n < ε :=
    (tendsto_order.mp (tendsto_reciprocalError hδ hδ1)).2 ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  exact ⟨N, fun n hn x hx => (reciprocalPolynomial_error_le n hδ hx).trans_lt (hN n hn)⟩

theorem reciprocalPolynomial_tendstoUniformlyOn {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    TendstoUniformlyOn (fun n x => (reciprocalPolynomial n).eval x)
      (fun x : ℝ => x⁻¹) atTop (Set.Icc δ 1) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := reciprocalPolynomial_eventually_error_lt hδ hδ1 hε
  apply Filter.eventually_atTop.mpr
  refine ⟨N, fun n hn x hx => ?_⟩
  simpa only [Real.dist_eq, abs_sub_comm] using hN n hn x hx

theorem reciprocalPolynomial_eval_sq_le (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1) 1) :
    ((reciprocalPolynomial n).eval x) ^ 2 ≤ (n : ℝ) := by
  have hq0 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hq1 : 1 - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  let S : ℝ := ∑ k ∈ Finset.range n, (1 - x ^ 2) ^ k
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun k _ => pow_nonneg hq0 k)
  have hSle : S ≤ (n : ℝ) := by
    calc
      S ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum (fun _k _ => pow_le_one₀ hq0 hq1)
      _ = (n : ℝ) := by simp
  have htel : x ^ 2 * S = 1 - (1 - x ^ 2) ^ n := by
    have h := mul_reciprocalPolynomial_eval n x
    rw [reciprocalPolynomial_eval_sum] at h
    change x * (x * S) = _ at h
    nlinarith [h]
  have hxs : x ^ 2 * S ≤ 1 := by
    rw [htel]
    exact sub_le_self _ (pow_nonneg hq0 n)
  have he : ((reciprocalPolynomial n).eval x) ^ 2 = (x ^ 2 * S) * S := by
    rw [reciprocalPolynomial_eval_sum]
    change (x * S) ^ 2 = _
    ring
  rw [he]
  calc
    (x ^ 2 * S) * S ≤ 1 * S := mul_le_mul_of_nonneg_right hxs hS0
    _ ≤ (n : ℝ) := by simpa using hSle

theorem reciprocalPolynomial_abs_le_sqrt (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1) 1) :
    |(reciprocalPolynomial n).eval x| ≤ Real.sqrt (n : ℝ) := by
  have h := Real.sqrt_le_sqrt (reciprocalPolynomial_eval_sq_le n hx)
  simpa only [Real.sqrt_sq_eq_abs] using h

theorem scaledReciprocalPolynomial_norm_le_one (n : ℕ) (c : ℝ)
    (hc : |c| * Real.sqrt (n : ℝ) ≤ 1) {x : ℝ}
    (hx : x ∈ Set.Icc (-1) 1) :
    ‖(C (c : ℂ) * complexReciprocalPolynomial n).eval (x : ℂ)‖ ≤ 1 := by
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    complexReciprocalPolynomial_eval_real, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (reciprocalPolynomial_abs_le_sqrt n hx)
    (abs_nonneg c)).trans hc

theorem normalizedReciprocalPolynomial_norm_le_one {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Set.Icc (-1) 1) :
    ‖(C (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) *
      complexReciprocalPolynomial n).eval (x : ℂ)‖ ≤ 1 := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  apply scaledReciprocalPolynomial_norm_le_one n (Real.sqrt (n : ℝ))⁻¹ _ hx
  rw [abs_of_pos (inv_pos.mpr hs), inv_mul_cancel₀ (ne_of_gt hs)]

theorem reciprocal_response_norm_at_one {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) :
    ‖(responseP base zs).eval (1 : ℂ)‖ = 1 := by
  have h : Complex.normSq ((responseP base zs).eval (1 : ℂ)) = 1 := by
    simpa using response_normalization hb zs hzs 1
  rw [Complex.norm_def, h, Real.sqrt_one]

theorem reciprocal_response_endpoint_error {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (c : ℝ) :
    abs (1 - |c|) ≤ ‖(responseP base zs).eval (1 : ℂ) - (c : ℂ)‖ := by
  have h := abs_norm_sub_norm_le ((responseP base zs).eval (1 : ℂ)) (c : ℂ)
  simpa only [reciprocal_response_norm_at_one hb zs hzs, Complex.norm_real, Real.norm_eq_abs] using
      h

section Pseudoinverse
variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

noncomputable def reciprocalMatrixApprox (A : Matrix O I ℂ) (n : ℕ) : Matrix I O ℂ :=
  (A * aeval (Aᴴ * A) ((reciprocalFactor n).map Complex.ofRealHom))ᴴ

theorem complexReciprocalPolynomial_eq_oddSingularPolynomial (n : ℕ) :
    complexReciprocalPolynomial n =
      oddSingularPolynomial ((reciprocalFactor n).map Complex.ofRealHom) := by
  exact complexReciprocalPolynomial_eq_factor n

theorem reciprocalMatrixApprox_eq_oddSingularTransform (A : Matrix O I ℂ) (n : ℕ) :
    reciprocalMatrixApprox A n =
      (oddSingularTransform A (fun x => (complexReciprocalPolynomial n).eval (x : ℂ)))ᴴ := by
  rw [reciprocalMatrixApprox, mul_gram_aeval_eq_oddSingularTransform]
  apply congrArg Matrix.conjTranspose
  apply congrArg (oddSingularTransform A)
  funext x
  simp [complexReciprocalPolynomial_eq_factor]

theorem reciprocalMatrixApprox_error_le (A : Matrix O I ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hupper : ∀ i : Fin (Fintype.card I), matrixSingularValues A i ≤ 1)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      δ ≤ matrixSingularValues A i) (n : ℕ) :
    ‖reciprocalMatrixApprox A n - matrixPseudoinverse A‖ ≤ reciprocalError δ n := by
  rw [reciprocalMatrixApprox_eq_oddSingularTransform, matrixPseudoinverse,
    ← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
  apply oddSingularTransform_error_le_positive A _ _ (reciprocalError_nonneg hδ hδ1 n)
  intro i hi
  exact complexReciprocalPolynomial_error_le n hδ ⟨hgap i hi, hupper i⟩

end Pseudoinverse
end Qatlib.Concepts.QsvtCore.LinearSystems
