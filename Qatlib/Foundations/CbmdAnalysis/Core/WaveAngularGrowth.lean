/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.WaveBesselODE
import Qatlib.Foundations.CbmdAnalysis.Core.DysonEnergy
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Complex
open scoped InnerProductSpace ComplexConjugate

section Energy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem wave_pair_energy_le (B D : E →L[ℂ] E) (hB : B.IsSymmetric) (r : ℂ) (u v : E) :
    (inner ℂ u (r • B v)).re + (inner ℂ v (-(r • B u) - r⁻¹ • D u)).re ≤
      (|r.im| * ‖B‖ + ‖r‖⁻¹ * ‖D‖) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have hs : inner ℂ v (B u) = conj (inner ℂ u (B v)) := by
    calc
      inner ℂ v (B u) = conj (inner ℂ (B u) v) := (inner_conj_symm (𝕜 := ℂ) v (B u)).symm
      _ = _ := congrArg (starRingEnd ℂ) (hB.apply_clm u v)
  have he : (inner ℂ u (r • B v)).re + (inner ℂ v (-(r • B u) - r⁻¹ • D u)).re =
      -2 * r.im * (inner ℂ u (B v)).im + (inner ℂ v (-(r⁻¹ • D u))).re := by
    simp only [inner_sub_right, inner_neg_right, inner_smul_right, hs,
      Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hxy : ‖inner ℂ u (B v)‖ ≤ ‖B‖ * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ ‖u‖ * ‖B v‖ := norm_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖B‖ * ‖v‖) := mul_le_mul_of_nonneg_left (B.le_opNorm v) (norm_nonneg _)
      _ = _ := by ring
  have hcross : -2 * r.im * (inner ℂ u (B v)).im ≤
      2 * |r.im| * ‖B‖ * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ |-2 * r.im * (inner ℂ u (B v)).im| := le_abs_self _
      _ = 2 * |r.im| * |(inner ℂ u (B v)).im| := by rw [abs_mul, abs_mul]; norm_num
      _ ≤ 2 * |r.im| * (‖B‖ * ‖u‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans hxy) (by positivity)
      _ = _ := by ring
  have hpert : (inner ℂ v (-(r⁻¹ • D u))).re ≤ ‖r‖⁻¹ * ‖D‖ * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ ‖v‖ * ‖-(r⁻¹ • D u)‖ := re_inner_le_norm (𝕜 := ℂ) _ _
      _ = ‖v‖ * (‖r‖⁻¹ * ‖D u‖) := by rw [norm_neg, norm_smul, norm_inv]
      _ ≤ ‖v‖ * (‖r‖⁻¹ * (‖D‖ * ‖u‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (D.le_opNorm u) (by positivity))
          (norm_nonneg _)
      _ = _ := by ring
  have hsquare : 2 * ‖u‖ * ‖v‖ ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  have hcross' := mul_le_mul_of_nonneg_left hsquare (mul_nonneg (abs_nonneg r.im) (norm_nonneg B))
  have hpert' :=
      mul_le_mul_of_nonneg_left hsquare
      (mul_nonneg (inv_nonneg.mpr (norm_nonneg r)) (norm_nonneg D))
  rw [he]
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg r))
    (norm_nonneg D)) (norm_nonneg u)) (norm_nonneg v)]

theorem wave_pair_trajectory_norm_le (B D : E →L[ℂ] E) (hB : B.IsSymmetric) (r : ℂ)
    (u v : ℝ → E)
    (hu : ∀ s, HasDerivAt u (r • B (v s)) s)
    (hv : ∀ s, HasDerivAt v (-(r • B (u s)) - r⁻¹ • D (u s)) s)
    (hv0 : v 0 = 0) (t : ℝ) (ht : 0 ≤ t) :
    ‖u t‖ ≤ Real.exp (t * (|r.im| * ‖B‖ + ‖r‖⁻¹ * ‖D‖)) * ‖u 0‖ := by
  letI := InnerProductSpace.rclikeToReal ℂ E
  let c := |r.im| * ‖B‖ + ‖r‖⁻¹ * ‖D‖
  let S : ℝ → ℝ := fun s => ‖u s‖ ^ 2 + ‖v s‖ ^ 2
  have hS (s : ℝ) : HasDerivAt S
      (2 * ((inner ℂ (u s) (r • B (v s))).re +
        (inner ℂ (v s) (-(r • B (u s)) - r⁻¹ • D (u s))).re)) s := by
    have hsu : HasDerivAt (fun s => ‖u s‖ ^ 2)
        (2 * (inner ℂ (u s) (r • B (v s))).re) s := by
      simpa only [real_inner_eq_re_inner (𝕜 := ℂ)] using! (hu s).norm_sq
    have hsv : HasDerivAt (fun s => ‖v s‖ ^ 2)
        (2 * (inner ℂ (v s) (-(r • B (u s)) - r⁻¹ • D (u s))).re) s := by
      simpa only [real_inner_eq_re_inner (𝕜 := ℂ)] using! (hv s).norm_sq
    convert! hsu.add hsv using 1
    ring
  let f : ℝ → ℝ := fun s => Real.exp (-2 * c * s) * S s
  have hd (s : ℝ) : HasDerivAt f
      (Real.exp (-2 * c * s) * (-2 * c) * S s + Real.exp (-2 * c * s) *
        (2 * ((inner ℂ (u s) (r • B (v s))).re +
          (inner ℂ (v s) (-(r • B (u s)) - r⁻¹ • D (u s))).re))) s := by
    simpa only [id_eq, mul_one] using! (((hasDerivAt_id s).const_mul (-2 * c)).exp).mul (hS s)
  have hm : Antitone f := by
    apply antitone_of_hasDerivAt_nonpos hd
    intro s
    (try dsimp only)
    simp only [Pi.zero_apply]
    have hh := mul_le_mul_of_nonneg_left (wave_pair_energy_le B D hB r (u s) (v s))
      (Real.exp_pos (-2 * c * s)).le
    change _ ≤ Real.exp (-2 * c * s) * (c * S s) at hh
    nlinarith
  have hb := hm ht
  have hf0 : f 0 = ‖u 0‖ ^ 2 := by simp [f, S, hv0]
  rw [hf0] at hb
  have hu2 : Real.exp (-2 * c * t) * ‖u t‖ ^ 2 ≤ ‖u 0‖ ^ 2 := by
    have hnonneg : 0 ≤ Real.exp (-2 * c * t) * ‖v t‖ ^ 2 := by positivity
    dsimp [f, S] at hb
    nlinarith
  have hexp : Real.exp (-2 * c * t) = Real.exp (-c * t) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp, ← mul_pow] at hu2
  have hroot := (sq_le_sq₀ (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    (norm_nonneg _)).mp hu2
  have hh := mul_le_mul_of_nonneg_left hroot (Real.exp_pos (c * t)).le
  rw [← mul_assoc, ← Real.exp_add, show c * t + -c * t = 0 by ring,
    Real.exp_zero, one_mul] at hh
  change ‖u t‖ ≤ Real.exp (t * c) * ‖u 0‖
  simpa only [mul_comm c t] using hh

end Energy

section ActualOperator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem wavePropagator_angular_of_square (L B C : E →L[ℂ] E)
    (hB : B.IsSymmetric) (hBC : B * C = 1) (hCB : C * B = 1)
    (r : ℂ) (hr : r ≠ 0) (t : ℝ) (ht : 0 ≤ t) :
    ‖wavePropagator (L + r ^ 2 • (B * B)) (t : ℂ)‖ ≤
      Real.exp (t * (|r.im| * ‖B‖ + ‖r‖⁻¹ * ‖C * L‖)) := by
  let A := L + r ^ 2 • (B * B)
  let W : ℝ → (E →L[ℂ] E) := fun s => wavePropagator A (s : ℂ)
  have hW (s : ℝ) : HasDerivAt W (deriv W s) s := by
    change HasDerivAt (fun s : ℝ => wavePropagator A (s : ℂ))
      (deriv (fun s : ℝ => wavePropagator A (s : ℂ)) s) s
    rw [wavePropagator_real_deriv_eq]
    exact Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vector_hasDerivAt_comp_ofReal
        (wavePropagator_analytic A (s : ℂ)).differentiableAt.hasDerivAt
  have hW2 (s : ℝ) : HasDerivAt (deriv W) (-(A * W s)) s :=
    wavePropagator_real_hasDerivAt_deriv A s
  have hCA : C * A = C * L + r ^ 2 • B := by
    simp only [A, mul_add, mul_smul_comm, ← mul_assoc, hCB, one_mul]
  change ‖W t‖ ≤ _
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro x
  let u : ℝ → E := fun s => W s x
  let v : ℝ → E := fun s => r⁻¹ • C (deriv W s x)
  have hu (s : ℝ) : HasDerivAt u (r • B (v s)) s := by
    have h :=
        ((ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hW s)
    change HasDerivAt u (deriv W s x) s at h
    convert! h using 1
    dsimp only [v]
    rw [map_smul, smul_smul, mul_inv_cancel₀ hr, one_smul]
    change (B * C) (deriv W s x) = _
    rw [hBC, ContinuousLinearMap.one_apply]
  have hv (s : ℝ) : HasDerivAt v (-(r • B (u s)) - r⁻¹ • (C * L) (u s)) s := by
    have h :=
        ((ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hW2 s)
    have h' := ((r⁻¹ • C).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h
    change HasDerivAt v (r⁻¹ • C ((-(A * W s)) x)) s at h'
    convert! h' using 1
    change -(r • B (W s x)) - r⁻¹ • (C * L) (W s x) =
      r⁻¹ • C (-(A (W s x)))
    rw [map_neg]
    change _ = r⁻¹ • (-((C * A) (W s x)))
    rw [hCA, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_neg, smul_add, smul_smul]
    have hr2 : r⁻¹ * r ^ 2 = r := by field_simp
    rw [hr2]
    abel
  have hv0 : v 0 = 0 := by
    have hd : deriv W 0 = 0 := (wavePropagator_real_hasDerivAt_zero A).deriv
    simp [v, hd]
  have h := wave_pair_trajectory_norm_le B (C * L) hB r u v hu hv hv0 t ht
  simpa only [u, W, Complex.ofReal_zero, wavePropagator_zero,
    ContinuousLinearMap.one_apply] using h

end ActualOperator

section Matrix
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem wavePropagator_matrix_toOperator (A : Matrix n n ℂ) (t : ℂ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)) (wavePropagator A t) =
      wavePropagator ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)) A) t := by
  let e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)
  let L := e.toAlgEquiv.toLinearMap.toContinuousLinearMap
  have h := L.map_tsum (wave_series_summable A t)
  change e (∑' k : ℕ, (((2 * k).factorial : ℂ)⁻¹) • (-(t ^ 2) • A) ^ k) =
    ∑' k : ℕ, e ((((2 * k).factorial : ℂ)⁻¹) • (-(t ^ 2) • A) ^ k) at h
  change e (∑' k : ℕ, (((2 * k).factorial : ℂ)⁻¹) • (-(t ^ 2) • A) ^ k) = _
  rw [h, wavePropagator]
  apply tsum_congr
  intro k
  simp only [map_smul, map_pow]
  rfl

theorem wavePropagator_matrix_angular (L H : Matrix n n ℂ) (hH : H.PosDef)
    (r : ℂ) (hr : r ≠ 0) (t : ℝ) (ht : 0 ≤ t) :
    ‖wavePropagator (L + r ^ 2 • H) (t : ℂ)‖ ≤
      Real.exp (t * (|r.im| * Real.sqrt ‖H‖ +
        ‖r‖⁻¹ * ‖Ring.inverse (CFC.sqrt H) * L‖)) := by
  let e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)
  let B := CFC.sqrt H
  let C := Ring.inverse B
  have hBpos : B.PosSemidef := (CFC.sqrt_nonneg H).posSemidef
  have hBsym : (e B).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hBpos.isHermitian
  have hBunit : IsUnit B := (CFC.isUnit_sqrt_iff H hH.posSemidef.nonneg).mpr hH.isUnit
  have hBC : e B * e C = 1 := by
    rw [← map_mul]
    exact (congrArg e (Ring.mul_inverse_cancel B hBunit)).trans e.map_one
  have hCB : e C * e B = 1 := by
    rw [← map_mul]
    exact (congrArg e (Ring.inverse_mul_cancel B hBunit)).trans e.map_one
  have hBB : B * B = H := CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg
  have hnorm : ‖e B‖ = Real.sqrt ‖H‖ := by
    have hs : star B = B := hBpos.isHermitian
    have hn := CStarRing.norm_star_mul_self (x := B)
    rw [hs, hBB] at hn
    change ‖B‖ = Real.sqrt ‖H‖
    rw [hn, Real.sqrt_mul_self (norm_nonneg B)]
  have h := wavePropagator_angular_of_square (e L) (e B) (e C) hBsym hBC hCB r hr t ht
  rw [← map_mul, hBB, ← map_smul, ← map_add] at h
  rw [← wavePropagator_matrix_toOperator, hnorm, ← map_mul] at h
  exact h

end Matrix
end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
