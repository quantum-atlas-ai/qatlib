/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixWeights.WeightsCore
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Data.Finset.Max
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.MatrixWeights.WeightsCore

namespace Qatlib.Concepts.MatrixWeights.LambdaMin

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder
set_option warningAsError false

private theorem mwScalarChord (eta x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-eta * x) ≤ 1 - (1 - Real.exp (-eta)) * x := by
  have h := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (-eta))
    (sub_nonneg.mpr hx1) hx0 (by ring : (1 - x) + x = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero] at h
  convert! h using 1 <;> ring

private theorem mwChordOrder (D : ℕ) (M : Operator D) (eta : ℝ)
    (hM : M.PosSemidef) (hM1 : M ≤ 1) :
    NormedSpace.exp (-eta • M) ≤ 1 - (1 - Real.exp (-eta)) • M := by
  let H : HermitianMat (Fin D) ℂ := ⟨M, hM.isHermitian⟩
  have hc : H.cfc (fun x => Real.exp (-eta * x)) ≤
      H.cfc (fun x => 1 - (1 - Real.exp (-eta)) * x) := by
    rw [← sub_nonneg, ← HermitianMat.cfc_sub_apply, HermitianMat.cfc_nonneg_iff]
    intro i
    have hlo : 0 ≤ H.H.eigenvalues i := hM.eigenvalues_nonneg i
    have hhi : H.H.eigenvalues i ≤ 1 :=
      (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hM.isHermitian 1).mpr
        (by simpa only [one_smul] using! hM1) i
    linarith [mwScalarChord eta (H.H.eigenvalues i) hlo hhi]
  have he : H.cfc (fun x => Real.exp (-eta * x)) = ((-eta) • H).exp := by
    rw [HermitianMat.exp, ← HermitianMat.cfc_const_mul_id (r := -eta),
      ← HermitianMat.cfc_comp_apply]
  have hr : H.cfc (fun x => 1 - (1 - Real.exp (-eta)) * x) =
      1 - (1 - Real.exp (-eta)) • H := by
    rw [HermitianMat.cfc_sub_apply, HermitianMat.cfc_const, HermitianMat.cfc_const_mul_id]
    simp only [one_smul]
  rw [he, hr] at hc
  have hmat : ((-eta) • H).exp.mat = NormedSpace.exp (-eta • M) := by
    rw [mmw_hermitian_exp_mat]
    rfl
  simpa only [HermitianMat.le_iff, HermitianMat.mat_sub, HermitianMat.mat_smul,
    HermitianMat.mat_one, hmat] using! hc

private theorem mwChordRatio (D : ℕ) (M : ℕ → Operator D) (eta : ℝ) (t : ℕ)
    (hD : 0 < D) (hM : ∀ s, (M s).PosSemidef ∧ M s ≤ 1) :
    (Matrix.trace (mmwWeight D M eta (t + 1))).re /
      (Matrix.trace (mmwWeight D M eta t)).re ≤
      1 - (1 - Real.exp (-eta)) * (Matrix.trace (M t * mmwState D M eta t)).re := by
  let S := ∑ s ∈ Finset.range t, M s
  have hs : S.IsHermitian := isSelfAdjoint_sum _ (fun s _ => (hM s).1.isHermitian)
  have hx : (-eta • S).IsHermitian := hs.smul (by simp [IsSelfAdjoint])
  have hy : (-eta • M t).IsHermitian := (hM t).1.isHermitian.smul (by simp [IsSelfAdjoint])
  have hgt := matrix_mw_golden_thompson_trace_potential D (-eta • S) (-eta • M t) hx hy
  have hnext : mmwWeight D M eta (t + 1) = NormedSpace.exp ((-eta • S) + (-eta • M t)) := by
    simp only [mmwWeight, Finset.sum_range_succ, S, smul_add]
  rw [← hnext] at hgt
  change (Matrix.trace (mmwWeight D M eta (t + 1))).re ≤
    (Matrix.trace (mmwWeight D M eta t * NormedSpace.exp (-eta • M t))).re at hgt
  have hm := mmw_trace_mul_mono D (mmwWeight D M eta t) _ _
    (mmwWeight_posSemidef D M eta t hD (fun s => (hM s).1.isHermitian))
    (mwChordOrder D (M t) eta (hM t).1 (hM t).2)
  have hu := hgt.trans hm
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, Complex.sub_re, Complex.smul_re, smul_eq_mul] at hu
  rw [Matrix.trace_mul_comm (mmwWeight D M eta t) (M t)] at hu
  have hz := (matrix_mw_actual_gibbs_iterates_density D M eta t hD
    (fun s => (hM s).1.isHermitian)).1
  rw [mmw_trace_loss_normalization]
  apply (div_le_iff₀ hz).mpr
  have he : (1 - (1 - Real.exp (-eta)) *
      ((Matrix.trace (M t * mmwWeight D M eta t)).re /
        (Matrix.trace (mmwWeight D M eta t)).re)) *
      (Matrix.trace (mmwWeight D M eta t)).re =
      (Matrix.trace (mmwWeight D M eta t)).re -
        (1 - Real.exp (-eta)) * (Matrix.trace (M t * mmwWeight D M eta t)).re := by
    field_simp
  rw [he]
  exact hu

private theorem mwChordLogStep (D : ℕ) (M : ℕ → Operator D) (eta : ℝ) (t : ℕ)
    (hD : 0 < D) (hM : ∀ s, (M s).PosSemidef ∧ M s ≤ 1) :
    Real.log (Matrix.trace (mmwWeight D M eta (t + 1))).re -
      Real.log (Matrix.trace (mmwWeight D M eta t)).re ≤
      -(1 - Real.exp (-eta)) * (Matrix.trace (M t * mmwState D M eta t)).re := by
  have hp (s : ℕ) := (matrix_mw_actual_gibbs_iterates_density D M eta s hD
    (fun j => (hM j).1.isHermitian)).1
  have hr := mwChordRatio D M eta t hD hM
  rw [← Real.log_div (hp (t + 1)).ne' (hp t).ne']
  exact (Real.log_le_sub_one_of_pos (div_pos (hp (t + 1)) (hp t))).trans (by linarith)

theorem matrix_mw_chord_comparator
    (D T : ℕ) (M : ℕ → Operator D) (eta : ℝ) (sigma : Operator D)
    (hD : 0 < D) (hM : ∀ s, (M s).PosSemidef ∧ M s ≤ 1)
    (hsigma : IsDensityOperator sigma) :
    (1 - Real.exp (-eta)) *
        (∑ t ∈ Finset.range T, (Matrix.trace (M t * mmwState D M eta t)).re) ≤
      Real.log D + eta * (∑ t ∈ Finset.range T, (Matrix.trace (M t * sigma)).re) := by
  let c := 1 - Real.exp (-eta)
  have hu (n : ℕ) : Real.log (Matrix.trace (mmwWeight D M eta n)).re ≤
      Real.log D - c * (∑ t ∈ Finset.range n, (Matrix.trace (M t * mmwState D M eta t)).re) := by
    induction n with
    | zero => simp [mmwWeight, Matrix.trace_one]
    | succ n ih =>
      have hs := mwChordLogStep D M eta n hD hM
      rw [Finset.sum_range_succ]
      dsimp [c] at *
      nlinarith
  let X : Operator D := -eta • ∑ t ∈ Finset.range T, M t
  have hs : (∑ t ∈ Finset.range T, M t).IsHermitian :=
    isSelfAdjoint_sum _ (fun s _ => (hM s).1.isHermitian)
  have hx : X.IsHermitian := hs.smul (by simp [IsSelfAdjoint])
  have hj := mmw_density_exp_jensen D X sigma hx hsigma
  have hl := Real.log_le_log (Real.exp_pos _) hj
  rw [Real.log_exp] at hl
  change (Matrix.trace (sigma * X)).re ≤ Real.log (Matrix.trace (mmwWeight D M eta T)).re at hl
  have he : (Matrix.trace (sigma * X)).re =
      -eta * (∑ t ∈ Finset.range T, (Matrix.trace (M t * sigma)).re) := by
    simp only [X, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul,
      Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [Matrix.trace_mul_comm]
  rw [he] at hl
  have hmain : c * (∑ t ∈ Finset.range T, (Matrix.trace (M t * mmwState D M eta t)).re) ≤
      Real.log D + eta * (∑ t ∈ Finset.range T, (Matrix.trace (M t * sigma)).re) := by
    linarith [hu T]
  exact hmain

theorem matrix_mw_sum_trace_le_scaled_comparator
    (D T : ℕ) (M : ℕ → Operator D) (eta : ℝ) (sigma : Operator D)
    (hD : 0 < D) (heta : 0 < eta)
    (hM : ∀ s, (M s).PosSemidef ∧ M s ≤ 1) (hsigma : IsDensityOperator sigma) :
    (∑ t ∈ Finset.range T, (Matrix.trace (M t * mmwState D M eta t)).re) ≤
      (1 + eta) * (∑ t ∈ Finset.range T, (Matrix.trace (M t * sigma)).re) +
        (1 + eta) * Real.log D / eta := by
  let c := 1 - Real.exp (-eta)
  have hmain := matrix_mw_chord_comparator D T M eta sigma hD hM hsigma
  have hn : 0 ≤ ∑ t ∈ Finset.range T, (Matrix.trace (M t * mmwState D M eta t)).re := by
    apply Finset.sum_nonneg
    intro t _
    have hdens := (matrix_mw_actual_gibbs_iterates_density D M eta t hD
      (fun s => (hM s).1.isHermitian)).2
    have hzero : (0 : Operator D) ≤ M t :=
        Matrix.le_iff.mpr (by simpa only [sub_zero] using! (hM t).1)
    have h := mmw_trace_mul_mono D (mmwState D M eta t) 0 (M t) hdens.1 hzero
    rw [Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, Matrix.trace_mul_comm] at h
    exact h
  have hexp : Real.exp (-eta) ≤ (1 + eta)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos eta) (by positivity : 0 < 1 + eta)).mpr
      (by simpa only [add_comm] using! Real.add_one_le_exp eta)
  have hc : eta / (1 + eta) ≤ c := by
    have hi : eta / (1 + eta) = 1 - (1 + eta)⁻¹ := by field_simp; ring
    rw [hi]
    exact sub_le_sub_left hexp 1
  have hbound := (mul_le_mul_of_nonneg_right hc hn).trans hmain
  have hdiv : eta * (∑ t ∈ Finset.range T, (Matrix.trace (M t * mmwState D M eta t)).re) /
      (1 + eta) ≤ Real.log D + eta * (∑ t ∈ Finset.range T, (Matrix.trace (M t * sigma)).re) := by
    simpa only [div_mul_eq_mul_div] using! hbound
  have hscaled := (div_le_iff₀ (by positivity : 0 < 1 + eta)).mp hdiv
  apply (mul_le_mul_iff_left₀ heta).mp
  have hidentity : ((1 + eta) * (∑ t ∈ Finset.range T, (Matrix.trace (M t * sigma)).re) +
      (1 + eta) * Real.log D / eta) * eta =
      (Real.log D + eta * (∑ t ∈ Finset.range T, (Matrix.trace (M t * sigma)).re)) * (1 + eta) := by
    field_simp
    ring
  rw [hidentity]
  simpa only [mul_comm] using! hscaled

private theorem mwSourceRateBound (eps : ℝ) (heps : 0 < eps) (hepshalf : eps < 1 / 2) :
    -Real.log (1 - eps) ≤ eps + eps ^ 2 := by
  have hrem : 0 < 1 - eps := by linarith
  have hnorm : ‖(eps : ℂ)‖ = eps := Complex.norm_of_nonneg heps.le
  have htail := Complex.norm_log_one_sub_inv_sub_self_le
    (show ‖(eps : ℂ)‖ < 1 by rw [hnorm]; linarith)
  have hre := (Complex.re_le_norm (Complex.log (1 - (eps : ℂ))⁻¹ - (eps : ℂ))).trans htail
  have hcast : (1 - (eps : ℂ))⁻¹ = (((1 - eps)⁻¹ : ℝ) : ℂ) := by
    simp only [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one]
  rw [Complex.sub_re, hcast, Complex.log_ofReal_re, Real.log_inv, Complex.ofReal_re,
    hnorm] at hre
  have hinv : (1 - eps)⁻¹ ≤ (2 : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ hrem).mpr
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hinv (sq_nonneg eps)]

theorem matrix_mw_source_comparator
    (D T : ℕ) (M : ℕ → Operator D) (eps : ℝ) (sigma : Operator D)
    (hD : 0 < D) (heps : 0 < eps) (hepshalf : eps < 1 / 2)
    (hM : ∀ s ∈ Finset.range T, (M s).PosSemidef ∧ M s ≤ 1)
    (hsigma : IsDensityOperator sigma) :
    (∑ t ∈ Finset.range T,
        (Matrix.trace (M t * mmwState D M (-Real.log (1 - eps)) t)).re) ≤
      (1 + eps) * (∑ t ∈ Finset.range T, (Matrix.trace (M t * sigma)).re) +
        Real.log D / eps := by
  let eta := -Real.log (1 - eps)
  let N : ℕ → Operator D := fun s => if s < T then M s else 0
  have hN (s : ℕ) : (N s).PosSemidef ∧ N s ≤ 1 := by
    dsimp only [N]
    split_ifs with hs
    · exact hM s (Finset.mem_range.mpr hs)
    · exact ⟨Matrix.PosSemidef.zero, Matrix.le_iff.mpr
        (by simpa only [sub_zero] using! (Matrix.PosSemidef.one : (1 : Operator D).PosSemidef))⟩
  have hprefix (t : ℕ) (ht : t ≤ T) : mmwState D N eta t = mmwState D M eta t := by
    have hsum : (∑ s ∈ Finset.range t, N s) = ∑ s ∈ Finset.range t, M s := by
      apply Finset.sum_congr rfl
      intro s hs
      exact if_pos (lt_of_lt_of_le (Finset.mem_range.mp hs) ht)
    simp only [mmwState, mmwWeight, hsum]
  have hactual : (∑ t ∈ Finset.range T, (Matrix.trace (N t * mmwState D N eta t)).re) =
      ∑ t ∈ Finset.range T, (Matrix.trace (M t * mmwState D M eta t)).re := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [hprefix t (Finset.mem_range.mp ht).le]
    simp only [N, if_pos (Finset.mem_range.mp ht)]
  have hcomparator : (∑ t ∈ Finset.range T, (Matrix.trace (N t * sigma)).re) =
      ∑ t ∈ Finset.range T, (Matrix.trace (M t * sigma)).re := by
    apply Finset.sum_congr rfl
    intro t ht
    simp only [N, if_pos (Finset.mem_range.mp ht)]
  have hsharp := matrix_mw_chord_comparator D T N eta sigma hD hN hsigma
  rw [hactual, hcomparator] at hsharp
  have hchord : 1 - Real.exp (-eta) = eps := by
    dsimp only [eta]
    rw [neg_neg, Real.exp_log (by linarith : 0 < 1 - eps)]
    ring
  rw [hchord] at hsharp
  have hnonneg : 0 ≤ ∑ t ∈ Finset.range T, (Matrix.trace (M t * sigma)).re := by
    apply Finset.sum_nonneg
    intro t ht
    have hzero : (0 : Operator D) ≤ M t :=
      Matrix.le_iff.mpr (by simpa only [sub_zero] using! (hM t ht).1)
    have h := mmw_trace_mul_mono D sigma 0 (M t) hsigma.1 hzero
    rw [Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, Matrix.trace_mul_comm] at h
    exact h
  have hrate := mul_le_mul_of_nonneg_right (mwSourceRateBound eps heps hepshalf) hnonneg
  apply (mul_le_mul_iff_left₀ heps).mp
  have hcancel : eps * (Real.log D / eps) = Real.log D := by
    field_simp [heps.ne']
  dsimp only [eta] at hsharp ⊢
  nlinarith

theorem matrix_mw_source_min_eigenvalue
    (D T : ℕ) (M : ℕ → Operator D) (eps : ℝ)
    (hD : 0 < D) (heps : 0 < eps) (hepshalf : eps < 1 / 2)
    (hM : ∀ s ∈ Finset.range T, (M s).PosSemidef ∧ M s ≤ 1) :
    let hS : (∑ t ∈ Finset.range T, M t).IsHermitian :=
      isSelfAdjoint_sum _ (fun t ht => (hM t ht).1.isHermitian)
    ∃ i : Fin D, (∀ j, hS.eigenvalues i ≤ hS.eigenvalues j) ∧
      (∑ t ∈ Finset.range T,
          (Matrix.trace (M t * mmwState D M (-Real.log (1 - eps)) t)).re) ≤
        (1 + eps) * hS.eigenvalues i + Real.log D / eps := by
  (try dsimp only)
  let S : Operator D := ∑ t ∈ Finset.range T, M t
  have hS : S.IsHermitian := isSelfAdjoint_sum _ (fun t ht => (hM t ht).1.isHermitian)
  have hne : (Finset.univ : Finset (Fin D)).Nonempty :=
    ⟨⟨0, hD⟩, Finset.mem_univ _⟩
  obtain ⟨i, _hi, hmin⟩ := Finset.exists_min_image Finset.univ hS.eigenvalues hne
  refine ⟨i, fun j => hmin j (Finset.mem_univ j), ?_⟩
  let v : QState (Fin D) := ⇑(hS.eigenvectorBasis i)
  have hv : Normalized v := (normalized_iff_norm_toEuclidean_fromVec v).mpr
    (hS.eigenvectorBasis.orthonormal.1 i)
  have he : S *ᵥ v = (hS.eigenvalues i : ℂ) • v := by
    simpa only [RCLike.real_smul_eq_coe_smul] using! hS.mulVec_eigenvectorBasis i
  have htrace : Matrix.trace (S * outerProduct v) = Qatlib.Foundations.PureStateMath.Inner v (S *ᵥ v) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, outerProduct, Matrix.of_apply,
      Qatlib.Foundations.PureStateMath.Inner, dotProduct, Matrix.mulVec, Pi.star_apply, starRingEnd_apply]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hsum : (∑ t ∈ Finset.range T, (Matrix.trace (M t * outerProduct v)).re) =
      hS.eigenvalues i := by
    have hsumtrace : (∑ t ∈ Finset.range T, (Matrix.trace (M t * outerProduct v)).re) =
        (Matrix.trace (S * outerProduct v)).re := by
      simp only [S, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
    rw [hsumtrace, htrace, he, Qatlib.Foundations.PureStateMath.Inner, dotProduct_smul]
    change ((hS.eigenvalues i : ℂ) * Qatlib.Foundations.PureStateMath.Inner v v).re = hS.eigenvalues i
    rw [(normalized_iff_inner_self v).mp hv, mul_one, Complex.ofReal_re]
  have hbound := matrix_mw_source_comparator D T M eps (outerProduct v)
    hD heps hepshalf hM (isDensityOperator_outerProduct hv)
  rwa [hsum] at hbound

end Qatlib.Concepts.MatrixWeights.LambdaMin
