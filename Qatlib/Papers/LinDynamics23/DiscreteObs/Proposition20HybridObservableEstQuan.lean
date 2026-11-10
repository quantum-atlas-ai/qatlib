/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LinDynamics23.DiscreteObs.Proposition20HybridObservableEstStat
import Qatlib.Papers.LinDynamics23.DiscreteObs.Proposition20HybridObservableBiasQuan
import Qatlib.Concepts.ShadowModels.UStatBackend.FinitePairUStatistic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.UStatBackend
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

namespace Qatlib.Papers.LinDynamics23.DiscreteObs

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

theorem hybridObservable_sample_bound {I : Type} [Fintype I] [DecidableEq I]
    {N : ℕ} (c : Fin N → ℂ) (W : Fin N → Matrix I I ℂ) (O : Matrix I I ℂ)
    (x : QState I) (hx : ‖toEuclidean_fromVec x‖ = 1)
    (hW : ∀ j, W j ∈ 𝐔[I]) (a : Fin N × Fin N) :
    |hybridObservableSampleValue c W O x a| ≤ ‖O‖ := by
  have hw (j : Fin N) : ‖toEuclidean_fromVec (W j *ᵥ x)‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp
      (normalized_applyGate (hW j) ((normalized_iff_norm_toEuclidean_fromVec x).mpr hx))
  have hi : ‖Inner (W a.1 *ᵥ x) (O *ᵥ (W a.2 *ᵥ x))‖ ≤ ‖O‖ := by
    simpa only [hw, mul_one] using! adv_inner_matrix_bound O (W a.1 *ᵥ x) (W a.2 *ᵥ x)
  unfold hybridObservableSampleValue
  split_ifs with hzero
  · simpa only [abs_zero] using! norm_nonneg O
  · have hd : 0 < ‖c a.1‖ * ‖c a.2‖ :=
      lt_of_le_of_ne (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Ne.symm hzero)
    rw [abs_div, abs_of_pos hd, div_le_iff₀ hd]
    calc
      _ ≤ ‖star (c a.1) * c a.2 * Inner (W a.1 *ᵥ x) (O *ᵥ (W a.2 *ᵥ x))‖ :=
        Complex.abs_re_le_norm _
      _ = (‖c a.1‖ * ‖c a.2‖) * ‖Inner (W a.1 *ᵥ x) (O *ᵥ (W a.2 *ᵥ x))‖ :=
        by rw [norm_mul, norm_mul, norm_star]
      _ ≤ (‖c a.1‖ * ‖c a.2‖) * ‖O‖ := mul_le_mul_of_nonneg_left hi hd.le
      _ = _ := mul_comm _ _

theorem hybridObservable_sample_expect {I : Type} [Fintype I] [DecidableEq I]
    {N : ℕ} (c : Fin N → ℂ) (hγ : 0 < ∑ j, ‖c j‖)
    (W : Fin N → Matrix I I ℂ) (O : Matrix I I ℂ) (x : QState I) :
    (hybridObservableSampleDist c hγ).expect (hybridObservableSampleValue c W O x) =
      (Inner ((∑ j, c j • W j) *ᵥ x) (O *ᵥ ((∑ j, c j • W j) *ᵥ x))).re /
        (∑ j, ‖c j‖)^2 := by
  have hterm (a : Fin N × Fin N) :
      (hybridObservableSampleDist c hγ).prob a * hybridObservableSampleValue c W O x a =
      (star (c a.1) * c a.2 * Inner (W a.1 *ᵥ x) (O *ᵥ (W a.2 *ᵥ x))).re /
        (∑ j, ‖c j‖)^2 := by
    dsimp only [hybridObservableSampleDist, hybridObservableSampleValue]
    split_ifs with hz
    · rcases mul_eq_zero.mp hz with h1 | h2
      · have hc : c a.1 = 0 := norm_eq_zero.mp h1
        simp [hc]
      · have hc : c a.2 = 0 := norm_eq_zero.mp h2
        simp [hc]
    · field_simp [hz]
      exact mul_div_cancel_left₀ _ hz
  unfold FinDist.expect
  simp_rw [hterm]
  rw [← Finset.sum_div]
  congr 1
  simpa only [Fintype.sum_prod_type, Complex.re_sum] using!
    congrArg Complex.re (hybridObservable_double_sum c W O x)

theorem hybridObservable_mom_log_bound (M : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hM : Real.log (1 / δ) / Real.log (2 / Real.sqrt 3) ≤ (M : ℝ)) :
    (3 : ℝ)^(M / 2) / 2^M ≤ δ := by
  have hs : 0 < Real.sqrt 3 := by positivity
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 ≤ Real.sqrt 3 := by nlinarith
  have hslt : Real.sqrt 3 < 2 := by nlinarith
  have ha : 1 < 2 / Real.sqrt 3 := (lt_div_iff₀ hs).mpr (by simpa)
  have hlog : 0 < Real.log (2 / Real.sqrt 3) := Real.log_pos ha
  have hb := (div_le_iff₀ hlog).mp hM
  rw [one_div, Real.log_inv] at hb
  have hnum : (3 : ℝ)^(M / 2) ≤ (Real.sqrt 3)^M := by
    calc
      _ = (Real.sqrt 3)^(2 * (M / 2)) := by rw [pow_mul, hs2]
      _ ≤ _ := pow_le_pow_right₀ hs1 (m := 2 * (M / 2)) (n := M) (by omega)
  have hinv : Real.sqrt 3 / 2 = (2 / Real.sqrt 3)⁻¹ := by field_simp
  have htail : (Real.sqrt 3 / 2)^M ≤ δ := by
    apply (Real.log_le_log_iff (pow_pos (by positivity) M) hδ).mp
    rw [Real.log_pow, hinv, Real.log_inv]
    linarith
  calc
    _ ≤ (Real.sqrt 3)^M / 2^M := div_le_div_of_nonneg_right hnum (by positivity)
    _ = (Real.sqrt 3 / 2)^M := (div_pow _ _ _).symm
    _ ≤ δ := htail

theorem proposition20HybridObservableEstimation : Proposition20HybridObservableEstimation := by
  intro I _ _ N c W B i₀ O target ε δ Lm Mm hW hB _hO hε hδ hLm hMm hγ
  (try dsimp only)
  intro hbias hLbudget hMbudget
  let x : QState I := B *ᵥ Ket i₀
  let v : QState I := (∑ j, c j • W j) *ᵥ x
  let γ : ℝ := ∑ j, ‖c j‖
  let p := hybridObservableSampleDist c hγ
  let f := hybridObservableSampleValue c W O x
  have hx : ‖toEuclidean_fromVec x‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec x).mp (normalized_applyGate hB (normalized_ket i₀))
  have hg : 0 < γ := hγ
  have hg2 : 0 < γ^2 := pow_pos hg 2
  have hmean : γ^2 * p.expect f = (Inner v (O *ᵥ v)).re := by
    have h := hybridObservable_sample_expect c hγ W O x
    change p.expect f = (Inner v (O *ᵥ v)).re / γ^2 at h
    rw [h]
    field_simp
  have hval (a : Fin N × Fin N) : (f a)^2 ≤ ‖O‖^2 := by
    have h := hybridObservable_sample_bound c W O x hx hW a
    simpa only [sq_abs] using!
      (pow_le_pow_left₀ (abs_nonneg (f a)) h 2)
  have hvar : p.variance f ≤ ‖O‖^2 := by
    calc
      _ ≤ ∑ a, p.prob a * (f a)^2 := finite_pair_variance_le_second p f
      _ ≤ ∑ a, p.prob a * ‖O‖^2 := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hval a) (p.nonneg a)
      _ = _ := by rw [← Finset.sum_mul, p.sum_one, one_mul]
  let ε₀ : ℝ := ε / (2 * γ^2)
  have he0 : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hbudget : 16 * γ^4 * ‖O‖^2 ≤ (Lm : ℝ) * ε^2 :=
    (div_le_iff₀ (pow_pos hε 2)).mp hLbudget
  have hscale : 4 * ‖O‖^2 ≤ (Lm : ℝ) * ε₀^2 := by
    dsimp [ε₀]
    rw [div_pow, ← mul_div_assoc,
      show (2 * γ^2)^2 = 4 * γ^4 by ring, le_div_iff₀ (by positivity)]
    nlinarith
  have hvar0 : 4 * p.variance f ≤ (Lm : ℝ) * ε₀^2 :=
    (mul_le_mul_of_nonneg_left hvar (by norm_num)).trans hscale
  have hincl (ω : Fin Mm → Fin Lm → Fin N × Fin N)
      (hbad : ε < |γ^2 * p.medianOfMeans f ω - target|) :
      ε₀ < |p.medianOfMeans f ω - p.expect f| := by
    by_contra hn
    have hsmall : |p.medianOfMeans f ω - p.expect f| ≤ ε₀ := le_of_not_gt hn
    have hsample : |γ^2 * p.medianOfMeans f ω - (Inner v (O *ᵥ v)).re| ≤ ε / 2 := by
      rw [← hmean, ← mul_sub, abs_mul, abs_of_pos hg2]
      calc
        _ ≤ γ^2 * ε₀ := mul_le_mul_of_nonneg_left hsmall hg2.le
        _ = ε / 2 := by dsimp [ε₀]; field_simp
    have htotal := (abs_sub_le (γ^2 * p.medianOfMeans f ω)
      (Inner v (O *ᵥ v)).re target).trans (add_le_add hsample hbias)
    linarith
  change (∑ ω ∈ Finset.univ.filter
      (fun ω : Fin Mm → Fin Lm → Fin N × Fin N =>
        ε < |γ^2 * p.medianOfMeans f ω - target|), ∏ m, p.probOf (ω m)) ≤ δ
  calc
    _ ≤ ∑ ω ∈ Finset.univ.filter
        (fun ω : Fin Mm → Fin Lm → Fin N × Fin N =>
          ε₀ < |p.medianOfMeans f ω - p.expect f|), ∏ m, p.probOf (ω m) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ω hω
        rcases Finset.mem_filter.mp hω with ⟨hmem, hbad⟩
        exact Finset.mem_filter.mpr ⟨hmem, hincl ω hbad⟩
      · intro ω _ _
        exact Finset.prod_nonneg fun m _ => Finset.prod_nonneg fun j _ => p.nonneg _
    _ ≤ (3 : ℝ)^(Mm / 2) / 2^Mm :=
      p.median_of_means_concentration f hLm hMm ε₀ he0 hvar0
    _ ≤ δ := hybridObservable_mom_log_bound Mm δ hδ hMbudget

end Qatlib.Papers.LinDynamics23.DiscreteObs
