/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.SketchBuild.CompactImportanceSketch
import Qatlib.Concepts.SketchArith.SketchBuild.SketchFrobeniusConcentration
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Qatlib.Concepts.SqEstimation.RejectionSample.SQRejectionAndNorm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QPCAAssume18.ClassicalPca

def frobeniusEnergy {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ) : ℝ :=
  ∑ i, ∑ k, Complex.normSq (A i k)

theorem source_theorem9_frobenius_energy_eq {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ) :
    frobeniusEnergy A = Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared A := by
  unfold frobeniusEnergy Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared
    Qatlib.Concepts.SketchArith.SketchBuild.sketchRowSquared
  rfl

def sketchParameter (normFSq sigma : ℝ) : ℝ := normFSq / sigma ^ 2

def logRatio (k : ℕ) (delta : ℝ) : ℝ := Real.log ((k : ℝ) / delta)

def sketchDimensions (K eps L : ℝ) : ℝ := K ^ 4 / eps ^ 2 * L

def epsParameter (epsSigma epsV eta K : ℝ) : ℝ :=
  min (min ((1 / 10) * epsSigma * (K * Real.sqrt K)) (epsV ^ 2 * eta))
    ((1 / 4) * (Real.sqrt K)⁻¹)

def sigmaPrime (sigma eps normFSq : ℝ) : ℝ := sigma - eps * Real.sqrt normFSq

def algorithm2Cost (K eps L : ℝ) : ℝ := K ^ 12 / eps ^ 6 * L ^ 3

def sqInteractionCost (T K eps L : ℝ) : ℝ := T * K ^ 8 / eps ^ 4 * L ^ 2

def algorithm5Cost (T K eps : ℝ) (k : ℕ) (delta : ℝ) : ℝ :=
  algorithm2Cost K eps (logRatio k delta) + sqInteractionCost T K eps (logRatio k delta)

def sqVectorNormCost (T K eps L nu : ℝ) : ℝ :=
  T * (sketchDimensions K eps L) ^ 2 * K * (nu ^ 2)⁻¹ * L

theorem source_theorem9_eps_le_sigma_branch (epsSigma epsV eta K : ℝ) :
    epsParameter epsSigma epsV eta K ≤ (1 / 10) * epsSigma * (K * Real.sqrt K) :=
  (min_le_left _ _).trans (min_le_left _ _)

theorem source_theorem9_eps_le_vector_branch (epsSigma epsV eta K : ℝ) :
    epsParameter epsSigma epsV eta K ≤ epsV ^ 2 * eta :=
  (min_le_left _ _).trans (min_le_right _ _)

theorem source_theorem9_eps_le_inv_sqrt_branch (epsSigma epsV eta K : ℝ) :
    epsParameter epsSigma epsV eta K ≤ (1 / 4) * (Real.sqrt K)⁻¹ :=
  min_le_right _ _

theorem source_theorem9_k_le_parameter (k : ℕ) (normFSq sigma : ℝ)
    (hsigma : 0 < sigma) (hE : (k : ℝ) * sigma ^ 2 ≤ normFSq) :
    (k : ℝ) ≤ sketchParameter normFSq sigma := by
  unfold sketchParameter
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < sigma ^ 2)]
  linarith

theorem source_theorem9_sigmaPrime_ge (sigma eps K normFSq : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hnorm : normFSq = sigma ^ 2 * K)
    (heps : eps ≤ (1 / 4) * (Real.sqrt K)⁻¹) :
    3 / 4 * sigma ≤ sigmaPrime sigma eps normFSq := by
  have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hsqrt : Real.sqrt normFSq = sigma * Real.sqrt K := by
    rw [hnorm, Real.sqrt_mul (sq_nonneg sigma) K, Real.sqrt_sq hsigma.le]
  unfold sigmaPrime
  rw [hsqrt]
  have hbound : eps * (sigma * Real.sqrt K) ≤ sigma / 4 := by
    have hcancel : (Real.sqrt K)⁻¹ * Real.sqrt K = 1 := inv_mul_cancel₀ (ne_of_gt hsqrtK)
    calc eps * (sigma * Real.sqrt K)
        ≤ ((1 / 4) * (Real.sqrt K)⁻¹) * (sigma * Real.sqrt K) :=
          mul_le_mul_of_nonneg_right heps (by positivity)
      _ = (1 / 4) * sigma * ((Real.sqrt K)⁻¹ * Real.sqrt K) := by ring
      _ = sigma / 4 := by rw [hcancel]; ring
  linarith

theorem source_theorem9_parameter_prime_le (normFSq sigma eps : ℝ)
    (hsigma : 0 < sigma) (hnorm : 0 ≤ normFSq)
    (hprime : 3 / 4 * sigma ≤ sigmaPrime sigma eps normFSq) :
    sketchParameter normFSq (sigmaPrime sigma eps normFSq) ≤
      16 / 9 * sketchParameter normFSq sigma := by
  have hbase : 0 < 3 / 4 * sigma := by positivity
  have hsq : (3 / 4 * sigma) ^ 2 ≤ (sigmaPrime sigma eps normFSq) ^ 2 :=
    pow_le_pow_left₀ hbase.le hprime 2
  unfold sketchParameter
  calc normFSq / (sigmaPrime sigma eps normFSq) ^ 2
      ≤ normFSq / (3 / 4 * sigma) ^ 2 :=
        div_le_div_of_nonneg_left hnorm (by positivity) hsq
    _ = 16 / 9 * (normFSq / sigma ^ 2) := by
        have hsne : sigma ≠ 0 := ne_of_gt hsigma
        field_simp
        ring

theorem source_theorem9_sigma_error_sum (eps epsSigma K normFSq : ℝ)
    (hK : 0 < K) (hnorm : 0 ≤ normFSq)
    (heps : eps ≤ epsSigma * (K * Real.sqrt K)) :
    eps * normFSq / (K * Real.sqrt K) ≤ epsSigma * normFSq := by
  have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hden : 0 < K * Real.sqrt K := by positivity
  rw [div_le_iff₀ hden]
  calc eps * normFSq ≤ (epsSigma * (K * Real.sqrt K)) * normFSq :=
        mul_le_mul_of_nonneg_right heps hnorm
    _ = epsSigma * normFSq * (K * Real.sqrt K) := by ring

theorem source_theorem9_sigma_error_pointwise {ι : Type} [Fintype ι]
    (f : ι → ℝ) (B : ℝ) (hnonneg : ∀ i, 0 ≤ f i) (hsum : ∑ i, f i ≤ B) (i : ι) :
    f i ≤ B :=
  le_trans (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)) hsum

theorem source_theorem9_gap_identification (epsSigma eta normFSq gap : ℝ)
    (hnorm : 0 < normFSq) (hgap : eta * normFSq ≤ gap) (heps : 2 * epsSigma < eta) :
    2 * (epsSigma * normFSq) < gap := by
  have h1 : 2 * epsSigma * normFSq < eta * normFSq :=
    mul_lt_mul_of_pos_right heps hnorm
  nlinarith

theorem source_theorem9_vector_error (epsV eta eps err : ℝ)
    (heta : 0 < eta) (hepsV : 0 ≤ epsV) (heps : eps ≤ epsV ^ 2 * eta)
    (h : err ≤ Real.sqrt (eps / eta)) :
    err ≤ epsV := by
  have hratio : eps / eta ≤ epsV ^ 2 := by
    rw [div_le_iff₀ heta]
    linarith
  calc err ≤ Real.sqrt (eps / eta) := h
    _ ≤ Real.sqrt (epsV ^ 2) := Real.sqrt_le_sqrt hratio
    _ = epsV := Real.sqrt_sq hepsV

theorem source_theorem9_algorithm5_cost (T K eps : ℝ) (k : ℕ) (delta : ℝ) :
    algorithm5Cost T K eps k delta
      = K ^ 12 / eps ^ 6 * (logRatio k delta) ^ 3
        + T * K ^ 8 / eps ^ 4 * (logRatio k delta) ^ 2 := by
  unfold algorithm5Cost algorithm2Cost sqInteractionCost
  rfl

theorem source_theorem9_algorithm2_cost_mono (K K' eps L : ℝ)
    (hK' : 0 ≤ K') (hle : K' ≤ 16 / 9 * K) (heps : 0 < eps) (hL : 0 ≤ L) :
    algorithm2Cost K' eps L ≤ algorithm2Cost (16 / 9 * K) eps L := by
  unfold algorithm2Cost
  have h1 : K' ^ 12 ≤ (16 / 9 * K) ^ 12 := pow_le_pow_left₀ hK' hle 12
  have h2 : K' ^ 12 / eps ^ 6 ≤ (16 / 9 * K) ^ 12 / eps ^ 6 :=
    div_le_div_of_nonneg_right h1 (by positivity)
  exact mul_le_mul_of_nonneg_right h2 (pow_nonneg hL 3)

theorem source_theorem9_sq_output_cost (T K eps L : ℝ) (heps : eps ≠ 0) :
    sqVectorNormCost T K eps L (1 / 100)
      = 10000 * (T * K ^ 9 / eps ^ 4 * L ^ 3) := by
  unfold sqVectorNormCost sketchDimensions
  have h100 : ((1 / 100 : ℝ) ^ 2)⁻¹ = 10000 := by norm_num
  rw [h100]
  field_simp

section WeylBridge

open scoped Matrix.Norms.L2Operator

theorem source_theorem9_singular_weyl_mirsky (O I : Type) [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A B : Matrix O I ℂ) :
    (∀ i : ℕ, |Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i
        - Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues B i| ≤ ‖A - B‖) ∧
    (∑ i ∈ Finset.range (Fintype.card I),
        (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i
          - Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues B i) ^ 2) ≤
      (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius (A - B)) ^ 2 :=
  Qatlib.Concepts.SpectralSketch.SpectrumPerturb.rectangular_singular_weyl_and_mirsky
    O I A B

end WeylBridge

theorem source_theorem9_sketch_description {K : Type} [Fintype K]
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist K) (r : ℕ)
    (ω : Fin r → K) :
    Qatlib.Concepts.SketchArith.SketchBuild.compactSketchBuild p r ω =
      (List.ofFn (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData p r ω), r, r) :=
  Qatlib.Concepts.SketchArith.SketchBuild.compactSketchBuild_eq p r ω

theorem source_theorem9_rejection_trials {I : Type} {B : ℕ} (omega : Fin B → I × Bool) :
    (Qatlib.Concepts.SqEstimation.RejectionSample.sqRejectRun omega).2 ≤ 4 * B :=
  Qatlib.Concepts.SqEstimation.RejectionSample.sqRejectRun_cost_le omega

section FrobeniusBridge

open scoped Matrix.Norms.Frobenius

theorem source_theorem9_frobenius_norm_sq {K C : Type} [Fintype K] [Fintype C]
    (A : Matrix K C ℂ) :
    ‖A‖ ^ 2 = Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared A :=
  Qatlib.Concepts.SketchArith.SketchBuild.sketch_frobenius_norm_sq A

end FrobeniusBridge

theorem source_theorem9_sigma_error_range (k : ℕ) (f : ℕ → ℝ) (B : ℝ)
    (hnonneg : ∀ i ∈ Finset.range k, 0 ≤ f i)
    (hsum : ∑ i ∈ Finset.range k, f i ≤ B) {i : ℕ} (hi : i ∈ Finset.range k) :
    f i ≤ B :=
  le_trans (Finset.single_le_sum hnonneg hi) hsum

theorem source_theorem9_core_content {k : ℕ} (f : ℕ → ℝ)
    (err sigma eps epsSigma epsV eta K normFSq : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hnorm : 0 ≤ normFSq)
    (hnormK : normFSq = sigma ^ 2 * K)
    (heps : eps ≤ epsParameter epsSigma epsV eta K)
    (hnonneg : ∀ i ∈ Finset.range k, 0 ≤ f i)
    (hsum : ∑ i ∈ Finset.range k, f i ≤ eps * normFSq / (K * Real.sqrt K))
    (herr : err ≤ Real.sqrt (eps / eta))
    (heta : 0 < eta) (hepsV : 0 ≤ epsV) (hepsSigma : 0 ≤ epsSigma) :
    3 / 4 * sigma ≤ sigmaPrime sigma eps normFSq
    ∧ sketchParameter normFSq (sigmaPrime sigma eps normFSq)
      ≤ 16 / 9 * sketchParameter normFSq sigma
    ∧ (∀ i ∈ Finset.range k, f i ≤ epsSigma * normFSq)
    ∧ err ≤ epsV := by
  have he1 : eps ≤ epsSigma * (K * Real.sqrt K) := by
    have hb := heps.trans (source_theorem9_eps_le_sigma_branch epsSigma epsV eta K)
    have hp : 0 ≤ epsSigma * (K * Real.sqrt K) := by positivity
    nlinarith
  have he2 : eps ≤ epsV ^ 2 * eta :=
    heps.trans (source_theorem9_eps_le_vector_branch epsSigma epsV eta K)
  have he3 : eps ≤ (1 / 4) * (Real.sqrt K)⁻¹ :=
    heps.trans (source_theorem9_eps_le_inv_sqrt_branch epsSigma epsV eta K)
  have hprime : 3 / 4 * sigma ≤ sigmaPrime sigma eps normFSq :=
    source_theorem9_sigmaPrime_ge sigma eps K normFSq hsigma hK hnormK he3
  refine ⟨hprime,
    source_theorem9_parameter_prime_le normFSq sigma eps hsigma hnorm hprime, ?_, ?_⟩
  · intro i hi
    exact source_theorem9_sigma_error_range k f (epsSigma * normFSq) hnonneg
      (le_trans hsum (source_theorem9_sigma_error_sum eps epsSigma K normFSq hK hnorm he1)) hi
  · exact source_theorem9_vector_error epsV eta eps err heta hepsV he2 herr

end Qatlib.Papers.QPCAAssume18.ClassicalPca
