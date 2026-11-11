/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.Parameters

/-!
# Accuracy of actual PCA records

Defines correctness of retained PCA outputs through squared singular value estimates and vector
approximation up to a complex phase. The theorems turn simultaneous Gram control, a singular
value cutoff, and spectral gaps into record accuracy and a failure bound for [Tang2021].

## Main statements

* `pca_actual_record_accuracy`: Under the cutoff, gap, and good Gram hypotheses, every retained
  small-sketch value has error at most `s * sketchSquared A`, and its lifted vector is within
  `v` of the target up to phase [Tang2021].
* `pca_actual_pca_failure`: With the specified parameters, the probability that the actual
  sketch record fails `pcaRecordCorrect` is at most `delta` [Tang2021].

## References

* [Tang, 2021][Tang2021]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.RandCompile.ChannelBudget

/-- Event probability is monotone under implication for decidable predicates on sample records. -/
theorem pca_event_mono_decidable {X : Type} [Fintype X] (p : FinDist X) {L : ℕ}
    (P Q : (Fin L→X)→Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ z,P z→Q z) : p.probEvent P≤p.probEvent Q := by
  unfold FinDist.probEvent
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z,h z (Finset.mem_filter.mp hz).2⟩
  · intro z _ _
    exact Finset.prod_nonneg fun i _ => p.nonneg _

/-- Embeds a retained index in a larger finite index type using `hkN`. -/
def pcaRetainedIndex {k N : ℕ} (hkN : k ≤ N) (i : Fin k) : Fin N :=
    ⟨i.val, lt_of_lt_of_le i.isLt hkN⟩

/-- The number of singular values above the positive cutoff is bounded by the chosen Gram sample
count. -/
theorem pca_retained_le_samples {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (k : ℕ) (hkd : k ≤ d) (sigma : ℝ) (hsigma : 0 < sigma)
    (hcut : ∀ i ∈ Finset.range k, sigma ≤ matrixSingularValues A i) (e delta : ℝ) :
    k ≤ pcaGramSamples (sketchSquared A / sigma^2) e delta := by
  have hc := pca_cutoff_count A k hkd sigma hsigma hcut
  have hkR : (k:ℝ) ≤ sketchSquared A/sigma^2 := (le_div_iff₀ (sq_pos_of_pos hsigma)).mpr hc
  exact_mod_cast hkR.trans (pcaGramSamples_rank (sketchSquared A/sigma^2) e delta).2

/-- Under the cutoff, gap, and good Gram hypotheses, every retained small-sketch value has error
at most `s * sketchSquared A`, and its lifted vector is within `v` of the target up to phase
[Tang2021]. -/
theorem pca_actual_record_accuracy {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (hd : 0 < d) (k : ℕ) (hk : 1 ≤ k)
    (hkn : k ≤ n) (hkd : k ≤ d) (sigma eta s v delta : ℝ)
    (hsigma : 0 < sigma) (heta : 0 < eta) (hs : 0 < s) (hv : 0 < v) (hv1 : v ≤ 1)
    (hcut : ∀ i ∈ Finset.range k, sigma ≤ matrixSingularValues A i)
    (hgap : ∀ i ∈ Finset.range k,
      eta*sketchSquared A ≤ matrixSingularValues A i^2-matrixSingularValues A (i+1)^2)
    (z : (Fin (pcaGramSamples (sketchSquared A/sigma^2)
      (epsParameter s v eta (sketchSquared A/sigma^2)) delta) → Fin n) ×
      (Fin (pcaGramSamples (sketchSquared A/sigma^2)
        (epsParameter s v eta (sketchSquared A/sigma^2)) delta) → Fin d))
    (hgood : ¬pcaBadGram A hA hd _
      (pcaGramTolerance (sketchSquared A/sigma^2) (epsParameter s v eta (sketchSquared A/sigma^2))) z) :
    ∀ i : Fin k,
      let iq := pcaRetainedIndex (pca_retained_le_samples A k hkd sigma hsigma hcut
        (epsParameter s v eta (sketchSquared A/sigma^2)) delta) i;
      let R := pcaRowSketch A hA _ z.1;
      let W := pcaSmallMatrix A hA hd _ z.1 z.2;
      |pcaSmallValue W iq-matrixSingularValues A i.val^2| ≤ s*sketchSquared A ∧
      ∃ zeta : ℂ, ‖zeta‖=1 ∧
        ‖pcaOutput R W iq-zeta • pcaTarget A (pcaRetainedIndex hkd i)‖ ≤ v := by
  let F := sketchSquared A
  let K := F/sigma^2
  let e := epsParameter s v eta K
  let t := pcaGramTolerance K e
  let q := pcaGramSamples K e delta
  let R := pcaRowSketch A hA q z.1
  let W := pcaSmallMatrix A hA hd q z.1 z.2
  have hK1 : 1≤K := pca_effective_rank_one_le A k hk hkd sigma hsigma hcut
  have hK0 : 0<K := by linarith
  have he : 0<e := pca_source_parameter_pos s v eta K hs hv heta hK0
  have ht0 : 0≤t := by dsimp [t,pcaGramTolerance]; positivity
  have hF : F=K*sigma^2 := by dsimp [K]; field_simp
  have hEta1 := pca_relative_gap_le_one A hA k hk hkd eta hgap
  have htCut := pca_tolerance_cutoff F sigma K e hsigma hK1 hF
    (source_theorem9_eps_le_inv_sqrt_branch s v eta K)
  have htSpec := pca_tolerance_spectrum K e s hK1 hs.le
    (source_theorem9_eps_le_sigma_branch s v eta K)
  have htGap := pca_tolerance_gap K e v eta hK1 hv.le hv1 heta.le
    (source_theorem9_eps_le_vector_branch s v eta K)
  have hrow : spectralFrobenius (Rᴴ*R-Aᴴ*A)≤t*F := le_of_not_gt fun h => hgood (Or.inl h)
  have hcol : spectralFrobenius (W*Wᴴ-R*Rᴴ)≤t*F := le_of_not_gt fun h => hgood (Or.inr h)
  have hRenergy : sketchSquared R≤F := pcaRowSketch_energy A hA q
    (pcaGramSamples_rank K e delta).1 z.1
  have hRnorm := pca_row_operator_bound A R sigma K hsigma hK1 hF hRenergy
  intro i
  let iq := pcaRetainedIndex (pca_retained_le_samples A k hkd sigma hsigma hcut e delta) i
  let id := pcaRetainedIndex hkd i
  have hi : i.val<min n d := lt_min (lt_of_lt_of_le i.isLt hkn) (lt_of_lt_of_le i.isLt hkd)
  have hspec : |pcaSmallValue W iq-matrixSingularValues A i.val^2|≤2*t*F :=
    pca_actual_small_spectrum A hA hd t ht0 z hgood hi
  have hcutSq : sigma^2≤matrixSingularValues A i.val^2 :=
    pow_le_pow_left₀ hsigma.le (hcut i.val (Finset.mem_range.mpr i.isLt)) 2
  have hmu : sigma^2/2≤pcaSmallValue W iq := by
    have h := (abs_le.mp hspec).1
    nlinarith
  have hclose : |pcaSmallValue W iq-matrixSingularValues A id^2|≤(eta*F)/2 :=
    hspec.trans (by nlinarith [mul_le_mul_of_nonneg_right htGap hA.le])
  obtain ⟨zeta,hzeta,hphase⟩ := pca_output_phase A R W k id iq i.isLt sigma (eta*F)
    (t*F) (t*F) hsigma (mul_pos heta hA) hgap hmu htCut hclose hrow hcol
  refine ⟨hspec.trans (by nlinarith [mul_le_mul_of_nonneg_right htSpec hA.le]), zeta,hzeta,?_⟩
  exact hphase.trans (pca_tolerance_vector F sigma K e eta v (pcaSmallValue W iq) ‖R‖
    hA hsigma hK1 he.le heta hEta1 hv.le hv1 hF
    (source_theorem9_eps_le_vector_branch s v eta K) hmu hRnorm)

/-- Correctness of a sketch record: all retained squared singular value estimates meet the
energy-scaled tolerance, and all lifted vectors meet the phase-adjusted vector tolerance. -/
def pcaRecordCorrect {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (k q : ℕ) (hkd : k≤d) (hkq : k≤q)
    (s v : ℝ) (z : (Fin q→Fin n) × (Fin q→Fin d)) : Prop :=
  ∀ i : Fin k,
    |pcaSmallValue (pcaSmallMatrix A hA hd q z.1 z.2) (pcaRetainedIndex hkq i)-
      matrixSingularValues A i.val^2| ≤ s*sketchSquared A ∧
    ∃ zeta : ℂ, ‖zeta‖=1 ∧
      ‖pcaOutput (pcaRowSketch A hA q z.1) (pcaSmallMatrix A hA hd q z.1 z.2)
        (pcaRetainedIndex hkq i)-zeta • pcaTarget A (pcaRetainedIndex hkd i)‖≤v

/-- With the specified parameters, the probability that the actual sketch record fails
`pcaRecordCorrect` is at most `delta` [Tang2021]. -/
theorem pca_actual_pca_failure {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (hd : 0 < d) (k : ℕ) (hk : 1 ≤ k)
    (hkn : k ≤ n) (hkd : k ≤ d) (sigma eta s v delta : ℝ)
    (hsigma : 0 < sigma) (heta : 0 < eta) (hs : 0 < s) (hv : 0 < v) (hv1 : v ≤ 1)
    (hdelta : 0<delta) (hdelta1 : delta<1)
    (hcut : ∀ i ∈ Finset.range k, sigma ≤ matrixSingularValues A i)
    (hgap : ∀ i ∈ Finset.range k,
      eta*sketchSquared A ≤ matrixSingularValues A i^2-matrixSingularValues A (i+1)^2) :
    let K := sketchSquared A/sigma^2;
    let e := epsParameter s v eta K;
    let q := pcaGramSamples K e delta;
    (pcaSketchLaw A hA hd q).probEvent (fun omega : Fin 1→((Fin q→Fin n) × (Fin q→Fin d)) =>
      ¬pcaRecordCorrect A hA hd k q hkd
        (pca_retained_le_samples A k hkd sigma hsigma hcut e delta) s v (omega 0)) ≤ delta := by
  (try dsimp only)
  let K := sketchSquared A/sigma^2
  let e := epsParameter s v eta K
  have hK : 0<K := div_pos hA (sq_pos_of_pos hsigma)
  have he := pca_source_parameter_pos s v eta K hs hv heta hK
  apply (pca_event_mono_decidable (pcaSketchLaw A hA hd (pcaGramSamples K e delta))
    (fun omega : Fin 1→((Fin (pcaGramSamples K e delta)→Fin n) × (Fin (pcaGramSamples K e delta)→Fin d)) =>
      ¬pcaRecordCorrect A hA hd k (pcaGramSamples K e delta) hkd
        (pca_retained_le_samples A k hkd sigma hsigma hcut e delta) s v (omega 0))
    (fun omega => pcaBadGram A hA hd _ (pcaGramTolerance K e) (omega 0)) ?_).trans
    (pca_actual_gram_concentration A hA hd K e delta hK he hdelta hdelta1)
  intro omega hbad
  by_contra hgood
  exact hbad (pca_actual_record_accuracy A hA hd k hk hkn hkd sigma eta s v delta
    hsigma heta hs hv hv1 hcut hgap (omega 0) hgood)

end Qatlib.Papers.QPCAAssume18.ClassicalPca
