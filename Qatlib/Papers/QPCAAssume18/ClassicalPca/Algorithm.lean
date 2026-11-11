/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.PaidSmallSvd
import Qatlib.Papers.QPCAAssume18.ClassicalPca.AccessBudget

/-!
# Correct and accessible classical PCA records

Combines spectral accuracy with sample-and-query access for the actual PCA sketch. A good record
has nonzero retained outputs with bounded rejection inflation, and the parameter choice gives
simultaneous correctness and accessibility with high probability in the construction of
[Tang2021].

## Main statements

* `pca_actual_record_access`: Under the cutoff, precision, and good Gram hypotheses, every
  retained output is nonzero and has sample-and-query inflation at most `4 * q * K`.
* `source_classical_pca_producer`: Under the stated cutoff and spectral gap assumptions, actual
  PCA preprocessing produces a correct and accessible record with failure probability at most
  `delta` [Tang2021].

## References

* [Tang, 2021][Tang2021]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Matrix
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SqEstimation.RejectionSample

/-- Under the cutoff, precision, and good Gram hypotheses, every retained output is nonzero and
has sample-and-query inflation at most `4 * q * K`. -/
theorem pca_actual_record_access {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (k : ℕ) (hk : 1≤k) (hkn : k≤n) (hkd : k≤d)
    (sigma e delta : ℝ) (hsigma : 0<sigma)
    (he : e≤(1/4)*(Real.sqrt (sketchSquared A/sigma^2))⁻¹)
    (hcut : ∀ i∈Finset.range k,sigma≤Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i)
    (z : (Fin (pcaGramSamples (sketchSquared A/sigma^2) e delta)→Fin n) ×
      (Fin (pcaGramSamples (sketchSquared A/sigma^2) e delta)→Fin d))
    (hgood : ¬pcaBadGram A hA hd _ (pcaGramTolerance (sketchSquared A/sigma^2) e) z) :
    ∀ i : Fin k,
      let iq := pcaRetainedIndex (pca_retained_le_samples A k hkd sigma hsigma hcut e delta) i;
      let W := pcaSmallMatrix A hA hd _ z.1 z.2;
      0<‖pcaOutput (pcaRowSketch A hA _ z.1) W iq‖ ∧
        pcaSQInflation A hA z.1 W iq≤4*(pcaGramSamples (sketchSquared A/sigma^2) e delta:ℝ)*
          (sketchSquared A/sigma^2) := by
  let F := sketchSquared A
  let K := F/sigma^2
  let t := pcaGramTolerance K e
  have hK1 : 1≤K := pca_effective_rank_one_le A k hk hkd sigma hsigma hcut
  have hF : F=K*sigma^2 := by dsimp [K]; field_simp
  have ht := pca_tolerance_cutoff F sigma K e hsigma hK1 hF he
  have hcol := le_of_not_gt (fun h => hgood (Or.inr h))
  have ht0 : 0≤t := by
    have hrow := le_of_not_gt (fun h => hgood (Or.inl h))
    have hFrob :=
        (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius_nonneg _).trans hrow
    exact nonneg_of_mul_nonneg_left hFrob hA
  intro i
  have hspec := pca_actual_small_spectrum A hA hd t ht0 z hgood
    (lt_min (lt_of_lt_of_le i.isLt hkn) (lt_of_lt_of_le i.isLt hkd))
  have hcutSq := pow_le_pow_left₀ hsigma.le (hcut i.val (Finset.mem_range.mpr i.isLt)) 2
  have hmu : sigma^2/2≤pcaSmallValue (pcaSmallMatrix A hA hd _ z.1 z.2)
      (pcaRetainedIndex (pca_retained_le_samples A k hkd sigma hsigma hcut e delta) i) := by
    have hs := (abs_le.mp hspec).1
    change sigma^2/2≤Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues
      (pcaSmallMatrix A hA hd _ z.1 z.2) i.val^2
    nlinarith
  exact pca_actual_sq_inflation A hA (pcaGramSamples_rank K e delta).1 z.1 _ _ sigma (t*F) K
    hsigma hF hmu ht hcol

/-- Accessibility of a sketch record: each retained output has positive norm and
sample-and-query inflation at most `4 * q * K`. -/
def pcaRecordAccessible {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (k q : ℕ) (hkq : k≤q) (K : ℝ)
    (z : (Fin q→Fin n) × (Fin q→Fin d)) : Prop :=
  ∀ i : Fin k,
    0<‖pcaOutput (pcaRowSketch A hA q z.1) (pcaSmallMatrix A hA hd q z.1 z.2) (pcaRetainedIndex hkq i)‖ ∧
    pcaSQInflation A hA z.1 (pcaSmallMatrix A hA hd q z.1 z.2) (pcaRetainedIndex hkq i)≤4*(q:ℝ)*K

/-- Under the stated cutoff and spectral gap assumptions, actual PCA preprocessing produces a
correct and accessible record with failure probability at most `delta` [Tang2021]. -/
theorem source_classical_pca_producer {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (k : ℕ) (hk : 1≤k) (hkn : k≤n) (hkd : k≤d)
    (sigma eta s v delta : ℝ) (hsigma : 0<sigma) (heta : 0<eta) (hs : 0<s)
    (hv : 0<v) (hv1 : v≤1) (hdelta : 0<delta) (hdelta1 : delta<1)
    (hcut : ∀ i∈Finset.range k,sigma≤Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i)
    (hgap : ∀ i∈Finset.range k,eta*sketchSquared A≤
      Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i^2-
      Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A (i+1)^2) :
    let K := sketchSquared A/sigma^2;
    let e := epsParameter s v eta K;
    let q := pcaGramSamples K e delta;
    let hkq := pca_retained_le_samples A k hkd sigma hsigma hcut e delta;
    (pcaSketchLaw A hA hd q).probEvent (fun omega : Fin 1→((Fin q→Fin n)×(Fin q→Fin d)) =>
      ¬(pcaRecordCorrect A hA hd k q hkd hkq s v (omega 0) ∧
        pcaRecordAccessible A hA hd k q hkq K (omega 0)))≤delta := by
  (try dsimp only)
  let K := sketchSquared A/sigma^2
  let e := epsParameter s v eta K
  have hK : 0<K := div_pos hA (sq_pos_of_pos hsigma)
  have he := pca_source_parameter_pos s v eta K hs hv heta hK
  apply (pca_event_mono_decidable (pcaSketchLaw A hA hd (pcaGramSamples K e delta))
    (fun omega : Fin 1→((Fin (pcaGramSamples K e delta)→Fin n)×(Fin (pcaGramSamples K e delta)→Fin d)) =>
      ¬(pcaRecordCorrect A hA hd k _ hkd (pca_retained_le_samples A k hkd sigma hsigma hcut e delta) s v (omega 0) ∧
        pcaRecordAccessible A hA hd k _ (pca_retained_le_samples A k hkd sigma hsigma hcut e delta) K (omega 0)))
    (fun omega => pcaBadGram A hA hd _ (pcaGramTolerance K e) (omega 0)) ?_).trans
      (pca_actual_gram_concentration A hA hd K e delta hK he hdelta hdelta1)
  intro omega hbad
  by_contra hgood
  apply hbad
  exact ⟨pca_actual_record_accuracy A hA hd k hk hkn hkd sigma eta s v delta
      hsigma heta hs hv hv1 hcut hgap (omega 0) hgood,
    pca_actual_record_access A hA hd k hk hkn hkd sigma e delta hsigma
      (source_theorem9_eps_le_inv_sqrt_branch s v eta K) hcut (omega 0) hgood⟩

end Qatlib.Papers.QPCAAssume18.ClassicalPca
