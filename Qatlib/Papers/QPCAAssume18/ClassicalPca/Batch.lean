/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.ActualProtocol
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SketchSpectral.EvenSvtLaw

def pcaCallComponent {k Q : ℕ} (j : Fin (k*Q)) : Fin k := (finProdFinEquiv.symm j).1

def pcaCallConfidence (k Q : ℕ) (delta : ℝ) : ℝ := delta/(3*(k:ℝ)*(max 1 Q:ℕ))

abbrev PcaCallRecord (d q : ℕ) (K alpha : ℝ) :=
  (Fin (2*pcaNormRounds alpha+1)→Fin (pcaNormSamples (4*(q:ℝ)*K))→Fin d×Bool) ×
    (Fin (pcaRejectSamples q K alpha)→Fin d×Bool)

def pcaCallLaw {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (k q Q : ℕ) (hkq : k≤q) (K alpha : ℝ)
    (z : (Fin q→Fin n) × (Fin q→Fin d)) (j : Fin (k*Q)) : FinDist (PcaCallRecord d q K alpha) :=
  pcaProtocolLaw (pcaActualTrial A hA hd z.1 (pcaSmallMatrix A hA hd q z.1 z.2)
    (pcaRetainedIndex hkq (pcaCallComponent j))) (pcaNormRounds alpha)
    (pcaNormSamples (4*(q:ℝ)*K)) (pcaRejectSamples q K alpha)

def pcaCallBad {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (k q Q : ℕ) (hkq : k≤q) (K alpha : ℝ)
    (z : (Fin q→Fin n) × (Fin q→Fin d)) (j : Fin (k*Q)) (record : PcaCallRecord d q K alpha) : Prop :=
  let W := pcaSmallMatrix A hA hd q z.1 z.2;
  let i := pcaRetainedIndex hkq (pcaCallComponent j);
  let energy := ‖pcaOutput (pcaRowSketch A hA q z.1) W i‖^2;
  let envelopeEnergy := ∑ l,Complex.normSq (Qatlib.Concepts.SqEstimation.RejectionSample.sqLinearEnvelope
    (pcaOutputCoefficients W i) (pcaConjugateRows (pcaRowSketch A hA q z.1)) l);
  pcaProtocolBad energy envelopeEnergy q (pcaNormRounds alpha)
    (pcaNormSamples (4*(q:ℝ)*K)) (pcaRejectSamples q K alpha) record

def pcaBatchLaw {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (k q Q : ℕ) (hkq : k≤q) (K alpha : ℝ) :
    FinDist (((Fin q→Fin n) × (Fin q→Fin d)) × (Fin (k*Q)→PcaCallRecord d q K alpha)) :=
  pcaJointLaw (pcaSketchLaw A hA hd q) (fun z => independentSampleLaw (pcaCallLaw A hA hd k q Q hkq K alpha z))

def pcaBatchBad {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (k q Q : ℕ) (hkq : k≤q) (K alpha t : ℝ)
    (record : ((Fin q→Fin n) × (Fin q→Fin d)) × (Fin (k*Q)→PcaCallRecord d q K alpha)) : Prop :=
  pcaBadGram A hA hd q t record.1 ∨ ∃j,pcaCallBad A hA hd k q Q hkq K alpha record.1 j (record.2 j)

theorem pca_call_budget (k Q : ℕ) (hk : 1≤k) (delta : ℝ) (hdelta : 0≤delta) :
    ((k*Q:ℕ):ℝ)*(2*pcaCallConfidence k Q delta)≤2*delta/3 := by
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hQ : (0:ℝ)<(max 1 Q:ℕ) := by exact_mod_cast (show 0<max 1 Q by omega)
  have hQQ : (Q:ℝ)≤(max 1 Q:ℕ) := by exact_mod_cast le_max_right 1 Q
  have hratio : (Q:ℝ)/(max 1 Q:ℕ)≤1 := (div_le_one hQ).mpr hQQ
  calc
    _ = (2*delta/3)*((Q:ℝ)/(max 1 Q:ℕ)) := by
      unfold pcaCallConfidence
      rw [Nat.cast_mul]
      field_simp
    _ ≤ (2*delta/3)*1 := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := mul_one _

theorem source_classical_pca_batch_failure {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (k Q : ℕ) (hk : 1≤k) (hkn : k≤n) (hkd : k≤d)
    (sigma eta s v delta : ℝ) (hsigma : 0<sigma) (heta : 0<eta) (hs : 0<s) (hv : 0<v)
    (hdelta : 0<delta) (hdelta1 : delta<1)
    (hcut : ∀i∈Finset.range k,sigma≤Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i) :
    let K := sketchSquared A/sigma^2;
    let e := epsParameter s v eta K;
    let q := pcaGramSamples K e (delta/3);
    let hkq := pca_retained_le_samples A k hkd sigma hsigma hcut e (delta/3);
    let alpha := pcaCallConfidence k Q delta;
    pcaFiniteMass (pcaBatchLaw A hA hd k q Q hkq K alpha)
      (pcaBatchBad A hA hd k q Q hkq K alpha (pcaGramTolerance K e))≤delta := by
  (try dsimp only)
  let K := sketchSquared A/sigma^2
  let e := epsParameter s v eta K
  let q := pcaGramSamples K e (delta/3)
  let hkq := pca_retained_le_samples A k hkd sigma hsigma hcut e (delta/3)
  let alpha := pcaCallConfidence k Q delta
  have hK : 0<K := div_pos hA (sq_pos_of_pos hsigma)
  have he := pca_source_parameter_pos s v eta K hs hv heta hK
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hQ : (1:ℝ)≤(max 1 Q:ℕ) := by exact_mod_cast le_max_left 1 Q
  have ha : 0<alpha := by dsimp [alpha,pcaCallConfidence]; positivity
  have ha1 : alpha≤1 := by
    dsimp [alpha,pcaCallConfidence]
    apply (div_le_one (by positivity : 0<3*(k:ℝ)*(max 1 Q:ℕ))).mpr
    nlinarith
  have hf : pcaFiniteMass (pcaSketchLaw A hA hd q) (pcaBadGram A hA hd q (pcaGramTolerance K e))≤delta/3 := by
    have h :=
        pca_actual_gram_concentration A hA hd K e (delta/3) hK he (by positivity) (by linarith)
    rw [probEvent_single] at h
    simpa only [pcaFiniteMass,Finset.sum_filter] using! h
  have hcond (z : (Fin q→Fin n)×(Fin q→Fin d))
      (hz : ¬pcaBadGram A hA hd q (pcaGramTolerance K e) z) :
      pcaFiniteMass (independentSampleLaw (pcaCallLaw A hA hd k q Q hkq K alpha z))
        (fun access => ∃j,pcaCallBad A hA hd k q Q hkq K alpha z j (access j))≤2*delta/3 := by
    have haccess := pca_actual_record_access A hA hd k hk hkn hkd sigma e (delta/3) hsigma
      (source_theorem9_eps_le_inv_sqrt_branch s v eta K) hcut z hz
    have hu := pca_independent_union (pcaCallLaw A hA hd k q Q hkq K alpha z)
      (pcaCallBad A hA hd k q Q hkq K alpha z) (2*alpha) (by
        intro j
        exact pca_actual_protocol_failure A hA hd (pcaGramSamples_rank K e (delta/3)).1 z.1
          (pcaSmallMatrix A hA hd q z.1 z.2) (pcaRetainedIndex hkq (pcaCallComponent j)) K alpha
          (haccess (pcaCallComponent j)).1 (haccess (pcaCallComponent j)).2 ha ha1)
    exact hu.trans (pca_call_budget k Q hk delta hdelta.le)
  have h := pca_joint_failure (pcaSketchLaw A hA hd q)
    (fun z => independentSampleLaw (pcaCallLaw A hA hd k q Q hkq K alpha z))
    (pcaBadGram A hA hd q (pcaGramTolerance K e))
    (fun z access => ∃j,pcaCallBad A hA hd k q Q hkq K alpha z j (access j))
    (delta/3) (2*delta/3) (by positivity) hf hcond
  exact h.trans_eq (by ring)

theorem pca_empty_retained {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (s v K : ℝ)
    (z : (Fin q→Fin n)×(Fin q→Fin d)) :
    pcaRecordCorrect A hA hd 0 q (Nat.zero_le _) (Nat.zero_le _) s v z ∧
      pcaRecordAccessible A hA hd 0 q (Nat.zero_le _) K z := by
  constructor <;> intro i <;> exact Fin.elim0 i

theorem source_classical_pca_batch {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (k Q : ℕ) (hk : 1≤k) (hkn : k≤n) (hkd : k≤d)
    (sigma eta s v delta : ℝ) (hsigma : 0<sigma) (heta : 0<eta) (hs : 0<s)
    (hv : 0<v) (hv1 : v≤1) (hdelta : 0<delta) (hdelta1 : delta<1)
    (hcut : ∀i∈Finset.range k,sigma≤Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i)
    (hgap : ∀i∈Finset.range k,eta*sketchSquared A≤
      Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i^2-
      Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A (i+1)^2) :
    let K := sketchSquared A/sigma^2;
    let e := epsParameter s v eta K;
    let q := pcaGramSamples K e (delta/3);
    let hkq := pca_retained_le_samples A k hkd sigma hsigma hcut e (delta/3);
    let alpha := pcaCallConfidence k Q delta;
    let law := pcaBatchLaw A hA hd k q Q hkq K alpha;
    let bad := pcaBatchBad A hA hd k q Q hkq K alpha (pcaGramTolerance K e);
    pcaFiniteMass law bad≤delta ∧
    ∀record,¬bad record→pcaRecordCorrect A hA hd k q hkd hkq s v record.1 ∧
      pcaRecordAccessible A hA hd k q hkq K record.1 ∧
      ∀j,¬pcaCallBad A hA hd k q Q hkq K alpha record.1 j (record.2 j) := by
  (try dsimp only)
  refine ⟨source_classical_pca_batch_failure A hA hd k Q hk hkn hkd sigma eta s v delta
    hsigma heta hs hv hdelta hdelta1 hcut,?_⟩
  intro record hgood
  have hg := not_or.mp hgood
  refine ⟨pca_actual_record_accuracy A hA hd k hk hkn hkd sigma eta s v (delta/3)
      hsigma heta hs hv hv1 hcut hgap record.1 hg.1,
    pca_actual_record_access A hA hd k hk hkn hkd sigma _ (delta/3) hsigma
      (source_theorem9_eps_le_inv_sqrt_branch s v eta _) hcut record.1 hg.1,?_⟩
  intro j hj
  exact hg.2 ⟨j,hj⟩

end Qatlib.Papers.QPCAAssume18.ClassicalPca
