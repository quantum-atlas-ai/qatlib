/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.Batch
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Matrix
open Qatlib.Concepts.SketchArith.SketchBuild

theorem pca_source_parameter_le_one (s v eta K : ℝ) (hK : 1≤K) : epsParameter s v eta K≤1 := by
  have hs := (pca_rank_sqrt K hK).1
  have hi : (Real.sqrt K)⁻¹≤1 := (inv_le_one₀ (by linarith)).mpr hs
  have he := source_theorem9_eps_le_inv_sqrt_branch s v eta K
  nlinarith

theorem source_classical_pca_paid_cost {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (k : ℕ) (hk : 1≤k) (hkd : k≤d)
    (sigma s v eta delta T : ℝ) (hsigma : 0<sigma) (hs : 0<s) (hv : 0<v) (heta : 0<eta)
    (hdelta : 0<delta) (hdelta1 : delta≤1) (hT : 0≤T)
    (hcut : ∀i∈Finset.range k,sigma≤Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i) :
    let K := sketchSquared A/sigma^2;
    let e := epsParameter s v eta K;
    let q := pcaGramSamples K e (delta/3);
    ∀(svd : PcaSmallSvdPrimitive q) rows cols,
      pcaPaidPreprocess svd A hA hd rows cols T≤
        pcaSampleFactor^3*(K^12/e^6*Real.log (12/delta)^3)+
        11*pcaSampleFactor^2*T*(K^8/e^4*Real.log (12/delta)^2) := by
  (try dsimp only)
  let K := sketchSquared A/sigma^2
  let e := epsParameter s v eta K
  have hK := pca_effective_rank_one_le A k hk hkd sigma hsigma hcut
  have he := pca_source_parameter_pos s v eta K hs hv heta (by linarith)
  intro svd rows cols
  have h := (pcaPaidPreprocess_le svd A hA hd rows cols T).trans
    (pca_preprocess_source_budget K e (delta/3) T hK he (pca_source_parameter_le_one s v eta K hK)
      (by positivity) (by linarith) hT)
  have hid : 4/(delta/3)=12/delta := by ring
  simpa only [hid] using! h

theorem source_classical_pca_access_cost {I : Type} {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (k Q : ℕ) (hk : 1≤k) (hkd : k≤d) (sigma s v eta delta T energy : ℝ)
    (hsigma : 0<sigma) (hs : 0<s) (hv : 0<v) (heta : 0<eta)
    (hdelta : 0<delta) (hdelta1 : delta≤1) (hT : 1≤T)
    (hcut : ∀i∈Finset.range k,sigma≤Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i) :
    let K := sketchSquared A/sigma^2;
    let e := epsParameter s v eta K;
    let q := pcaGramSamples K e (delta/3);
    let alpha := pcaCallConfidence k Q delta;
    ∀omega : Fin (2*pcaNormRounds alpha+1)→Fin (pcaNormSamples (4*(q:ℝ)*K))→I×Bool,
      pcaNormRunWork energy T q (pcaNormRounds alpha) (pcaNormSamples (4*(q:ℝ)*K)) omega≤
        (20000000*pcaSampleFactor^2/Real.log 2)*T*(K^9/e^4)*
          Real.log (12*(k:ℝ)*(max 1 Q:ℕ)/delta)^3 := by
  (try dsimp only)
  let K := sketchSquared A/sigma^2
  let e := epsParameter s v eta K
  have hK := pca_effective_rank_one_le A k hk hkd sigma hsigma hcut
  have he := pca_source_parameter_pos s v eta K hs hv heta (by linarith)
  have hN : 1≤k*max 1 Q := by
    have hp := Nat.mul_pos (by omega : 0<k) (by omega : 0<max 1 Q)
    omega
  have halpha : (delta/3)/((k*max 1 Q:ℕ):ℝ)=pcaCallConfidence k Q delta := by
    unfold pcaCallConfidence
    rw [Nat.cast_mul]
    ring
  intro omega
  have h := pca_norm_access_source_budget (I:=I) energy T K e (delta/3) (4*(pcaGramSamples K e (delta/3):ℝ)*K)
    (k*max 1 Q) hN hK he (pca_source_parameter_le_one s v eta K hK) (by positivity) (by linarith)
    (by positivity) (le_refl _) hT
  rw [halpha] at h
  have hid : 4*((k*max 1 Q:ℕ):ℝ)/(delta/3)=12*(k:ℝ)*(max 1 Q:ℕ)/delta := by
    rw [Nat.cast_mul]
    ring
  simpa only [hid] using! h omega

end Qatlib.Papers.QPCAAssume18.ClassicalPca
