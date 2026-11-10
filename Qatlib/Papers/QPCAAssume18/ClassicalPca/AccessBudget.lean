/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.VectorSQConfidence
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Qatlib.Concepts.SqEstimation.RejectionSample

def pcaRejectSamples (q : ℕ) (K delta : ℝ) : ℕ := ⌈4*(q:ℝ)*K*Real.log (1/delta)⌉₊+1

theorem pca_rejection_cap_failure (q : ℕ) (K phi delta : ℝ) (hphi1 : 1≤phi)
    (hphiK : phi≤4*(q:ℝ)*K) (hdelta : 0<delta) (hdelta1 : delta≤1) :
    (1-1/phi)^pcaRejectSamples q K delta≤delta := by
  have hphi : 0<phi := by linarith
  have hL : 0≤Real.log (1/delta) := Real.log_nonneg ((one_le_div hdelta).mpr hdelta1)
  have hbudget : phi*Real.log (1/delta)≤(pcaRejectSamples q K delta:ℝ) := by
    have hceil := Nat.le_ceil (4*(q:ℝ)*K*Real.log (1/delta))
    have hm := mul_le_mul_of_nonneg_right hphiK hL
    unfold pcaRejectSamples
    push_cast
    linarith
  have hbase : 0≤1-1/phi := sub_nonneg.mpr ((div_le_one hphi).mpr hphi1)
  have hp := pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg (1/phi)) (pcaRejectSamples q K delta)
  have hexp : Real.exp (-(1/phi))^pcaRejectSamples q K delta=
      Real.exp (-((pcaRejectSamples q K delta:ℝ)/phi)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at hp
  have hratio : Real.log (1/delta)≤(pcaRejectSamples q K delta:ℝ)/phi :=
    (le_div_iff₀ hphi).mpr (by nlinarith)
  have he := Real.exp_le_exp.mpr (neg_le_neg hratio)
  have hidentity : Real.exp (-Real.log (1/delta))=delta := by
    rw [Real.exp_neg,Real.exp_log (by positivity : 0<1/delta)]
    field_simp
  exact hp.trans (he.trans_eq hidentity)

theorem pca_norm_run_relative {I : Type} (norm energy : ℝ) (q r B : ℕ)
    (omega : Fin (2*r+1)→Fin B→I×Bool) (hnorm : 0<norm)
    (henergy : energy=norm^2)
    (hgood : |(pcaNormRun energy q r B omega).1-energy|≤(1/100:ℝ)*energy) :
    |Real.sqrt ((pcaNormRun energy q r B omega).1)-norm|≤(1/100:ℝ)*norm := by
  have h := sq_relative_sqrt (pcaNormRun energy q r B omega).1 energy (1/100)
    (by rw [henergy]; positivity) (by norm_num) hgood
  rw [henergy,Real.sqrt_sq hnorm.le] at h
  simpa only [henergy] using! h

theorem pca_access_confidence_source (k : ℕ) (hk : 1≤k) (delta : ℝ)
    (hdelta : 0<delta) (hhalf : delta≤1/2) :
    2*(pcaNormRounds (delta/k):ℝ)+1≤5*Real.log ((k:ℝ)/delta)/Real.log 2 := by
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hk0 : (0:ℝ)<k := by linarith
  have hd : 0<delta/k := div_pos hdelta hk0
  have hsmall : delta/(k:ℝ)≤1/2 := by apply (div_le_iff₀ hk0).mpr; nlinarith
  have h := pcaNormRounds_source_log (delta/k) hd hsmall
  have hid : 1/(delta/(k:ℝ))=(k:ℝ)/delta := by field_simp
  rwa [hid] at h

theorem pca_norm_access_source_budget {I : Type} (energy T K e delta phi : ℝ) (k : ℕ)
    (hk : 1≤k) (hK : 1≤K) (he : 0<e) (he1 : e≤1)
    (hdelta : 0<delta) (hhalf : delta≤1/2) (hphi : 0≤phi)
    (hphiK : phi≤4*(pcaGramSamples K e delta:ℝ)*K) (hT : 1≤T)
    (omega : Fin (2*pcaNormRounds (delta/k)+1)→Fin (pcaNormSamples phi)→I×Bool) :
    pcaNormRunWork energy T (pcaGramSamples K e delta) (pcaNormRounds (delta/k))
      (pcaNormSamples phi) omega≤
      (20000000*pcaSampleFactor^2/Real.log 2)*T*(K^9/e^4)*Real.log (4*(k:ℝ)/delta)^3 := by
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let L := Real.log (4*(k:ℝ)/delta)
  have harg : 4/delta≤4*(k:ℝ)/delta := by apply (div_le_div_iff_of_pos_right hdelta).mpr; nlinarith
  have hL : Real.log (4/delta)≤L := Real.log_le_log (by positivity) harg
  have hL0 : 0≤Real.log (4/delta) := Real.log_nonneg (by
    apply (le_div_iff₀ hdelta).mpr; linarith)
  have hq := pca_samples_source_upper K e delta hK he he1 hdelta (by linarith)
  have hfactor : 0≤pcaSampleFactor := by unfold pcaSampleFactor; positivity
  have hqL : (pcaGramSamples K e delta:ℝ)≤pcaSampleFactor*(K^4/e^2*L) :=
    hq.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hL (by positivity)) hfactor)
  have hq2 := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (pcaGramSamples K e delta)) hqL 2
  have hround := pca_access_confidence_source k hk delta hdelta hhalf
  have hlower : Real.log ((k:ℝ)/delta)≤L := Real.log_le_log (by positivity) (by
    apply (div_le_div_iff_of_pos_right hdelta).mpr; nlinarith)
  have hr : 2*(pcaNormRounds (delta/k):ℝ)+1≤5*L/Real.log 2 :=
    hround.trans (div_le_div_of_nonneg_right (by linarith) hlog2.le)
  have hb := pca_norm_run_paid_bound energy T K phi (pcaGramSamples K e delta)
    (pcaNormRounds (delta/k)) (pcaGramSamples_rank K e delta).1 hK hphi hphiK hT omega
  have hx : (K^4/e^2*L)^2=K^8/e^4*L^2 := by field_simp
  rw [mul_pow,hx] at hq2
  have hK0 : 0≤K := by linarith
  have hT0 : 0≤T := by linarith
  have hpaid := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hq2 (by positivity : 0≤4000000*T)) hK0
  have hprod := mul_le_mul hpaid hr (by positivity : 0≤2*(pcaNormRounds (delta/k):ℝ)+1)
    (by positivity : 0≤4000000*T*(pcaSampleFactor^2*(K^8/e^4*L^2))*K)
  apply hb.trans
  apply hprod.trans_eq
  dsimp [L]
  field_simp
  ring

end Qatlib.Papers.QPCAAssume18.ClassicalPca
