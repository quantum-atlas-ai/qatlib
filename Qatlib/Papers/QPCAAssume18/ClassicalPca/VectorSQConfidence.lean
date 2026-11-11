/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.Budget
import Qatlib.Concepts.SqEstimation.InnerProduct.SQInnerProductEstimation

/-!
# Confidence and work for PCA norm estimates

Chooses the median repetition count for estimating PCA output energy and records the sampling
and selection work. Logarithmic confidence bounds and an explicit work estimate support the
norm-access costs in [Tang2021].

## Main statements

* `pcaNormRounds_failure`: For positive `delta`, the chosen repetition parameter makes the
  displayed median tail bound at most `delta`.
* `pca_norm_run_paid_bound`: For the stated inflation and access-cost bounds, norm-run work is
  at most `4000000 * T * q^2 * K * (2 * r + 1)`.

## References

* [Tang, 2021][Tang2021]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SqEstimation.RejectionSample
open Qatlib.Concepts.SqEstimation.InnerProduct

/-- The median repetition parameter given by the base-four ceiling logarithm of the natural
ceiling of `1 / delta`. -/
def pcaNormRounds (delta : ℝ) : ℕ := Nat.clog 4 ⌈1/delta⌉₊

/-- The median tail expression simplifies to `(1 / 4)^(r + 1)`. -/
theorem pca_median_tail_formula (r : ℕ) :
    2 * (2 : ℝ) ^ (2 * r + 1) * (1 / 16 : ℝ) ^ (r + 1) =
      (1 / 4 : ℝ) ^ (r + 1) := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    have hindex : 2 * (r + 1) + 1 = (2 * r + 1) + 2 := by omega
    calc
      _ = (2 * (2 : ℝ) ^ (2 * r + 1) * (1 / 16 : ℝ) ^ (r + 1)) * (1 / 4) := by
        rw [hindex, pow_add, pow_succ]
        norm_num
        ring
      _ = (1 / 4 : ℝ) ^ (r + 1 + 1) := by rw [ih]; simp only [pow_succ]

/-- For positive `delta`, the chosen repetition parameter makes the displayed median tail bound
at most `delta`. -/
theorem pcaNormRounds_failure (delta : ℝ) (hdelta : 0 < delta) :
    2 * (2 : ℝ) ^ (2 * pcaNormRounds delta + 1) *
      (1 / 16 : ℝ) ^ (pcaNormRounds delta + 1) ≤ delta := by
  have hceil : 1 / delta ≤ (⌈1 / delta⌉₊ : ℝ) := Nat.le_ceil _
  have hpow : (⌈1 / delta⌉₊ : ℝ) ≤ (4 : ℝ) ^ pcaNormRounds delta := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 4) ⌈1 / delta⌉₊
  have hnext : (4 : ℝ) ^ pcaNormRounds delta ≤ (4 : ℝ) ^ (pcaNormRounds delta + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
  have hbudget : 1 ≤ delta * (4 : ℝ) ^ (pcaNormRounds delta + 1) := by
    have h := (div_le_iff₀ hdelta).mp (hceil.trans (hpow.trans hnext))
    nlinarith
  rw [pca_median_tail_formula, one_div_pow]
  exact (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 4) _)).mpr hbudget

/-- For `0 < delta ≤ 1`, the repetition parameter is strictly less than `logb 4 (2 / delta) +
1`. -/
theorem pcaNormRounds_log_upper (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    (pcaNormRounds delta : ℝ) < Real.logb 4 (2 / delta) + 1 := by
  have hinv : 1 ≤ 1 / delta := (one_le_div hdelta).mpr hdelta1
  have hN : (1 : ℝ) ≤ (⌈1 / delta⌉₊ : ℝ) := hinv.trans (Nat.le_ceil _)
  have hnonneg : 0 ≤ Real.logb 4 (⌈1 / delta⌉₊ : ℝ) :=
    Real.logb_nonneg (by norm_num) hN
  have hround : (pcaNormRounds delta : ℝ) < Real.logb 4 (⌈1 / delta⌉₊ : ℝ) + 1 := by
    unfold pcaNormRounds
    rw [← Real.natCeil_logb_natCast 4 ⌈1 / delta⌉₊]
    exact Nat.ceil_lt_add_one hnonneg
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / delta)
  have hN2 : (⌈1 / delta⌉₊ : ℝ) ≤ 2 / delta := by
    have htwo : 2 / delta = 2 * (1 / delta) := by ring
    rw [htwo]
    linarith
  have hmono := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 4)
    (by linarith : (0 : ℝ) < (⌈1 / delta⌉₊ : ℝ)) (by positivity : 0 < 2 / delta)).mpr hN2
  exact hround.trans_le (by linarith)

/-- For `0 < delta ≤ 1 / 2`, the number `2 * pcaNormRounds delta + 1` is at most `5 * log (1 /
delta) / log 2`. -/
theorem pcaNormRounds_source_log (delta : ℝ) (hdelta : 0 < delta)
    (hhalf : delta ≤ 1 / 2) :
    2 * (pcaNormRounds delta : ℝ) + 1 ≤ 5 * Real.log (1 / delta) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : (2 : ℝ) ≤ 1 / delta := (le_div_iff₀ hdelta).mpr (by linarith)
  have hL : Real.log 2 ≤ Real.log (1 / delta) := Real.log_le_log (by norm_num) harg
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlogratio : Real.log (2 / delta) = Real.log 2 + Real.log (1 / delta) := by
    rw [Real.log_div (by norm_num) hdelta.ne', Real.log_div (by norm_num) hdelta.ne']
    simp only [Real.log_one]
    ring
  have hround := pcaNormRounds_log_upper delta hdelta (by linarith)
  have hidentity : (2 * Real.logb 4 (2 / delta) + 3) * Real.log 2 =
      Real.log (1 / delta) + 4 * Real.log 2 := by
    rw [Real.logb, hlogratio, hlog4]
    field_simp
    ring
  apply (le_div_iff₀ hlog2).mpr
  have hB : 2 * (pcaNormRounds delta : ℝ) + 1 < 2 * Real.logb 4 (2 / delta) + 3 := by linarith
  have hprod := mul_lt_mul_of_pos_right hB hlog2
  rw [hidentity] at hprod
  linarith

/-- The median-of-means energy estimate together with its explicit sampling-work and
selection-comparison counts. -/
def pcaNormRun {I : Type} (energy : ℝ) (q r B : ℕ)
    (omega : Fin (2*r+1)→Fin B→I×Bool) : ℝ×ℕ×ℕ :=
  let means := fun j => (∑ b,if (omega j b).2 then (1:ℝ) else 0)/(B:ℝ);
  let selected := sqSelect (List.ofFn means) r;
  (energy*selected.1,(3*q+3)*(2*r+1)*B,selected.2)

/-- The value returned by `pcaNormRun` equals `sqNormSquaredEstimate`. -/
theorem pcaNormRun_value {I : Type} (energy : ℝ) (q r B : ℕ)
    (omega : Fin (2*r+1)→Fin B→I×Bool) :
    (pcaNormRun energy q r B omega).1=sqNormSquaredEstimate energy r B omega := by
  simp only [pcaNormRun,sqNormSquaredEstimate,sqSelect_ofFn_median]

/-- The selection-comparison count of a norm run is at most `10000 * (2 * r + 1)`. -/
theorem pcaNormRun_comparisons {I : Type} (energy : ℝ) (q r B : ℕ)
    (omega : Fin (2*r+1)→Fin B→I×Bool) :
    (pcaNormRun energy q r B omega).2.2≤10000*(2*r+1) := by
  have h := (sqSelect_rank_and_cost (List.ofFn fun j =>
    (∑ b,if (omega j b).2 then (1:ℝ) else 0)/(B:ℝ)) r (by simp; omega)).2
  simpa only [pcaNormRun,List.length_ofFn] using! h

/-- The work of a norm run, charging `T` for each recorded sampling operation and one for each
selection comparison. -/
def pcaNormRunWork {I : Type} (energy T : ℝ) (q r B : ℕ)
    (omega : Fin (2*r+1)→Fin B→I×Bool) : ℝ :=
  T*(pcaNormRun energy q r B omega).2.1+(pcaNormRun energy q r B omega).2.2

/-- For the stated inflation and access-cost bounds, norm-run work is at most `4000000 * T * q^2
* K * (2 * r + 1)`. -/
theorem pca_norm_run_paid_bound {I : Type} (energy T K phi : ℝ) (q r : ℕ)
    (hq : 0<q) (hK : 1≤K) (hphi : 0≤phi) (hphiK : phi≤4*(q:ℝ)*K) (hT : 1≤T)
    (omega : Fin (2*r+1)→Fin (pcaNormSamples phi)→I×Bool) :
    pcaNormRunWork energy T q r (pcaNormSamples phi) omega≤
      4000000*T*(q:ℝ)^2*K*(2*r+1) := by
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  have hqK : 1≤(q:ℝ)*K := by nlinarith
  have hceil := Nat.ceil_lt_add_one (show 0≤160000*phi by positivity)
  have hB : (pcaNormSamples phi:ℝ)≤640002*(q:ℝ)*K := by
    unfold pcaNormSamples
    push_cast
    nlinarith
  have htrial : (3*(q:ℝ)+3)*(pcaNormSamples phi:ℝ)≤3840012*(q:ℝ)^2*K := by
    calc
      _ ≤ (6*(q:ℝ))*(640002*(q:ℝ)*K) :=
        mul_le_mul (by linarith) hB (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have hcomp : ((pcaNormRun energy q r (pcaNormSamples phi) omega).2.2:ℝ)≤10000*(2*r+1) := by
    exact_mod_cast pcaNormRun_comparisons energy q r (pcaNormSamples phi) omega
  have hbase : 10000≤159988*T*(q:ℝ)^2*K := by
    have hqq : 1≤(q:ℝ)^2 := by nlinarith
    have hqk : 1≤(q:ℝ)^2*K := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) (by positivity : 0≤(q:ℝ)^2*K)]
  unfold pcaNormRunWork
  change T*((3*q+3)*(2*r+1)*pcaNormSamples phi:ℕ)+_≤_
  push_cast
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htrial (by linarith : 0≤T))
    (by positivity : 0≤2*(r:ℝ)+1)
  have hc := mul_le_mul_of_nonneg_right hbase (by positivity : 0≤2*(r:ℝ)+1)
  nlinarith

end Qatlib.Papers.QPCAAssume18.ClassicalPca
