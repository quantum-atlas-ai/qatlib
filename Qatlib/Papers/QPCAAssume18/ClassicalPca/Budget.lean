/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.ActualProducer
import Qatlib.Papers.QPCAAssume18.ClassicalPca.VectorSQBudget
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Preprocessing budgets for classical PCA

Bounds the concrete Gram sample count by its source asymptotic expression and accounts for all
small-matrix entry queries. The resulting cubic small-SVD and quadratic oracle-work bounds give
the preprocessing dependence stated for the classical PCA sketch in [Tang2021].

## Main statements

* `pcaSmallEntryTable_count`: The entry-query costs in the small-matrix table sum to `q^2`.
* `pca_preprocess_source_budget`: The selected sample count yields preprocessing work bounded by
  the explicit `K^12 / e^6` cubic-log term and `T * K^8 / e^4` squared-log term [Tang2021].

## References

* [Tang, 2021][Tang2021]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Matrix
open Qatlib.Concepts.SketchArith.SketchBuild

/-- The explicit sample-count constant `80000 + 4 / log 4`. -/
def pcaSampleFactor : ℝ := 80000+4/Real.log 4

/-- For `K ≥ 1`, `0 < e ≤ 1`, and `0 < delta ≤ 1`, the Gram sample count is at most
`pcaSampleFactor * (K^4 / e^2 * log (4 / delta))`. -/
theorem pca_samples_source_upper (K e delta : ℝ) (hK : 1≤K) (he : 0<e)
    (he1 : e≤1) (hdelta : 0<delta) (hdelta1 : delta≤1) :
    (pcaGramSamples K e delta:ℝ)≤pcaSampleFactor*(K^4/e^2*Real.log (4/delta)) := by
  let X := K^4/e^2*Real.log (4/delta)
  have hK0 : 0<K := by linarith
  have hlog : 0<Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have harg : (4:ℝ)≤4/delta := (le_div_iff₀ hdelta).mpr (by linarith)
  have hL : Real.log (4:ℝ)≤Real.log (4/delta) := Real.log_le_log (by norm_num) harg
  have hL0 : 0<Real.log (4/delta) := hlog.trans_le hL
  have hpow : K≤K^4 := by nlinarith [sq_nonneg (K-1),sq_nonneg (K^2-1)]
  have heSq : e^2≤1 := by nlinarith
  have hbase : K≤K^4/e^2 := (le_div_iff₀ (sq_pos_of_pos he)).mpr (by nlinarith)
  have hX : K*Real.log 4≤X := by
    exact (mul_le_mul_of_nonneg_right hbase hlog.le).trans
      (mul_le_mul_of_nonneg_left hL (by positivity))
  have hX0 : 0≤X := by dsimp [X]; positivity
  have hkX : K≤X/Real.log 4 := (le_div_iff₀ hlog).mpr hX
  have h1X : 1≤X/Real.log 4 := hK.trans hkX
  have hceilK := Nat.ceil_lt_add_one hK0.le
  have hceilX := Nat.ceil_lt_add_one (show 0≤80000*X by positivity)
  have hq : (pcaGramSamples K e delta:ℝ)<K+80000*X+3 := by
    unfold pcaGramSamples
    push_cast
    have hid : 80000*K^4/e^2*Real.log (4/delta)=80000*X := by dsimp [X]; ring
    rw [hid]
    linarith
  unfold pcaSampleFactor
  change (pcaGramSamples K e delta:ℝ)≤(80000+4/Real.log 4)*X
  have hid : (4/Real.log 4)*X=4*(X/Real.log 4) := by ring
  rw [add_mul,hid]
  linarith

/-- The list of queried row-sketch entries at the sampled columns, paired with their query
costs. -/
def pcaSmallEntryTable {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (rows : Fin q→Fin n) (cols : Fin q→Fin d) :
    List (ℂ×ℕ) :=
  List.ofFn fun z : Fin (q*q) =>
    compactSketchEntry (compactSketchData (pcaRowLaw A hA) q rows) A
      ((finProdFinEquiv.symm z).1) (cols ((finProdFinEquiv.symm z).2))

/-- The entry-query costs in the small-matrix table sum to `q^2`. -/
theorem pcaSmallEntryTable_count {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (rows : Fin q→Fin n) (cols : Fin q→Fin d) :
    ((pcaSmallEntryTable A hA rows cols).map Prod.snd).sum=q^2 := by
  simp [pcaSmallEntryTable,compactSketchEntry,Function.comp_def,pow_two]

/-- The cubic work allowance `(q : ℝ)^3` for the small SVD. -/
def pcaSmallSvdWork (q : ℕ) : ℝ := (q:ℝ)^3

/-- The preprocessing work allowance combining cubic small-SVD work and the explicit
oracle-access ledger. -/
def pcaPreprocessWork (q : ℕ) (T : ℝ) : ℝ := pcaSmallSvdWork q+T*(5*(q:ℝ)^2+3*q+3)

/-- For positive `q` and nonnegative access cost `T`, preprocessing work is bounded by `q^3 + 11
* T * q^2`. -/
theorem pca_preprocess_paid_bound (q : ℕ) (hq : 0<q) (T : ℝ) (hT : 0≤T) :
    pcaPreprocessWork q T≤(q:ℝ)^3+11*T*(q:ℝ)^2 := by
  have hqR : (1:ℝ)≤q := by exact_mod_cast hq
  unfold pcaPreprocessWork pcaSmallSvdWork
  have hpoly : 5*(q:ℝ)^2+3*q+3≤11*(q:ℝ)^2 := by nlinarith [sq_nonneg ((q:ℝ)-1)]
  nlinarith [mul_le_mul_of_nonneg_left hpoly hT]

/-- The selected sample count yields preprocessing work bounded by the explicit `K^12 / e^6`
cubic-log term and `T * K^8 / e^4` squared-log term [Tang2021]. -/
theorem pca_preprocess_source_budget (K e delta T : ℝ) (hK : 1≤K) (he : 0<e)
    (he1 : e≤1) (hdelta : 0<delta) (hdelta1 : delta≤1) (hT : 0≤T) :
    pcaPreprocessWork (pcaGramSamples K e delta) T≤
      pcaSampleFactor^3*(K^12/e^6*Real.log (4/delta)^3)+
      11*pcaSampleFactor^2*T*(K^8/e^4*Real.log (4/delta)^2) := by
  let q := pcaGramSamples K e delta
  let X := K^4/e^2*Real.log (4/delta)
  have hu := pca_samples_source_upper K e delta hK he he1 hdelta hdelta1
  have hq0 : (0:ℝ)≤q := Nat.cast_nonneg q
  have h2 := pow_le_pow_left₀ hq0 hu 2
  have h3 := pow_le_pow_left₀ hq0 hu 3
  have hb := pca_preprocess_paid_bound q (pcaGramSamples_rank K e delta).1 T hT
  have hx2 : X^2=K^8/e^4*Real.log (4/delta)^2 := by dsimp [X]; field_simp
  have hx3 : X^3=K^12/e^6*Real.log (4/delta)^3 := by dsimp [X]; field_simp
  rw [mul_pow,hx2] at h2
  rw [mul_pow,hx3] at h3
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : 0≤11*T)]

end Qatlib.Papers.QPCAAssume18.ClassicalPca
