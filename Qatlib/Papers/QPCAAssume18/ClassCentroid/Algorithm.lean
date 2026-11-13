/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassCentroid.ActualRun
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Charged nearest-centroid estimation

Defines `sourceCentroidRun`, which reads the normalization quantity and runs the median
estimator with explicit access and selection costs. Following the classical nearest-centroid
construction of [Tang2021], the module bounds the additive-error failure mass and derives a
uniform work bound proportional to `T * Z ^ 2 / eps ^ 2 * log (1 / delta)` under the stated
parameter restrictions.

## Main statements

* `sourceCentroidWork_source`: Under the stated error, confidence, and access-cost bounds, every
  source run has work at most `(112910 / log 2) * T * Z ^ 2 / eps ^ 2 * log (1 / delta)`, where
  `Z = averageNormSq u V`.
* `source_nearest_centroid_charged`: The charged nearest-centroid estimator has additive-error
  failure mass at most `delta` and satisfies the stated uniform work bound [Tang2021].

## References

* [Tang, 2021][Tang2021]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.QPCAAssume18.ClassCentroid

/-- The Frobenius energy of the matrix together with a ledger containing one matrix-energy
access. -/
def matrixEnergyRead {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℂ) :
    ℝ × List (CentroidCall n d) := (frobeniusEnergy V, [.matrixEnergy])

/-- The normalization quantity obtained from the vector energy and the average matrix energy,
together with the concatenated access ledger. -/
def centroidZRead {n d : ℕ} (u : Fin d → ℂ) (V : Matrix (Fin n) (Fin d) ℂ) :
    ℝ × List (CentroidCall n d) :=
  let a := energyRead u V 0
  let b := matrixEnergyRead V
  (a.1 + (1 / (n : ℝ)) * b.1, a.2 ++ b.2)

/-- The normalization read returns `averageNormSq u V` and records exactly two accesses. -/
theorem centroidZRead_spec {n d : ℕ} (u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) :
    (centroidZRead u V).1 = averageNormSq u V ∧ (centroidZRead u V).2.length = 2 := by
  constructor <;> rfl

/-- The nearest-centroid estimator using the coordinate anchor and the prescribed sample and
round counts, returning its estimate, access ledger, and selection-comparison count. -/
def sourceCentroidRun {n d : ℕ} (u : Fin d → ℂ) (V : Matrix (Fin n) (Fin d) ℂ)
    (hd : 0 < d) (eps delta : ℝ)
    (omega : Fin (2 * centroidRounds delta + 1) →
      Fin (centroidSamples (averageNormSq u V) eps) → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    ℂ × List (CentroidCall n d) × ℕ :=
  let z := centroidZRead u V
  let run := centroidRunRead (coordinateAnchor hd) u V (centroidSamples z.1 eps)
    (centroidRounds delta) omega
  (run.1, z.2 ++ run.2.1, run.2.2)

/-- The probability mass of random tapes for which the real part of `sourceCentroidRun` differs
from the squared centroid distance by more than `eps`. -/
def sourceCentroidFailureMass {n d : ℕ} (u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (hd : 0 < d) (eps delta : ℝ) : ℝ :=
  ∑ omega ∈ Finset.univ.filter (fun omega : Fin (2 * centroidRounds delta + 1) →
      Fin (centroidSamples (averageNormSq u V) eps) →
      (Fin d × Fin (n + 1) × Fin (n + 1)) =>
    eps < |(sourceCentroidRun u V hd eps delta omega).1.re -
      ∑ k, Complex.normSq (u k - (n : ℂ)⁻¹ * ∑ i, V i k)|),
    ∏ b, (centroidTensorInput (coordinateAnchor hd) u V hn (coordinateAnchor_energy hd)).samples.probOf
      (omega b)

/-- The failure mass of the source-parameterized run equals `centroidFailureMass` with the
coordinate anchor and the prescribed sample and round counts. -/
theorem sourceCentroidFailureMass_eq {n d : ℕ} (u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (hd : 0 < d) (eps delta : ℝ) :
    sourceCentroidFailureMass u V hn hd eps delta =
      centroidFailureMass (coordinateAnchor hd) u V hn (coordinateAnchor_energy hd)
        (centroidSamples (averageNormSq u V) eps) (centroidRounds delta) eps := rfl

/-- For positive error and failure parameters, the nearest-centroid estimator has additive-error
failure mass at most `delta` [Tang2021]. -/
theorem sourceCentroid_correct {n d : ℕ} (u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (hd : 0 < d)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta) :
    sourceCentroidFailureMass u V hn hd eps delta ≤ delta := by
  rw [sourceCentroidFailureMass_eq]
  exact source_nearest_centroid_actual u V hn hd eps delta heps hdelta

/-- The charged work of `sourceCentroidRun`, counting each ledger access at cost `T` and adding
its selection-comparison count. -/
def sourceCentroidWork {n d : ℕ} (u : Fin d → ℂ) (V : Matrix (Fin n) (Fin d) ℂ)
    (hd : 0 < d) (eps delta T : ℝ)
    (omega : Fin (2 * centroidRounds delta + 1) →
      Fin (centroidSamples (averageNormSq u V) eps) → (Fin d × Fin (n + 1) × Fin (n + 1))) : ℝ :=
  T * (sourceCentroidRun u V hd eps delta omega).2.1.length +
    (sourceCentroidRun u V hd eps delta omega).2.2

/-- The charged source run costs `2 * T` for normalization reads plus the work of the underlying
centroid run. -/
theorem sourceCentroidWork_eq {n d : ℕ} (u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hd : 0 < d) (eps delta T : ℝ)
    (omega : Fin (2 * centroidRounds delta + 1) →
      Fin (centroidSamples (averageNormSq u V) eps) → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    sourceCentroidWork u V hd eps delta T omega =
      2 * T + centroidRunWork (coordinateAnchor hd) u V
        (centroidSamples (averageNormSq u V) eps) (centroidRounds delta) T omega := by
  simp only [sourceCentroidWork, sourceCentroidRun, centroidZRead, matrixEnergyRead,
    energyRead, sourceRow, averageNormSq, Fin.cases_zero, List.length_append,
    List.length_cons, List.length_nil, Nat.cast_add, centroidRunWork]
  ring

/-- For nonnegative access cost, every source run satisfies the explicit finite work bound in
terms of the normalization quantity, error, and round count. -/
theorem sourceCentroidWork_finite {n d : ℕ} (u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hd : 0 < d) (eps delta T : ℝ) (hT : 0 ≤ T)
    (omega : Fin (2 * centroidRounds delta + 1) →
      Fin (centroidSamples (averageNormSq u V) eps) → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    sourceCentroidWork u V hd eps delta T omega ≤
      2 * T + (10 * T * (256 * (averageNormSq u V) ^ 2 / eps ^ 2 + 2) + 20000) *
        (2 * (centroidRounds delta : ℝ) + 1) := by
  rw [sourceCentroidWork_eq]
  have hrun := centroidRunWork_bound (coordinateAnchor hd) u V
    (centroidSamples (averageNormSq u V) eps) (centroidRounds delta) T hT omega
  have hm := (centroidSamples_upper (averageNormSq u V) eps).le
  have h1 := mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) hT)
  have h2 := mul_le_mul_of_nonneg_right h1
    (by positivity : (0 : ℝ) ≤ 2 * (centroidRounds delta : ℝ) + 1)
  linarith

/-- For `0 < delta ≤ 1`, the round count is less than `logb 4 (2 / delta) + 1`. -/
theorem centroidRounds_log_upper (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    (centroidRounds delta : ℝ) < Real.logb 4 (2 / delta) + 1 := by
  have hinv : 1 ≤ 1 / delta := (one_le_div hdelta).mpr hdelta1
  have hN : (1 : ℝ) ≤ (⌈1 / delta⌉₊ : ℝ) := hinv.trans (Nat.le_ceil _)
  have hnonneg : 0 ≤ Real.logb 4 (⌈1 / delta⌉₊ : ℝ) :=
    Real.logb_nonneg (by norm_num) hN
  have hround : (centroidRounds delta : ℝ) < Real.logb 4 (⌈1 / delta⌉₊ : ℝ) + 1 := by
    unfold centroidRounds
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

/-- For `0 < delta ≤ 1 / 2`, the number of median blocks is at most `5 * log (1 / delta) / log
2`. -/
theorem centroidRounds_source_log (delta : ℝ) (hdelta : 0 < delta)
    (hhalf : delta ≤ 1 / 2) :
    2 * (centroidRounds delta : ℝ) + 1 ≤ 5 * Real.log (1 / delta) / Real.log 2 := by
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
  have hround := centroidRounds_log_upper delta hdelta (by linarith)
  have hidentity : (2 * Real.logb 4 (2 / delta) + 3) * Real.log 2 =
      Real.log (1 / delta) + 4 * Real.log 2 := by
    rw [Real.logb, hlogratio, hlog4]
    field_simp
    ring
  apply (le_div_iff₀ hlog2).mpr
  have hB : 2 * (centroidRounds delta : ℝ) + 1 < 2 * Real.logb 4 (2 / delta) + 3 := by linarith
  have hprod := mul_lt_mul_of_pos_right hB hlog2
  rw [hidentity] at hprod
  linarith

/-- Under the stated error, confidence, and access-cost bounds, every source run has work at
most `(112910 / log 2) * T * Z ^ 2 / eps ^ 2 * log (1 / delta)`, where `Z = averageNormSq u
V`. -/
theorem sourceCentroidWork_source {n d : ℕ} (u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hd : 0 < d) (eps delta T : ℝ)
    (heps : 0 < eps) (hepsZ : eps ≤ averageNormSq u V)
    (hdelta : 0 < delta) (hhalf : delta ≤ 1 / 2) (hT : 1 ≤ T)
    (omega : Fin (2 * centroidRounds delta + 1) →
      Fin (centroidSamples (averageNormSq u V) eps) → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    sourceCentroidWork u V hd eps delta T omega ≤
      (112910 / Real.log 2) * T * (averageNormSq u V) ^ 2 / eps ^ 2 * Real.log (1 / delta) := by
  let Z := averageNormSq u V
  let R := Z ^ 2 / eps ^ 2
  let B := 2 * (centroidRounds delta : ℝ) + 1
  have hT0 : 0 ≤ T := by linarith
  have hZ : 0 < Z := heps.trans_le hepsZ
  have hsq : eps ^ 2 ≤ Z ^ 2 := pow_le_pow_left₀ heps.le hepsZ 2
  have hR : 1 ≤ R := (one_le_div (sq_pos_of_pos heps)).mpr hsq
  have hR0 : 0 ≤ R := by linarith
  have hB : 1 ≤ B := by
    dsimp [B]
    have h := Nat.cast_nonneg (α := ℝ) (centroidRounds delta)
    linarith
  have hB0 : 0 ≤ B := by linarith
  have hm : (centroidSamples Z eps : ℝ) ≤ 258 * R := by
    have h := centroidSamples_upper Z eps
    have heq : 256 * Z ^ 2 / eps ^ 2 = 256 * R := by dsimp [R]; ring
    rw [heq] at h
    linarith
  have hTM : 10 * T * (centroidSamples Z eps : ℝ) ≤ 2580 * T * R := by
    calc
      _ ≤ 10 * T * (258 * R) := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := by ring
  have hTR : 1 ≤ T * R := one_le_mul_of_one_le_of_one_le hT hR
  have hcoeff : 10 * T * (centroidSamples Z eps : ℝ) + 20000 ≤ 22580 * T * R := by
    nlinarith
  have hRB : 1 ≤ R * B := one_le_mul_of_one_le_of_one_le hR hB
  have hprep : 2 * T ≤ 2 * T * R * B := by
    have h := mul_le_mul_of_nonneg_left hRB (by positivity : (0 : ℝ) ≤ 2 * T)
    nlinarith
  have hrun := centroidRunWork_bound (coordinateAnchor hd) u V
    (centroidSamples Z eps) (centroidRounds delta) T hT0 omega
  have hfirst : sourceCentroidWork u V hd eps delta T omega ≤ 22582 * T * R * B := by
    rw [sourceCentroidWork_eq]
    have hc := mul_le_mul_of_nonneg_right hcoeff hB0
    change centroidRunWork (coordinateAnchor hd) u V (centroidSamples Z eps)
      (centroidRounds delta) T omega ≤
        (10 * T * (centroidSamples Z eps : ℝ) + 20000) * B at hrun
    nlinarith
  have hblog := centroidRounds_source_log delta hdelta hhalf
  have hsecond := mul_le_mul_of_nonneg_left hblog
    (by positivity : (0 : ℝ) ≤ 22582 * T * R)
  apply hfirst.trans
  calc
    _ ≤ 22582 * T * R * (5 * Real.log (1 / delta) / Real.log 2) := hsecond
    _ = _ := by dsimp [R, Z]; ring

/-- The charged nearest-centroid estimator has additive-error failure mass at most `delta` and
satisfies the stated uniform work bound [Tang2021]. -/
theorem source_nearest_centroid_charged {n d : ℕ} (u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (hd : 0 < d)
    (eps delta T : ℝ) (heps : 0 < eps) (hepsZ : eps ≤ averageNormSq u V)
    (hdelta : 0 < delta) (hhalf : delta ≤ 1 / 2) (hT : 1 ≤ T) :
    sourceCentroidFailureMass u V hn hd eps delta ≤ delta ∧
      ∀ omega, sourceCentroidWork u V hd eps delta T omega ≤
        (112910 / Real.log 2) * T * (averageNormSq u V) ^ 2 / eps ^ 2 * Real.log (1 / delta) := by
  exact ⟨sourceCentroid_correct u V hn hd eps delta heps hdelta,
    fun omega => sourceCentroidWork_source u V hd eps delta T heps hepsZ hdelta hhalf hT omega⟩

end Qatlib.Papers.QPCAAssume18.ClassCentroid
