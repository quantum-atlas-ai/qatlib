/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassCentroid.ActualBudgets

/-!
# Primitive query traces for centroid estimation

This module implements traced reads of normalized rows, norm weights, tensor entries, and
importance samples from the original complex vector and matrix. The traces make the
sample-and-query access used by the classical nearest-centroid construction in [Tang2021]
explicit, including the anchor branch for zero source rows.

## Main statements

* `unitEntryRead_value`, `weightRead_value`, and `blockEntryRead_value` identify traced reads
  with their mathematical values.
* `tensorReads_value` and `importanceRead_value` recover the tensor estimator from primitive
  reads.
* `tensorReads_queries`, `importanceRead_queries`, and `centroidRecordRead_queries` bound the
  traces by two and four, six, and ten calls, respectively.

## References

* [Tang, 2021][Tang2021], *Quantum principal component analysis only achieves an exponential
  speedup because of its state preparation assumptions*, Theorem 4 and Algorithm 4.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.QPCAAssume18.ClassCentroid

open Qatlib.Concepts.SqEstimation.InnerProduct

/-- The primitive input-access events recorded by the centroid estimator: row and matrix
energies, entries, row-mixture draws, coordinate samples, and use of the known anchor. -/
inductive CentroidCall (n d : ℕ) where
  | rowEnergy (j : Fin (n + 1))
  | matrixEnergy
  | entry (j : Fin (n + 1)) (i : Fin d)
  | rowMixture
  | sampleCoordinate (j : Fin (n + 1))
  | knownAnchor
  deriving DecidableEq

/-- Selects `u` at the leading index and the corresponding row of `V` at each successor index. -/
def sourceRow {n d : ℕ} (u : Fin d → ℂ) (V : Matrix (Fin n) (Fin d) ℂ)
    (j : Fin (n + 1)) : Fin d → ℂ := Fin.cases u (fun i => V i) j

/-- Returns the squared norm of a source row together with a single row-energy call. -/
def energyRead {n d : ℕ} (u : Fin d → ℂ) (V : Matrix (Fin n) (Fin d) ℂ)
    (j : Fin (n + 1)) : ℝ × List (CentroidCall n d) :=
  (vectorEnergy (sourceRow u V j), [.rowEnergy j])

/-- Returns an entry of a source row together with a single entry-query call. -/
def entryRead {n d : ℕ} (u : Fin d → ℂ) (V : Matrix (Fin n) (Fin d) ℂ)
    (j : Fin (n + 1)) (i : Fin d) : ℂ × List (CentroidCall n d) :=
  (sourceRow u V j i, [.entry j i])

/-- Returns a normalized source-row entry and its access trace, using the anchor entry when the
source row has zero squared norm. A nonzero row requires both a row-energy read and an entry
read. -/
def unitEntryRead {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (j : Fin (n + 1)) (i : Fin d) :
    ℂ × List (CentroidCall n d) :=
  let q := energyRead u V j
  if q.1 = 0 then (anchor i, q.2) else
    let v := entryRead u V j i
    ((Real.sqrt q.1 : ℂ)⁻¹ * v.1, q.2 ++ v.2)

/-- The value returned by `unitEntryRead` is exactly the corresponding entry of
`centroidUnitRow`. -/
theorem unitEntryRead_value {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (j : Fin (n + 1)) (i : Fin d) :
    (unitEntryRead anchor u V j i).1 = centroidUnitRow anchor u V j i := by
  refine Fin.cases ?_ (fun k => ?_) j
  · by_cases h : vectorEnergy u = 0 <;>
      simp [unitEntryRead, energyRead, entryRead, sourceRow, centroidUnitRow, normalizeInput, h]
  · by_cases h : vectorEnergy (V k) = 0 <;>
      simp [unitEntryRead, energyRead, entryRead, sourceRow, centroidUnitRow, normalizeInput, h]

/-- Reading one normalized source-row entry records at most two primitive calls. -/
theorem unitEntryRead_queries {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (j : Fin (n + 1)) (i : Fin d) :
    (unitEntryRead anchor u V j i).2.length ≤ 2 := by
  simp only [unitEntryRead, energyRead, entryRead]
  split_ifs <;> simp

/-- The coefficient multiplying a source-row norm in its centroid weight: `1` for the leading
row and `-1 / sqrt(n)` for a matrix row. -/
def centroidWeightFactor (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  Fin.cases 1 (fun _ => -(Real.sqrt (n : ℝ))⁻¹) j

/-- Returns a centroid weight by multiplying the source-row norm by `centroidWeightFactor`,
recording one row-energy call. -/
def weightRead {n d : ℕ} (u : Fin d → ℂ) (V : Matrix (Fin n) (Fin d) ℂ)
    (j : Fin (n + 1)) : ℂ × List (CentroidCall n d) :=
  let q := energyRead u V j
  ((centroidWeightFactor n j : ℂ) * (Real.sqrt q.1 : ℂ), q.2)

/-- The value returned by `weightRead` equals the corresponding entry of `centroidWeights`. -/
theorem weightRead_value {n d : ℕ} (u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (j : Fin (n + 1)) :
    (weightRead u V j).1 = centroidWeights u V j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [weightRead, energyRead, sourceRow, centroidWeightFactor, centroidWeights]
  · simp [weightRead, energyRead, sourceRow, centroidWeightFactor, centroidWeights]
    ring

/-- Returns a normalized source-row entry multiplied by its centroid row scale, retaining the
normalized-entry access trace. -/
def blockEntryRead {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (j : Fin (n + 1)) (i : Fin d) :
    ℂ × List (CentroidCall n d) :=
  let q := unitEntryRead anchor u V j i
  ((centroidRowScale n j : ℂ) * q.1, q.2)

/-- The value returned by `blockEntryRead` is the corresponding entry of `centroidBlock`. -/
theorem blockEntryRead_value {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (j : Fin (n + 1)) (i : Fin d) :
    (blockEntryRead anchor u V j i).1 = centroidBlock anchor u V j i := by
  simp only [blockEntryRead, unitEntryRead_value, centroidBlock_factor]

/-- For a unit anchor, each row norm of `centroidBlock` equals its prescribed centroid row
scale. -/
theorem centroidBlock_rowNorm_eq_scale {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (ha : vectorEnergy anchor = 1)
    (j : Fin (n + 1)) : rowNorm (centroidBlock anchor u V) j = centroidRowScale n j := by
  have hsq := centroidBlock_row_norm anchor u V ha j
  have hr : 0 ≤ rowNorm (centroidBlock anchor u V) j := Real.sqrt_nonneg _
  have hs : 0 ≤ centroidRowScale n j := by
    refine Fin.cases (by norm_num [centroidRowScale]) (fun i => ?_) j
    change 0 ≤ (Real.sqrt (n : ℝ))⁻¹
    positivity
  nlinarith

/-- Reads an entry of the first centroid tensor by multiplying a block entry by the second row's
scale, and retains the block-entry trace. -/
def tensorARead {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (p : Fin d × Fin (n + 1) × Fin (n + 1)) :
    ℂ × List (CentroidCall n d) :=
  let q := blockEntryRead anchor u V p.2.1 p.1
  (q.1 * (centroidRowScale n p.2.2 : ℂ), q.2)

/-- Reads an entry of the second centroid tensor from two norm weights and a block entry,
dividing by the second row's scale and concatenating the traces. -/
def tensorBRead {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (p : Fin d × Fin (n + 1) × Fin (n + 1)) :
    ℂ × List (CentroidCall n d) :=
  let a := weightRead u V p.2.1
  let b := weightRead u V p.2.2
  let q := blockEntryRead anchor u V p.2.2 p.1
  (star a.1 * b.1 * q.1 / (centroidRowScale n p.2.2 : ℂ), a.2 ++ b.2 ++ q.2)

/-- For a unit anchor, `tensorARead` and `tensorBRead` return the corresponding entries of
`generalTensorA` and `generalTensorB`. -/
theorem tensorReads_value {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (ha : vectorEnergy anchor = 1)
    (p : Fin d × Fin (n + 1) × Fin (n + 1)) :
    (tensorARead anchor u V p).1 = generalTensorA anchor u V p ∧
      (tensorBRead anchor u V p).1 = generalTensorB anchor u V p := by
  constructor
  · simp only [tensorARead, blockEntryRead_value, generalTensorA, tensorA,
      centroidBlock_rowNorm_eq_scale anchor u V ha]
  · simp only [tensorBRead, weightRead_value, blockEntryRead_value, generalTensorB, tensorB,
      centroidBlock_rowNorm_eq_scale anchor u V ha]

/-- Reading an entry of the first tensor records at most two calls, and reading an entry of the
second records at most four. -/
theorem tensorReads_queries {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ)
    (p : Fin d × Fin (n + 1) × Fin (n + 1)) :
    (tensorARead anchor u V p).2.length ≤ 2 ∧
      (tensorBRead anchor u V p).2.length ≤ 4 := by
  constructor
  · exact unitEntryRead_queries anchor u V p.2.1 p.1
  · change ([CentroidCall.rowEnergy p.2.1] ++ [CentroidCall.rowEnergy p.2.2] ++
        (unitEntryRead anchor u V p.2.2 p.1).2).length ≤ 4
    simp only [List.length_append, List.length_cons, List.length_nil]
    have h := unitEntryRead_queries anchor u V p.2.2 p.1
    omega

/-- Returns the importance-weighted product `4 * conj(a) * b / |a|^2` from the traced tensor
entries, or zero when `a` vanishes, together with its access trace. -/
def importanceRead {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (p : Fin d × Fin (n + 1) × Fin (n + 1)) :
    ℂ × List (CentroidCall n d) :=
  let a := tensorARead anchor u V p
  if Complex.normSq a.1 = 0 then (0, a.2) else
    let b := tensorBRead anchor u V p
    ((4 : ℂ) * star a.1 * b.1 / (Complex.normSq a.1 : ℂ), a.2 ++ b.2)

/-- For positive `n` and a unit anchor, the traced importance value equals `sqImportanceValue`
for the centroid tensor input and second tensor. -/
theorem importanceRead_value {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1)
    (p : Fin d × Fin (n + 1) × Fin (n + 1)) :
    (importanceRead anchor u V p).1 =
      sqImportanceValue (centroidTensorInput anchor u V hn ha) (generalTensorB anchor u V) p := by
  simp only [importanceRead, (tensorReads_value anchor u V ha p).1,
    (tensorReads_value anchor u V ha p).2, sqImportanceValue, centroidTensorInput]
  split_ifs <;> rfl

/-- Computing one centroid importance value records at most six primitive calls. -/
theorem importanceRead_queries {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ)
    (p : Fin d × Fin (n + 1) × Fin (n + 1)) :
    (importanceRead anchor u V p).2.length ≤ 6 := by
  simp only [importanceRead]
  split_ifs
  · exact (tensorReads_queries anchor u V p).1.trans (by norm_num)
  · simp only [List.length_append]
    have h := tensorReads_queries anchor u V p
    omega

/-- Records two row-mixture draws, a first-row energy read, and either an anchor draw or a
source-row coordinate sample according to whether that energy is zero. -/
def centroidDrawCalls {n d : ℕ} (u : Fin d → ℂ) (V : Matrix (Fin n) (Fin d) ℂ)
    (p : Fin d × Fin (n + 1) × Fin (n + 1)) : List (CentroidCall n d) :=
  [.rowMixture, .rowMixture, .rowEnergy p.2.1] ++
    if (energyRead u V p.2.1).1 = 0 then [.knownAnchor] else [.sampleCoordinate p.2.1]

/-- Returns a centroid importance value and a trace combining the hierarchical sampling calls
with the importance-value reads. -/
def centroidRecordRead {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (p : Fin d × Fin (n + 1) × Fin (n + 1)) :
    ℂ × List (CentroidCall n d) :=
  let q := importanceRead anchor u V p
  (q.1, centroidDrawCalls u V p ++ q.2)

/-- One sampled centroid importance record uses at most ten primitive calls, including both
sampling and value evaluation. -/
theorem centroidRecordRead_queries {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ)
    (p : Fin d × Fin (n + 1) × Fin (n + 1)) :
    (centroidRecordRead anchor u V p).2.length ≤ 10 := by
  have hdraw : (centroidDrawCalls u V p).length = 4 := by
    unfold centroidDrawCalls
    split_ifs <;> rfl
  simp only [centroidRecordRead, List.length_append, hdraw]
  have h := importanceRead_queries anchor u V p
  omega

end Qatlib.Papers.QPCAAssume18.ClassCentroid
