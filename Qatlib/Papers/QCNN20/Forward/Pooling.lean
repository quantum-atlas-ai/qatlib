/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QCNN20.Forward.Convolution

@[expose] public section

/-!
# Online pooling of sampled activations

[KerenidisLandmanPrakash2020], Section D.2.2, updates pooled outputs as activation
values are read. Maximum pooling keeps the maximum so far. Mean pooling retains a
sum and count so that successive samples contribute equally. These pool statistics
can be scattered to all affected patches using
`Qatlib.Papers.QCNN20.PatchMemory.scatterPixel`.

[ICLR paper](https://openreview.net/forum?id=Hygab1rKDS)
-/

set_option autoImplicit false

namespace Qatlib.Papers.QCNN20.Forward

/-- Map spatial indices to a pooling region, keeping the channel index. -/
def poolingRegion (size : ℕ) (pixel : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (pixel.1 / size, pixel.2.1 / size, pixel.2.2)

/-- Update a sampled maximum, starting from zero for nonnegative activations. -/
noncomputable def maxPool (samples : List ℝ) : ℝ := samples.foldl max 0

/-- An additional activation replaces the current maximum exactly when it is larger. -/
theorem max_pool_append (samples : List ℝ) (activation : ℝ) :
    maxPool (samples ++ [activation]) = max (maxPool samples) activation := by
  simp [maxPool, List.foldl_append]

/-- The sum and sample count maintained for one average-pooling cell. -/
structure MeanPool where
  /-- Sum of the observed activations in this pooling cell. -/
  total : ℝ
  /-- Number of samples contributing to the cell. -/
  count : ℕ

/-- Accumulate a new activation in the online mean. -/
def MeanPool.add (pool : MeanPool) (activation : ℝ) : MeanPool :=
  ⟨pool.total + activation, pool.count + 1⟩

/-- Read the mean of the observations accumulated so far. -/
noncomputable def MeanPool.value (pool : MeanPool) : ℝ :=
  pool.total / pool.count

/-- The online update contributes the new observation with the same weight as every earlier one. -/
theorem mean_pool_add (pool : MeanPool) (activation : ℝ) :
    (pool.add activation).value = (pool.total + activation) / (pool.count + 1 : ℕ) :=
  rfl

end Qatlib.Papers.QCNN20.Forward
