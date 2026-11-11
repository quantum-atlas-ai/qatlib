/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Mask combinations and pipeline resource models

This module defines Boolean masks, modular sample labels, and the matching criterion
`combinationSucceeds`. It also introduces `PipelineSchedule` and explicit query, time, and space
models together with comparison envelopes for the dihedral hidden subgroup pipeline.

This development follows [Regev2004a].

## Main statements

* `combinationSucceeds`: a label has between two and thirty-two matching masks.
* `PipelineSchedule`: positive block and routine counts covering the input size.
* `PipelineSchedule.time` and `PipelineSchedule.space`: resource ledgers for a schedule.

## References

* [Regev, 2004][Regev2004a]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.DihedralHSP04.MainResults

/-- Boolean masks on `l + 4` coordinates. -/
abbrev Mask (l : ℕ) : Type := Fin (l + 4) → Bool

/-- The all-false mask on `l + 4` coordinates. -/
def zeroMask (l : ℕ) : Mask l := fun _ => false

/-- Every coordinate of `zeroMask` is false. -/
@[simp] theorem zeroMask_apply (l : ℕ) (j : Fin (l + 4)) :
    zeroMask l j = false := rfl

/-- Samples consisting of `l + 4` labels in `ZMod (2 ^ l)`. -/
abbrev SampleSpace (l : ℕ) : Type := Fin (l + 4) → ZMod (2 ^ l)

/-- The sum modulo `2 ^ l` of the sample coordinates selected by a Boolean mask. -/
def dotMod (l : ℕ) (b : Mask l) (y : SampleSpace l) : ZMod (2 ^ l) :=
  ∑ j : Fin (l + 4), if b j then y j else 0

/-- The integer coefficient vector obtained by subtracting the indicator of `b₁` from that of
`b₂`. -/
def maskSub (l : ℕ) (b₁ b₂ : Mask l) : Fin (l + 4) → ℤ :=
  fun j => (if b₂ j then (1 : ℤ) else 0) - (if b₁ j then (1 : ℤ) else 0)

/-- The modular dot product of an integer coefficient vector with a sample. -/
def dotCoeff (l : ℕ) (c : Fin (l + 4) → ℤ) (y : SampleSpace l) : ZMod (2 ^ l) :=
  ∑ j : Fin (l + 4), (c j : ZMod (2 ^ l)) * y j

/-- The finite set of masks whose modular dot product with `y` equals `z`. -/
def matchSet (l : ℕ) (y : SampleSpace l) (z : ZMod (2 ^ l)) : Finset (Mask l) :=
  Finset.univ.filter (fun b => dotMod l b y = z)

/-- The number of masks matching the modular label `z` in the sample `y`. -/
def matchCount (l : ℕ) (y : SampleSpace l) (z : ZMod (2 ^ l)) : ℕ :=
  (matchSet l y z).card

/-- The condition that the matching count lies between two and thirty-two, inclusive. -/
def combinationSucceeds (l : ℕ) (y : SampleSpace l) (z : ZMod (2 ^ l)) : Prop :=
  2 ≤ matchCount l y z ∧ matchCount l y z ≤ 32

/-- The condition that `x` is divisible by `2 ^ l`. -/
def hasLowBitsZero (l x : ℕ) : Prop := x % 2 ^ l = 0

/-- The real comparison envelope `2 ^ (C * sqrt (n * log n))` for subexponential time estimates. -/
def subexponentialEnvelope (n : ℕ) (C : ℝ) : ℝ :=
  Real.rpow 2 (C * Real.sqrt ((n : ℝ) * Real.log n))

/-- The cubic space comparison envelope `((n : ℝ) + 1) ^ 3`. -/
def polynomialSpaceEnvelope (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ 3

/-- A pipeline schedule with positive block size `l` and routine count `k`, satisfying `n ≤ 1 +
k * l`. -/
structure PipelineSchedule where

  n : ℕ

  l : ℕ

  k : ℕ

  covers : n ≤ 1 + k * l

  block_pos : 0 < l

  routine_pos : 0 < k

/-- The query count model `(P.l + 4) ^ P.k` for a pipeline schedule. -/
def PipelineSchedule.queries (P : PipelineSchedule) : ℕ := (P.l + 4) ^ P.k

/-- The combination cost model `2 ^ (P.l + 4) * (P.l + 4)` for a schedule. -/
def PipelineSchedule.combineCost (P : PipelineSchedule) : ℕ :=
  2 ^ (P.l + 4) * (P.l + 4)

/-- The time model given by the product of the query count and combination cost. -/
def PipelineSchedule.time (P : PipelineSchedule) : ℕ :=
  P.queries * P.combineCost

/-- The space model `P.k * (P.l + 4) * (P.n + 1)` for a pipeline schedule. -/
def PipelineSchedule.space (P : PipelineSchedule) : ℕ :=
  P.k * (P.l + 4) * (P.n + 1)

end Qatlib.Papers.DihedralHSP04.MainResults
