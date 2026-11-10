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

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.DihedralHSP04.MainResults

abbrev Mask (l : ℕ) : Type := Fin (l + 4) → Bool

def zeroMask (l : ℕ) : Mask l := fun _ => false

@[simp] theorem zeroMask_apply (l : ℕ) (j : Fin (l + 4)) :
    zeroMask l j = false := rfl

abbrev SampleSpace (l : ℕ) : Type := Fin (l + 4) → ZMod (2 ^ l)

def dotMod (l : ℕ) (b : Mask l) (y : SampleSpace l) : ZMod (2 ^ l) :=
  ∑ j : Fin (l + 4), if b j then y j else 0

def maskSub (l : ℕ) (b₁ b₂ : Mask l) : Fin (l + 4) → ℤ :=
  fun j => (if b₂ j then (1 : ℤ) else 0) - (if b₁ j then (1 : ℤ) else 0)

def dotCoeff (l : ℕ) (c : Fin (l + 4) → ℤ) (y : SampleSpace l) : ZMod (2 ^ l) :=
  ∑ j : Fin (l + 4), (c j : ZMod (2 ^ l)) * y j

def matchSet (l : ℕ) (y : SampleSpace l) (z : ZMod (2 ^ l)) : Finset (Mask l) :=
  Finset.univ.filter (fun b => dotMod l b y = z)

def matchCount (l : ℕ) (y : SampleSpace l) (z : ZMod (2 ^ l)) : ℕ :=
  (matchSet l y z).card

def combinationSucceeds (l : ℕ) (y : SampleSpace l) (z : ZMod (2 ^ l)) : Prop :=
  2 ≤ matchCount l y z ∧ matchCount l y z ≤ 32

def hasLowBitsZero (l x : ℕ) : Prop := x % 2 ^ l = 0

def subexponentialEnvelope (n : ℕ) (C : ℝ) : ℝ :=
  Real.rpow 2 (C * Real.sqrt ((n : ℝ) * Real.log n))

def polynomialSpaceEnvelope (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ 3

structure PipelineSchedule where

  n : ℕ

  l : ℕ

  k : ℕ

  covers : n ≤ 1 + k * l

  block_pos : 0 < l

  routine_pos : 0 < k

def PipelineSchedule.queries (P : PipelineSchedule) : ℕ := (P.l + 4) ^ P.k

def PipelineSchedule.combineCost (P : PipelineSchedule) : ℕ :=
  2 ^ (P.l + 4) * (P.l + 4)

def PipelineSchedule.time (P : PipelineSchedule) : ℕ :=
  P.queries * P.combineCost

def PipelineSchedule.space (P : PipelineSchedule) : ℕ :=
  P.k * (P.l + 4) * (P.n + 1)

end Qatlib.Papers.DihedralHSP04.MainResults
