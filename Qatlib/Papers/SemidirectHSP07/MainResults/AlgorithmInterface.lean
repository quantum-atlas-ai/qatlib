/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP07.MainResults

def bitLength (n : ℕ) : ℕ := Nat.log 2 n + 1

def polyBound (r p : ℕ) : ℕ := 100 * ((r + 2) * bitLength p) ^ 3

def polyBoundCyclic (n : ℕ) : ℕ := 100 * (bitLength n) ^ 3

def polyBoundFamily {ι : Type*} [Fintype ι] (r p : ℕ) (q : ι → ℕ) : ℕ :=
  100 * ((r + 2) * bitLength p + Finset.univ.sum (fun i => bitLength (q i))) ^ 3

structure HSPAlgorithm (G : Type*) [Group G] where

  queryCount : ℕ

  successProb : ℚ

end Qatlib.Papers.SemidirectHSP07.MainResults
