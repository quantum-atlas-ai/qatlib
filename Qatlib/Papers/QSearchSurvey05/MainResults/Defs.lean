/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSearchSurvey05.MainResults

def IsLocalMinimum {n : ℕ} (f : (Fin n → Bool) → ℤ) (x : Fin n → Bool) : Prop :=
  ∀ i : Fin n, f x ≤ f (Function.update x i (Bool.not (x i)))

abbrev GridCell (d n : ℕ) := Fin d → Fin n

def bitToZMod2 (b : Bool) : ZMod 2 :=
  if b then 1 else 0

def MatrixProductHolds {n : ℕ} (A B C : Matrix (Fin n) (Fin n) Bool) : Prop :=
  ∀ i j : Fin n,
    (∑ k : Fin n, bitToZMod2 (A i k) * bitToZMod2 (B k j)) = bitToZMod2 (C i j)

def LocalMinQueryLedger (n : ℕ) (m : ℝ) : ℝ :=
  Real.sqrt m + (2 : ℝ) ^ n * Real.sqrt (n : ℝ) / m

def LocalMinOptimalMemory (n : ℕ) : ℝ :=
  (2 : ℝ) ^ ((2 : ℝ) / 3 * (n : ℝ)) * (n : ℝ) ^ ((1 : ℝ) / 3)

end Qatlib.Papers.QSearchSurvey05.MainResults
