/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator

abbrev CM (d : ℕ) : Type := Matrix (Fin d) (Fin d) ℂ

def IsPhase (z : ℂ) : Prop := z * star z = 1

def BraidWord {G : Type*} [Group G] {m : ℕ} (σ : Fin m → G) (l : ℕ) (b : G) : Prop :=
  ∃ w : List (Fin m × Bool), w.length ≤ l ∧
    (w.map (fun p => if p.2 then σ p.1 else (σ p.1)⁻¹)).prod = b

def BraidRelations {G : Type*} [Group G] {m : ℕ} (σ : Fin m → G) : Prop :=
  (∀ i j : Fin m, (i : ℕ) + 2 ≤ (j : ℕ) ∨ (j : ℕ) + 2 ≤ (i : ℕ) → Commute (σ i) (σ j)) ∧
  (∀ i k : Fin m, (i : ℕ) + 1 = (k : ℕ) → σ i * σ k * σ i = σ k * σ i * σ k)

def PolyLogOverhead (overhead : ℕ → ℕ) : Prop :=
  ∃ d : ℕ, ∀ L : ℕ, overhead L ≤ (Nat.log 2 (L + 1) + 1) ^ d

structure JonesSector where

  d : ℕ

  n : ℕ

  M : Fin (n - 1) → CM d

  q : ℂ

end Qatlib.Papers.ModularFunct00.MainResults
