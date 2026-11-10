/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PottsTutte07.MainResults.Definitions
import Qatlib.Papers.PottsTutte07.MainResults.Scales
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PottsTutte07.MainResults

open scoped BigOperators

def IsUnitaryType (q : ℂ) (Wodd Weven : Set ℂ) : Prop :=
  Wodd.Nonempty ∧ Weven.Nonempty ∧
  (∀ v ∈ Wodd, ‖v + q‖ = ‖v‖) ∧
  (∀ v ∈ Weven, ‖1 + v‖ = 1) ∧
  (∀ v ∈ Wodd, ∃ w ∈ Wodd, w + v + q = 0) ∧
  (∀ v ∈ Weven, ∃ w ∈ Weven, w + v + w * v = 0)

def IsComplexNonUnitaryType (q : ℂ) (Wodd Weven : Set ℂ) : Prop :=
  ¬ IsUnitaryType q Wodd Weven ∧
  ((∃ v ∈ Wodd, v.im ≠ 0) ∨ (∃ v ∈ Weven, v.im ≠ 0) ∨ q.im ≠ 0)

def IsRealNonUnitaryType (q : ℂ) (Wodd Weven : Set ℂ) : Prop :=
  ¬ IsUnitaryType q Wodd Weven ∧
  q.im = 0 ∧ 4 * Real.cos (Real.pi / 5) ^ 2 < q.re ∧
  (∀ v ∈ Wodd, v.im = 0) ∧ (∀ v ∈ Weven, v.im = 0)

structure TutteInstance where
  numV : ℕ
  numE : ℕ
  q : ℂ
  weights : Fin numE → ℂ
  Eodd : Finset (Fin numE)
  target : ℂ
  window : ℝ

def entryDist {n : Type*} [Fintype n] (A B : Matrix n n ℂ) : ℝ :=
  ∑ i : n, ∑ j : n, ‖A i j - B i j‖

def DenseIn {n : Type*} [Fintype n] (target gen : Set (Matrix n n ℂ)) : Prop :=
  ∀ U ∈ target, ∀ ε : ℝ, 0 < ε → ∃ g ∈ gen, entryDist g U < ε

def SpecialUnitarySet (K : ℕ) [NeZero K] : Set (Matrix (Fin K) (Fin K) ℂ) :=
  {U | IsUnitary U ∧ Matrix.det U = 1}

def SpecialLinearSet (K : ℕ) [NeZero K] : Set (Matrix (Fin K) (Fin K) ℂ) :=
  {U | Matrix.det U = 1}

def SpecialLinearRealSet (K : ℕ) [NeZero K] : Set (Matrix (Fin K) (Fin K) ℂ) :=
  {U | (∀ i j, (U i j).im = 0) ∧ Matrix.det U = 1}

def generatedBy {K : ℕ} (gens : Set (Matrix (Fin K) (Fin K) ℂ)) : Set (Matrix (Fin K) (Fin K) ℂ) :=
  (Submonoid.closure gens : Set (Matrix (Fin K) (Fin K) ℂ))

def wordEval {K : ℕ} (word : List (Matrix (Fin K) (Fin K) ℂ)) : Matrix (Fin K) (Fin K) ℂ :=
  word.prod

def polyLogBound (δ : ℝ) : ℕ :=
  Nat.ceil (Real.log (1 / δ)) ^ 2 + 1

end Qatlib.Papers.PottsTutte07.MainResults
