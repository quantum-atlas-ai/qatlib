/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Qatlib.Concepts.SearchStopping.UnknownCount.Theorem3SourceFamilyTigh
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CollisionProb97.MainResults

open scoped BigOperators
open Qatlib.Concepts.SearchStopping.UnknownCount

universe u

def RToOne {X Y : Type u} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (F : X → Y) (r : ℕ) : Prop :=
  ∀ y ∈ Finset.image F (Finset.univ : Finset X),
    (Finset.univ.filter (fun x => F x = y)).card = r

def collisionCandidates {X Y : Type u} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (F : X → Y) (K : Finset X) : Finset X :=
  Finset.univ.filter (fun x => x ∉ K ∧ F x ∈ K.image F)

def clawCandidates {Y Z : Type u} [Fintype Y] [DecidableEq Y] [DecidableEq Z]
    (G : Y → Z) (T : Finset Z) : Finset Y :=
  Finset.univ.filter (fun y => G y ∈ T)

def bbhtConstant (l : ℝ) : ℝ := (l / 4) * (1 / (l - 1) + 4 / (4 - 3 * l))

def groverCoefficient (l : ℝ) : ℝ := 1 + 4 * bbhtConstant l

def proposedCollisionBudget (g N t k : ℝ) : ℝ := k + g * Real.sqrt (N / t) + 1

def proposedClawBudget (g N t : ℝ) : ℝ := g * Real.sqrt (N / t)

def tableEntryCount (k : ℕ) : ℕ := k

def proposedThreeK (k : ℕ) : ℕ := k + 2 * k

def proposedRecordCount (k : ℕ) : ℕ := k

theorem groverCoefficient_eq (l : ℝ) :
    groverCoefficient l = 1 + 4 * (l / 4 * (1 / (l - 1) + 4 / (4 - 3 * l))) := rfl

theorem bbhtConstant_pos (l : ℝ) (hl : 1 < l) (hl4 : l < 4 / 3) : 0 < bbhtConstant l := by
  have h1 : 0 < l - 1 := by linarith
  have h2 : 0 < 4 - 3 * l := by linarith
  have h3 : 0 < l / 4 := by linarith
  unfold bbhtConstant
  exact mul_pos h3 (add_pos (div_pos one_pos h1) (div_pos (by norm_num) h2))

theorem groverCoefficient_pos (l : ℝ) (hl : 1 < l) (hl4 : l < 4 / 3) :
    0 < groverCoefficient l := by
  have h := bbhtConstant_pos l hl hl4
  unfold groverCoefficient
  linarith

theorem proposedRecordCount_eq (k : ℕ) : proposedRecordCount k = k := rfl

theorem proposedRecordCount_isTheta :
    Asymptotics.IsTheta Filter.atTop (fun k : ℕ => (proposedRecordCount k : ℝ))
      (fun k : ℕ => (k : ℝ)) := by
  have h : (fun k : ℕ => (proposedRecordCount k : ℝ)) = fun k : ℕ => (k : ℝ) := by
    funext k
    exact_mod_cast proposedRecordCount_eq k
  rw [h]

end Qatlib.Papers.CollisionProb97.MainResults
