/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamNANDTree07.MainResults.NandGateLimit

open ENNReal

def leafY : Bool → ℝ≥0∞
  | true => 0
  | false => ⊤

def stepY (y₁ y₂ : ℝ≥0∞) : ℝ≥0∞ := (y₁ + y₂)⁻¹

def nand (a b : Bool) : Bool := !(a && b)

theorem stepY_leafY (a b : Bool) : stepY (leafY a) (leafY b) = leafY (nand a b) := by
  cases a <;> cases b <;> simp [stepY, leafY, nand]

theorem stepY_leafY_eq_top_iff (a b : Bool) :
    stepY (leafY a) (leafY b) = ⊤ ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [stepY, leafY]

theorem stepY_leafY_eq_zero_iff (a b : Bool) :
    stepY (leafY a) (leafY b) = 0 ↔ a = false ∨ b = false := by
  cases a <;> cases b <;> simp [stepY, leafY]

inductive NandTree : Type
  | leaf : Bool → NandTree
  | node : NandTree → NandTree → NandTree
  deriving DecidableEq

def evalNand : NandTree → Bool
  | .leaf b => b
  | .node l r => nand (evalNand l) (evalNand r)

def bottomY : NandTree → ℝ≥0∞
  | .leaf b => leafY b
  | .node l r => stepY (bottomY l) (bottomY r)

theorem bottomY_eq_leafY_evalNand (t : NandTree) :
    bottomY t = leafY (evalNand t) := by
  induction t with
  | leaf b => rfl
  | node l r ihl ihr =>
      simp only [bottomY, evalNand, ihl, ihr, stepY_leafY]

theorem bottomY_eq_zero_iff (t : NandTree) : bottomY t = 0 ↔ evalNand t = true := by
  rw [bottomY_eq_leafY_evalNand]
  cases evalNand t <;> simp [leafY]

theorem bottomY_eq_top_iff (t : NandTree) : bottomY t = ⊤ ↔ evalNand t = false := by
  rw [bottomY_eq_leafY_evalNand]
  cases evalNand t <;> simp [leafY]

end Qatlib.Papers.HamNANDTree07.MainResults.NandGateLimit
