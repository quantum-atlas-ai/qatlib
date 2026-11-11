/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations

/-!
# NAND evaluation through extended-real reciprocal sums

This module represents Boolean values by 0 and infinity using `leafY` and proves that the
reciprocal-sum rule `stepY` implements `nand`. The recursive construction `bottomY` agrees with
`leafY` applied to the Boolean evaluation of every `NandTree`. See [FarhiGoldstoneGutmann2008]
for the Hamiltonian NAND-tree setting.

## Main statements

* `stepY_leafY`: Applying `stepY` to the encodings of two Booleans gives the encoding of their
  NAND.
* `bottomY_eq_leafY_evalNand`: The recursive extended-real value of every NAND tree is the
  encoding of its Boolean evaluation.
* `bottomY_eq_zero_iff`: A NAND tree has extended-real value zero exactly when its Boolean
  evaluation is true.

## References

* [Farhi et al., 2008][FarhiGoldstoneGutmann2008]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamNANDTree07.MainResults.NandGateLimit

open ENNReal

/-- The extended nonnegative real encoding of a Boolean, sending true to 0 and false to
infinity. -/
def leafY : Bool → ℝ≥0∞
  | true => 0
  | false => ⊤

/-- The reciprocal-sum operation (y₁ + y₂)⁻¹ on extended nonnegative reals. -/
def stepY (y₁ y₂ : ℝ≥0∞) : ℝ≥0∞ := (y₁ + y₂)⁻¹

/-- The Boolean NAND operation, the negation of the conjunction of its inputs. -/
def nand (a b : Bool) : Bool := !(a && b)

/-- Applying `stepY` to the encodings of two Booleans gives the encoding of their NAND. See
[FarhiGoldstoneGutmann2008]. -/
theorem stepY_leafY (a b : Bool) : stepY (leafY a) (leafY b) = leafY (nand a b) := by
  cases a <;> cases b <;> simp [stepY, leafY, nand]

/-- The reciprocal-sum output on two encoded Booleans is infinity exactly when both inputs are
true. -/
theorem stepY_leafY_eq_top_iff (a b : Bool) :
    stepY (leafY a) (leafY b) = ⊤ ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [stepY, leafY]

/-- The reciprocal-sum output on two encoded Booleans is zero exactly when at least one input is
false. -/
theorem stepY_leafY_eq_zero_iff (a b : Bool) :
    stepY (leafY a) (leafY b) = 0 ↔ a = false ∨ b = false := by
  cases a <;> cases b <;> simp [stepY, leafY]

/-- Finite binary NAND trees with Boolean-labeled leaves and binary internal nodes. -/
inductive NandTree : Type
  | leaf : Bool → NandTree
  | node : NandTree → NandTree → NandTree
  deriving DecidableEq

/-- The recursive Boolean evaluation of a `NandTree`, using NAND at each internal node. -/
def evalNand : NandTree → Bool
  | .leaf b => b
  | .node l r => nand (evalNand l) (evalNand r)

/-- The recursive extended-real evaluation of a `NandTree`, using `leafY` at leaves and `stepY`
at internal nodes. -/
def bottomY : NandTree → ℝ≥0∞
  | .leaf b => leafY b
  | .node l r => stepY (bottomY l) (bottomY r)

/-- The recursive extended-real value of every NAND tree is the encoding of its Boolean
evaluation. See [FarhiGoldstoneGutmann2008]. -/
theorem bottomY_eq_leafY_evalNand (t : NandTree) :
    bottomY t = leafY (evalNand t) := by
  induction t with
  | leaf b => rfl
  | node l r ihl ihr =>
      simp only [bottomY, evalNand, ihl, ihr, stepY_leafY]

/-- A NAND tree has extended-real value zero exactly when its Boolean evaluation is true. -/
theorem bottomY_eq_zero_iff (t : NandTree) : bottomY t = 0 ↔ evalNand t = true := by
  rw [bottomY_eq_leafY_evalNand]
  cases evalNand t <;> simp [leafY]

/-- A NAND tree has extended-real value infinity exactly when its Boolean evaluation is false. -/
theorem bottomY_eq_top_iff (t : NandTree) : bottomY t = ⊤ ↔ evalNand t = false := by
  rw [bottomY_eq_leafY_evalNand]
  cases evalNand t <;> simp [leafY]

end Qatlib.Papers.HamNANDTree07.MainResults.NandGateLimit
