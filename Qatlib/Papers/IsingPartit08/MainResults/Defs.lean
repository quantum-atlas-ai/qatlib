/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Algebraic data for the Ising partition correspondence

This module defines binary quadratic forms, matrix kernels, and the signed and unsigned Eulerian
sums used in [Geraci2008]. It also introduces the normalization factor and the propositions
`HadamardTestEstimate` and `MasterCorrespondence` used to state numerical error propagation.

## Main statements

* `signedEulerianSum`: weights kernel vectors by their quadratic signs and Hamming weights.
* `parityCondition`: requires the quadratic form to vanish on the kernel.
* `MasterCorrespondence`: relates an amplitude to a sum by a scalar normalizer.

## References

* [Geraci, 2008][Geraci2008]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical

attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.IsingPartit08.MainResults

/-- The type of binary vectors with `R` coordinates. -/
abbrev F2Vec (R : ℕ) := Fin R → ZMod 2

/-- The real parity sign, equal to `1` at zero and `-1` otherwise. -/
def paritySign (x : ZMod 2) : ℝ := if x = 0 then 1 else -1

/-- The parity sign at zero equals `1`. -/
@[simp] theorem paritySign_zero : paritySign 0 = 1 := if_pos rfl

/-- The parity sign of a nonzero binary value equals `-1`. -/
theorem paritySign_ne_zero {x : ZMod 2} (hx : x ≠ 0) : paritySign x = -1 := if_neg hx

/-- The binary quadratic form `∑ i, ∑ j, a i * B i j * a j`. -/
def quadForm {R : ℕ} (B : Matrix (Fin R) (Fin R) (ZMod 2)) (a : F2Vec R) : ZMod 2 :=
  ∑ i, ∑ j, a i * B i j * a j

/-- The Hamming weight of a binary vector, counted by its nonzero coordinates. -/
def wt {R : ℕ} (a : F2Vec R) : ℕ := (Finset.univ.filter (fun i => a i ≠ 0)).card

/-- The unique binary vector with zero coordinates has Hamming weight zero. -/
@[simp] theorem wt_zero_eq_zero : wt (fun _ : Fin 0 => (0 : ZMod 2)) = 0 := by
  simp [wt]

/-- The predicate that every row of `CH` has zero binary dot product with `a`. -/
def inKernelCH {R N : ℕ} (CH : Matrix (Fin R) (Fin N) (ZMod 2)) (a : F2Vec N) : Prop :=
  ∀ i, ∑ j, CH i j * a j = 0

/-- The finite set of binary vectors in the kernel of `CH`. -/
def kerSet {R N : ℕ} (CH : Matrix (Fin R) (Fin N) (ZMod 2)) : Finset (F2Vec N) :=
  Finset.univ.filter (fun a => inKernelCH CH a)

/-- The sum over `kerSet CH` of `lam ^ wt a` multiplied by the parity sign of `quadForm B a`. -/
def signedEulerianSum {R N : ℕ} (B : Matrix (Fin N) (Fin N) (ZMod 2))
    (CH : Matrix (Fin R) (Fin N) (ZMod 2)) (lam : ℝ) : ℝ :=
  ∑ a ∈ kerSet CH, paritySign (quadForm B a) * lam ^ wt a

/-- The unsigned sum of `lam ^ wt a` over `kerSet CH`. -/
def eulerianSum {R N : ℕ} (CH : Matrix (Fin R) (Fin N) (ZMod 2)) (lam : ℝ) : ℝ :=
  ∑ a ∈ kerSet CH, lam ^ wt a

/-- The condition that `quadForm B a` vanishes for every vector in `kerSet CH`. -/
def parityCondition {R N : ℕ} (B : Matrix (Fin N) (Fin N) (ZMod 2))
    (CH : Matrix (Fin R) (Fin N) (ZMod 2)) : Prop :=
  ∀ a ∈ kerSet CH, quadForm B a = 0

/-- The nonnegative square root of `(lam ^ 2 + 1) ^ edges`. -/
def normalizerOf (lam : ℝ) (edges : ℕ) : ℝ := Real.sqrt ((lam ^ 2 + 1) ^ edges)

/-- A gate label consisting of a binary vector with `R` coordinates. -/
structure AnsatzGate (R : ℕ) where

  b : F2Vec R

/-- The numerical error bound `|m - q| ≤ p` for an estimate `m` of `q`. -/
def HadamardTestEstimate (q p m : ℝ) : Prop := |m - q| ≤ p

/-- The scalar identity `q * normalizer = s` relating an amplitude to the corresponding sum. -/
def MasterCorrespondence (q normalizer s : ℝ) : Prop := q * normalizer = s

end Qatlib.Papers.IsingPartit08.MainResults
