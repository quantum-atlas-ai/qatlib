/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# MUBCompletion26 — shared vocabulary for the extension analysis (§6–§9)

Fixed source: arXiv:2610.12180v1, §2 (definitions of unit rays, unbiasedness,
mutual unbiasedness, flatness) and §8 (ternary clock `D`).

This module fixes the small set of predicates used by the extension results:
unit vectors, unbiasedness to a basis, mutual unbiasedness of two bases,
orthonormality of columns, the ternary clock, setwise clock invariance of a
ray set, and roots of unity.
-/

open Matrix
open scoped Matrix BigOperators

set_option autoImplicit false

namespace Qatlib.Papers.MUBCompletion26.Completion.Clock

/-- A unit vector in `ℂ^n`. -/
def IsUnitVec {n : ℕ} (h : Fin n → ℂ) : Prop := (∑ i, Complex.normSq (h i)) = 1

/-- `h` is unbiased to the basis given by the columns of `E`: every overlap with
a column has squared modulus `1/n`. -/
def UnbiasedTo {n : ℕ} (E : Matrix (Fin n) (Fin n) ℂ) (h : Fin n → ℂ) : Prop :=
  ∀ k : Fin n, Complex.normSq ((Eᴴ *ᵥ h) k) = (1 : ℝ) / n

/-- The transition matrix of two bases has all entries of squared modulus
`1/n` (mutual unbiasedness, arXiv:2610.12180v1 §2). -/
def PairwiseMU {n : ℕ} (E F : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ j k : Fin n, Complex.normSq ((Eᴴ * F) j k) = (1 : ℝ) / n

/-- The columns of `E` are orthonormal. -/
def OrthonormalCols {n : ℕ} (E : Matrix (Fin n) (Fin n) ℂ) : Prop := Eᴴ * E = 1

/-- The ternary clock `D` acting on the six coordinates in the native
qutrit--qubit order: phases `1, ω, ω²` repeated twice. -/
def ternaryClock (ω : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.diagonal (fun i => ω ^ ((i : ℕ) % 3))

/-- The six rays of `V` are setwise invariant under `D`: `D` permutes them,
allowing arbitrary nonzero scalar multiples (individual unit phases). -/
def SetwiseDInvariant (D V : Matrix (Fin 6) (Fin 6) ℂ) : Prop :=
  ∀ k : Fin 6, ∃ (l : Fin 6) (c : ℂ), c ≠ 0 ∧ (D *ᵥ fun i => V i k) = c • (fun i => V i l)

/-- `z` is a root of unity. -/
def IsRootOfUnity (z : ℂ) : Prop := ∃ n : ℕ, 0 < n ∧ z ^ n = 1

end Qatlib.Papers.MUBCompletion26.Completion.Clock
