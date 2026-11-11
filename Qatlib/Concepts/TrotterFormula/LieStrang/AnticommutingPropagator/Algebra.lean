/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.LieStrang.AnticommutingPropagator.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Algebra of anticommuting propagators

This module proves polynomial identities for `shiftedGenerator` and `rescaledStep` when `P` and
`Q` are anticommuting involutions. The calculations reduce matrix products to scalar coefficient
identities, using the matrix-algebra setting of [Bhatia1997].

## Main statements

* `shiftedGenerator_square`: the shifted generator squares to `(a² - ω²)` times identity.
* `rescaledStep_inverse`: opposite step parameters give two-sided inverses under the coefficient
  relation.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.TrotterFormula.LieStrang.AnticommutingPropagator
open Matrix
open scoped Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- For anticommuting involutions `P` and `Q`, the square of `iω P + a Q` is `(a² - ω²)` times
identity. -/
theorem shiftedGenerator_square (P Q : Matrix I I ℂ) (a ω : ℝ)
    (hP : P * P = 1) (hQ : Q * Q = 1) (hPQ : P * Q = -(Q * P)) :
    shiftedGenerator P Q a ω * shiftedGenerator P Q a ω =
      (((a ^ 2 - ω ^ 2 : ℝ) : ℂ)) • (1 : Matrix I I ℂ) := by
  have hI : (Complex.I * (ω : ℂ)) * (Complex.I * (ω : ℂ)) =
      -((ω : ℂ) * (ω : ℂ)) := by
    calc
      _ = (Complex.I * Complex.I) * ((ω : ℂ) * (ω : ℂ)) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  unfold shiftedGenerator
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
  rw [hP, hQ, hPQ, hI]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  push_cast
  ring

/-- For anticommuting involutions and `c² + (ω² - a²) * s² = 1`, the rescaled steps with
parameters `s` and `-s` are two-sided inverses. -/
theorem rescaledStep_inverse (P Q : Matrix I I ℂ) (a ω c s : ℝ)
    (hP : P * P = 1) (hQ : Q * Q = 1) (hPQ : P * Q = -(Q * P))
    (hcs : c ^ 2 + (ω ^ 2 - a ^ 2) * s ^ 2 = 1) :
    rescaledStep P Q a ω c (-s) * rescaledStep P Q a ω c s = 1 ∧
      rescaledStep P Q a ω c s * rescaledStep P Q a ω c (-s) = 1 := by
  have hB := shiftedGenerator_square P Q a ω hP hQ hPQ
  have hscalar : (c : ℂ) ^ 2 + ((ω : ℂ) ^ 2 - (a : ℂ) ^ 2) * (s : ℂ) ^ 2 = 1 := by
    exact_mod_cast hcs
  constructor <;>
    simp only [rescaledStep, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      smul_smul, one_mul, mul_one, hB, Complex.ofReal_neg] <;>
    ext i j <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;>
    push_cast <;>
    linear_combination ((1 : Matrix I I ℂ) i j) * hscalar

end Qatlib.Concepts.TrotterFormula.LieStrang.AnticommutingPropagator
