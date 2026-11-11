/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# PointerHamiltonian — the pointer-ancilla Hamiltonian of equation (13)

Leyton--Osborne, *A quantum algorithm to solve nonlinear differential equations*,
fixed arXiv:0812.4423v1.

Source location: §3, equations (12)--(18), and Appendix A.3 equation (30).

The paper turns the non-unitary operator `A` of (12) into a genuine Hamiltonian
by adjoining a pointer qubit,

  `H = -i A ⊗ |1⟩⟨0| + i A† ⊗ |0⟩⟨1|`,

evolves `|φ⟩|φ⟩|0⟩` for a time `ε`, postselects on pointer `1`, and obtains
`ε A |φ⟩|φ⟩` together with a `ε²/2` success probability.  The exact unitary used
in place of the truncated exponential is (18),

  `U_ε = √(I − ε²H²) + iεH`,   `|ε| ≤ 1/‖H‖`.

This module proves:

* the exact action of `H` on the pointer-`0` and pointer-`1` branches;
* the first-order expansion `(1 + iεH)|v⟩|0⟩ = |v⟩|0⟩ + ε (Av)|1⟩` of (15);
* that the pointer-`1` branch of the exact evolution `U_ε` is exactly
  `ε (Av)`, provided the even part `√(I − ε²H²)` is pointer-diagonal;
* the scalar (eigenvalue) form of unitarity: for `|t| ≤ 1` the complex number
  `√(1 − t²) + i t` has modulus one, which is the action of `U_ε` on an
  eigenvector of `H` with eigenvalue `t/ε`.

Not formalised here: the pointer-diagonal block structure of `H²` with the
explicit `A†A` / `AA†` blocks, and the general finite-dimensional unitarity of
`U = P + iεH` from the functional-calculus hypotheses `P† = P`,
`P² = I − ε²H²`, `PH = HP`.  Those are the remaining gaps behind claim c007.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.NonlinODE08.TensorBranch

/-- The two-copy system register: two `n+1`-level amplitude slots. -/
abbrev Sys (n : ℕ) := Fin (n + 1) × Fin (n + 1)

/-- A linear operator on the two-copy register, written as its matrix entries. -/
abbrev Mat (n : ℕ) := Sys n → Sys n → ℂ

/-- The state with pointer `0` and system amplitude `w`. -/
def ptrZero {n : ℕ} (w : Sys n → ℂ) : Sys n × Fin 2 → ℂ
  | (o, 0) => w o
  | (_, 1) => 0

/-- The state with pointer `1` and system amplitude `w`. -/
def ptrOne {n : ℕ} (w : Sys n → ℂ) : Sys n × Fin 2 → ℂ
  | (_, 0) => 0
  | (o, 1) => w o

/-- The pointer Hamiltonian (13) applied to a state: on the pointer-`0` branch it
acts with `i A†` read from the pointer-`1` component, and on the pointer-`1`
branch with `-i A` read from the pointer-`0` component. -/
def hamApply {n : ℕ} (aM : Mat n) (v : Sys n × Fin 2 → ℂ) : Sys n × Fin 2 → ℂ
  | (o, 0) => ∑ inp : Sys n, Complex.I * starRingEnd ℂ (aM inp o) * v (inp, 1)
  | (o, 1) => ∑ inp : Sys n, (-Complex.I) * aM o inp * v (inp, 0)

/-- `i` times `-i` is one, the identity behind the first-order expansion (15). -/
theorem I_mul_neg_I : Complex.I * (-Complex.I) = 1 := by
  rw [mul_neg, Complex.I_mul_I]
  norm_num

/-- `(-i)` times `i` is one. -/
theorem neg_I_mul_I : (-Complex.I) * Complex.I = 1 := by
  rw [neg_mul, Complex.I_mul_I]
  norm_num

/-- The pointer-`0` branch of `H` applied to `|v⟩|0⟩` vanishes. -/
theorem ham_apply_ptrZero {n : ℕ} (aM : Mat n) (w : Sys n → ℂ) (o : Sys n) :
    hamApply aM (ptrZero w) (o, 0) = 0 := by
  simp [hamApply, ptrZero]

/-- The pointer-`1` branch of `H|v⟩|0⟩` is `-i A v`, equation (15). -/
theorem ham_apply_ptrZero_one {n : ℕ} (aM : Mat n) (w : Sys n → ℂ) (o : Sys n) :
    hamApply aM (ptrZero w) (o, 1) = (-Complex.I) * (∑ inp : Sys n, aM o inp * w inp) := by
  simp only [hamApply, ptrZero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro inp _
  ring

/-- The pointer-`1` branch of `H` applied to `|w⟩|1⟩` vanishes. -/
theorem ham_apply_ptrOne {n : ℕ} (aM : Mat n) (w : Sys n → ℂ) (o : Sys n) :
    hamApply aM (ptrOne w) (o, 1) = 0 := by
  simp [hamApply, ptrOne]

/-- The pointer-`0` branch of `H|w⟩|1⟩` is `i A† w`. -/
theorem ham_apply_ptrOne_zero {n : ℕ} (aM : Mat n) (w : Sys n → ℂ) (o : Sys n) :
    hamApply aM (ptrOne w) (o, 0) =
      Complex.I * (∑ inp : Sys n, starRingEnd ℂ (aM inp o) * w inp) := by
  simp only [hamApply, ptrOne]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro inp _
  ring

/-- Equation (15) to first order: the pointer-`1` component of `(1 + iεH)|v⟩|0⟩`
is exactly `ε (A v)`. -/
theorem first_order_ptrZero_one {n : ℕ} (aM : Mat n) (w : Sys n → ℂ) (ε : ℝ) (o : Sys n) :
    ptrZero w (o, 1) + (Complex.I * ((ε : ℝ) : ℂ)) * hamApply aM (ptrZero w) (o, 1)
      = ((ε : ℝ) : ℂ) * (∑ inp : Sys n, aM o inp * w inp) := by
  rw [ham_apply_ptrZero_one]
  simp only [ptrZero, zero_add]
  calc
    Complex.I * ((ε : ℝ) : ℂ) * ((-Complex.I) * ∑ inp : Sys n, aM o inp * w inp)
        = (Complex.I * (-Complex.I)) * (((ε : ℝ) : ℂ) *
            ∑ inp : Sys n, aM o inp * w inp) := by ring
    _ = ((ε : ℝ) : ℂ) * ∑ inp : Sys n, aM o inp * w inp := by
          rw [I_mul_neg_I, one_mul]

/-- The exact pointer-`1` branch of the evolution (18): if the even part
`√(I − ε²H²)` is pointer-diagonal, then the pointer-`1` component of
`U_ε|v⟩|0⟩` is exactly `ε(A v)`, which is the paper's posterior state (17). -/
theorem exact_branch_ptrZero_one {n : ℕ} (aM : Mat n)
    (P : (Sys n × Fin 2 → ℂ) → (Sys n × Fin 2 → ℂ))
    (hP1 : ∀ (w : Sys n → ℂ) (o : Sys n), P (ptrZero w) (o, 1) = 0)
    (w : Sys n → ℂ) (ε : ℝ) (o : Sys n) :
    P (ptrZero w) (o, 1) + (Complex.I * ((ε : ℝ) : ℂ)) * hamApply aM (ptrZero w) (o, 1)
      = ((ε : ℝ) : ℂ) * (∑ inp : Sys n, aM o inp * w inp) := by
  rw [hP1 w o]
  exact first_order_ptrZero_one aM w ε o

/-- Scalar (eigenvalue) form of unitarity: for `|t| ≤ 1` the complex number
`√(1 − t²) + i t` has modulus one.  This is the action of `U_ε` on an eigenvector
of `H` with eigenvalue `t/ε`. -/
theorem scalar_normSq_unitary (t : ℝ) (ht : t ^ 2 ≤ 1) :
    Complex.normSq ((Real.sqrt (1 - t ^ 2) : ℂ) + Complex.I * ((t : ℝ) : ℂ)) = 1 := by
  have hre : (((Real.sqrt (1 - t ^ 2) : ℂ) + Complex.I * ((t : ℝ) : ℂ))).re
      = Real.sqrt (1 - t ^ 2) := by
    simp
  have him : (((Real.sqrt (1 - t ^ 2) : ℂ) + Complex.I * ((t : ℝ) : ℂ))).im = t := by
    simp
  rw [Complex.normSq_apply, hre, him]
  have hsq : Real.sqrt (1 - t ^ 2) * Real.sqrt (1 - t ^ 2) = 1 - t ^ 2 :=
    Real.mul_self_sqrt (by linarith)
  nlinarith

end Qatlib.Papers.NonlinODE08.TensorBranch
