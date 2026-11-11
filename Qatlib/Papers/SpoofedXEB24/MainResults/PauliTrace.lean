/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic

open Matrix
set_option autoImplicit false

/-!
# Two-qubit Pauli algebra for `SpoofedXEB24`

The paper (Tanggara–Gu–Bharti, arXiv:2405.00789v2, Appendix F) evaluates Weingarten
traces of products of unnormalised two-qubit Paulis.  This module supplies the purely
algebraic input of that evaluation:

* the four unnormalised single-qubit Pauli matrices `Pauli1.toMat` and their
  multiplication law `Pauli1.toMat a * Pauli1.toMat b = phase a b • Pauli1.toMat (mul a b)`;
* the two-qubit Paulis `Pauli2` as Kronecker products, with the same phase law;
* the trace classification `tr (P a) = 4` when `a` is the two-qubit identity and `0`
  otherwise, together with the resulting criterion: a product of two-qubit Paulis has
  nonzero trace exactly when its label product is the identity.

The phase factor is essential.  The literal phrasing of Lemma 1 in the paper says that
`Tr (W_π Q_1 ⊗ ⋯ ⊗ Q_k) = 4^{c_π}` whenever the cyclic Pauli products are `I ⊗ I`; for
two-qubit Paulis the product of an odd number of anticommuting factors can be `± i (I ⊗ I)`,
so the trace is `± 4 i` rather than `4`.  `trace_prod_toMat` records the exact value
including this phase, and `trace_prod_toMat_ne_zero_iff` records the vanishing criterion
that is phase independent.
-/

namespace Qatlib.Papers.SpoofedXEB24.MainResults

/-- The four single-qubit Pauli labels. -/
inductive Pauli1 where
  | I
  | X
  | Y
  | Z
  deriving DecidableEq, Repr

instance : Fintype Pauli1 :=
  ⟨{Pauli1.I, Pauli1.X, Pauli1.Y, Pauli1.Z}, by intro x; cases x <;> simp⟩

/-- The unnormalised single-qubit Pauli matrices `I, X, Y, Z`. -/
noncomputable def Pauli1.toMat : Pauli1 → Matrix (Fin 2) (Fin 2) ℂ
  | .I => 1
  | .X => !![0, 1; 1, 0]
  | .Y => !![0, -Complex.I; Complex.I, 0]
  | .Z => !![1, 0; 0, -1]

/-- Label multiplication on single-qubit Paulis: the Pauli with `P a * P b = ±1, ±i · P (a * b)`. -/
def Pauli1.mul : Pauli1 → Pauli1 → Pauli1
  | .I, b => b
  | a, .I => a
  | .X, .X => .I
  | .Y, .Y => .I
  | .Z, .Z => .I
  | .X, .Y => .Z
  | .Y, .Z => .X
  | .Z, .X => .Y
  | .Y, .X => .Z
  | .Z, .Y => .X
  | .X, .Z => .Y

/-- The scalar phase in `P a * P b = phase a b • P (a * b)`. -/
noncomputable def Pauli1.phase : Pauli1 → Pauli1 → ℂ
  | .I, _ => 1
  | _, .I => 1
  | .X, .X => 1
  | .Y, .Y => 1
  | .Z, .Z => 1
  | .X, .Y => Complex.I
  | .Y, .Z => Complex.I
  | .Z, .X => Complex.I
  | .Y, .X => -Complex.I
  | .Z, .Y => -Complex.I
  | .X, .Z => -Complex.I

/-- Products of single-qubit Pauli matrices are phases times Pauli matrices. -/
lemma Pauli1.toMat_mul (a b : Pauli1) :
    Pauli1.toMat a * Pauli1.toMat b = Pauli1.phase a b • Pauli1.toMat (Pauli1.mul a b) := by
  cases a <;> cases b <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Pauli1.toMat, Pauli1.mul, Pauli1.phase]

/-- The trace of a single-qubit Pauli is `2` at the identity and `0` elsewhere. -/
lemma Pauli1.trace_toMat (a : Pauli1) :
    (Pauli1.toMat a).trace = if a = Pauli1.I then 2 else 0 := by
  cases a <;> simp [Pauli1.toMat, Matrix.trace]

/-- Every Pauli phase is nonzero. -/
lemma Pauli1.phase_ne_zero (a b : Pauli1) : Pauli1.phase a b ≠ 0 := by
  cases a <;> cases b <;> simp [Pauli1.phase]

/-- A two-qubit Pauli is a pair of single-qubit Pauli labels. -/
abbrev Pauli2 := Pauli1 × Pauli1

/-- The unnormalised two-qubit Pauli matrix `A ⊗ B`. -/
noncomputable def Pauli2.toMat (p : Pauli2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kroneckerMap (· * ·) (Pauli1.toMat p.1) (Pauli1.toMat p.2)

/-- Label multiplication on two-qubit Paulis. -/
def Pauli2.mul (p q : Pauli2) : Pauli2 := (p.1.mul q.1, p.2.mul q.2)

/-- The scalar phase in `P p * P q = phase p q • P (p * q)`. -/
noncomputable def Pauli2.phase (p q : Pauli2) : ℂ := Pauli1.phase p.1 q.1 * Pauli1.phase p.2 q.2

/-- Every two-qubit Pauli phase is nonzero. -/
lemma Pauli2.phase_ne_zero (p q : Pauli2) : Pauli2.phase p q ≠ 0 :=
  mul_ne_zero (Pauli1.phase_ne_zero _ _) (Pauli1.phase_ne_zero _ _)

/-- Products of two-qubit Pauli matrices are phases times two-qubit Pauli matrices. -/
lemma Pauli2.toMat_mul (p q : Pauli2) :
    Pauli2.toMat p * Pauli2.toMat q = Pauli2.phase p q • Pauli2.toMat (Pauli2.mul p q) := by
  rw [Pauli2.toMat, Pauli2.toMat, Pauli2.toMat, ← Matrix.mul_kronecker_mul, Pauli1.toMat_mul,
    Pauli1.toMat_mul, Matrix.kroneckerMap_smul_left (f := (· * ·))
      (hf := fun a b => by simp [mul_assoc])]
  rw [Matrix.kroneckerMap_smul_right (f := (· * ·))
      (hf := fun a b => by simp [mul_comm, mul_assoc]), Pauli2.phase, Pauli2.mul, smul_smul]

/-- The trace of a two-qubit Pauli is `4` at the identity and `0` elsewhere. -/
lemma Pauli2.trace_toMat (p : Pauli2) :
    (Pauli2.toMat p).trace = if p = (Pauli1.I, Pauli1.I) then 4 else 0 := by
  rw [Pauli2.toMat, Matrix.trace_kronecker, Pauli1.trace_toMat, Pauli1.trace_toMat]
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> simp
  all_goals norm_num

/-- The two-qubit identity Pauli matrix is the identity matrix. -/
lemma Pauli2.toMat_identity : Pauli2.toMat (Pauli1.I, Pauli1.I) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pauli2.toMat, Pauli1.toMat, Matrix.kroneckerMap]

/-- Products of two-qubit Pauli matrices are non-zero scalar multiples of two-qubit Pauli
matrices. -/
theorem exists_smul_prod_toMat (l : List Pauli2) :
    ∃ (c : ℂ) (lbl : Pauli2), c ≠ 0 ∧ (l.map Pauli2.toMat).prod = c • Pauli2.toMat lbl := by
  induction l with
  | nil => exact ⟨1, (Pauli1.I, Pauli1.I), one_ne_zero, by simp [Pauli2.toMat_identity]⟩
  | cons p rest ih =>
      obtain ⟨c, lbl, hc, h⟩ := ih
      refine ⟨Pauli2.phase p lbl * c, Pauli2.mul p lbl, ?_, ?_⟩
      · exact mul_ne_zero (Pauli2.phase_ne_zero _ _) hc
      · rw [List.map_cons, List.prod_cons, h, Matrix.mul_smul, Pauli2.toMat_mul, smul_smul,
          mul_comm c]

/-- **Trace of a product of two-qubit Paulis.** If the product is the non-zero scalar
multiple `c • P(lbl)`, its trace is `4 c` when `lbl` is the two-qubit identity and `0`
otherwise. -/
theorem trace_prod_toMat (l : List Pauli2) (c : ℂ) (lbl : Pauli2)
    (h : (l.map Pauli2.toMat).prod = c • Pauli2.toMat lbl) :
    (l.map Pauli2.toMat).prod.trace = if lbl = (Pauli1.I, Pauli1.I) then 4 * c else 0 := by
  rw [h, Matrix.trace_smul, Pauli2.trace_toMat]
  by_cases hl : lbl = (Pauli1.I, Pauli1.I)
  · simp [hl]; ring
  · simp [hl]

/-- **Non-vanishing criterion for a product of two-qubit Paulis**: the trace vanishes exactly
when the product is not a multiple of the identity. -/
theorem trace_prod_toMat_ne_zero_iff (l : List Pauli2) (c : ℂ) (lbl : Pauli2)
    (hc : c ≠ 0) (h : (l.map Pauli2.toMat).prod = c • Pauli2.toMat lbl) :
    (l.map Pauli2.toMat).prod.trace ≠ 0 ↔ lbl = (Pauli1.I, Pauli1.I) := by
  rw [trace_prod_toMat l c lbl h]
  by_cases hl : lbl = (Pauli1.I, Pauli1.I)
  · simp [hl, hc]
  · simp [hl]

end Qatlib.Papers.SpoofedXEB24.MainResults
