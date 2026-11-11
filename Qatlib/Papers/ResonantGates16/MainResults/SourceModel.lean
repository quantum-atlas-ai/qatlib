/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-!
# ResonantGates16 — source model (signal calculus for resonant equiangular gates)

Paper: Guang Hao Low, Theodore J. Yoder, Isaac L. Chuang,
*The methodology of resonant equiangular composite quantum gates*,
arXiv:1603.03996 (fixed version: prefetched PDF, pages 2–6).

This module fixes the *object layer* of the paper so that Theorems 1–3 and
Lemmas 1–3 can be stated faithfully in the paper layer.

## What the paper defines

* Eq. (1) (p. 2): the primitive rotation `R̂_φ(θ) = exp(-i (θ/2) σ_φ)`, with
  `σ_φ = cos φ · σ_x + sin φ · σ_y`.
* Eq. (2) (p. 2): the length-`L` composite `U(θ) = R̂_{φ_L}(θ) … R̂_{φ_1}(θ)`.
* Eq. (4) (p. 2): the `(A,B,C,D)` representation of `U(θ)` with `x = cos(θ/2)`,
  `y = sin(θ/2)`:
  `U = A(x)·1 + iB(x)σ_z + iC(y)σ_x + iD(y)σ_y` (L odd),
  `U = A(x)·1 + iB(x)σ_z + i x C(y)σ_x + i x D(y)σ_y` (L even).
* Definition 1 (p. 2): `(A,B,C,D)` is *achievable* iff some `L` and phases
  `φ⃗ ∈ ℝ^L` produce `U(θ)` of the Eq. (4) form.

## Encoding notes

* `A,B,C,D` are taken as `Polynomial ℝ`. Theorem 1 condition (1) ("A,B,C,D are
  real") is therefore carried by the coefficient type, exactly as the paper's
  `a_k,b_k,c_k,d_k ∈ ℝ`.
* The parity conditions of Theorem 1(3) are stated through
  `OddPoly p := p.comp (-X) = -p` and `EvenPoly p := p.comp (-X) = p`.
* The normalization of Theorem 1(4) is stated *pointwise in `θ`* (with
  `x = cos(θ/2)`, `y = sin(θ/2)`, so `x² + y² = 1`), which is the identity the
  paper uses; this avoids any two-variable substitution machinery while being
  logically the same constraint on the polynomials restricted to the unit
  circle.
-/

namespace Qatlib.Papers.ResonantGates16.MainResults.SourceModel

open Matrix Polynomial
open scoped Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Pauli matrices -/

/-- Pauli `σ_x`. -/
def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli `σ_y`. -/
def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Pauli `σ_z`. -/
def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The identity `2×2` matrix, written out for `simp`-friendly rewriting. -/
def idMat : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

/-- The `(0,0)` entry of the identity matrix is `1`. -/
@[simp] theorem idMat_apply_zero_zero : idMat 0 0 = 1 := rfl
/-- The `(0,1)` entry of the identity matrix is `0`. -/
@[simp] theorem idMat_apply_zero_one : idMat 0 1 = 0 := rfl
/-- The `(1,0)` entry of the identity matrix is `0`. -/
@[simp] theorem idMat_apply_one_zero : idMat 1 0 = 0 := rfl
/-- The `(1,1)` entry of the identity matrix is `1`. -/
@[simp] theorem idMat_apply_one_one : idMat 1 1 = 1 := rfl

/-- The written-out identity matrix equals the matrix identity `1`. -/
theorem idMat_eq_one : idMat = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [idMat]

/-! ## Primitive rotation `R̂_φ(θ)` (Eq. 1)

`exp(-i α σ_φ) = cos α · 1 - i sin α · σ_φ` with `α = θ/2`, and
`σ_φ = cos φ · σ_x + sin φ · σ_y = [[0, cos φ - i sin φ], [cos φ + i sin φ, 0]]`.
Hence `R̂_φ(θ) = [[cos(θ/2), -i sin(θ/2)(cos φ - i sin φ)],
                  [-i sin(θ/2)(cos φ + i sin φ), cos(θ/2)]]`.
We write `e^{-iφ} = cos φ - i sin φ` directly, so no `Complex.exp` is needed. -/

/-- `R̂_φ(θ) = exp(-i (θ/2) σ_φ)`, Eq. (1), p. 2. -/
noncomputable def primitiveGate (φ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let c : ℂ := (Real.cos (θ / 2) : ℂ)
  let s : ℂ := (Real.sin (θ / 2) : ℂ)
  let cp : ℂ := (Real.cos φ : ℂ)
  let sp : ℂ := (Real.sin φ : ℂ)
  !![c, -Complex.I * s * (cp - Complex.I * sp);
     -Complex.I * s * (cp + Complex.I * sp), c]

/-- At `θ = 0` the primitive rotation is the identity (`R̂_φ(0) = 1`). -/
@[simp] theorem primitiveGate_zero (φ : ℝ) : primitiveGate φ 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primitiveGate, idMat]

/-! ## Composite response `U(θ)` (Eq. 2)

`qspProduct [φ_1,…,φ_L] θ = R̂_{φ_L}(θ) · … · R̂_{φ_1}(θ)`, i.e. the phase list
is in application order (`φ_1` applied first) and the matrix product is ordered
as in Eq. (2). -/

/-- Left-fold product realising `U(θ) = R̂_{φ_L}(θ) … R̂_{φ_1}(θ)` (Eq. 2). -/
noncomputable def qspProduct : List ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ
  | [], _ => 1
  | φ :: φs, θ => qspProduct φs θ * primitiveGate φ θ

/-- The length-`L` response of a phase vector `φ⃗ ∈ ℝ^L`, Eq. (2). -/
noncomputable def responseMatrix (L : ℕ) (φs : Fin L → ℝ) (θ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  qspProduct (List.ofFn φs) θ

/-- The empty phase list gives the identity response. -/
@[simp] theorem qspProduct_nil (θ : ℝ) : qspProduct [] θ = 1 := rfl

/-- Every response vanishes to the identity at `θ = 0` (`R̂_φ(0) = 1`). -/
theorem qspProduct_zero (φs : List ℝ) : qspProduct φs 0 = 1 := by
  induction φs with
  | nil => rfl
  | cons φ φs ih => simp [qspProduct, ih]

/-- `U(0) = 1` for every phase vector (used in the endpoint/necessity direction
of Theorem 1).

Source: Thm. 1 proof, p. 3 — "(2) is true as `U(0) = 1` in Eq. 2." -/
@[simp] theorem responseMatrix_zero (L : ℕ) (φs : Fin L → ℝ) :
    responseMatrix L φs 0 = 1 := by
  unfold responseMatrix
  exact qspProduct_zero _

/-! ## The `(A,B,C,D)` tuple representation (Eq. 4)

`A,B` are polynomials in `x = cos(θ/2)`; `C,D` are polynomials in `y = sin(θ/2)`.
For odd `L`, `U = A·1 + iB σ_z + iC σ_x + iD σ_y`; for even `L`,
`U = A·1 + iB σ_z + i x C σ_x + i x D σ_y` (Eq. 4, p. 2). -/

/-- `x = cos(θ/2)` as a complex number. -/
noncomputable def xOf (θ : ℝ) : ℂ := (Real.cos (θ / 2) : ℂ)

/-- `y = sin(θ/2)` as a complex number. -/
noncomputable def yOf (θ : ℝ) : ℂ := (Real.sin (θ / 2) : ℂ)

/-- The Eq. (4) matrix for a tuple `(A,B,C,D)`, as a function of `θ`. -/
noncomputable def tupleMatrix (L : ℕ) (A B C D : Polynomial ℝ) (θ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let av : ℂ := ((A.eval (Real.cos (θ / 2)) : ℝ) : ℂ)
  let bv : ℂ := ((B.eval (Real.cos (θ / 2)) : ℝ) : ℂ)
  let cv : ℂ := ((C.eval (Real.sin (θ / 2)) : ℝ) : ℂ)
  let dv : ℂ := ((D.eval (Real.sin (θ / 2)) : ℝ) : ℂ)
  if L % 2 = 1 then
    av • idMat + (Complex.I * bv) • sigmaZ
      + (Complex.I * cv) • sigmaX + (Complex.I * dv) • sigmaY
  else
    av • idMat + (Complex.I * bv) • sigmaZ
      + (Complex.I * xOf θ * cv) • sigmaX + (Complex.I * xOf θ * dv) • sigmaY

/-! ## Conditions of Theorem 1 -/

/-- A polynomial is odd: `p(-X) = -p`. -/
def OddPoly (p : Polynomial ℝ) : Prop := p.comp (-X) = -p

/-- A polynomial is even: `p(-X) = p`. -/
def EvenPoly (p : Polynomial ℝ) : Prop := p.comp (-X) = p

/-- Theorem 1 condition (3): parity of `A,B,C,D`.
For odd `L` all four are odd; for even `L`, `A,B` are even and `C,D` odd. -/
def ParityOK (L : ℕ) (A B C D : Polynomial ℝ) : Prop :=
  OddPoly C ∧ OddPoly D ∧
    (L % 2 = 1 → OddPoly A ∧ OddPoly B) ∧
    (L % 2 = 0 → EvenPoly A ∧ EvenPoly B)

/-- Theorem 1 condition (2): `A(1) = 1 ∨ B(1) = 0` (p. 3, as printed). -/
def EndpointOK (A B : Polynomial ℝ) : Prop :=
  A.eval 1 = 1 ∨ B.eval 1 = 0

/-- Theorem 1 condition (4): unitarity normalization, pointwise on the unit
circle (`x = cos(θ/2)`, `y = sin(θ/2)`), as in Eq. (7), p. 3. -/
def NormOK (L : ℕ) (A B C D : Polynomial ℝ) : Prop :=
  ∀ θ : ℝ,
    if L % 2 = 1 then
      (A.eval (Real.cos (θ / 2))) ^ 2 + (B.eval (Real.cos (θ / 2))) ^ 2
        + (C.eval (Real.sin (θ / 2))) ^ 2 + (D.eval (Real.sin (θ / 2))) ^ 2 = 1
    else
      (A.eval (Real.cos (θ / 2))) ^ 2 + (B.eval (Real.cos (θ / 2))) ^ 2
        + (Real.cos (θ / 2)) ^ 2 * (C.eval (Real.sin (θ / 2))) ^ 2
        + (Real.cos (θ / 2)) ^ 2 * (D.eval (Real.sin (θ / 2))) ^ 2 = 1

/-- `(A,B,C,D)` has degree at most `L` (each entry). -/
def DegreeOK (L : ℕ) (A B C D : Polynomial ℝ) : Prop :=
  A.natDegree ≤ L ∧ B.natDegree ≤ L ∧ C.natDegree ≤ L ∧ D.natDegree ≤ L

/-- **Definition 1 (p. 2): achievable tuples.** `(A,B,C,D)` is achievable at
length `L` iff some phases `φ⃗ ∈ ℝ^L` realise the Eq. (4) response exactly:
`U(θ) = A(x)·1 + …` for all `θ`. -/
def Achievable (L : ℕ) (A B C D : Polynomial ℝ) : Prop :=
  ∃ φs : Fin L → ℝ, ∀ θ : ℝ,
    responseMatrix L φs θ = tupleMatrix L A B C D θ

/-! ## Odd/even polynomial helpers (used by the parity condition) -/

/-- An odd polynomial evaluates to `0` at `0`. -/
theorem OddPoly.eval_zero {p : Polynomial ℝ} (hp : OddPoly p) : p.eval 0 = 0 := by
  have h := congrArg (fun q => q.eval (0 : ℝ)) hp
  simp only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X] at h
  have h2 : p.eval 0 = -p.eval 0 := by simpa using h
  linarith

/-- An even polynomial has equal values at `x` and `-x`. -/
theorem EvenPoly.eval_neg {p : Polynomial ℝ} (hp : EvenPoly p) (x : ℝ) :
    p.eval (-x) = p.eval x := by
  have h := congrArg (fun q => q.eval x) hp
  simpa [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X] using h

/-- An odd polynomial satisfies `p(-x) = -p(x)`. -/
theorem OddPoly.eval_neg {p : Polynomial ℝ} (hp : OddPoly p) (x : ℝ) :
    p.eval (-x) = -p.eval x := by
  have h := congrArg (fun q => q.eval x) hp
  simpa [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X] using h

end Qatlib.Papers.ResonantGates16.MainResults.SourceModel
