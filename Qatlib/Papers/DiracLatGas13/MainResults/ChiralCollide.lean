/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Chiral-symmetry-breaking collide operator (Appendix C)

Source: J. Yepez, *Quantum lattice gas model of Dirac particles in 1+1 dimensions*,
arXiv:1307.3595v1 (2013), Appendix C, pp. 29–30.

The collide operator acts on the four local occupancy states `{|0⟩, |↑⟩, |↓⟩, |↑↓⟩}`
(basis order `0, ↑, ↓, ↑↓`).  In terms of the number operators `n↑ = a↑†a↑`,
`n↓ = a↓†a↓` and the phase `B = e^{-i mcℓ√(γ²-1)/ℏ}` the paper writes

```
  Υ = 1 - n↑ - n↓ + n↑n↓ - i(mc²τ/ℏ)(B a↓†a↑ + h.c.)
        + √(1-(mc²τ/ℏ)²)(n↑ + n↓ - 2 n↑n↓)
        + exp[-i arccos √(1-(mc²τ/ℏ)²)] n↑n↓ .
```

This is the boxed 4×4 matrix (with `cosh z = √(1-(mc²τ/ℏ)²)`, `sinh z = -i mc²τ/ℏ`)

```
        ⎡ 1    0         0       0  ⎤
  Υ  =  ⎢ 0  cosh z   B* sinh z  0  ⎥
        ⎢ 0  B sinh z   cosh z   0  ⎥ ,
        ⎣ 0    0         0      e^z ⎦
```

whose generator `N` (with `N³ = N`, `N² = diag(0,1,1,1)`) is tri-idempotent, so
`Υ = 1 + sinh z · N + (cosh z - 1) · N²`.  We formalise the matrix, the operator
decomposition, the tri-idempotence, the closed form and the one-parameter
(semi)group law.  The equality of the top-left `(↑,↓)`-block phase with the
`exp[-i arccos ·]` entry of the last term is the trigonometric identification
`e^{-i arccos c} = c - i√(1-c²)`, recorded as the hypothesis `hec`.
-/

set_option autoImplicit false

-- The entrywise 4×4 matrix identities below are elementary but expand to large
-- polynomial goals; give elaboration a larger deterministic heartbeat budget.
set_option maxHeartbeats 2000000

open Matrix

namespace Qatlib.Papers.DiracLatGas13.MainResults

noncomputable section

/-! ## §1. Occupation-number matrices on the four-state local space -/

/-- Number operator for the up-spin occupancy, `n↑ = diag(0,1,0,1)`. -/
def nUp : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 1]

/-- Number operator for the down-spin occupancy, `n↓ = diag(0,0,1,1)`. -/
def nDown : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- The vacuum projector `1 - n↑ - n↓ + n↑n↓` appearing in `Υ`. -/
def vacProj : Matrix (Fin 4) (Fin 4) ℂ := 1 - nUp - nDown + nUp * nDown

/-- The hop term `a↓† a↑` (maps an up-spin occupancy to a down-spin one),
with matrix entry `B` at `(↓, ↑)`. -/
def hop (B : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, B, 0, 0;
     0, 0, 0, 0]

/-- The hermitian conjugate `a↑† a↓`, entry `B*` at `(↑, ↓)`. -/
def hopDag (B : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0;
     0, 0, star B, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- The tri-idempotent collide generator `N = a↓†a↑ + a↑†a↓ + n↑n↓`, i.e.
`N³ = N` while `N² = diag(0,1,1,1)` (Appendix C). -/
def N4 (B : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0;
     0, 0, star B, 0;
     0, B, 0, 0;
     0, 0, 0, 1]

/-- The boxed collide operator `Υ` of Appendix C, written with `b = cosh z` and
`s = sinh z` (so that the `(↑↓, ↑↓)` entry is `e^z = b + s`). -/
def upsilon4 (b s B : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, b, star B * s, 0;
     0, s * B, b, 0;
     0, 0, 0, b + s]

/-! ## §2. The operator decomposition of `Υ` -/

/-- The vacuum projector `1 - n↑ - n↓ + n↑n↓` is `diag(1,0,0,0)`. -/
theorem vacProj_eq :
    vacProj = !![1, 0, 0, 0;
                 0, 0, 0, 0;
                 0, 0, 0, 0;
                 0, 0, 0, 0] := by
  unfold vacProj
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nUp, nDown, Fin.sum_univ_four] <;>
    norm_num

/-- `n↑ + n↓ - 2 n↑n↓ = diag(0,1,1,0)`, the singly-occupied projector. -/
theorem numberSum_eq :
    nUp + nDown - (2 : ℂ) • (nUp * nDown)
      = !![0, 0, 0, 0;
           0, 1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nUp, nDown, Fin.sum_univ_four] <;>
    norm_num

/-- **Operator form of the collide operator** (Appendix C, first boxed display):
with `b = cosh z = √(1-(mc²τ/ℏ)²)`, `s = sinh z = -i mc²τ/ℏ` and the phase
`B = e^{-i mcℓ√(γ²-1)/ℏ}`, the matrix `Υ` is

`(1 - n↑ - n↓ + n↑n↓) + s·(B a↓†a↑ + h.c.) + b·(n↑ + n↓ - 2n↑n↓) + ec·n↑n↓`

where `ec = exp[-i arccos √(1-(mc²τ/ℏ)²)]`.  The hypothesis `hec : ec = b + s`
is the trigonometric identification `e^{-i arccos c} = c - i√(1-c²)`
(with `s = -i√(1-c²)`, `b = c`). -/
theorem upsilon4_operator_decomposition (b s B ec : ℂ) (hec : ec = b + s) :
    upsilon4 b s B
      = vacProj + s • (hop B + hopDag B) + b • (nUp + nDown - (2 : ℂ) • (nUp * nDown))
          + ec • (nUp * nDown) := by
  subst hec
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upsilon4, vacProj, hop, hopDag, nUp, nDown, Matrix.mul_apply,
      Fin.sum_univ_four] <;>
    try ring <;>
    simp

/-- **Tri-idempotence of the generator** (Appendix C): for a phase `B`
(`B B* = 1`), `N³ = N`. -/
theorem N4_tri_idempotent (B : ℂ) (hB : B * star B = 1) :
    N4 B * N4 B * N4 B = N4 B := by
  have hBne : B ≠ 0 := by
    intro h
    rw [h, zero_mul] at hB
    exact zero_ne_one hB
  have hstar : star B = B⁻¹ := eq_inv_of_mul_eq_one_right hB
  unfold N4
  rw [hstar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four] <;>
    try field_simp <;> ring

/-- `N² = diag(0,1,1,1)` for a phase `B` (Appendix C). -/
theorem N4_sq (B : ℂ) (hB : B * star B = 1) :
    N4 B * N4 B = !![0, 0, 0, 0;
                       0, 1, 0, 0;
                       0, 0, 1, 0;
                       0, 0, 0, 1] := by
  have hBne : B ≠ 0 := by
    intro h
    rw [h, zero_mul] at hB
    exact zero_ne_one hB
  have hstar : star B = B⁻¹ := eq_inv_of_mul_eq_one_right hB
  unfold N4
  rw [hstar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four] <;>
    try field_simp <;> ring

/-- **Closed form = tri-idempotent generator expansion** (Appendix C, pp. 29–30):
for a phase `B`, the collide operator equals `1 + sinh z · N + (cosh z - 1) · N²`,
the Euler/geometric expansion of `e^{zN}`. -/
theorem upsilon4_eq_generator_expansion (b s B : ℂ) (hB : B * star B = 1) :
    upsilon4 b s B
      = 1 + s • N4 B + (b - 1) • (N4 B) ^ 2 := by
  have hBne : B ≠ 0 := by
    intro h
    rw [h, zero_mul] at hB
    exact zero_ne_one hB
  have hstar : star B = B⁻¹ := eq_inv_of_mul_eq_one_right hB
  unfold upsilon4 N4
  rw [hstar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_four] <;>
    try field_simp <;> ring

/-- The closed form is a one-parameter (semi)group in `(cosh z, sinh z)`:
composing two `Υ`'s composes the parameters by the addition formulas, which is
the semigroup law of the exponential `e^{zN}`. -/
theorem upsilon4_mul (b s b' s' B : ℂ) (hB : B * star B = 1) :
    upsilon4 b s B * upsilon4 b' s' B
      = upsilon4 (b * b' + s * s') (b * s' + s * b') B := by
  have hBne : B ≠ 0 := by
    intro h
    rw [h, zero_mul] at hB
    exact zero_ne_one hB
  have hstar : star B = B⁻¹ := eq_inv_of_mul_eq_one_right hB
  unfold upsilon4
  rw [hstar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four] <;>
    try field_simp <;> ring

end

end Qatlib.Papers.DiracLatGas13.MainResults
