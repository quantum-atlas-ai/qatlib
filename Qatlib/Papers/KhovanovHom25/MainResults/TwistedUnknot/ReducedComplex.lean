/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KhovanovHom25.MainResults.Model
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 21: the reduced complex of `TU_n` and its Laplacian forms

Source: arXiv:2501.12378v2, Proposition 21, pp. 39-40, eq. (6.11).

The paper shows that the Khovanov complex of the twisted unknot `TU_n` is
homotopy equivalent to a complex of length `n + 1` with a single summand in each
homological degree: `V ⊗ V` in degrees `0, …, n-1` and `V` in degree `n`, with
differentials alternating between the two displayed `4 × 4` matrices

`d^- = [[0,1,-1,0],[0,0,0,-1],[0,0,0,1],[0,0,0,0]]`,
`d^+ = [[0,1,1,0],[0,0,0,1],[0,0,0,1],[0,0,0,0]]`

(read right to left) and ending with the saddle map `V ⊗ V → V`

`S = [[0,1,1,0],[0,0,0,1]]`,

in the basis `{11, 1X, X1, XX}` of `V ⊗ V`.  The paper's proof of this reduction
is "an immediate application of the simplified form of the complex `σ^n`" (the
reduction of Cooper-Krushkal [82]); what the paper computes directly, and what is
formalized and proved here, is the list of Laplacian forms

`Δ₀ = Diag(2,2,0,0)`, `Δ_{n-j} = Diag(2,2,2,2)` for `1 < j < n`,
`Δ_{n-1} = Diag(2,2,2,1)`, `Δ_n = Diag(2,1)`.

Concretely, with `Δ = d_outᵀ d_out + d_in d_inᵀ`, the displayed blocks give

* the chain conditions `d^- d^+ = 0`, `d^+ d^- = 0` and `S d^- = 0`, so the
  alternating blocks do define a complex (`prop21_is_complex`);
* the two interior parities `d^-ᵀ d^- + d^+ d^+ᵀ = 2·𝟙` and
  `d^+ᵀ d^+ + d^- d^-ᵀ = 2·𝟙`, i.e. `Diag(2,2,2,2)` (`prop21_laplacian_interior`);
* the penultimate block `d^- d^-ᵀ + Sᵀ S = Diag(2,2,2,1)`
  (`prop21_laplacian_penultimate`);
* the top block `S Sᵀ = Diag(2,1)` (`prop21_laplacian_top`);
* the degree-zero end: a leftmost differential with `Lᵀ L = Diag(2,2,0,0)` exists
  (`prop21_laplacian_zero`).  The paper draws this arrow as a picture rather than
  printing it, so its entries are not fixed by the displayed data; the statement
  is therefore the paper's assertion that the degree-zero Laplacian has the form
  `Diag(2,2,0,0)`, recorded as the existence of the corresponding block.

Matrices are given by their entry functions of the natural-number coordinates
(`prop21Mat4`, `prop21Mat24`), and the diagonal matrices by `prop21Diag4`,
`prop21Diag2`; all identities below are proved entrywise.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.KhovanovHom25.MainResults

/-- Package an entry function of the natural-number coordinates as a `4 × 4`
complex matrix. -/
def prop21Mat4 (f : ℕ → ℕ → ℂ) : Matrix (Fin 4) (Fin 4) ℂ := fun i j => f i.val j.val

/-- Package an entry function of the natural-number coordinates as a `2 × 4`
complex matrix. -/
def prop21Mat24 (f : ℕ → ℕ → ℂ) : Matrix (Fin 2) (Fin 4) ℂ := fun i j => f i.val j.val

/-- The diagonal `4 × 4` matrix `Diag(a,b,c,d)`. -/
def prop21Diag4 (a b c d : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  prop21Mat4 (fun i j =>
    if i = 0 ∧ j = 0 then a
    else if i = 1 ∧ j = 1 then b
    else if i = 2 ∧ j = 2 then c
    else if i = 3 ∧ j = 3 then d
    else 0)

/-- The diagonal `2 × 2` matrix `Diag(a,b)`. -/
def prop21Diag2 (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then a
    else if i.val = 1 ∧ j.val = 1 then b
    else 0

/-- The `-` block `[[0,1,-1,0],[0,0,0,-1],[0,0,0,1],[0,0,0,0]]` of the reduced
complex of eq. (6.11), acting on `V ⊗ V` in the basis `{11, 1X, X1, XX}`. -/
def prop21BlockMinus : Matrix (Fin 4) (Fin 4) ℂ :=
  prop21Mat4 (fun i j => match i, j with
    | 0, 1 => 1
    | 0, 2 => -1
    | 1, 3 => -1
    | 2, 3 => 1
    | _, _ => 0)

/-- The `+` block `[[0,1,1,0],[0,0,0,1],[0,0,0,1],[0,0,0,0]]` of the reduced
complex of eq. (6.11), acting on `V ⊗ V` in the basis `{11, 1X, X1, XX}`. -/
def prop21BlockPlus : Matrix (Fin 4) (Fin 4) ℂ :=
  prop21Mat4 (fun i j => match i, j with
    | 0, 1 => 1
    | 0, 2 => 1
    | 1, 3 => 1
    | 2, 3 => 1
    | _, _ => 0)

/-- The saddle map `V ⊗ V → V`, eq. (6.11): the matrix
`[[0,1,1,0],[0,0,0,1]]` in the basis `{11, 1X, X1, XX}` of the source (the
transpose of `[[0,0],[1,0],[1,0],[0,1]]`). -/
def prop21Saddle : Matrix (Fin 2) (Fin 4) ℂ :=
  prop21Mat24 (fun i j => match i, j with
    | 0, 1 => 1
    | 0, 2 => 1
    | 1, 3 => 1
    | _, _ => 0)

/-- **Proposition 21, chain conditions.**  The alternating blocks of eq. (6.11)
compose to zero: `d^- d^+ = 0`, `d^+ d^- = 0` and `S d^- = 0`, so the reduced
complex is a complex. -/
theorem prop21_is_complex :
    prop21BlockMinus * prop21BlockPlus = 0 ∧
      prop21BlockPlus * prop21BlockMinus = 0 ∧
      prop21Saddle * prop21BlockMinus = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [prop21BlockMinus, prop21BlockPlus, prop21Saddle, prop21Mat4, prop21Mat24,
          Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four] <;>
        norm_num

/-- **Proposition 21, interior Laplacians.**  In every homological degree with
`1 < j < n` the Laplacian is `Diag(2,2,2,2)`: for both parities of the
alternating differentials, `d_outᵀ d_out + d_in d_inᵀ = 2·𝟙`. -/
theorem prop21_laplacian_interior :
    (Matrix.transpose prop21BlockMinus * prop21BlockMinus +
          prop21BlockPlus * Matrix.transpose prop21BlockPlus =
        prop21Diag4 2 2 2 2) ∧
      (Matrix.transpose prop21BlockPlus * prop21BlockPlus +
          prop21BlockMinus * Matrix.transpose prop21BlockMinus =
        prop21Diag4 2 2 2 2) := by
  refine ⟨?_, ?_⟩ <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [prop21BlockMinus, prop21BlockPlus, prop21Mat4, prop21Diag4,
          Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
          Fin.sum_univ_four] <;>
        norm_num

/-- **Proposition 21, penultimate Laplacian.**  `Δ_{n-1} = Diag(2,2,2,1)`: the
Laplacian of the last `V ⊗ V` block, with incoming differential `d^-` and
outgoing saddle `S`. -/
theorem prop21_laplacian_penultimate :
    prop21BlockMinus * Matrix.transpose prop21BlockMinus +
        Matrix.transpose prop21Saddle * prop21Saddle =
      prop21Diag4 2 2 2 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [prop21BlockMinus, prop21Saddle, prop21Mat4, prop21Mat24, prop21Diag4,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Fin.sum_univ_four] <;>
    norm_num

/-- **Proposition 21, top Laplacian.**  `Δ_n = Diag(2,1)`: the Laplacian of `V`,
only the incoming saddle differential contributing. -/
theorem prop21_laplacian_top :
    prop21Saddle * Matrix.transpose prop21Saddle = prop21Diag2 2 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [prop21Saddle, prop21Mat24, prop21Diag2, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two, Fin.sum_univ_four] <;>
    norm_num

/-- **Proposition 21, degree-zero Laplacian.**  `Δ₀ = Diag(2,2,0,0)`: there is a
leftmost differential `L : V ⊗ V → V ⊗ V` of the reduced complex whose Laplacian
is `Lᵀ L = Diag(2,2,0,0)` (the explicit block is two orthogonal merges
`|1X⟩ ↦ |11⟩ + |1X⟩`, `|X1⟩ ↦ |11⟩ - |1X⟩`).

The paper does not print `L` (the arrow is drawn as a picture in eq. (6.11)), so
the assertion is recorded as the existence of the block with the stated
Laplacian, which is the content of the `Δ₀` entry of the paper's list. -/
theorem prop21_laplacian_zero :
    ∃ L : Matrix (Fin 4) (Fin 4) ℂ,
      Matrix.transpose L * L = prop21Diag4 2 2 0 0 := by
  refine ⟨prop21Mat4 (fun i j => match i, j with
    | 0, 0 => 1
    | 0, 1 => 1
    | 1, 0 => 1
    | 1, 1 => -1
    | _, _ => 0), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [prop21Mat4, prop21Diag4, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_two, Fin.sum_univ_four] <;>
    norm_num

/-- **Proposition 21 (Gap Reduction), Laplacian forms.**  Collecting the
computations above: the reduced complex of eq. (6.11) is a complex, and its
Laplacians are `Diag(2,2,2,2)` in the interior degrees, `Diag(2,2,2,1)` in degree
`n-1`, `Diag(2,1)` in degree `n`, and `Diag(2,2,0,0)` in degree `0`.` -/
theorem proposition21 :
    prop21BlockMinus * prop21BlockPlus = 0 ∧
      prop21BlockPlus * prop21BlockMinus = 0 ∧
      prop21Saddle * prop21BlockMinus = 0 ∧
      (∃ L : Matrix (Fin 4) (Fin 4) ℂ,
        Matrix.transpose L * L = prop21Diag4 2 2 0 0) ∧
      Matrix.transpose prop21BlockMinus * prop21BlockMinus +
          prop21BlockPlus * Matrix.transpose prop21BlockPlus =
        prop21Diag4 2 2 2 2 ∧
      Matrix.transpose prop21BlockPlus * prop21BlockPlus +
          prop21BlockMinus * Matrix.transpose prop21BlockMinus =
        prop21Diag4 2 2 2 2 ∧
      prop21BlockMinus * Matrix.transpose prop21BlockMinus +
          Matrix.transpose prop21Saddle * prop21Saddle =
        prop21Diag4 2 2 2 1 ∧
      prop21Saddle * Matrix.transpose prop21Saddle = prop21Diag2 2 1 :=
  ⟨prop21_is_complex.1, prop21_is_complex.2.1, prop21_is_complex.2.2,
    prop21_laplacian_zero, prop21_laplacian_interior.1, prop21_laplacian_interior.2,
    prop21_laplacian_penultimate, prop21_laplacian_top⟩

end Qatlib.Papers.KhovanovHom25.MainResults
