/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.BSSSdpSymmetry
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Permutation

@[expose] public section

/-!
# Source Proposition 16: output selectors transport by input permutations

[CarolanEtAl2025], Section 3.3, Definition 15 and Proposition 16, Equation (61)
([arXiv:2503.21090v2](https://arxiv.org/abs/2503.21090v2)).

For a symmetry `(π, ρ, σ)` of a query problem, the diagonal output selector
`Δ_y` of Definition 13 is transported to `Δ_{σ(y)}` by conjugation with the
input permutation matrix `P_π`:

`Δ_y = P_π⁻¹ Δ_{σ(y)} P_π`.

The module makes the paper's convention explicit: `P_π` sends the basis vector
`e_j` to `e_{π j}`; entrywise `(P_π⁻¹ A P_π)[x, x'] = A[π x, π x']`, which is
the diagonal computation of Equations (62)–(65). The definition
`sourcePermMatrix` uses the Mathlib permutation matrix of `π⁻¹`.

The Euclidean operator norm of `P_π` equals one on every
nonempty input type. The selector identity is one ingredient in the SDP
feasibility transport of Lemma 17.

## Main statements

* `sourcePermMatrix_inv`: the paper's `P_π⁻¹` is the permutation matrix of
  `π⁻¹`, i.e. the transpose of `P_π`.
* `sourcePermMatrix_conj_apply`: conjugation evaluates the matrix at the
  permuted pair of indices.
* `source_proposition16_delta_conjugation`: Proposition 16 in matrix form for
  the BSS selectors `bssDelta` of any `IsBssSymmetry`.
* `sourcePermMatrix_l2_opNorm_eq`: the Euclidean operator norm of `P_π` is
  one on a nonempty input type.
-/

set_option autoImplicit false

namespace Qatlib.Papers.OrderedSearch25.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.OrderedOracle.TiSdpBridge

variable {X Y : Type} [DecidableEq X] [DecidableEq Y]

/-- The permutation matrix `P_π` of arXiv:2503.21090v2 Equation (61): it sends
the basis vector `e_j` to `e_{π j}`. In Mathlib's convention this
is the matrix of `π⁻¹`, since that convention sends `e_j` to
`e_{π⁻¹ j}`. -/
def sourcePermMatrix (π : Equiv.Perm X) : Matrix X X ℂ := (π⁻¹).permMatrix ℂ

/-- Entrywise form of the paper's `P_π`: the entry `(i, j)` is one exactly
when `i = π j`. -/
@[simp]
theorem sourcePermMatrix_apply (π : Equiv.Perm X) (i j : X) :
    sourcePermMatrix π i j = if i = π j then (1 : ℂ) else 0 := by
  simp [sourcePermMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Equiv.Perm.inv_def, Equiv.eq_symm_apply, eq_comm]

/-- The transpose of the paper's permutation matrix represents the inverse permutation. -/
theorem sourcePermMatrix_transpose (π : Equiv.Perm X) :
    (sourcePermMatrix π)ᵀ = sourcePermMatrix π.symm := by
  change ((π⁻¹).permMatrix ℂ)ᵀ = ((π⁻¹)⁻¹).permMatrix ℂ
  exact Matrix.transpose_permMatrix (π⁻¹)

variable [Fintype X]

/-- `P_π P_π⁻¹ = 1`: the paper's permutation matrices form a group action. -/
theorem sourcePermMatrix_mul (π : Equiv.Perm X) :
    sourcePermMatrix π * sourcePermMatrix π.symm = 1 := by
  change (π⁻¹).permMatrix ℂ * π.permMatrix ℂ = 1
  rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

/-- The matrix inverse of the paper's `P_π` is the permutation matrix of
`π⁻¹`; in particular `P_π` is orthogonal and `P_π⁻¹ = P_πᵀ`. -/
theorem sourcePermMatrix_inv (π : Equiv.Perm X) :
    (sourcePermMatrix π)⁻¹ = sourcePermMatrix π.symm := by
  have hd : IsUnit (sourcePermMatrix π).det := by
    rw [sourcePermMatrix, Matrix.det_permutation]
    exact (Equiv.Perm.sign (π⁻¹)).isUnit.map (Int.castRingHom ℂ)
  have hp : sourcePermMatrix π * sourcePermMatrix π.symm = 1 :=
    sourcePermMatrix_mul π
  calc (sourcePermMatrix π)⁻¹
      = (sourcePermMatrix π)⁻¹ * (sourcePermMatrix π * sourcePermMatrix π.symm) := by
          rw [hp, Matrix.mul_one]
    _ = sourcePermMatrix π.symm :=
        Matrix.nonsing_inv_mul_cancel_left _ _ hd

/-- Conjugation by the paper's `P_π` evaluates a matrix at the permuted pair
of indices: `(P_π⁻¹ A P_π)[i, j] = A[π i, π j]`, the entrywise content of
Equation (65). -/
theorem sourcePermMatrix_conj_apply (π : Equiv.Perm X) (A : Matrix X X ℂ) (i j : X) :
    ((sourcePermMatrix π)⁻¹ * A * sourcePermMatrix π) i j = A (π i) (π j) := by
  rw [sourcePermMatrix_inv]
  change (π.permMatrix ℂ * A * (π⁻¹).permMatrix ℂ : Matrix X X ℂ) i j = _
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    Matrix.submatrix_apply, id, Equiv.Perm.inv_def, Equiv.symm_symm]

/-- **Source Proposition 16, Equation (61)**: for a BSS symmetry
`(π, ρ, σ)` of the query problem and every output label `y`, the diagonal
selector `Δ_y` is the conjugate of `Δ_{σ(y)}` by the input permutation
matrix `P_π`:

`Δ_y = P_π⁻¹ Δ_{σ(y)} P_π`.

Only the output condition `σ (f x) = f (π x)` of `IsBssSymmetry` is used;
the query-location component `ρ` enters through the symmetry hypothesis of
Definition 15. -/
theorem source_proposition16_delta_conjugation {m : ℕ} (bit : X → Fin m → Bool) (f : X → Y)
    (π : Equiv.Perm X) (ρ : Equiv.Perm (Fin m)) (σ : Equiv.Perm Y)
    (h : IsBssSymmetry bit f π ρ σ) (y : Y) :
    bssDelta f y = (sourcePermMatrix π)⁻¹ * bssDelta f (σ y) * sourcePermMatrix π := by
  apply Matrix.ext
  intro x x'
  rw [sourcePermMatrix_conj_apply]
  exact (bssDelta_transport bit f π ρ σ h y x x').symm

/-- The Euclidean operator norm of the paper's `P_π` equals one
whenever the input type is nonempty. -/
theorem sourcePermMatrix_l2_opNorm_eq [Nonempty X] (π : Equiv.Perm X) :
    ‖sourcePermMatrix π‖ = 1 := by
  simpa [sourcePermMatrix] using Matrix.permMatrix_l2_opNorm_eq (n := X) (𝕜 := ℂ) π⁻¹

end Qatlib.Papers.OrderedSearch25.MainResults
