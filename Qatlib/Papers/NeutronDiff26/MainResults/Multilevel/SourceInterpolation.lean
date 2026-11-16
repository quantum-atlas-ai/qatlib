/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NeutronDiff26.MainResults.Framework.DiscreteModel

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# NeutronDiff26 — multilevel interpolation and the BPX preconditioner

Fixed paper: arXiv:2604.05098v2 (2 October 2026).

The 1D interpolation operator `I^1_{l→l+1}` of Definition 9 is the piecewise
linear interpolation matrix from a coarse uniform grid of `n+1` points to the
fine grid of `2n+1` points (Equation (117)); `linearInterp1` below is that
matrix.  `tensorEntry` / `tensorPowMatrix` formalise the `d`-fold tensor product
of Lemma 12 (Equation (124)).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NeutronDiff26.MainResults.Multilevel

open Matrix
open scoped BigOperators
open Qatlib.Papers.NeutronDiff26.MainResults.Framework

/-- A spectral-norm bound `‖A‖ ≤ c`, written through the Rayleigh quotient of
`Aᵀ A`: `xᵀ Aᵀ A x ≤ c² ‖x‖²` for every vector `x`.  For symmetric `A` this is
equivalent to the eigenvalue bound `|λ| ≤ c`. -/
def SpectralNormAtMost {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι ℝ) (c : ℝ) : Prop :=
  ∀ x : ι → ℝ, rayleigh (Aᵀ * A) x ≤ c ^ 2 * sumSq x

/-- The 1D piecewise linear interpolation matrix `I^1_{l→l+1}` of Definition 9
and Equation (117): the fine grid has `2n+1` points and the coarse grid `n+1`
points; each fine point is either a coarse point (weight `1`) or the midpoint
of two coarse points (weight `1/2` each). -/
def linearInterp1 (n : ℕ) : Matrix (Fin (2 * n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    if i.val = 2 * j.val then 1
    else if i.val = 2 * j.val + 1 then 1 / 2
    else if i.val + 1 = 2 * j.val then 1 / 2
    else 0

/-! ## The tensor-product identity of Lemma 12 -/

/-- The entry of the `d`-fold tensor product at multi-indices `i`, `j`:
recursively defined by peeling off the last coordinate. -/
def tensorEntry {m : ℕ} (I : Matrix (Fin m) (Fin m) ℝ) :
    (d : ℕ) → (Fin d → Fin m) → (Fin d → Fin m) → ℝ
  | 0, _, _ => 1
  | d + 1, i, j =>
      tensorEntry I d (fun k => i k.castSucc) (fun k => j k.castSucc) *
        I (i (Fin.last d)) (j (Fin.last d))

/-- The `d`-fold tensor product matrix `I^{⊗d}` of Lemma 12, indexed by
multi-indices `Fin d → Fin m`. -/
def tensorPowMatrix {m : ℕ} (I : Matrix (Fin m) (Fin m) ℝ) (d : ℕ) :
    Matrix (Fin d → Fin m) (Fin d → Fin m) ℝ :=
  Matrix.of fun i j => tensorEntry I d i j

/-- The entries of the `d`-fold tensor product factorise over coordinates. -/
theorem tensorEntry_eq_prod {m : ℕ} (I : Matrix (Fin m) (Fin m) ℝ) (d : ℕ)
    (i j : Fin d → Fin m) :
    tensorEntry I d i j = ∏ k : Fin d, I (i k) (j k) := by
  induction d with
  | zero => simp [tensorEntry]
  | succ d ih =>
      simp only [tensorEntry]
      rw [ih, Fin.prod_univ_castSucc]

/-- Paper Lemma 12, p. 25, Equation (124).

For any dimension `d`, the interpolation operator in `d` dimensions is the
`d`-fold tensor product of the 1D interpolation operators:
`I^d_{l→l'} = ⨂_{i=1}^d I^1_{l→l'}`, i.e. every matrix entry factorises as
`∏_k I (i k) (j k)`.

This is the entry-level form of the identity, proved by induction on `d`
using `Fin.prod_univ_castSucc`. -/
theorem interp_tensor_identity {m : ℕ} (I : Matrix (Fin m) (Fin m) ℝ) (d : ℕ)
    (i j : Fin d → Fin m) :
    tensorPowMatrix I d i j = ∏ k : Fin d, I (i k) (j k) := by
  simp only [tensorPowMatrix, Matrix.of_apply]
  exact tensorEntry_eq_prod I d i j

end Qatlib.Papers.NeutronDiff26.MainResults.Multilevel
