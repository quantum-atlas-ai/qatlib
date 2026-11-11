/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Method of lines for parabolic PDEs — shared model of arXiv:2606.03407v1

Fixed version: **arXiv:2606.03407v1** (submitted 2026-06-02).
Throughout this block `[u(x,T)]_x` denotes the vector obtained by restricting a
function to the tensor grid, and the *mean l2 norm* is (PDF p.9, §2.1)

`‖u‖⋆ := (1/N) ‖u‖₂`.

The file fixes the algebraic objects that the paper reuses across its results:
the midpoint grid, the mean l2 norm, the diagonal similarity `P = diag(1,θ,…)`
with `θ = √((1+α)/(1−α))`, the interior / Neumann-boundary / cyclic tridiagonal
matrices of Appendix C, and the composite Gauss–Legendre coefficients of §4.2.

Nothing here assumes a PDE result; the analytic estimates live in the sibling
files and reference these definitions.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.MethodOfLines26.ParabolicBase.Source

open Matrix
open scoped Classical BigOperators

/-! ## The mean l2 norm of a grid vector -/

/-- The paper's mean l2 norm `‖u‖⋆ = (1/N)‖u‖₂` on `N` grid nodes
(arXiv:2606.03407v1, §2.1, PDF p.9). -/
noncomputable def meanL2Norm {N : ℕ} (v : Fin N → ℝ) : ℝ :=
  (1 / (N : ℝ)) * Real.sqrt (∑ i, (v i) ^ 2)

/-- The mean l2 norm is nonnegative. -/
theorem meanL2Norm_nonneg {N : ℕ} (v : Fin N → ℝ) : 0 ≤ meanL2Norm v := by
  unfold meanL2Norm
  have h1 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ Real.sqrt (∑ i, (v i) ^ 2) := Real.sqrt_nonneg _
  exact mul_nonneg h1 h2

/-- The mean l2 norm vanishes exactly on the zero vector. -/
theorem meanL2Norm_eq_zero_iff {N : ℕ} (v : Fin N → ℝ) :
    meanL2Norm v = 0 ↔ v = 0 := by
  unfold meanL2Norm
  rcases eq_or_ne N 0 with hN | hN
  · subst hN
    constructor
    · intro _; funext i; exact i.elim0
    · intro _; simp
  · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
    rw [mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact absurd h (by positivity)
      · have hsum_nonneg : 0 ≤ ∑ i, (v i) ^ 2 :=
          Finset.sum_nonneg fun i _ => sq_nonneg (v i)
        have hs : (∑ i, (v i) ^ 2) = 0 := (Real.sqrt_eq_zero hsum_nonneg).mp h
        ext i
        have hterm : (v i) ^ 2 = 0 := by
          exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hs i
            (Finset.mem_univ i)
        exact sq_eq_zero_iff.mp hterm
    · intro hv
      subst hv
      simp

/-! ## The diagonal similarity of Appendix C -/

/-- `θ = √((1+α)/(1−α))` (arXiv:2606.03407v1, Lemma 19/20, PDF p.62). -/
noncomputable def theta (α : ℝ) : ℝ := Real.sqrt ((1 + α) / (1 - α))

/-- The diagonal similarity `P = diag(1, θ, …, θ^{N−1})`. -/
noncomputable def simP (N : ℕ) (α : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal fun i => theta α ^ i.val

/-- The inverse diagonal `P⁻¹ = diag(1, θ⁻¹, …, θ^{−(N−1)})`. -/
noncomputable def simPInv (N : ℕ) (α : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal fun i => (theta α ^ i.val)⁻¹

/-! ## The tridiagonal difference matrices of Appendix C -/

/-- Lemma 19's matrix `A` (interior Dirichlet/periodic difference matrix):
diagonal `2`, super-diagonal `−(1+α)`, sub-diagonal `−(1−α)`
(arXiv:2606.03407v1, Appendix C, PDF p.62). -/
def tridiagInterior (N : ℕ) (α : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    if i = j then 2
    else if j.val = i.val + 1 then -(1 + α)
    else if i.val = j.val + 1 then -(1 - α)
    else 0

/-- Lemma 20's matrix `A` (Neumann-boundary difference matrix): the first
diagonal entry is `1+α`, the last is `1−α`, interior diagonal `2`, super-diagonal
`−(1+α)`, sub-diagonal `−(1−α)` (arXiv:2606.03407v1, Appendix C, PDF p.62). -/
def tridiagBoundary (N : ℕ) (α : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    if i = j then
      (if i.val = 0 then 1 + α else if i.val = N - 1 then 1 - α else 2)
    else if j.val = i.val + 1 then -(1 + α)
    else if i.val = j.val + 1 then -(1 - α)
    else 0

/-- Lemma 21's matrix `Ã` (cyclic tridiagonal, both corners present),
arXiv:2606.03407v1, Appendix C, PDF p.63.  The super-diagonal is `−(1+α)`,
the sub-diagonal `−(1−α)`, the top-right corner `−(1−α)` and the bottom-left
corner `−(1+α)`, exactly as displayed in the paper. -/
def cyclicTridiag (N : ℕ) (α : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    if i = j then 2
    else if j.val = i.val + 1 ∨ (i.val = 0 ∧ j.val = N - 1) then
      (if i.val = 0 ∧ j.val = N - 1 then -(1 - α) else -(1 + α))
    else if i.val = j.val + 1 ∨ (j.val = 0 ∧ i.val = N - 1) then
      (if j.val = 0 ∧ i.val = N - 1 then -(1 + α) else -(1 - α))
    else 0

/-! ## The `D` factors of the `Ã = D Dᵀ` decompositions -/

/-- Lemma 19's `D : ℝ^{N×(N+1)}` with `D i i = √(1+α)` and
`D i (i+1) = −√(1−α)` (PDF p.62). -/
noncomputable def DInterior (N : ℕ) (α : ℝ) : Matrix (Fin N) (Fin (N + 1)) ℝ :=
  fun i k =>
    if k.val = i.val then Real.sqrt (1 + α)
    else if k.val = i.val + 1 then -Real.sqrt (1 - α)
    else 0

/-- Lemma 20's `D : ℝ^{N×N}`: `D i i = √(1+α)` for `i < N−1`, the last
diagonal entry is `0`, and `D i (i−1) = −√(1−α)`; this is the exact matrix
displayed in Lemma 20 (its last row is `… −√(1−α) 0`, PDF p.63). -/
noncomputable def DBoundary (N : ℕ) (α : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i k =>
    if k.val = i.val then (if i.val = N - 1 then 0 else Real.sqrt (1 + α))
    else if i.val = k.val + 1 then -Real.sqrt (1 - α)
    else 0

/-- The quadratic form `x ↦ xᵀ A x` of a real square matrix, used to state the
eigenvalue / positive-semidefiniteness conclusions of Lemma 19–21 without
invoking a spectral theorem. -/
noncomputable def quadForm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (v : Fin N → ℝ) : ℝ :=
  ∑ i, v i * (A *ᵥ v) i

/-! ## Composite Gauss–Legendre coefficients -/

/-- The composite Gauss–Legendre weights at a subinterval: the product of a
positive node weight and the subinterval length.  Lemma 7 records that these
coefficients are nonnegative and sum to the quadrature value of `‖b‖₂`
(arXiv:2606.03407v1, eq. (36), PDF p.23). -/
noncomputable def compositeGaussCoeff (M : ℕ) (w : Fin M → ℝ) (h : ℝ) :
    Fin M → ℝ :=
  fun j => w j * h

/-- Nonnegativity of the composite Gauss–Legendre coefficients. -/
theorem compositeGaussCoeff_nonneg {M : ℕ} (w : Fin M → ℝ) (h : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hh : 0 ≤ h) :
    ∀ j, 0 ≤ compositeGaussCoeff M w h j := by
  intro j
  exact mul_nonneg (hw j) hh

end Qatlib.Papers.MethodOfLines26.ParabolicBase.Source
