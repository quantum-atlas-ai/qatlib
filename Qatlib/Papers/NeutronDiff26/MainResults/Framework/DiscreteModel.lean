/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option backward.isDefEq.respectTransparency false

/-!
# NeutronDiff26 — discrete model vocabulary

Fixed paper: Childs--Johnston--Kiedrowski--Vempati--Yu,
*Quantum Algorithms for Heterogeneous PDEs: The Neutron Diffusion Eigenvalue Problem*,
arXiv:2604.05098v2 (2 October 2026); local copy
`assets/2604.05098.pdf` / `2604.05098.txt`.  The qatlas markdown endpoint was
returning HTTP 503 during this build, so the PDF v2 text is the authoritative
source; the few claims whose printed numbering is absent from v2 are marked in
the individual statements.

This module fixes only the *objects* used by the paper-layer contracts:

* `massMatrix1` / `laplaceMatrix1` — the explicit 1D mass and stiffness matrices
  of Definition 5/6 computed in Equations (29) and (30);
* `massMatrix3` / `laplaceMatrix3` — their 3D Kronecker forms from Equations
  (32) and (34);
* `cubeMassMatrix` — the `8 × 8` cube mass matrix of Lemma 5, Equation (38);
* `rayleigh` / `RayleighBetween` — the Rayleigh quotient and the eigenvalue
  bracket statement (a symmetric matrix whose Rayleigh quotient lies in
  `[lo, hi]` has all eigenvalues in `[lo, hi]`);
* `Sandwiched` — the coefficient sandwich (e.g. Equations (35), (36), (42)) by
  which the paper transfers bounds from `P^(3)` or `M^(3)` to `L` or `A`;
* `ConditionNumberAtMost` — a spectral condition-number bound.

All mathematical content is in the sibling modules; this file only introduces
definitions and elementary facts about them.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NeutronDiff26.MainResults.Framework

open Matrix
open scoped BigOperators Kronecker

/-! ## One-dimensional mass and stiffness matrices -/

/-- The 1D nodal mass matrix `M^(1)` of Definition 5, in the explicit
tridiagonal form displayed in Equation (29) of the paper:
diagonal `4h/6`, off-diagonals `h/6`. -/
def massMatrix1 (n : ℕ) (h : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i = j then 4 * h / 6
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then h / 6
    else 0

/-- The 1D stiffness (Laplacian) matrix `P^(1)` of Definition 6, in the
explicit tridiagonal form displayed in Equation (30) of the paper:
diagonal `2/h`, off-diagonals `-1/h`. -/
def laplaceMatrix1 (n : ℕ) (h : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i = j then 2 / h
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 / h
    else 0

/-- The 3D index set `(i,j,k)` of the nodal basis. -/
abbrev Grid3 (n : ℕ) := (Fin n × Fin n) × Fin n

/-- The 3D mass matrix `M^(3) = M^(1) ⊗ M^(1) ⊗ M^(1)` of Equation (32). -/
def massMatrix3 (n : ℕ) (h : ℝ) : Matrix (Grid3 n) (Grid3 n) ℝ :=
  (massMatrix1 n h ⊗ₖ massMatrix1 n h) ⊗ₖ massMatrix1 n h

/-- The 3D stiffness matrix
`P^(3) = P^(1) ⊗ M^(1) ⊗ M^(1) + M^(1) ⊗ P^(1) ⊗ M^(1) + M^(1) ⊗ M^(1) ⊗ P^(1)`
of Equation (34). -/
def laplaceMatrix3 (n : ℕ) (h : ℝ) : Matrix (Grid3 n) (Grid3 n) ℝ :=
  (laplaceMatrix1 n h ⊗ₖ massMatrix1 n h ⊗ₖ massMatrix1 n h)
    + (massMatrix1 n h ⊗ₖ laplaceMatrix1 n h ⊗ₖ massMatrix1 n h)
    + (massMatrix1 n h ⊗ₖ massMatrix1 n h ⊗ₖ laplaceMatrix1 n h)

/-! ## The `8 × 8` cube mass matrix of Lemma 5 -/

/-- The index set of the eight trilinear basis functions on one cube. -/
abbrev Cube8 := (Fin 2 × Fin 2) × Fin 2

/-- The integer pattern of Equation (38): entry `(p,q)` is `2` raised to the
number of coordinates on which `p` and `q` agree.  Scaling by `h^3/216` gives
the cube mass matrix of Lemma 5. -/
def cubeMassPattern : Matrix Cube8 Cube8 ℝ :=
  Matrix.of fun p q =>
    (if p.1.1 = q.1.1 then (2 : ℝ) else 1) *
      (if p.1.2 = q.1.2 then (2 : ℝ) else 1) *
      (if p.2 = q.2 then (2 : ℝ) else 1)

/-- The `8 × 8` cube mass matrix `M^t = (h^3/216) • cubeMassPattern` of
Lemma 5, Equation (38). -/
def cubeMassMatrix (h : ℝ) : Matrix Cube8 Cube8 ℝ :=
  (h ^ 3 / 216) • cubeMassPattern

/-! ## Rayleigh quotients and spectral brackets -/

/-- The Rayleigh quotient `xᵀ A x` of a real matrix. -/
def rayleigh {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * A i j * x j

/-- The squared Euclidean norm of a coefficient vector. -/
def sumSq {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := ∑ i, (x i) ^ 2

/-- The squared Euclidean norm of a coefficient vector is nonnegative. -/
theorem sumSq_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ sumSq x := by
  unfold sumSq
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)

/-- `RayleighBetween A lo hi` says: every Rayleigh quotient of `A` lies between
`lo` and `hi` (scaled by `‖x‖²`).  For symmetric `A` this is exactly the
eigenvalue bracket `lo ≤ λ_min` and `λ_max ≤ hi`. -/
def RayleighBetween {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (lo hi : ℝ) : Prop :=
  ∀ x : ι → ℝ, lo * sumSq x ≤ rayleigh A x ∧ rayleigh A x ≤ hi * sumSq x

/-- `Sandwiched A B lo hi` records that the quadratic form of `A` is squeezed
between `lo` and `hi` times that of `B`.  This is the mesh-transfer step of
Equations (35), (36) and (42): the coefficients `D` and `Σ_a` are bounded
between `lo` and `hi` pointwise, so the assembled stiffness/absorption matrix
is squeezed by the corresponding constant multiple of `P^(3)` or `M^(3)`. -/
def Sandwiched {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) (lo hi : ℝ) : Prop :=
  ∀ x : ι → ℝ, lo * rayleigh B x ≤ rayleigh A x ∧ rayleigh A x ≤ hi * rayleigh B x

/-- A spectral condition-number bound: all Rayleigh quotients of `A` lie in
`[lo, κ * lo]` for some `lo > 0`. -/
def ConditionNumberAtMost {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (κ : ℝ) : Prop :=
  ∃ lo : ℝ, 0 < lo ∧ RayleighBetween A lo (κ * lo)

/-- The submatrix of `C` on a finite index set `s`. -/
def submatrixOn {I : Type*} [Fintype I] (C : Matrix I I ℝ) (s : Set I)
    [Fintype s] : Matrix s s ℝ :=
  C.submatrix (fun i => (i : I)) (fun i => (i : I))

/-! ## Big-O vocabulary -/

/-- `EventuallyLe f g` is the paper's `f = O(g)` restricted to the mesh
parameter `h → 0`: there is a positive constant `C` with `f h ≤ C * g h` for
all sufficiently small positive `h`. -/
def EventuallyLe (f g : ℝ → ℝ) : Prop :=
  ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ → f h ≤ C * g h

end Qatlib.Papers.NeutronDiff26.MainResults.Framework
