/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatrixProd07.MainResults.Defs

/-!
# Parent Hamiltonian state spaces

The module defines zero-energy ground state predicates and matrix product manifolds with
arbitrary boundary matrices. `proposition3_factorization` expresses any matrix as a finite sum
of left and right multiples of a fixed nonzero matrix, providing an algebraic tool for these
constructions. These constructions are associated with [PerezGarciaEtAl2007].

## Main statements

* `UniqueGroundState`: kernel vectors are scalar multiples of the chosen state.
* `GManifoldTI`: the matrix product manifold for a repeated tensor.
* `proposition3_factorization`: two-sided spanning from any nonzero bond matrix.

## References

* [Perez-Garcia et al., 2007][PerezGarciaEtAl2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatrixProd07.MainResults.ParentHamiltonian

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Papers.MatrixProd07.MainResults
open Matrix
open scoped BigOperators ComplexConjugate

/-- The space of complex amplitude functions on configurations of `N` sites of local dimension
`d`. -/
abbrev Ket (N d : ℕ) := (Fin N → Fin d) → ℂ

/-- The complex inner product on amplitude functions, conjugate linear in the first argument. -/
def inner {N d : ℕ} (φ ψ : Ket N d) : ℂ := ∑ x, starRingEnd ℂ (φ x) * ψ x

/-- The zero-energy condition `H ψ = 0`. -/
def IsGroundState {N d : ℕ} (H : Ket N d →ₗ[ℂ] Ket N d) (ψ : Ket N d) : Prop := H ψ = 0

/-- The condition that `ψ` is annihilated by `H` and every vector annihilated by `H` is a scalar
multiple of `ψ`. -/
def UniqueGroundState {N d : ℕ} (H : Ket N d →ₗ[ℂ] Ket N d) (ψ : Ket N d) : Prop :=
  IsGroundState H ψ ∧ ∀ φ, IsGroundState H φ → ∃ c : ℂ, φ = c • ψ

/-- The condition that the kernel of `H` is exactly the complex linear span of `M`. -/
def HasKernelSpanning {N d : ℕ} (H : Ket N d →ₗ[ℂ] Ket N d) (M : Set (Ket N d)) : Prop :=
  ∀ φ, H φ = 0 ↔ φ ∈ Submodule.span ℂ M

/-- The ordered product of the site-dependent matrices selected by a configuration. -/
noncomputable def siteWord {N d D : ℕ} (B : (m : Fin N) → Fin d → BM D) (x : Fin N → Fin d) :
    BM D :=
  (List.ofFn (fun m : Fin N => B m (x m))).foldl (fun acc M => acc * M) 1

/-- The set of amplitude functions of the form `x ↦ trace (X * siteWord B x)` for an arbitrary
boundary matrix `X`. -/
def GManifoldOBC {M d D : ℕ} (B : (m : Fin M) → Fin d → BM D) : Set (Ket M d) :=
  {φ | ∃ X : BM D, φ = fun x => Matrix.trace (X * siteWord B x)}

/-- The matrix product manifold obtained by repeating the tensor family `A` at all sites. -/
def GManifoldTI {L d D : ℕ} (A : Fin d → BM D) : Set (Ket L d) :=
  GManifoldOBC (fun (_ : Fin L) => A)

/-- The periodic amplitude function given by the trace of the product of repeated tensors
selected by a configuration. -/
def blockState {N d D : ℕ} (A : Fin d → BM D) : Ket N d :=
  fun x => Matrix.trace (siteWord (fun (_ : Fin N) => A) x)

/-- The set of amplitudes obtained by choosing a block and an arbitrary boundary matrix for its
repeated tensor family. -/
def blockManifold {N d D b : ℕ} (Ablk : Fin b → Fin d → BM D) : Set (Ket N d) :=
  {φ | ∃ (j : Fin b) (X : BM D), φ = fun x => Matrix.trace (X * siteWord (fun (_ : Fin N) => Ablk j) x)}

/-- For any nonzero matrix `C`, every matrix `X` is a sum indexed by pairs of bond indices of
terms `R i * C * S i`. See [PerezGarciaEtAl2007]. -/
theorem proposition3_factorization {D : ℕ} (C X : BM D) (hC : C ≠ 0) :
    ∃ R S : (Fin D × Fin D) → BM D, X = ∑ i, R i * C * S i := by
  obtain ⟨a, b, hab⟩ : ∃ a b : Fin D, C a b ≠ 0 := by
    by_contra h
    push Not at h
    exact hC (by ext a b; exact h a b)
  have hterm : ∀ p q : Fin D,
      Matrix.single p q (X p q) =
        Matrix.single p a ((C a b)⁻¹ * X p q) * C * Matrix.single b q 1 := by
    intro p q
    rw [Matrix.single_mul_mul_single]
    congr 1
    field_simp
  refine ⟨fun i => Matrix.single i.1 a ((C a b)⁻¹ * X i.1 i.2),
          fun i => Matrix.single b i.2 1, ?_⟩
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun p _ =>
    Finset.sum_congr rfl fun q _ => by simpa using (hterm p q)

end Qatlib.Papers.MatrixProd07.MainResults.ParentHamiltonian
