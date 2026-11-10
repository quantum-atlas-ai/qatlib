/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatrixProd07.MainResults.Defs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatrixProd07.MainResults.ParentHamiltonian

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Papers.MatrixProd07.MainResults
open Matrix
open scoped BigOperators ComplexConjugate

abbrev Ket (N d : ℕ) := (Fin N → Fin d) → ℂ

def inner {N d : ℕ} (φ ψ : Ket N d) : ℂ := ∑ x, starRingEnd ℂ (φ x) * ψ x

def IsGroundState {N d : ℕ} (H : Ket N d →ₗ[ℂ] Ket N d) (ψ : Ket N d) : Prop := H ψ = 0

def UniqueGroundState {N d : ℕ} (H : Ket N d →ₗ[ℂ] Ket N d) (ψ : Ket N d) : Prop :=
  IsGroundState H ψ ∧ ∀ φ, IsGroundState H φ → ∃ c : ℂ, φ = c • ψ

def HasKernelSpanning {N d : ℕ} (H : Ket N d →ₗ[ℂ] Ket N d) (M : Set (Ket N d)) : Prop :=
  ∀ φ, H φ = 0 ↔ φ ∈ Submodule.span ℂ M

noncomputable def siteWord {N d D : ℕ} (B : (m : Fin N) → Fin d → BM D) (x : Fin N → Fin d) :
    BM D :=
  (List.ofFn (fun m : Fin N => B m (x m))).foldl (fun acc M => acc * M) 1

def GManifoldOBC {M d D : ℕ} (B : (m : Fin M) → Fin d → BM D) : Set (Ket M d) :=
  {φ | ∃ X : BM D, φ = fun x => Matrix.trace (X * siteWord B x)}

def GManifoldTI {L d D : ℕ} (A : Fin d → BM D) : Set (Ket L d) :=
  GManifoldOBC (fun (_ : Fin L) => A)

def blockState {N d D : ℕ} (A : Fin d → BM D) : Ket N d :=
  fun x => Matrix.trace (siteWord (fun (_ : Fin N) => A) x)

def blockManifold {N d D b : ℕ} (Ablk : Fin b → Fin d → BM D) : Set (Ket N d) :=
  {φ | ∃ (j : Fin b) (X : BM D), φ = fun x => Matrix.trace (X * siteWord (fun (_ : Fin N) => Ablk j) x)}

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
