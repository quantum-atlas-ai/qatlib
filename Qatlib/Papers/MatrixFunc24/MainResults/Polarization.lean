/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MatrixFunc24.MainResults.SourceModel
public import Mathlib.LinearAlgebra.Matrix.Hermitian

@[expose] public section


set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open Matrix
open Qatlib.Papers.MatrixFunc24.MainResults.SourceModel

namespace Qatlib.Papers.MatrixFunc24.MainResults.Walk

/-- The computational basis vector `|x⟩` on `N`. -/
def ket {N : Type} [DecidableEq N] (x : N) : N → ℂ :=
  fun i => if i = x then 1 else 0

/-- The Hermitian (sesquilinear) form `⟨ψ|A|ψ⟩ = Σ_{i,j} conj(ψ_i) A_{ij} ψ_j`. -/
def quadForm {N : Type} [Fintype N] (A : MatrixN N) (ψ : N → ℂ) : ℂ :=
  ∑ i, ∑ j, star (ψ i) * A i j * ψ j

/-- Polarization recovers each matrix entry from four quadratic forms. -/
theorem lemma49_offdiagonal_polarization
    {N : Type} [Fintype N] [DecidableEq N]
    (A : MatrixN N) (_hA : A.IsHermitian) (k j : N) :
    quadForm A (fun i => ket k i + ket j i) -
        quadForm A (fun i => ket k i - ket j i) -
        Complex.I * (quadForm A (fun i => ket k i + Complex.I * ket j i) -
          quadForm A (fun i => ket k i - Complex.I * ket j i)) =
      4 * A k j := by
  have conj_if (p : Prop) [Decidable p] (a b : ℂ) :
      (starRingEnd ℂ) (if p then a else b) =
        if p then (starRingEnd ℂ) a else (starRingEnd ℂ) b := by
    split_ifs <;> rfl
  simp [quadForm, ket, star_add, star_sub, conj_if, add_mul, sub_mul,
    mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ite_mul, mul_ite, mul_assoc]
  ring_nf
  simp
  ring


end Qatlib.Papers.MatrixFunc24.MainResults.Walk
