/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.StateTesting26.MainResults.Model.StateModel

@[expose] public section

/-!
# The two-copy SWAP observable

Equation (1.9) of the paper reads `Tr(SWAP · ρ ⊗ ρ) = tr(ρ²)`. This identity is the observable
behind every purity read-out in the paper, in particular the `SWAP(t)` batches of Section 1.2.1
and of Appendix A.

The statement below is phrased for the model layer of the paper, whose two-copy operators live on
the tuple type `Fin 2 → Fin d` (`Qatlib.Papers.StateTesting26.MainResults.Model.swapTwo` and
`Qatlib.Papers.StateTesting26.MainResults.Model.tensorPowerMat`) rather than on the product type
`Fin d × Fin d` used by the two-register `SWAP` of the sibling paper `StateHSP24`. The two index
conventions are related by `finTwoArrowEquivProd`, and the proof of the trace identity is a direct
entrywise computation: the SWAP matrix carries a single nonzero entry per row. No positivity,
Hermiticity or normalisation of `ρ` is needed.

Paper: [arXiv:2604.07460v2](https://arxiv.org/abs/2604.07460v2), Eqs. (1.8)–(1.9) and (3.2).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.StateTesting26.MainResults

open Qatlib.Papers.StateTesting26.MainResults.Model

/-- Reading a two-entry tuple as a pair. This is the coordinate change between the model layer's
two-register Hilbert space `Fin 2 → Fin d` and the product register `Fin d × Fin d`. -/
def finTwoArrowEquivProd (d : ℕ) : (Fin 2 → Fin d) ≃ (Fin d × Fin d) where
  toFun i := (i 0, i 1)
  invFun p := fun a => if a = 0 then p.1 else p.2
  left_inv := by
    intro i
    funext a
    fin_cases a <;> simp
  right_inv := by
    intro p
    simp

/-- Reindexing a sum over two-entry tuples as a sum over pairs, along with the coordinate
equivalence `finTwoArrowEquivProd`. -/
theorem sum_finTwoArrow_eq_sum_prod {d : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Fin d × Fin d → M) :
    (∑ i : Fin 2 → Fin d, f (i 0, i 1)) = ∑ p : Fin d × Fin d, f p :=
  Fintype.sum_equiv (finTwoArrowEquivProd d) (fun i => f (i 0, i 1)) f (fun _ => rfl)

/-- The diagonal entries of `SWAP · ρ^{⊗2}`: at the row `i` the only nonzero SWAP entry selects
the reversed tuple `(i 1, i 0)`, so the diagonal entry is `ρ (i 1) (i 0) · ρ (i 0) (i 1)`. -/
theorem swapTwo_mul_tensorPowerMat_two_apply {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (i : Fin 2 → Fin d) :
    (swapTwo (d := d) * tensorPowerMat ρ 2) i i = ρ (i 1) (i 0) * ρ (i 0) (i 1) := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (fun a : Fin 2 => if a = 0 then i 1 else i 0)]
  · simp [swapTwo, tensorPowerMat]
  · intro k _ hk
    by_cases h : i 0 = k 1 ∧ i 1 = k 0
    · exfalso
      apply hk
      funext a
      fin_cases a <;> simp_all
    · simp [swapTwo, h]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Equation (1.9) for the two-copy model operator**: `Tr(SWAP · ρ^{⊗2}) = tr(ρ²)`, where
`ρ^{⊗2}` is the model layer's `tensorPowerMat ρ 2`. The statement holds for an arbitrary complex
matrix `ρ`. -/
theorem trace_swapTwo_tensorPowerMat_two {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (swapTwo (d := d) * tensorPowerMat ρ 2).trace = (ρ * ρ).trace := by
  classical
  have hstep : (swapTwo (d := d) * tensorPowerMat ρ 2).trace
      = ∑ i : Fin 2 → Fin d, ρ (i 1) (i 0) * ρ (i 0) (i 1) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    exact Finset.sum_congr rfl fun i _ => swapTwo_mul_tensorPowerMat_two_apply ρ i
  have hleft : (swapTwo (d := d) * tensorPowerMat ρ 2).trace
      = ∑ p : Fin d × Fin d, ρ p.2 p.1 * ρ p.1 p.2 := by
    rw [hstep]
    exact sum_finTwoArrow_eq_sum_prod (f := fun p : Fin d × Fin d => ρ p.2 p.1 * ρ p.1 p.2)
  have hright : (ρ * ρ).trace = ∑ p : Fin d × Fin d, ρ p.1 p.2 * ρ p.2 p.1 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    exact (Fintype.sum_prod_type
      (f := fun p : Fin d × Fin d => ρ p.1 p.2 * ρ p.2 p.1)).symm
  rw [hleft, hright]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

end Qatlib.Papers.StateTesting26.MainResults
