/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.Ring
import Qatlib.Foundations.PureStateMath.MixedState

set_option backward.isDefEq.respectTransparency false

/-!
# Cutting a local operator out of a tensor-product state (Lemma 4)

Source: Buhrman--Helsen--Weggemans, *Quantum PCPs: on Adaptivity, Multiple
Provers and Reductions to Local Hamiltonians*, arXiv:2403.04841v3 (Quantum 9,
1791 (2025)), Lemma 4, p. 16 (file lines 858--873, proof on pp. 16--17).

Statement: if `A` acts on a variable `q`-qubit register tensored with a fixed
`(n-q)`-qubit state `ρ_fixed`, then
`tr[A (ρ ⊗ ρ_fixed)] = tr[B ρ]` for an operator `B = B(ρ_fixed)` on the
`q`-qubit register.  If `ρ_fixed = |ψ⟩⟨ψ|` is pure, the entries of `B` are
`b_{α,α'} = ⟨α| ⟨ψ| A |α'⟩ |ψ⟩`.

This file formalises both facts on explicit matrices over `Fin d × Fin e`
(variable register `Fin d`, fixed register `Fin e`):

* `cutOperator A σ` is the paper's `B`, with entries
  `b_{α,α'} = Σ_{a,b} A_{(α,a),(α',b)} σ_{b,a}` (the general formula);
* `trace_cut` proves `tr[A (ρ ⊗ₖ σ)] = tr[cutOperator A σ * ρ]`;
* `cutOperator_rankOne` shows the pure-state entry formula.

The general entry formula and the trace identity are fully proved; the pure
entry identification is reduced to the rank-one specialisation.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumPCPs25.MainResults.Algebra

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open Qatlib.Foundations.PureStateMath

/-- The paper's operator `B = B(ρ_fixed)` of Lemma 4: the `d`-dimensional
operator with entries `b_{α,α'} = Σ_{a,b} A_{(α,a),(α',b)} σ_{b,a}`. -/
def cutOperator {d e : ℕ} (A : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
    (σ : Operator e) : Operator d :=
  fun i j => ∑ a : Fin e, ∑ b : Fin e, A (i, a) (j, b) * σ b a

/-- A rank-one pure-state matrix `|ψ⟩⟨ψ|`. -/
def rankOne {e : ℕ} (ψ : Fin e → ℂ) : Operator e := fun b a => ψ b * starRingEnd ℂ (ψ a)

/-- The pure-state entry formula of Lemma 4:
`b_{α,α'} = ⟨α| ⟨ψ| A |α'⟩ |ψ⟩ = Σ_{a,b} A_{(α,a),(α',b)} ψ_b \overline{ψ_a}`. -/
def pureCut {d e : ℕ} (A : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
    (ψ : Fin e → ℂ) : Operator d :=
  fun i j => ∑ a : Fin e, ∑ b : Fin e, A (i, a) (j, b) * ψ b * starRingEnd ℂ (ψ a)

/-- The pure-state specialisation of the cut operator (Lemma 4, second part):
when `σ = |ψ⟩⟨ψ|`, the matrix `B` has entries `⟨α|⟨ψ| A |α'⟩|ψ⟩`. -/
theorem cutOperator_rankOne {d e : ℕ} (A : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
    (ψ : Fin e → ℂ) : cutOperator A (rankOne ψ) = pureCut A ψ := by
  ext i j
  simp only [cutOperator, pureCut, rankOne, mul_assoc]

/-- **Lemma 4**, trace identity (arXiv:2403.04841v3, p. 16):
`tr[A (ρ ⊗ ρ_fixed)] = tr[B ρ]` with `B = cutOperator A ρ_fixed`. -/
theorem trace_cut {d e : ℕ} (A : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
    (ρ : Operator d) (σ : Operator e) :
    Matrix.trace (A * (ρ ⊗ₖ σ)) = Matrix.trace (cutOperator A σ * ρ) := by
  classical
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, cutOperator, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

end Qatlib.Papers.QuantumPCPs25.MainResults.Algebra
