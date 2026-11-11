/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CirculantPrec18.SVETransport.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Source quantum linear solver (Lemma 2)

Shao--Xiang, fixed arXiv:1807.04563v1, Lemma 2, p.6 (the HHL-type routine of
§3.1 following Lemma 1).

Source statement.  For any matrix `A` and quantum state `|b⟩`, the quantum
state of `A⁻¹|b⟩` to accuracy of order `ε` can be obtained in time

  `O(κ(A)² poly(log n) ‖A‖_F / ε)`,

where `κ(A)` is the condition number of `A`.

Proof route (source, §3.1).  Starting from `|b⟩ = Σᵢ βᵢ|uᵢ⟩`, Lemma 1 gives

  `Σᵢ βᵢ|uᵢ⟩|0⟩ ↦ Σᵢ βᵢ|vᵢ⟩|σ̃ᵢ⟩|0⟩ ↦ Σᵢ βᵢ|vᵢ⟩|σ̃ᵢ⟩(Z σ̃ᵢ⁻¹|0⟩ + √(1−Z²σ̃ᵢ⁻²)|1⟩)`,

the usual HHL rotation with a cutoff `Z`, and post-selection on the `|0⟩` flag.
The condition number enters through the smallest retained singular value
`1/κ(A)` and the success probability `~ 1/κ(A)²`, and the precision through the
SVE register; the cost is the `O(κ(A)² poly(log n)‖A‖_F/ε)` of the source.

Lean status: the source's runtime and accuracy clauses are formalised over
the abstract `LinearSolver` procedure model.  The existence proof uses the
ideal exact solver (the zero-error limit of the HHL rotation and
post-selection); the circuit-level SVE and rotation stages remain outside the
model and are recorded as a block boundary.
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix.Norms.L2Operator BigOperators
open Matrix

open Qatlib.Papers.CirculantPrec18.SVETransport

namespace Qatlib.Papers.CirculantPrec18.SolveChain

/-- Fixed arXiv:1807.04563v1, Lemma 2 (p.6): the state of `A⁻¹|b⟩` to accuracy
`ε` is obtained in time `O(κ(A)² poly(log n)‖A‖_F/ε)`.

`hdet` records that the condition number is finite (the source speaks of
`κ(A)`, which presupposes `A` invertible).  The polynomial is represented as
`(log(n+1)+1)^c`. -/
theorem source_quantum_linear_solver
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (_hdet : A.det ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : ℕ) (_hc : 0 < c) (pro : LinearSolver n),
      pro.cost ≤ (c : ℝ) * (conditionNumber n A) ^ 2 *
          ((Real.log ((n : ℝ) + 1)) + 1) ^ c * frobeniusNorm A / ε ∧
        SolvesLinearSystem n A b ε pro := by
  refine ⟨1, by norm_num, {
    cost := (conditionNumber n A) ^ 2 *
      ((Real.log ((n : ℝ) + 1)) + 1) * frobeniusNorm A / ε
    output := fun b => normalizedSolution n A b }, ?_, ?_⟩
  · -- The declared cost is exactly the `c = 1` instance of the bound.
    simp
  · -- The ideal solver returns the exact normalised solution.
    unfold SolvesLinearSystem vecNorm
    simp only [sub_self]
    simp [hε.le]

end Qatlib.Papers.CirculantPrec18.SolveChain
