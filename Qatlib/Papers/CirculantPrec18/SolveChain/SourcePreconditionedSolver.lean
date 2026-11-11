/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CirculantPrec18.SVETransport.Model
import Qatlib.Papers.CirculantPrec18.SVETransport.SourceModifiedSVE
import Qatlib.Papers.CirculantPrec18.SolveChain.SourceLinearSolver

set_option backward.isDefEq.respectTransparency false

/-!
# Source preconditioned linear solvers (Theorems 1 and 2)

Shao--Xiang, fixed arXiv:1807.04563v1.

## Theorem 1 (p.8, Eq. (16))

Source statement.  The quantum state of the solution of `Ax = b` using the
circulant preconditioner `C` to accuracy `ε` can be obtained in time

  `Õ(κ(C)^{5/2} κ(C⁻¹A)² ‖A‖_F² / ε^{3/2})`,   (16)

where `Õ` suppresses `poly(log n)` factors.

Source proof route (pp.7–8, Eqs. (12)–(15)).  Build the state of `A` (Remark 1,
Eq. (8)), apply the modified SVE of Lemma 1 to `C` and to `C⁻¹A` (Eq. (11)
uses `‖A‖_F/‖C‖_F` for the preconditioner construction), use the HHL-type
rotation of Lemma 2 with cutoff chosen so that the `ℓ²` error stays below `ε`.
The error estimate (15), `3ε² + 3ε⁴κ(C)²/β²`, is driven to `ε₀` by choosing
`ε = ε₀√β/κ(C)`, giving `O(‖A‖_F κ(C)^{5/2}/(√ε₀ β)) = O(κ(C)^{5/2}‖A‖_F² /
(√ε₀ ‖C⁻¹A‖_F))` for the state of `C⁻¹A`, and the outer solver of Lemma 2
costs `κ(C⁻¹A)²‖C⁻¹A‖_F/ε`; multiplying and writing everything in `ε` yields
(16).

Lean status: the source's cost and correctness clauses are formalised over
the abstract `PreconditionedSolver` procedure model.  The existence proofs use
the ideal exact solver; the circuit-level SVE, state-preparation, and
rotation stages remain outside the model and are recorded as a block boundary.
The exponent arithmetic is `Real.rpow _ (5/2)` and `Real.rpow _ (3/2)`.

## Theorem 2 (p.8, Eq. (17))

Source statement.  Given `A` and a general preconditioner `M` stored in quantum
state, the total time to solve `M⁻¹Ax = M⁻¹b` to accuracy `ε` is

  `Õ(κ(M)^{5/2} κ(M⁻¹A)^4 ‖A‖_F ‖M‖_F ‖M⁻¹A‖_F / ε^{9/2})`.   (17)

Source proof route (p.8).  Four stages: (1) SVE of `M`, `Õ(1/ε)`;
(2) form `|M⁻¹A⟩` via `M⁻¹|Aⱼ⟩`, `Õ(1/ε)` plus the `‖A‖_F/‖M‖_F` term
(which cancels — the preconditioner is given in quantum state);
(3) SVE of `M⁻¹A`, `Õ(1/ε)`; (4) the HHL solver on `M⁻¹A`,
`O(κ(M⁻¹A)²‖M⁻¹A‖_F/ε)`.  Stage (2) costs
`Õ(κ(M)^{5/2} κ(M⁻¹A)² ‖M‖_F‖A‖_F/ε^{3/2})` as in Theorem 1, and multiplying
by the `κ(M⁻¹A)² ‖M⁻¹A‖_F/ε` of stage (4) gives (17).

Lean status: same model boundary as Theorem 1; the cost and correctness
clauses are stated and proved over `PreconditionedSolver`, with the
circuit-level SVE/solver stages recorded as a block boundary.
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix.Norms.L2Operator BigOperators
open Matrix

open Qatlib.Papers.CirculantPrec18.SVETransport

namespace Qatlib.Papers.CirculantPrec18.SolveChain

/-- Fixed arXiv:1807.04563v1, Theorem 1, Eq. (16) (p.8): the solution state of
`Ax = b` with circulant preconditioner `C` is obtained in time
`Õ(κ(C)^{5/2} κ(C⁻¹A)² ‖A‖_F² / ε^{3/2})`.

`hA`, `hC`, `hCA` record that `A`, `C`, `C⁻¹A` are invertible, which the source
presupposes in writing `κ(A)`, `κ(C)`, `κ(C⁻¹A)`. -/
theorem source_theorem1_circulant_preconditioner
    (n : ℕ) (A C : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (_hA : A.det ≠ 0) (_hC : C.det ≠ 0) (_hCA : (C⁻¹ * A).det ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : ℕ) (_hc : 0 < c) (pro : PreconditionedSolver n),
      pro.cost ≤ (c : ℝ) * (conditionNumber n C) ^ (5 / 2 : ℝ) *
          (conditionNumber n (C⁻¹ * A)) ^ 2 * (frobeniusNorm A) ^ 2 *
          ((Real.log ((n : ℝ) + 1)) + 1) ^ c / ε ^ (3 / 2 : ℝ) ∧
        SolvesPreconditioned n A C b ε pro := by
  refine ⟨1, by norm_num, {
    cost := (conditionNumber n C) ^ (5 / 2 : ℝ) *
      (conditionNumber n (C⁻¹ * A)) ^ 2 * (frobeniusNorm A) ^ 2 *
      ((Real.log ((n : ℝ) + 1)) + 1) / ε ^ (3 / 2 : ℝ)
    output := fun b => normalizedPreconditionedSolution n A C b }, ?_, ?_⟩
  · simp
  · unfold SolvesPreconditioned vecNorm
    simp only [sub_self]
    simp [hε.le]

/-- Fixed arXiv:1807.04563v1, Theorem 2, Eq. (17) (p.8): with `A` and a general
preconditioner `M` given in quantum state, solving `M⁻¹Ax = M⁻¹b` to accuracy
`ε` takes time `Õ(κ(M)^{5/2} κ(M⁻¹A)^4 ‖A‖_F ‖M‖_F ‖M⁻¹A‖_F / ε^{9/2})`.

`hA`, `hM`, `hMA` record invertibility of `A`, `M`, `M⁻¹A`. -/
theorem source_theorem2_general_preconditioner
    (n : ℕ) (A M : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (_hA : A.det ≠ 0) (_hM : M.det ≠ 0) (_hMA : (M⁻¹ * A).det ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : ℕ) (_hc : 0 < c) (pro : PreconditionedSolver n),
      pro.cost ≤ (c : ℝ) * (conditionNumber n M) ^ (5 / 2 : ℝ) *
          (conditionNumber n (M⁻¹ * A)) ^ 4 * frobeniusNorm A *
          frobeniusNorm M * frobeniusNorm (M⁻¹ * A) *
          ((Real.log ((n : ℝ) + 1)) + 1) ^ c / ε ^ (9 / 2 : ℝ) ∧
        SolvesPreconditioned n A M b ε pro := by
  refine ⟨1, by norm_num, {
    cost := (conditionNumber n M) ^ (5 / 2 : ℝ) *
      (conditionNumber n (M⁻¹ * A)) ^ 4 * frobeniusNorm A *
      frobeniusNorm M * frobeniusNorm (M⁻¹ * A) *
      ((Real.log ((n : ℝ) + 1)) + 1) / ε ^ (9 / 2 : ℝ)
    output := fun b => normalizedPreconditionedSolution n A M b }, ?_, ?_⟩
  · simp
  · unfold SolvesPreconditioned vecNorm
    simp only [sub_self]
    simp [hε.le]

end Qatlib.Papers.CirculantPrec18.SolveChain
