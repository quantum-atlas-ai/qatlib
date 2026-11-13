/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# CirculantPrec18 — mathematical outputs and legacy cost labels

The records below describe singular-value estimates and solution vectors.
Their real-valued cost fields are independent metadata: no execution semantics
relates a cost to a returned vector or coefficient map. Correctness predicates
are solely mathematical accuracy specifications.

The source algorithm headlines in sibling modules are unproved proposition
definitions with names ending in `_statement`. The error propagation results
are proved separately; no SVE or HHL circuit is constructed.
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix.Norms.L2Operator BigOperators
open Matrix

namespace Qatlib.Papers.CirculantPrec18.SVETransport

/-- Squared Frobenius norm `Σᵢⱼ Aᵢⱼ²` of a real matrix. -/
def frobeniusSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- Frobenius norm `‖A‖_F` of a real matrix (paper §3.1). -/
def frobeniusNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (frobeniusSq A)

/-- Condition number `κ(A) = ‖A‖ · ‖A⁻¹‖`, using the ℓ² operator norm on
square real matrices. -/
def conditionNumber (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖A‖ * ‖A⁻¹‖

/-- ℓ² norm of a real vector. -/
def vecNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

/-! ## Model of the modified SVE of Lemma 1 (p.6)

The procedure consumes a coefficient family `α` over the right-singular basis
`{vᵢ}` and returns (i) the coefficient family `outputCoeff α` over the
left-singular basis `{uᵢ}` and (ii) singular-value estimates `sigmaHat`.
The source's map `Σ αᵢ|vᵢ⟩|0⟩ ↦ Σ αᵢ|uᵢ⟩|σ̃ᵢ⟩` preserves coefficients, which is
the `outputCoeff α = α` clause of `RealizesModifiedSVE`. -/

/-- Mathematical output metadata for the modified singular value estimation. -/
structure ModifiedSVE (n : ℕ) where
  /-- Unconstrained cost label, not a certified operation count. -/
  cost : ℝ
  /-- Estimated singular values written to the output register. -/
  sigmaHat : Fin n → ℝ
  /-- Probability that the post-selected branch succeeds. -/
  successProb : ℝ
  /-- Coefficient map on the right-singular basis. -/
  outputCoeff : (Fin n → ℝ) → Fin n → ℝ

/-- Source correctness of Lemma 1: every estimated singular value is within
`ε‖A‖_F`, the coefficient family is preserved (`|vᵢ⟩ → |uᵢ⟩`), and success has
probability at least `1 − 1/(n+1)`. -/
def RealizesModifiedSVE (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (σ : Fin n → ℝ)
    (ε : ℝ) (pro : ModifiedSVE n) : Prop :=
  (∀ i, |pro.sigmaHat i - σ i| ≤ ε * frobeniusNorm A) ∧
    pro.successProb ≥ 1 - 1 / ((n : ℝ) + 1) ∧
    (∀ α, pro.outputCoeff α = α)

/-! ## Model of the quantum linear solver of Lemma 2 (p.6) -/

/-- The normalised exact solution `A⁻¹|b⟩ / ‖A⁻¹|b⟩‖`. -/
def normalizedSolution (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    Fin n → ℝ :=
  (1 / vecNorm (A⁻¹ *ᵥ b)) • (A⁻¹ *ᵥ b)

/-- Mathematical output metadata for the quantum linear solver. -/
structure LinearSolver (n : ℕ) where
  /-- Unconstrained cost label, not a certified operation count. -/
  cost : ℝ
  /-- Output state as a function of the right-hand side. -/
  output : (Fin n → ℝ) → Fin n → ℝ

/-- Source correctness of Lemma 2: the output is within `ε` of the exact
normalised solution. -/
def SolvesLinearSystem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (ε : ℝ) (pro : LinearSolver n) : Prop :=
  vecNorm (pro.output b - normalizedSolution n A b) ≤ ε

/-! ## Model of the preconditioned solver of Theorems 1 and 2 (pp.8–9) -/

/-- The normalised exact solution of the preconditioned system
`C⁻¹ A x = C⁻¹ b`. -/
def normalizedPreconditionedSolution (n : ℕ) (A C : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) : Fin n → ℝ :=
  (1 / vecNorm ((C⁻¹ * A)⁻¹ *ᵥ (C⁻¹ *ᵥ b))) • ((C⁻¹ * A)⁻¹ *ᵥ (C⁻¹ *ᵥ b))

/-- Mathematical output metadata for the preconditioned linear solver. -/
structure PreconditionedSolver (n : ℕ) where
  /-- Unconstrained cost label, not a certified operation count. -/
  cost : ℝ
  /-- Output state as a function of the right-hand side. -/
  output : (Fin n → ℝ) → Fin n → ℝ

/-- Source correctness of Theorem 1 / Theorem 2: the output is within `ε` of
the exact normalised solution of `C⁻¹ A x = C⁻¹ b`. -/
def SolvesPreconditioned (n : ℕ) (A C : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (ε : ℝ) (pro : PreconditionedSolver n) : Prop :=
  vecNorm (pro.output b - normalizedPreconditionedSolution n A C b) ≤ ε

end Qatlib.Papers.CirculantPrec18.SVETransport
