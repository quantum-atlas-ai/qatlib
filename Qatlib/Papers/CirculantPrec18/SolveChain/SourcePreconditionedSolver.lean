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
# SourcePreconditionedSolver — resource specifications

**Statement only — not proved in Qatlib.**

The paper's quantum algorithm is not constructed in this module. Declarations
ending in `_statement` specify abstract output accuracy and resource targets;
they are propositions, with no existence proof or counted implementation.
The legacy record fields alone do not certify execution costs.
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix.Norms.L2Operator BigOperators
open Matrix

open Qatlib.Papers.CirculantPrec18.SVETransport

namespace Qatlib.Papers.CirculantPrec18.SolveChain

/-- **Statement only — not proved in Qatlib.**
Resource and accuracy specification for `source_theorem1_circulant_preconditioner`.
No circuit, oracle implementation, or execution-cost theorem is supplied here.
The existential record is a specification, not evidence of an algorithm. -/
def source_theorem1_circulant_preconditioner_statement
    (n : ℕ) (A C : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (_hA : A.det ≠ 0) (_hC : C.det ≠ 0) (_hCA : (C⁻¹ * A).det ≠ 0)
    (ε : ℝ) (hε : 0 < ε) : Prop :=
    ∃ (c : ℕ) (_hc : 0 < c) (pro : PreconditionedSolver n),
      0 ≤ pro.cost ∧
      pro.cost ≤ (c : ℝ) * (conditionNumber n C) ^ (5 / 2 : ℝ) *
          (conditionNumber n (C⁻¹ * A)) ^ 2 * (frobeniusNorm A) ^ 2 *
          ((Real.log ((n : ℝ) + 1)) + 1) ^ c / ε ^ (3 / 2 : ℝ) ∧
        SolvesPreconditioned n A C b ε pro

/-- **Statement only — not proved in Qatlib.**
Resource and accuracy specification for `source_theorem2_general_preconditioner`.
No circuit, oracle implementation, or execution-cost theorem is supplied here.
The existential record is a specification, not evidence of an algorithm. -/
def source_theorem2_general_preconditioner_statement
    (n : ℕ) (A M : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (_hA : A.det ≠ 0) (_hM : M.det ≠ 0) (_hMA : (M⁻¹ * A).det ≠ 0)
    (ε : ℝ) (hε : 0 < ε) : Prop :=
    ∃ (c : ℕ) (_hc : 0 < c) (pro : PreconditionedSolver n),
      0 ≤ pro.cost ∧
      pro.cost ≤ (c : ℝ) * (conditionNumber n M) ^ (5 / 2 : ℝ) *
          (conditionNumber n (M⁻¹ * A)) ^ 4 * frobeniusNorm A *
          frobeniusNorm M * frobeniusNorm (M⁻¹ * A) *
          ((Real.log ((n : ℝ) + 1)) + 1) ^ c / ε ^ (9 / 2 : ℝ) ∧
        SolvesPreconditioned n A M b ε pro

end Qatlib.Papers.CirculantPrec18.SolveChain
