/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CirculantPrec18.SVETransport.Model

set_option backward.isDefEq.respectTransparency false

/-!
# SourceLinearSolver — resource specifications

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
Resource and accuracy specification for `source_quantum_linear_solver`.
No circuit, oracle implementation, or execution-cost theorem is supplied here.
The existential record is a specification, not evidence of an algorithm. -/
def source_quantum_linear_solver_statement
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (_hdet : A.det ≠ 0) (ε : ℝ) (hε : 0 < ε) : Prop :=
    ∃ (c : ℕ) (_hc : 0 < c) (pro : LinearSolver n),
      0 ≤ pro.cost ∧
      pro.cost ≤ (c : ℝ) * (conditionNumber n A) ^ 2 *
          ((Real.log ((n : ℝ) + 1)) + 1) ^ c * frobeniusNorm A / ε ∧
        SolvesLinearSystem n A b ε pro

end Qatlib.Papers.CirculantPrec18.SolveChain
