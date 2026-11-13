/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSurvey23.MainResults.Scaling.CostScaling

set_option backward.isDefEq.respectTransparency false

/-!
# c014 — Tensor PCA: quartic speedup from two quadratic gains

Fixed source: Dalzell et al., *Quantum algorithms: A survey of applications and
end-to-end complexities*, arXiv:2310.03011, Section 9.3 (arXiv source lines 8872–8876).

Source conclusion: tensor PCA receives a quartic quantum speedup, obtained by
composing two independent quadratic speedups — amplitude estimation/amplification
for the spectral gap and phase estimation for the eigenvalue readout.  The
survey stresses that a clever initial state is essential; otherwise the
preparation cost erases the advantage.

Formalization notes: one quadratic speedup is the cost ceiling `√· = sqrtCost`.
Applying it twice gives `sqrtCost (sqrtCost N)`, whose fourth power exceeds the
classical scale `N` (`quartic_of_two_quadratic`).  The "clever initial state"
caveat is the statement that the preparation cost is not allowed to dominate;
we record it as the docstring condition and do not model a specific state.

The amplitude-amplification/estimation stage
is `Qatlib.Concepts.AmplitudeCore.AmplifyCore` (its
`theorem2QuadraticSpeedup` contract) and the eigenvalue readout stage is
`Qatlib.Concepts.AmplitudeCore.PhaseEstimation`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QuantumSurvey23.MainResults.Learning

open Qatlib.Papers.QuantumSurvey23.MainResults.Scaling

/-- The quantum tensor-PCA cost after two quadratic speedups: `√(√N)`. -/
def tensorPcaCost (N : ℕ) : ℕ := sqrtCost (sqrtCost N)

/-- One-stage quadratic speedup: the cost ceiling `√N` satisfies
`N < (√N+1)²`.  This is the amplitude-estimation/amplification gain. -/
theorem one_quadratic_stage (N : ℕ) : N < (sqrtCost N) ^ 2 :=
  sqrtCost_sq_gt N

/-- **c014a (Section 9.3).** Two quadratic stages compose to a quartic
speedup: `N < (√(√N))⁴`.  This is the tensor-PCA quartic gain. -/
theorem tensor_pca_quartic_speedup (N : ℕ) :
    N < (tensorPcaCost N) ^ 4 := by
  unfold tensorPcaCost
  exact quartic_of_two_quadratic N

/-- **c014b (Section 9.3).** The quantum tensor-PCA cost is the literal
composition of the phase-estimation ceiling applied to the amplification
ceiling. -/
theorem tensor_pca_is_two_stage_composition :
    tensorPcaCost = fun N => sqrtCost (sqrtCost N) := rfl

/-- **c014 (Section 9.3), combined assessment.** Both individual
stages are quadratic (`N < (√N+1)²`) and their composition is quartic
(`N < (√(√N+1)+1)⁴`).  The survey's caveat — a clever initial state is
essential — is a precondition on the preparation cost, not part of this
arithmetic. -/
theorem tensor_pca_quartic_assessment (N : ℕ) :
    N < (sqrtCost N) ^ 2 ∧ N < (tensorPcaCost N) ^ 4 :=
  ⟨one_quadratic_stage N, tensor_pca_quartic_speedup N⟩

end Qatlib.Papers.QuantumSurvey23.MainResults.Learning
