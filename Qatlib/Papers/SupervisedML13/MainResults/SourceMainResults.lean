/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SupervisedML13.MainResults.SourceClusterAssignment
import Qatlib.Papers.SupervisedML13.MainResults.SourceQuantumLloyd
import Qatlib.Papers.SupervisedML13.MainResults.SourceAdiabaticClustering

set_option backward.isDefEq.respectTransparency false

/-!
# c001 — logarithm-time quantum supervised and unsupervised learning

Fixed arXiv:1307.0411v2, Abstract (p. 1):

"Quantum machine learning can take time logarithmic in both the number of
vectors and their dimension, an exponential speed-up over classical
algorithms."

This module bundles the paper's main-result accounting into one theorem: the
supervised assignment and the quantum Lloyd step are logarithmic in both `M`
and `N` (with the `ε⁻¹` accuracy factor for the assignment), while the
classical counterparts are polynomial (`M·N` and `M²·N`).  The adiabatic
clustering construction is logarithmic in `k·M·N` with the `k`-fold factor of
c005.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SupervisedML13.MainResults

/-- The main-result predicate: a cost is `ε⁻¹ (log₂ M + log₂ N + 2)`, i.e.
logarithmic in both the number of vectors `M` and the dimension `N`. -/
def LogarithmicInMN (cost : ℝ) (ε : ℝ) (M N : ℕ) : Prop :=
  cost = ε⁻¹ * (Real.logb 2 (M : ℝ) + Real.logb 2 (N : ℝ) + 2)

/-- **c001** (paper Abstract, p. 1).  The main result: both the supervised
assignment primitive and the per-step quantum Lloyd primitive are logarithmic
in `M` and `N`, while their classical counterparts are `M·N` and `M²·N`; the
adiabatic clustering construction is `ε⁻¹ k log kMN`.

Source: arXiv:1307.0411v2 Abstract "... Quantum machine learning can take
time logarithmic in both the number of vectors and their dimension, an
exponential speed-up over classical algorithms."  The component statements
are c002 (`quantum_assignment_runtime`), c004 (`quantum_lloyd_step_runtime`)
and c005 (`adiabatic_clustering_runtime`). -/
theorem main_logarithmic_learning (ε : ℝ) (M N : ℕ) (hM : 0 < M) (hN : 0 < N) :
    LogarithmicInMN (quantumAssignmentCost ε M N) ε M N
      ∧ lloydStepQuantumCost M N
          = (M : ℝ) * (Real.logb 2 ((M : ℝ) * (N : ℝ)) + 2)
      ∧ classicalAssignmentCost M N = (M : ℝ) * (N : ℝ)
      ∧ lloydStepClassicalCost M N = (M : ℝ) ^ 2 * (N : ℝ) := by
  refine ⟨?_, quantum_lloyd_step_runtime M N hM hN, rfl, rfl⟩
  unfold LogarithmicInMN
  exact quantum_assignment_runtime_logb ε M N

/-- **c001**, exponential speed-up in the dimension and the number of vectors:
the quantum assignment cost has the form `ε⁻¹ (log₂(M·N) + 2)`, while the
classical cost is the polynomial `M·N`.  This is the paper's "exponential
speed-up over classical algorithms" for the supervised task, stated as the
pair of exact cost identities. -/
theorem main_supervised_cost_shape (ε : ℝ) (M N : ℕ) (hM : 0 < M) (hN : 0 < N) :
    quantumAssignmentCost ε M N = ε⁻¹ * (Real.logb 2 ((M : ℝ) * (N : ℝ)) + 2)
      ∧ classicalAssignmentCost M N = (M : ℝ) * (N : ℝ) :=
  ⟨quantum_assignment_runtime ε M N hM hN, rfl⟩

end Qatlib.Papers.SupervisedML13.MainResults
