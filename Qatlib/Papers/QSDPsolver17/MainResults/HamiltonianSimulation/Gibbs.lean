/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

set_option backward.isDefEq.respectTransparency false

/-!
# Gibbs

The headline algorithm and resource claims in this module are proposition definitions
with the suffix `_statement`: **Statement only — not proved in Qatlib.**
No circuit or oracle implementation is constructed for these specifications.
The remaining definitions and proved lemmas concern only mathematical identities.
Resource annotations in the legacy records have no execution semantics.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSDPsolver17.MainResults.HamiltonianSimulation
open Qatlib.Papers.QSDPsolver17.MainResults


/-- A purification-based Gibbs-state preparation: `reduced` is the state on
system `A`, `traceDistance` its trace distance from the Gibbs state,
`successProbability` the preparation success probability, and `costFactor` the
multiplicative overhead over the complexity of Theorem 43. -/
structure GibbsPreparation (n : ℕ) where
  reduced : Matrix (Fin n) (Fin n) ℂ
  traceDistance : Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ
  successProbability : Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ
  costFactor : Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `lemma44_purified_gibbs`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def lemma44_purified_gibbs_statement : Prop :=
    ∃ prep : GibbsPreparation 1,
      ∀ (H : Matrix (Fin 1) (Fin 1) ℂ) (z ε : ℝ),
        (2 : ℝ) / 3 ≤ prep.successProbability H ε →
        0 < z → z ≤ (Matrix.trace (matExp H)).re → 0 < ε → ε ≤ 1 →
        prep.traceDistance H ε ≤ ε ∧
        IsSoftO (prep.costFactor H ε) (Real.sqrt (1 / z)) (1 / ε)

end Qatlib.Papers.QSDPsolver17.MainResults.HamiltonianSimulation
