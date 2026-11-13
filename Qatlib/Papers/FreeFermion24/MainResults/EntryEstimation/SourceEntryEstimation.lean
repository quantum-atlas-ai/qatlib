/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FreeFermion24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# SourceEntryEstimation

The headline algorithm and resource claims in this module are proposition definitions
with the suffix `_statement`: **Statement only — not proved in Qatlib.**
No circuit or oracle implementation is constructed for these specifications.
The remaining definitions and proved lemmas concern only mathematical identities.
Resource annotations in the legacy records have no execution semantics.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

open Qatlib.Papers.FreeFermion24.MainResults.Model

namespace Qatlib.Papers.FreeFermion24.MainResults.EntryEstimation

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `lemma12_entryEstimation`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def lemma12_entryEstimation_statement
    (n : ℕ) (m : ℕ) (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (α ε εt δ : ℝ) (i j : Fin (2 ^ n))
    (B : ControlledBlockEncoding (2 ^ n) A α ε)
    (hα : 0 ≤ α) (hε : 0 ≤ ε) (hεt : 0 < εt) (hδ : 0 < δ) (hδ1 : δ < 1) : Prop :=
    ∃ E : RandomisedEstimator (2 ^ n),
      (∃ P : Polynomial ℝ, IsNatNonnegPoly P ∧ (E.k : ℝ) ≤ P.eval (n : ℝ)) ∧
      ThetaBound (E.calls : ℝ) ((1 / εt ^ 2) * Real.log (4 / δ))
        ((1 / εt ^ 2) * Real.log (4 / δ)) ∧
      1 - δ ≤ successProb A E i j (ε + α * εt)

end Qatlib.Papers.FreeFermion24.MainResults.EntryEstimation
