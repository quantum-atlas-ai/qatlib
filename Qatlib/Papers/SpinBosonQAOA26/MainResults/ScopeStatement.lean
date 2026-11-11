/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Scope of the main results (claim c012)

Fixed source: arXiv:2505.07929v2, Abstract and Section I (PDF pp. 1–2).

The paper distinguishes two kinds of statement and this distinction is itself part of what
is asserted:

* `mappingTheorem` — the exact operator identity between the QAOA state of the
  spin–boson model and the path-integral / tensor-network expression (Section II;
  Propositions 1 and 2 of the main text);
* `numericalEnergyEvidence` — the numerical evidence for the energy of the SK model
  obtained by evaluating the mapping on finite trees (Sections III–IV; the energy formula
  `ν_p = (i/2) ∑_j Γ_j (G_{0,j})²` and its small-`p` values are *numerically* checked).

The two must not be conflated: the mapping theorem is rigorous, while the reported SK
energies are numerical evidence.  This file records the distinction as data (an inductive
type of scope items) with the corresponding basic facts, all proved.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpinBosonQAOA26.MainResults.ScopeStatement

/-- The two kinds of statement that the paper must keep distinct (Abstract, Section I):
the rigorous mapping theorem, and the numerical energy evidence for the SK model. -/
inductive ScopeItem where
  /-- The exact mapping between the spin–boson QAOA state and its path-integral form. -/
  | mappingTheorem
  /-- The numerical evidence for the SK-model energy from finite-tree evaluations. -/
  | numericalEnergyEvidence
  deriving DecidableEq, Repr

/-- The two scope items are different: the exact mapping theorem is not the numerical
energy evidence.  This is the formal content of the paper's insistence (Abstract,
Section I) that the rigorous result and the numerical evidence be kept distinct. -/
theorem mappingTheorem_ne_numericalEnergyEvidence :
    ScopeItem.mappingTheorem ≠ ScopeItem.numericalEnergyEvidence := by
  decide

/-- The scope of the main results is exhausted by the two items: every scope item is
either the exact mapping theorem or the numerical energy evidence. -/
theorem scopeItem_cases (x : ScopeItem) :
    x = ScopeItem.mappingTheorem ∨ x = ScopeItem.numericalEnergyEvidence := by
  rcases x with _ | _ <;> simp

/-- The mapping theorem is the rigorous (non-numerical) part of the scope. -/
def isRigorous : ScopeItem → Bool
  | ScopeItem.mappingTheorem => true
  | ScopeItem.numericalEnergyEvidence => false

/-- The rigorous part of the scope is exactly the mapping theorem, and the numerical
energy evidence is not rigorous: restating the distinction in terms of `isRigorous`. -/
theorem isRigorous_iff (x : ScopeItem) :
    isRigorous x = true ↔ x = ScopeItem.mappingTheorem := by
  rcases x with _ | _ <;> simp [isRigorous]

end Qatlib.Papers.SpinBosonQAOA26.MainResults.ScopeStatement
