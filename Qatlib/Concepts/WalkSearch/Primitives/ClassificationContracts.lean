/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.ClassificationScan

/-!
# Corrected classification contract

Defines `classifySpecCorrected`, the deterministic contract for a full graph classification scan
with correct degree tests. It requires a query bound and either a valid triangle or a disjoint
pair partition with triangle-count and graph-edge bounds; the surrounding quantum graph-search
setting is surveyed in [Ambainis2005].

## Main statements

* `classifySpecCorrected`: The classification contract asserting the corrected query bound and,
  under graph containment, thinness, and correct-test hypotheses, either a valid triangle or a
  disjoint partition with the stated triangle and retained-edge bounds.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.WalkSearch.MainResults
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical

/-- The classification contract asserting the corrected query bound and, under graph
containment, thinness, and correct-test hypotheses, either a valid triangle or a disjoint
partition with the stated triangle and retained-edge bounds. -/
def classifySpecCorrected : Prop :=
  ∀ (n : ℕ) (G : UGraph n) (sgs : SGSExecution) (τ dHi dLo K c tThin : ℕ),
    0<n→1≤dLo→dLo≤dHi→1≤τ→
    ∀ (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed) (S : SymmetricPairSet n),
      G.edges⊆S.edges→S.edges⊆thinPairs G.edges tThin→
      classifyScanTestsCorrect G sgs τ dHi dLo K c ttape stape Finset.univ.toList S→
      let r:=classifyScan G sgs τ K c ttape stape Finset.univ.toList S
      r.queries≤classifyBudgetCorrected n dLo τ K c sgs ∧
      match r.triangle with
      | some (a,b,cc)=>tri3 G.edges a b cc ∧ (a,b)∈G.edges ∧ (a,cc)∈G.edges ∧ (b,cc)∈G.edges
      | none=>r.movedT.toFinset∪r.movedE=S.edges ∧ Disjoint r.movedT.toFinset r.movedE ∧
          triCount r.movedT.toFinset≤n.choose 2*τ ∧
          (r.movedE∩G.edges).card≤2*n*dHi+(n*n/(dLo*τ)+1)*(2*n*(tThin+1))

end Qatlib.Concepts.WalkSearch.Primitives
