/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TwoLevelLower
import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderChainDefs
import Qatlib.Foundations.PureStateMath.Qubit
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Matrix

namespace Qatlib.Concepts.WalkSearch.Th4Expander

def SzegedyTheorem4ExpanderChain : Prop :=
  ∀ (n d : ℕ) (adj : Fin n → Fin n → Bool),
    0 < n → 0 < d →
    (∀ i j, adj i j = adj j i) →
    (∀ i, (Finset.univ.filter (fun j => adj i j)).card = d) →
    IsTransitionMatrix (expanderStep n d adj) ∧
    (∀ i j, expanderStep n d adj i j = expanderStep n d adj j i) ∧
    (∀ i : Fin n, ∀ p : Fin n × Fin n,
      (SzegedyIsometry (expanderStep n d adj) *ᵥ Ket i) p ≠ 0 →
        p.1 = i ∧ adj i p.2)

end Qatlib.Concepts.WalkSearch.Th4Expander
