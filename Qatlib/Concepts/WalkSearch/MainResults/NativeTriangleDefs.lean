/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.GeneralMnrsFind
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.WalkSearch.MainResults
namespace NativeTriangleDefs

open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

abbrev triangleEdges (n : ℕ) := Finset (Fin n × Fin n)

def triangleOf {n : ℕ} (E : triangleEdges n) (t : Fin n × Fin n × Fin n) : Prop :=
  (t.1, t.2.1) ∈ E ∧ (t.2.1, t.2.2) ∈ E ∧ (t.1, t.2.2) ∈ E

def triangleSearchCost (n : ℕ) : ℕ := n ^ 3

end NativeTriangleDefs
end Qatlib.Concepts.WalkSearch.MainResults
