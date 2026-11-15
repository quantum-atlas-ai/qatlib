/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GraphQuery.CosetReduction.CosetDefs

@[expose] public section

set_option autoImplicit false
namespace Qatlib.Concepts.GraphQuery.CosetReduction

def SimpleGraphCosetReduction : Prop :=
  ∀ (V : Type) (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj],
    Nonempty (G ≃g H) ↔
      CosetIntersects (fun i j => decide (G.Adj i j)) (fun i j => decide (H.Adj i j))

end Qatlib.Concepts.GraphQuery.CosetReduction
