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

def GraphCosetReduction : Prop :=
  ∀ (V : Type) (A B : BoolMatrix V), MatrixIso A B ↔ CosetIntersects A B

end Qatlib.Concepts.GraphQuery.CosetReduction
