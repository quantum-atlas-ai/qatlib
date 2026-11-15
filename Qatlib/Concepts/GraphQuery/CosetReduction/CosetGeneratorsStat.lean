/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GraphQuery.CosetReduction.GeneratorDefs

@[expose] public section

set_option autoImplicit false
namespace Qatlib.Concepts.GraphQuery.CosetReduction

def CosetGenerators : Prop :=
  ∀ (n : ℕ) (A : BoolMatrix (Fin n)),
    Subgroup.closure (Set.range (encodedGenerator A)) = encodedSubgroup A ∧
    Subgroup.closure (Set.range (colorGenerator n)) = colorSubgroup (Fin n) ∧
    Fintype.card (Position (Fin n)) = 2 * n ^ 2 ∧
    Fintype.card (VertexSwapIndex n) = n ^ 2 ∧
    Fintype.card (ColorSwapIndex n) = 2 * n ^ 4

end Qatlib.Concepts.GraphQuery.CosetReduction
