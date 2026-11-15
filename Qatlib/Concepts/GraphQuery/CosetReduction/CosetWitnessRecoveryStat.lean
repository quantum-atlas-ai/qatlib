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
open scoped Pointwise

def CosetWitnessRecovery : Prop :=
  ∀ (V : Type) (A B : BoolMatrix V) (k : Equiv.Perm (Position V)),
    k ∈ colorSubgroup V →
    k ∈ cosetRepresentative A B • (encodedSubgroup A : Set (Equiv.Perm (Position V))) →
    ∃ p : Equiv.Perm V, (∀ i, recoverVertex A B k i = p i) ∧
      ∀ i j, B (p i) (p j) = A i j

end Qatlib.Concepts.GraphQuery.CosetReduction
