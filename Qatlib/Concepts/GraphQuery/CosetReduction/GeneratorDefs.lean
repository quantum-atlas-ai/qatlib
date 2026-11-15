/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GraphQuery.CosetReduction.CosetDefs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.ClosureSwap

@[expose] public section

set_option autoImplicit false
namespace Qatlib.Concepts.GraphQuery.CosetReduction

abbrev VertexSwapIndex (n : ℕ) := Fin n × Fin n
abbrev ColorSwapIndex (n : ℕ) := ((Fin n × Fin n) × (Fin n × Fin n)) × Bool

def encodedGenerator {n : ℕ} (A : BoolMatrix (Fin n))
    (ij : VertexSwapIndex n) : Equiv.Perm (Position (Fin n)) :=
  MulAut.conj (flipMatrix A) (liftPerm (Equiv.swap ij.1 ij.2))

def colorGenerator (n : ℕ) (z : ColorSwapIndex n) : Equiv.Perm (Position (Fin n)) :=
  Equiv.swap (z.1.1, z.2) (z.1.2, z.2)

end Qatlib.Concepts.GraphQuery.CosetReduction
