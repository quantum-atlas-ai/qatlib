/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.QuantumAccess.ResidualDiagnosticContracts

/-!
# Obstructions to unrestricted collision realization

`kCollision_native_empty_obstruction` refutes the unrestricted native-realization contract
because it requires a normalized state on an empty tuple space.
`input_dependent_zero_query_collision` separately shows that an existing witness can be placed
directly in the initial state to yield unit success with zero queries.

These results clarify the realization conditions used in collision and subset-finding models
[ChildsEisenberg2003].

## Main statements

* `kCollisionNative_obstruction`: the global native collision contract is false.
* `input_dependent_zero_query_collision`: a witness-dependent initial state yields a zero-query
  realization.

## References

* [Childs and Eisenberg, 2003][ChildsEisenberg2003]
-/

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.WalkSearch.Primitives
open Qatlib.Concepts.WalkSearch.Primitives
open Qatlib.Concepts.WalkSearch.QuantumAccess.Walk
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

/-- No collision solver satisfies `KCollisionSolver.NativeRealized`, since the contract includes
an empty tuple register. -/
theorem kCollision_native_empty_obstruction (kcs : KCollisionSolver) :
    ¬ KCollisionSolver.NativeRealized kcs := by
  intro h
  obtain ⟨_circuit, start, _unitary, hnorm, _queries, _born⟩ :=
    h 0 1 1 0 0 0 (fun _ => false)
  have hn := hnorm (Classical.choice kcs.seedNe)
  haveI : IsEmpty (Fin 1 → Fin 0) := ⟨fun f => Fin.elim0 (f 0)⟩
  simp [Normalized] at hn

/-- The unrestricted native collision capability proposition `KCollisionNative` is false. -/
theorem kCollisionNative_obstruction : ¬ KCollisionNative := by
  intro h
  obtain ⟨kcs, _hexp, _hκ, hnative⟩ := h 3 (by decide)
  exact kCollision_native_empty_obstruction kcs hnative

/-- If `R` has a satisfying tuple, there exist a normalized state and a unitary zero-query
circuit whose measurement satisfies `R` with probability one. -/
theorem input_dependent_zero_query_collision {n k : ℕ}
    (R : (Fin k → Fin n) → Bool) (hex : ∃ t, R t = true) :
    ∃ (C : Circuit (Fin k → Fin n)) (ψ : QState (Fin k → Fin n)),
      IsUnitaryCircuit C ∧ Normalized ψ ∧ QueryCount C = 0 ∧
      MeasureProb (Run (preparedMark (Finset.univ.filter (fun t => R t = true))) C ψ)
        (Finset.univ.filter (fun t => R t = true)) = 1 := by
  classical
  obtain ⟨t, ht⟩ := hex
  refine ⟨[], Ket t, isUnitaryCircuit_nil, normalized_ket t, rfl, ?_⟩
  simp [MeasureProb, bornProb_ket, ht]

end Qatlib.Concepts.WalkSearch.Primitives
