/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.QuantumAccess.ResidualDiagnosticContracts
set_option warningAsError false

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.WalkSearch.Primitives
open Qatlib.Concepts.WalkSearch.Primitives
open Qatlib.Concepts.WalkSearch.QuantumAccess.Walk
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

theorem kCollision_native_empty_obstruction (kcs : KCollisionSolver) :
    ¬ KCollisionSolver.NativeRealized kcs := by
  intro h
  obtain ⟨_circuit, start, _unitary, hnorm, _queries, _born⟩ :=
    h 0 1 1 0 0 0 (fun _ => false)
  have hn := hnorm (Classical.choice kcs.seedNe)
  haveI : IsEmpty (Fin 1 → Fin 0) := ⟨fun f => Fin.elim0 (f 0)⟩
  simp [Normalized] at hn

theorem kCollisionNative_obstruction : ¬ KCollisionNative := by
  intro h
  obtain ⟨kcs, _hexp, _hκ, hnative⟩ := h 3 (by decide)
  exact kCollision_native_empty_obstruction kcs hnative

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
