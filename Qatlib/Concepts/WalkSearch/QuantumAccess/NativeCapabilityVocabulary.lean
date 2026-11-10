/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkContracts
import Qatlib.Concepts.WalkSearch.Primitives.ScopedSearchInterface
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryAlgorithm
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Data.Fintype.Card
set_option warningAsError false

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.WalkSearch.QuantumAccess

open Qatlib
open Qatlib.Concepts.WalkSearch.Primitives
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

def SafeGrover.NativeRealized (sgs : Qatlib.Concepts.WalkSearch.Primitives.SafeGrover) : Prop :=
  ∀ (N : ℕ) (marked : Fin N → Bool) (check floor : ℕ),
    ∃ (circuit : sgs.seed → Circuit (Fin N)) (start : sgs.seed → QState (Fin N)),
      (∀ ρ, IsUnitaryCircuit (circuit ρ)) ∧
      (∀ ρ, Normalized (start ρ)) ∧
      (∀ ρ, QueryCount (circuit ρ) ≤
        4 * (Nat.sqrt (max N floor + 1) + 1) *
          (Nat.log 2 (max N floor + 1) + 2) * (check + 1)) ∧
      ((∃ x, marked x = true) →
        ∀ ρ, 1 - ((max N floor + 1 : ℝ) ^ (-(sgs.cExp : ℝ))) ≤
          MeasureProb (Run (preparedMark (Finset.univ.filter (fun x => marked x = true)))
            (circuit ρ) (start ρ))
            (Finset.univ.filter (fun x => marked x = true)))

def NoisySearch.NativeRealized (ncs : NoisySearch) : Prop :=
  ∀ (N : ℕ) (marked : Fin N → Bool) (test : Fin N → Bool) (tcost floor : ℕ),
    (∀ v, test v = true → marked v = true) →
    ∃ (circuit : ncs.seed → Circuit (Fin N)) (start : ncs.seed → QState (Fin N)),
      (∀ ρ, IsUnitaryCircuit (circuit ρ)) ∧
      (∀ ρ, Normalized (start ρ)) ∧
      (∀ ρ, QueryCount (circuit ρ) ≤
        4 * (Nat.sqrt (floor + 1) + 1) * (Nat.log 2 (floor + 1) + 2) * (tcost + 1)) ∧
      ((∃ v, marked v = true) →
        ∀ ρ, 1 - ((floor + 1 : ℝ) ^ (-(ncs.cExp : ℝ))) ≤
          MeasureProb (Run (preparedMark (Finset.univ.filter (fun v => marked v = true)))
            (circuit ρ) (start ρ))
            (Finset.univ.filter (fun v => marked v = true)))

def KCollisionSolver.NativeRealized (kcs : KCollisionSolver) : Prop :=
  ∀ (n k r s u c : ℕ) (R : (Fin k → Fin n) → Bool),
    ∃ (circuit : kcs.seed → Circuit (Fin k → Fin n))
      (start : kcs.seed → QState (Fin k → Fin n)),
      (∀ ρ, IsUnitaryCircuit (circuit ρ)) ∧
      (∀ ρ, Normalized (start ρ)) ∧
      (∀ ρ, (QueryCount (circuit ρ) : ℝ) ≤
        8 * (Nat.log 2 (n + 1) + 2) *
          ((s : ℝ) + ((n : ℝ) / r) ^ ((k : ℝ) / 2) * ((c : ℝ) + (Nat.sqrt r : ℝ) * u))) ∧
      ((∃ t, R t = true) →
        ∀ ρ, 1 - ((n + 1 : ℝ) ^ (-(kcs.cExp : ℝ))) ≤
          MeasureProb (Run (preparedMark (Finset.univ.filter (fun t => R t = true)))
            (circuit ρ) (start ρ))
            (Finset.univ.filter (fun t => R t = true)))

end Qatlib.Concepts.WalkSearch.QuantumAccess
