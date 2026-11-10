/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.CompiledProgram
import Qatlib.Papers.SingleQuery97.MainResults.WalshResources
import Qatlib.Papers.SingleQuery97.MainResults.BalancedQueries
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.ResourceProgram

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.PureStateMath.BornBridge
open EncoderCircuit LinearCodeProgram WalshProgram

variable {A m n : ℕ} [NeZero A]

noncomputable def program (g : Fin m → Fin n → ZMod A) :=
  CompiledProgram.word (sparseComponents g)

theorem run_program (g : Fin m → Fin n → ZMod A) (y : Fin n → ZMod A) :
    Run (oracle y) (program g)
      (TensorState (TensorState (Ket 0) (Ket 0)) (Ket (-1:ZMod A))) =
    TensorState (TensorState (Ket (response g y)) (Ket 0)) (charState (1:ZMod A)) :=
  CompiledProgram.run_word g (sparseComponents g) (sparse_sum g) y

theorem program_normalized (g : Fin m → Fin n → ZMod A) (y : Fin n → ZMod A) :
    Normalized (Run (oracle y) (program g)
      (TensorState (TensorState (Ket 0) (Ket 0)) (Ket (-1:ZMod A)))) := by
  rw [run_program]
  exact normalized_tensorState (normalized_tensorState (normalized_ket _) (normalized_ket _))
    (normalized_charState _)

noncomputable def measured (g : Fin m → Fin n → ZMod A) (y : Fin n → ZMod A) :=
  bornDistribution (Run (oracle y) (program g)
    (TensorState (TensorState (Ket 0) (Ket 0)) (Ket (-1:ZMod A)))) (program_normalized g y)

theorem measured_eq (g : Fin m → Fin n → ZMod A) (y : Fin n → ZMod A) :
    measured g y = outputLaw g y := by
  ext p
  simp only [measured, outputLaw, bornDistribution_apply, run_program, LinearCodeProgram.run_word]

theorem program_resources (g : Fin m → Fin n → ZMod A) :
    QueryCount (program g) = 1 ∧ GateCount (program g) = 2+2*(support g).card := by
  have h := CompiledProgram.word_resources (sparseComponents g)
  simpa only [program, sparseComponents, List.length_map, Finset.length_toList] using h

theorem walsh_time {N q : ℕ} (label : Fin N ≃ (Fin q → ZMod 2)) (T : ℕ) :
    GateCount (program (generators label)) + T*QueryCount (program (generators label)) =
      2+N*q+T := by
  rw [(program_resources _).1, (program_resources _).2, mul_one]
  have h := WalshResources.two_pass_walsh_count label
  rw [(additions_resources _).2, (additions_resources _).2, List.length_map] at h
  simp only [sparseComponents, List.length_map, Finset.length_toList] at h
  omega

theorem prefix_time {N m : ℕ} (label : Fin N → Fin m → ZMod 2) (T : ℕ) :
    GateCount (program (generators (BalancedQueries.oriented label))) +
      T*QueryCount (program (generators (BalancedQueries.oriented label))) ≤ 2+m*N+T := by
  rw [(program_resources _).1, (program_resources _).2, mul_one]
  have h := BalancedQueries.two_pass_bound label
  omega

theorem walsh_contract {N q : ℕ} (label : Fin N ≃ (Fin q → ZMod 2)) (t : Fin N) (T : ℕ) :
    Run (oracle (database t)) (program (generators label))
      (TensorState (TensorState (Ket 0) (Ket 0)) (Ket (-1:ZMod 2))) =
      TensorState (TensorState (Ket (label t)) (Ket 0)) (charState (1:ZMod 2)) ∧
    QueryCount (program (generators label)) = 1 ∧
    GateCount (program (generators label)) + T*QueryCount (program (generators label)) = 2+N*q+T := by
  refine ⟨?_, (program_resources _).1, walsh_time label T⟩
  rw [run_program, response_database]

noncomputable def prefixExperiment {N : ℕ} [NeZero N] (prior : PMF (Fin N))
    (bits : Fin N → ℕ → ZMod 2) (length : Fin N → ℕ) (m : ℕ) : PMF (Fin N × Fin N) :=
  prior.bind fun t =>
    (measured (generators (BalancedQueries.oriented (PrefixProgram.truncated bits m))) (database t)).map
      (fun p => (t, PrefixProgram.decoder bits length m
        (BalancedQueries.unorient (PrefixProgram.truncated bits m) p.1.1)))

theorem prefixExperiment_eq {N : ℕ} [NeZero N] (prior : PMF (Fin N))
    (bits : Fin N → ℕ → ZMod 2) (length : Fin N → ℕ) (m : ℕ) :
    prefixExperiment prior bits length m = BalancedQueries.experiment prior bits length m := by
  simp only [prefixExperiment, BalancedQueries.experiment, measured_eq]

theorem prefix_contract {N : ℕ} [NeZero N] (prior : PMF (Fin N))
    (bits : Fin N → ℕ → ZMod 2) (length : Fin N → ℕ)
    (hprefix : PrefixProgram.PrefixFree bits length) (m T : ℕ) :
    QueryCount (program (generators (BalancedQueries.oriented (PrefixProgram.truncated bits m)))) = 1 ∧
    GateCount (program (generators (BalancedQueries.oriented (PrefixProgram.truncated bits m)))) +
      T*QueryCount (program (generators (BalancedQueries.oriented (PrefixProgram.truncated bits m)))) ≤
        2+m*N+T ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (prefixExperiment prior bits length m) (fun p => p.2 ≠ p.1) ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event prior (fun t => m < length t) := by
  refine ⟨(program_resources _).1, prefix_time _ T, ?_⟩
  rw [prefixExperiment_eq]
  exact BalancedQueries.error_le_tail prior bits length hprefix m

end Qatlib.Papers.SingleQuery97.MainResults.ResourceProgram
