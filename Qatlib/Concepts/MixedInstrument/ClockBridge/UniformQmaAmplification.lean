/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.UniformQmaAmplificationDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LocalMachine.LocalTransport

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open Qatlib
open Matrix

set_option autoImplicit false

theorem mwGoodProjector_apply (p : WitnessVerifierProgram) (u : Reg (programQubits p)) :
    mwGoodProjector p u u = if u ∈ programOutputEvent p then 1 else 0 := by
  simp [mwGoodProjector]

theorem mwGoodProjector_apply_ne (p : WitnessVerifierProgram)
    (u v : Reg (programQubits p)) (hne : u ≠ v) :
    mwGoodProjector p u v = 0 := by
  simp [mwGoodProjector, hne]

theorem mwGoodProjector_hermitian (p : WitnessVerifierProgram) :
    (mwGoodProjector p)ᴴ = mwGoodProjector p := by
  ext u v
  by_cases hne : u = v
  · subst hne
    simp [mwGoodProjector_apply]
  · simp [mwGoodProjector_apply_ne p u v hne,
      mwGoodProjector_apply_ne p v u (Ne.symm hne)]

theorem mwBadProjector_apply (p : WitnessVerifierProgram) (u : Reg (programQubits p)) :
    mwBadProjector p u u = if u ∈ programOutputEvent p then 0 else 1 := by
  have hval := mwGoodProjector_apply p u
  by_cases hacc : u ∈ programOutputEvent p
  · simp [mwBadProjector, hval, hacc]
  · simp [mwBadProjector, hval, hacc]

theorem mwBadProjector_apply_ne (p : WitnessVerifierProgram)
    (u v : Reg (programQubits p)) (hne : u ≠ v) :
    mwBadProjector p u v = 0 := by
  simp [mwBadProjector, mwGoodProjector_apply_ne p u v hne, hne]

theorem mwRound_apply (p : WitnessVerifierProgram) (u : Reg (programQubits p)) :
    mwRound p u u = if u ∈ programOutputEvent p then 0 else 1 := by
  simp [mwRound]

theorem mwRound_apply_ne (p : WitnessVerifierProgram)
    (u v : Reg (programQubits p)) (hne : u ≠ v) :
    mwRound p u v = 0 := by
  simp [mwRound, hne]

theorem mwProcess_apply (p : WitnessVerifierProgram) (k : ℕ) (u : Reg (programQubits p)) :
    mwProcess p k u u = if u ∈ programOutputEvent p then 0 else 1 := by
  simp [mwProcess]

theorem mwProcess_apply_ne (p : WitnessVerifierProgram) (k : ℕ)
    (u v : Reg (programQubits p)) (hne : u ≠ v) :
    mwProcess p k u v = 0 := by
  simp [mwProcess, hne]

theorem mwProcess_preserves_witness (p : WitnessVerifierProgram) (k : ℕ)
    (u v : Reg (programQubits p)) (h : mwProcess p k u v ≠ 0) : u = v := by
  by_cases huv : u = v
  · exact huv
  · rw [mwProcess_apply_ne p k u v huv] at h
    exact absurd h (by simp)

theorem mwProcess_witness_frozen (p : WitnessVerifierProgram) (k : ℕ)
    (u v : Reg (programQubits p)) (h : mwProcess p k u v ≠ 0) :
    (fun i => u i) = (fun i => v i) := by
  have huv := mwProcess_preserves_witness p k u v h
  funext i
  simp [huv]

theorem clause4_complete :
    (∀ p : WitnessVerifierProgram, ∀ u : Reg (programQubits p),
        (mwGoodProjector p)ᴴ = mwGoodProjector p ∧
          mwGoodProjector p u u = if u ∈ programOutputEvent p then 1 else 0) ∧
      (∀ p : WitnessVerifierProgram, ∀ k : ℕ,
        ∀ u v : Reg (programQubits p),
          mwProcess p k u v ≠ 0 → u = v) := by
  refine ⟨?_, ?_⟩
  · intro p u
    exact ⟨mwGoodProjector_hermitian p, mwGoodProjector_apply p u⟩
  · intro p k u v h
    exact mwProcess_preserves_witness p k u v h

end Qatlib.Concepts.MixedInstrument.ClockBridge
