/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.UniformQmaAmplificationDefs

/-!
# Projector identities for witness verifier processes

This module computes the diagonal and off-diagonal entries of `mwGoodProjector`,
`mwBadProjector`, `mwRound`, and `mwProcess`. It proves that the good projector is Hermitian and
that every nonzero process entry connects equal register configurations.

These entrywise identities support the witness-preservation accounting used in the amplification
setting of [MarriottWatrous2005].

## Main statements

* `mwGoodProjector_hermitian`: proves Hermiticity of the good projector.
* `mwProcess_preserves_witness`: identifies configurations at nonzero entries.
* `clause4_complete`: collects the projector and preservation statements.

## References

* [Marriott and Watrous, 2005][MarriottWatrous2005]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LocalMachine.LocalTransport

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open Qatlib
open Matrix

set_option autoImplicit false

/-- The diagonal entry of the good projector is one on the program output event and zero
elsewhere. -/
theorem mwGoodProjector_apply (p : WitnessVerifierProgram) (u : Reg (programQubits p)) :
    mwGoodProjector p u u = if u ∈ programOutputEvent p then 1 else 0 := by
  simp [mwGoodProjector]

/-- Every off-diagonal entry of the good projector is zero. -/
theorem mwGoodProjector_apply_ne (p : WitnessVerifierProgram)
    (u v : Reg (programQubits p)) (hne : u ≠ v) :
    mwGoodProjector p u v = 0 := by
  simp [mwGoodProjector, hne]

/-- The good projector of a witness verifier program is Hermitian. -/
theorem mwGoodProjector_hermitian (p : WitnessVerifierProgram) :
    (mwGoodProjector p)ᴴ = mwGoodProjector p := by
  ext u v
  by_cases hne : u = v
  · subst hne
    simp [mwGoodProjector_apply]
  · simp [mwGoodProjector_apply_ne p u v hne,
      mwGoodProjector_apply_ne p v u (Ne.symm hne)]

/-- The diagonal entry of the bad projector is zero on the program output event and one
elsewhere. -/
theorem mwBadProjector_apply (p : WitnessVerifierProgram) (u : Reg (programQubits p)) :
    mwBadProjector p u u = if u ∈ programOutputEvent p then 0 else 1 := by
  have hval := mwGoodProjector_apply p u
  by_cases hacc : u ∈ programOutputEvent p
  · simp [mwBadProjector, hval, hacc]
  · simp [mwBadProjector, hval, hacc]

/-- Every off-diagonal entry of the bad projector is zero. -/
theorem mwBadProjector_apply_ne (p : WitnessVerifierProgram)
    (u v : Reg (programQubits p)) (hne : u ≠ v) :
    mwBadProjector p u v = 0 := by
  simp [mwBadProjector, mwGoodProjector_apply_ne p u v hne, hne]

/-- The diagonal entry of `mwRound` is zero on the program output event and one elsewhere. -/
theorem mwRound_apply (p : WitnessVerifierProgram) (u : Reg (programQubits p)) :
    mwRound p u u = if u ∈ programOutputEvent p then 0 else 1 := by
  simp [mwRound]

/-- Every off-diagonal entry of `mwRound` is zero. -/
theorem mwRound_apply_ne (p : WitnessVerifierProgram)
    (u v : Reg (programQubits p)) (hne : u ≠ v) :
    mwRound p u v = 0 := by
  simp [mwRound, hne]

/-- For every `k`, the diagonal entry of `mwProcess p k` is zero on the program output event and
one elsewhere. -/
theorem mwProcess_apply (p : WitnessVerifierProgram) (k : ℕ) (u : Reg (programQubits p)) :
    mwProcess p k u u = if u ∈ programOutputEvent p then 0 else 1 := by
  simp [mwProcess]

/-- Every off-diagonal entry of `mwProcess p k` is zero. -/
theorem mwProcess_apply_ne (p : WitnessVerifierProgram) (k : ℕ)
    (u v : Reg (programQubits p)) (hne : u ≠ v) :
    mwProcess p k u v = 0 := by
  simp [mwProcess, hne]

/-- A nonzero entry of `mwProcess p k` can only occur between equal register configurations. -/
theorem mwProcess_preserves_witness (p : WitnessVerifierProgram) (k : ℕ)
    (u v : Reg (programQubits p)) (h : mwProcess p k u v ≠ 0) : u = v := by
  by_cases huv : u = v
  · exact huv
  · rw [mwProcess_apply_ne p k u v huv] at h
    exact absurd h (by simp)

/-- A nonzero entry of `mwProcess p k` has identical input and output register functions. -/
theorem mwProcess_witness_frozen (p : WitnessVerifierProgram) (k : ℕ)
    (u v : Reg (programQubits p)) (h : mwProcess p k u v ≠ 0) :
    (fun i => u i) = (fun i => v i) := by
  have huv := mwProcess_preserves_witness p k u v h
  funext i
  simp [huv]

/-- Collects Hermiticity and diagonal entries of the good projector, together with equality of
register configurations at every nonzero process entry. The amplification setting is
motivated by [MarriottWatrous2005]. -/
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
