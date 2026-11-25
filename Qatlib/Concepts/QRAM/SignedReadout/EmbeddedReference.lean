/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.SignedReadout.HeraldedInterference
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.LocalQFTReadout
public import Mathlib.Data.Matrix.Block

@[expose] public section

/-!
# Empirical reference in the target workspace

An address embedding specifies where the solution entries are read after
decoding. Extend the empirical QRAM state loader by the identity on the
complement and route the input seed to the embedded zero address. This gives
the reference branch of a coherent experiment on the same basis as the solver.
The embedding and routing are exact basis operations.
This implements the empirical reference preparation from
[KerenidisLandmanPrakash2020], Appendix G, in the larger solver workspace.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.QRAM.SignedReadout

open Matrix
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid mass)
open Qatlib.Concepts.QRAM.AmplitudeAccess
  (signedTreePreparation signed_tree_preparation_unitary signed_tree_preparation_apply pathAmplitude)
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend (relabelState_ket)
open Qatlib.Concepts.BlockEncoding.EncodingCore (relabelGate_mem_unitary)
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge (relabelGate relabelState relabelState_apply applyGate_relabelGate)
open scoped Classical

variable {depth : ℕ} {I : Type} [Fintype I] [DecidableEq I]

/-- Separate the physical solution addresses from the other workspace labels. -/
def referenceWorkspaceEquiv (place : Address depth ↪ I) :
    Address depth ⊕ {i // i ∉ Set.range place} ≃ I :=
  ((Equiv.ofInjective place place.injective).sumCongr (Equiv.refl _)).trans
    (Equiv.sumCompl fun i => i ∈ Set.range place)

omit [Fintype I] in
/-- The left summand denotes the placed address in the actual workspace. -/
theorem reference_workspace_inl (place : Address depth ↪ I) (a : Address depth) :
    referenceWorkspaceEquiv place (Sum.inl a) = place a := rfl

/-- Load a signed QRAM tree at the selected basis addresses, after routing the input seed. -/
def embeddedTreePreparation (place : Address depth ↪ I) (seed : I) (tree : Tree ℝ depth) : Matrix I I ℂ :=
  relabelGate (referenceWorkspaceEquiv place) (fromBlocks (signedTreePreparation tree) 0 0 1) *
    permMatrix (Equiv.swap seed (place (ZeroStr depth)))

/-- Extending the signed tree loader by the identity and routing the seed preserves unitarity. -/
theorem embedded_tree_preparation_unitary (place : Address depth ↪ I) (seed : I)
    (tree : Tree ℝ depth) (hTree : Valid tree) : embeddedTreePreparation place seed tree ∈ Matrix.unitaryGroup I ℂ := by
  unfold embeddedTreePreparation
  apply Submonoid.mul_mem
  · apply relabelGate_mem_unitary _ (referenceWorkspaceEquiv place)
    have hPrep := Matrix.mem_unitaryGroup_iff'.mp (signed_tree_preparation_unitary tree hTree)
    rw [Matrix.star_eq_conjTranspose] at hPrep
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.one_mul, add_zero, zero_add, hPrep, Matrix.fromBlocks_one]
  · exact permMatrix_unitary (Equiv.swap_apply_self seed (place (ZeroStr depth)))

/-- The prepared tree state has its signed amplitudes at the embedded addresses and zero
amplitude on every other workspace label. -/
theorem embedded_tree_preparation_apply (place : Address depth ↪ I) (seed : I)
    (tree : Tree ℝ depth) (hTree : Valid tree) (hMass : 0 < mass tree) :
    ApplyGate (embeddedTreePreparation place seed tree) (Ket seed) =
      relabelState (referenceWorkspaceEquiv place) (Sum.elim (fun a => (pathAmplitude tree a : ℂ)) 0) := by
  let e := referenceWorkspaceEquiv place
  have hSeed : e (Sum.inl (ZeroStr depth)) = place (ZeroStr depth) := reference_workspace_inl place _
  rw [embeddedTreePreparation, applyGate_mul,
    applyGate_permMatrix_ket (Equiv.swap_apply_self seed (place (ZeroStr depth))), Equiv.swap_apply_left]
  change ApplyGate (relabelGate e (fromBlocks (signedTreePreparation tree) 0 0 1))
    (Ket (place (ZeroStr depth))) = _
  rw [← hSeed, ← relabelState_ket e (Sum.inl (ZeroStr depth)), applyGate_relabelGate]
  apply congrArg (relabelState e)
  let K := {i // i ∉ Set.range place}
  have hLeft : (Ket (Sum.inl (ZeroStr depth) : Address depth ⊕ K) ∘ Sum.inl) = Ket (ZeroStr depth) := by
    funext i
    simp [Qatlib.Foundations.PureStateMath.Ket]
  have hRight : (Ket (Sum.inl (ZeroStr depth) : Address depth ⊕ K) ∘ Sum.inr) = 0 := by
    funext i
    simp [Qatlib.Foundations.PureStateMath.Ket]
  rw [ApplyGate, Matrix.fromBlocks_mulVec, hLeft, hRight]
  simp only [Matrix.mulVec_zero, Matrix.zero_mulVec, add_zero]
  have hLoaded : (signedTreePreparation tree) *ᵥ Ket (ZeroStr depth) = fun a => (pathAmplitude tree a : ℂ) :=
    funext (signed_tree_preparation_apply tree hTree hMass)
  rw [hLoaded]

/-- Load the empirical QRAM amplitudes at the physical readout labels. -/
def embeddedReferencePreparation (place : Address depth ↪ I) (seed : I) (samples : List (Address depth)) :
    Matrix I I ℂ :=
  embeddedTreePreparation place seed (empiricalTree samples)

/-- The embedded reference circuit is unitary. -/
theorem embedded_reference_preparation_unitary (place : Address depth ↪ I) (seed : I)
    (samples : List (Address depth)) : embeddedReferencePreparation place seed samples ∈ Matrix.unitaryGroup I ℂ :=
  embedded_tree_preparation_unitary place seed (empiricalTree samples) (valid_empirical_tree samples)

/-- The reference at each placed address is the amplitude of the empirical QRAM state. -/
theorem embedded_reference_preparation_entry (place : Address depth ↪ I) (seed : I)
    (samples : List (Address depth)) (hSamples : samples ≠ []) (a : Address depth) :
    ApplyGate (embeddedReferencePreparation place seed samples) (Ket seed) (place a) =
      (pathAmplitude (empiricalTree samples) a : ℂ) := by
  let e := referenceWorkspaceEquiv place
  have hInverse : e.symm (place a) = Sum.inl a := e.symm_apply_eq.mpr (reference_workspace_inl place a).symm
  have hMass : 0 < mass (empiricalTree samples) := by
    rw [empirical_tree_mass samples hSamples]
    exact zero_lt_one
  rw [embeddedReferencePreparation, embedded_tree_preparation_apply place seed _ (valid_empirical_tree samples) hMass,
    relabelState_apply, hInverse, Sum.elim_inl]

end Qatlib.Concepts.QRAM.SignedReadout
