/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.BinReciprocal
public import Qatlib.Papers.QFVMChen22.TimeStep.StencilPhaseTape

@[expose] public section

/-!
# Conditional reciprocal on the first accepting bin

[ChenXueChenEtAl2022], Appendix C.3, uses the phased solver of
[ChildsKothariSomma2017], Section 5. Each stage performs its phase decision
and then applies its own Chebyshev reciprocal only on a first acceptance.
All stages act on a common workspace. The reciprocal labels may have
different sizes at different stages, and an earlier acceptance fixes
the full state slice under every later stage. This is the forward staged
unitary. Its aggregate approximation and amplification require separate
bounds.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Foundations.PureStateMath
  (ApplyGate Inner Ket QState TensorGate TensorState applyGate_mul applyGate_one applyGate_tensorGate
    inner_ket_ket normalized_ket tensorGate_unitary)
open Qatlib.Foundations.PureStateMath.BornBridge
  (applyGate_relabelGate norm_toEuclidean_relabelState normalized_iff_norm_toEuclidean_fromVec
    relabelGate relabelState toEuclidean_fromVec)
open Qatlib.Foundations.QueryWordCore.Circuit (Circuit IsUnitaryCircuit Step)
open Qatlib.Concepts.BlockEncoding.EncodingCore (relabelGate_mem_unitary)
open Qatlib.Concepts.LchsSimulation.StaticLchs (norm_applyGate_of_mem_unitaryGroup)
open Qatlib.Concepts.PolynomialCalc.QubitizedPower (walk walk_unitary)
open Qatlib.Concepts.QsvtCore.PhaseExistence (blockDiagFirst blockDiagFirst_unitary)
open Qatlib.Concepts.ReferenceError.RefTraceError (tensorState_l2_norm)
open Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter (spectralTargetState)
open Qatlib.Concepts.WalkSearch.MultiBandFilter (bandEmbed)
open Qatlib.Concepts.QRAM.AmplitudeAccess (applyGate_blockDiagFirst_slice)
open Qatlib.Foundations.QramData.SquaredNormTree (Address)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry)
open scoped BigOperators Classical

variable {n : ℕ} {M N : Type} [Fintype M] [Fintype N] [DecidableEq M] [DecidableEq N]

/-- The fixed workspace carries a separate coefficient register for the degree of each bin. -/
abbrev ReciprocalTape (condition : Fin n → ℝ) (precision : ℝ) :=
  (t : Fin n) → BinReciprocalTerm (condition t) precision

/-- The common workspace of the clock, the bin coefficient registers, and the shared signal. -/
abbrev BinStageWorkspace (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision : ℝ) (M : Type) :=
  PhaseTape width × (ReciprocalTape condition precision × M)

/-- The spectator registers of a reciprocal stage consist of the whole decision tape and
all coefficient registers other than the current one. -/
abbrev BinStageSpectators (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision : ℝ) (t : Fin n) :=
  PhaseTape width × ((s : {s : Fin n // s ≠ t}) → BinReciprocalTerm (condition s.val) precision)

/-- Route the current coefficient register next to the signal while keeping the decision bits
available as controls. -/
def focusBinReciprocal (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision : ℝ) (t : Fin n) :
    BinStageWorkspace width condition precision M ≃
      BinStageSpectators width condition precision t × (BinReciprocalTerm (condition t) precision × M) :=
  let split := (Equiv.piSplitAt t (fun s => BinReciprocalTerm (condition s) precision)).trans
    (Equiv.prodComm _ _)
  (Equiv.prodCongr (Equiv.refl (PhaseTape width))
    ((Equiv.prodCongr split (Equiv.refl M)).trans (Equiv.prodAssoc _ _ _))).trans
      (Equiv.prodAssoc _ _ _).symm

/-- An inverse is enabled when this step has accepted and all earlier steps are still false. -/
def firstBinAcceptance {width : Fin n → ℕ} (t : Fin n) (tape : PhaseTape width) : Prop :=
  (tape t).1 = true ∧ ¬∃ s, s < t ∧ (tape s).1 = true

/-- Apply the current bin reciprocal in its own registers when the phase decision selects it. -/
def conditionalBinReciprocal (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision mass : ℝ)
    (t : Fin n) (C : Matrix M N ℂ) (U : Matrix M M ℂ) :
    Matrix (BinStageWorkspace width condition precision M) (BinStageWorkspace width condition precision M) ℂ :=
  relabelGate (focusBinReciprocal (M := M) width condition precision t).symm
    (blockDiagFirst fun spectators =>
      if firstBinAcceptance (width := width) t spectators.1 then
        binReciprocalUnitary (condition t) precision mass C U
      else 1)

set_option maxHeartbeats 500000 in
/-- The conditioned inverse is unitary on the common workspace. -/
theorem conditional_bin_reciprocal_unitary (width : Fin n → ℕ) (condition : Fin n → ℝ)
    (precision mass : ℝ) (t : Fin n) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSelf : Uᴴ = U) (hSq : U * U = 1)
    (hPos : 0 < mass) (hMass : reciprocalMass (condition t) precision ≤ mass) :
    conditionalBinReciprocal width condition precision mass t C U ∈ Matrix.unitaryGroup _ ℂ := by
  let selected := binReciprocalUnitary (condition t) precision mass C U
  let blocks (spectators : BinStageSpectators width condition precision t) :=
    if firstBinAcceptance (width := width) t spectators.1 then selected else 1
  have hSelected : selected ∈ Matrix.unitaryGroup (BinReciprocalTerm (condition t) precision × M) ℂ :=
    bin_reciprocal_unitary (condition t) precision mass C U hC hSelf hSq hPos hMass
  have hBlocks (spectators : BinStageSpectators width condition precision t) :
      blocks spectators ∈ Matrix.unitaryGroup (BinReciprocalTerm (condition t) precision × M) ℂ := by
    by_cases h : firstBinAcceptance (width := width) t spectators.1
    · simpa only [blocks, ite_eq_left h] using hSelected
    · simp only [blocks, ite_eq_right h]
      exact Submonoid.one_mem _
  let A := BinStageSpectators width condition precision t
  let B := BinReciprocalTerm (condition t) precision × M
  let decA : DecidableEq A := inferInstance
  let decB : DecidableEq B := @instDecidableEqProd (BinReciprocalTerm (condition t) precision) M
    inferInstance inferInstance
  let decProduct : DecidableEq (A × B) := @instDecidableEqProd A B decA decB
  have hDiagonal := @blockDiagFirst_unitary A B inferInstance decA inferInstance decB blocks hBlocks
  exact @relabelGate_mem_unitary (A × B) (BinStageWorkspace width condition precision M)
    inferInstance decProduct inferInstance inferInstance _ hDiagonal
    (focusBinReciprocal (M := M) width condition precision t).symm

omit [DecidableEq N] in
/-- At an arbitrary input coordinate, the conditioned reciprocal acts on just the current
coefficient register and signal at the coordinate's spectator values. -/
theorem conditional_bin_reciprocal_action (width : Fin n → ℕ) (condition : Fin n → ℝ)
    (precision mass : ℝ) (t : Fin n) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (ψ : QState (BinStageWorkspace width condition precision M)) (p : BinStageWorkspace width condition precision M) :
    let e := focusBinReciprocal (M := M) width condition precision t
    ApplyGate (conditionalBinReciprocal width condition precision mass t C U) ψ p =
      ApplyGate (if firstBinAcceptance (width := width) t p.1 then
        binReciprocalUnitary (condition t) precision mass C U else 1)
        (fun q => ψ (e.symm ((e p).1, q))) (e p).2 := by
  intro e
  let blocks (spectators : BinStageSpectators width condition precision t) :=
    if firstBinAcceptance (width := width) t spectators.1 then
      binReciprocalUnitary (condition t) precision mass C U else 1
  have hInput : relabelState e.symm (relabelState e ψ) = ψ := by
    funext q
    simp [relabelState]
  change ApplyGate (relabelGate e.symm (blockDiagFirst blocks)) ψ p = _
  conv_lhs => rw [← hInput, applyGate_relabelGate]
  change ApplyGate (blockDiagFirst blocks) (relabelState e ψ) (e p) = _
  rw [applyGate_blockDiagFirst_slice]
  rfl

/-- A stage writes its phase decision and then applies the selected reciprocal before any
later phase test. -/
def stencilBinStage (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision mass : ℝ)
    (t : Fin n) (threshold : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ) :
    Matrix (BinStageWorkspace width condition precision M) (BinStageWorkspace width condition precision M) ℂ :=
  conditionalBinReciprocal width condition precision mass t C U *
    routedMagnitudeStage width t (TensorGate (1 : Matrix (ReciprocalTape condition precision)
      (ReciprocalTape condition precision) ℂ) (walk C U)) threshold

/-- The composed decision and conditioned inverse give a unitary stage. -/
theorem stencil_bin_stage_unitary (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision mass : ℝ)
    (t : Fin n) (threshold : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSelf : Uᴴ = U) (hSq : U * U = 1)
    (hWidth : 0 < width t) (hPos : 0 < mass) (hMass : reciprocalMass (condition t) precision ≤ mass) :
    stencilBinStage width condition precision mass t threshold C U ∈ Matrix.unitaryGroup _ ℂ := by
  have hWalk : walk C U ∈ Matrix.unitaryGroup M ℂ :=
    Matrix.mem_unitaryGroup_iff'.2 (walk_unitary C U hC hSelf hSq)
  unfold stencilBinStage
  apply Submonoid.mul_mem
  · exact conditional_bin_reciprocal_unitary _ _ _ _ _ C U hC hSelf hSq hPos hMass
  · exact routed_magnitude_stage_unitary _ _ _ (tensorGate_unitary (Submonoid.one_mem _) hWalk) hWidth threshold

omit [DecidableEq M] in
/-- Appending a fixed coefficient-tape label preserves the signal inner product. -/
private theorem reciprocal_tape_inner (condition : Fin n → ℝ) (precision : ℝ)
    (tape : ReciprocalTape condition precision) (ψ φ : QState M) :
    Inner (TensorState (Ket tape) ψ) (TensorState (Ket tape) φ) = Inner ψ φ := by
  calc
    _ = Inner (Ket tape) (Ket tape) * Inner ψ φ := by
      simp only [Qatlib.Foundations.PureStateMath.Inner, TensorState, dotProduct,
        Fintype.sum_prod_type, Pi.star_apply, star_mul]
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = _ := by rw [inner_ket_ket, ite_eq_left rfl, one_mul]

set_option maxHeartbeats 900000 in
/-- On a running spectral packet, the full bin stage differs from its ideal spectral
decision followed by the same reciprocal by at most the counted-phase classification error. -/
theorem stencil_bin_stage_running_error {J : Type} [Fintype J] [DecidableEq J]
    (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision mass : ℝ)
    (t : Fin n) (threshold : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSelf : Uᴴ = U) (hSq : U * U = 1)
    (hWidth : 2 ≤ width t) (hPos : 0 < mass) (hMass : reciprocalMass (condition t) precision ≤ mass)
    (history : RemainingPhaseTape width t) (hRunning : ¬phaseTapeStopped width t history)
    (tape : ReciprocalTape condition precision) (v : J → QState M) (c : J → ℂ)
    (phase eigenvalue : J → ℝ) (η : ℝ) (hη : 0 < η) (hHalf : η ≤ 1 / 2)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = eigenvalue j)
    (hMargin : ∀ j, 2 * Real.pi * η < abs (|eigenvalue j| - threshold))
    (hOrthogonal : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hSpectrum : ∀ j, walk C U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j) :
    let e := focusPhaseTape (I := ReciprocalTape condition precision × M) width t
    let extended := fun j => TensorState (Ket tape) (v j)
    let seed := bandEmbed (width t) (by omega) (∑ j, c j • extended j)
    let accept := bandEmbed (width t) (by omega)
      (spectralTargetState extended c (Finset.univ.filter fun j => threshold ≤ |eigenvalue j|))
    let ideal : QState (Bool × (Fin (width t) × (Bool × (ReciprocalTape condition precision × M)))) :=
      fun p => if p.1 then accept p.2 else (seed - accept) p.2
    let actual := ApplyGate (stencilBinStage width condition precision mass t threshold C U)
      (relabelState e.symm (TensorState (Ket history) (TensorState (Ket false) seed)))
    let reference := ApplyGate (conditionalBinReciprocal width condition precision mass t C U)
      (relabelState e.symm (TensorState (Ket history) ideal))
    ‖toEuclidean_fromVec (actual - reference)‖ ≤
      Real.sqrt 2 * (Real.sqrt (∑ j, ‖c j‖ ^ 2) * (1 / (2 * Real.sqrt (width t) * η))) := by
  intro e extended seed accept ideal actual reference
  let W := TensorGate (1 : Matrix (ReciprocalTape condition precision)
    (ReciprocalTape condition precision) ℂ) (walk C U)
  let reciprocal := conditionalBinReciprocal width condition precision mass t C U
  let input := TensorState (Ket false) seed
  let output := ApplyGate (countedMagnitudeFlag W (width t) threshold) input
  have hWalk : walk C U ∈ Matrix.unitaryGroup M ℂ :=
    Matrix.mem_unitaryGroup_iff'.2 (walk_unitary C U hC hSelf hSq)
  have hW : W ∈ Matrix.unitaryGroup _ ℂ := tensorGate_unitary (Submonoid.one_mem _) hWalk
  have hExtendedOrthogonal (j l : J) : Inner (extended j) (extended l) = if j = l then 1 else 0 := by
    change Inner (TensorState (Ket tape) (v j)) (TensorState (Ket tape) (v l)) = _
    rw [reciprocal_tape_inner, hOrthogonal]
  have hExtendedSpectrum (j : J) :
      W *ᵥ extended j = Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • extended j := by
    let z := Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ))
    change ApplyGate (TensorGate 1 (walk C U)) (TensorState (Ket tape) (v j)) = z • extended j
    rw [applyGate_tensorGate, applyGate_one, show ApplyGate (walk C U) (v j) = z • v j from hSpectrum j]
    funext p
    change Ket tape p.1 * (z * v j p.2) = z * (Ket tape p.1 * v j p.2)
    ring
  have hReciprocal : reciprocal ∈ Matrix.unitaryGroup _ ℂ :=
    conditional_bin_reciprocal_unitary width condition precision mass t C U hC hSelf hSq hPos hMass
  have hActual : actual = ApplyGate reciprocal (relabelState e.symm (TensorState (Ket history) output)) := by
    change ApplyGate (reciprocal * routedMagnitudeStage width t W threshold)
      (relabelState e.symm (TensorState (Ket history) input)) = _
    rw [applyGate_mul, routed_magnitude_stage_running width t W threshold history hRunning input]
  have hDiff : actual - reference =
      ApplyGate reciprocal (relabelState e.symm (TensorState (Ket history) (output - ideal))) := by
    rw [hActual]
    change ApplyGate reciprocal _ - ApplyGate reciprocal _ = _
    rw [show relabelState e.symm (TensorState (Ket history) (output - ideal)) =
        relabelState e.symm (TensorState (Ket history) output) -
          relabelState e.symm (TensorState (Ket history) ideal) by
      funext p
      simp [relabelState, TensorState, mul_sub]]
    simp only [ApplyGate, Matrix.mulVec_sub]
  have hKet : ‖toEuclidean_fromVec (Ket history)‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).1 (normalized_ket _)
  rw [hDiff, norm_applyGate_of_mem_unitaryGroup hReciprocal, norm_toEuclidean_relabelState,
    tensorState_l2_norm, hKet, one_mul]
  exact counted_magnitude_flag_full_error W hW (width t) hWidth
    extended c phase eigenvalue threshold η hη hHalf hCos hMargin hExtendedOrthogonal hExtendedSpectrum

omit [DecidableEq N] in
/-- Both operations of a stage fix every amplitude whose decision tape accepted earlier. -/
theorem stencil_bin_stage_stopped (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision mass : ℝ)
    (t : Fin n) (threshold : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (ψ : QState (BinStageWorkspace width condition precision M)) (p : BinStageWorkspace width condition precision M)
    (hStopped : ∃ s, s < t ∧ (p.1 s).1 = true) :
    ApplyGate (stencilBinStage width condition precision mass t threshold C U) ψ p = ψ p := by
  have hInactive : ¬firstBinAcceptance (width := width) t p.1 := fun h => h.2 hStopped
  unfold stencilBinStage
  rw [applyGate_mul, conditional_bin_reciprocal_action, ite_eq_right hInactive, applyGate_one]
  rw [Equiv.symm_apply_apply]
  exact routed_magnitude_stage_stopped _ _ _ _ ψ p.1 p.2 hStopped

/-- Choose the largest bin coefficient mass, with floor one for positivity even on an empty
schedule. -/
def commonBinMass (condition : Fin n → ℝ) (precision : ℝ) : ℝ :=
  let masses := Finset.univ.image (fun t => reciprocalMass (condition t) precision)
  (insert 1 masses).max' (Finset.insert_nonempty _ _)

/-- The maximum mass is positive and dominates the coefficient mass of each bin. -/
theorem common_bin_mass_bounds (condition : Fin n → ℝ) (precision : ℝ) :
    0 < commonBinMass condition precision ∧
      ∀ t, reciprocalMass (condition t) precision ≤ commonBinMass condition precision := by
  unfold commonBinMass
  refine ⟨zero_lt_one.trans_le (Finset.le_max' _ _ (Finset.mem_insert_self _ _)), ?_⟩
  intro t
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩)

/-- The gates for the encoded stencil, in chronological order of the decision clock. -/
def encodedStencilBinGates {depth columns : ℕ} (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns)
    (width : Fin n → ℕ) (condition threshold : Fin n → ℝ) (precision : ℝ) :
    let W := BinStageWorkspace width condition precision (StencilWorkspace depth geometry.stencilSize columns)
    List (Matrix W W ℂ) :=
  let C := stencilWalkFrame depth rowScratch columnScratch
  let U := stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch
  (List.finRange n).map fun t =>
    stencilBinStage width condition precision (commonBinMass condition precision) t (threshold t) C U

/-- Execute all bin stages on the actual encoded stencil, ordered by the decision clock. -/
def encodedStencilBinProgram {depth columns : ℕ} (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns)
    (width : Fin n → ℕ) (condition threshold : Fin n → ℝ) (precision : ℝ) :
    Circuit (BinStageWorkspace width condition precision (StencilWorkspace depth geometry.stencilSize columns)) :=
  (encodedStencilBinGates geometry coefficients entryScale rowScratch columnScratch
    width condition threshold precision).map Step.gate

/-- The actual encoded stencil produces a unitary program with the common normalization,
using a positive counter resolution at every stage. -/
theorem encoded_stencil_bin_program_unitary {depth columns : ℕ} (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns)
    (width : Fin n → ℕ) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columns)
    (hWidth : ∀ t, 0 < width t) :
    IsUnitaryCircuit
      (encodedStencilBinProgram geometry coefficients entryScale rowScratch columnScratch width condition threshold
        precision) := by
  obtain ⟨hC, hSelf, hSq, _⟩ :=
    stencil_walk_encoding geometry coefficients entryScale rowScratch columnScratch hScale hEntry hColumns
  obtain ⟨hPos, hMass⟩ := common_bin_mass_bounds condition precision
  intro G hG
  rw [encodedStencilBinProgram, encodedStencilBinGates, List.map_map] at hG
  obtain ⟨t, _, ht⟩ := List.mem_map.mp hG
  rw [← Step.gate.inj ht]
  exact stencil_bin_stage_unitary _ _ _ _ _ _ _ _ hC hSelf hSq (hWidth t) hPos (hMass t)

end Qatlib.Papers.QFVMChen22.TimeStep
