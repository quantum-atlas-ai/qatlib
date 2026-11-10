/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkSpectra04.WalkDefinition.SzegedyDefOneQuantizedWalkQuan
import Qatlib.Papers.QWalkSpectra04.WalkDefinition.SzegedyDefTwoDiscriminantQuan
import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BoundarySpectralSectors
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Papers.QWalkSpectra04.WalkDefinition
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Papers.QWalkSpectra04.WalkDefinition.Definitions

theorem source_definition_one_quantized_walk
    (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (c : I → J → ℝ) (r : J → I → ℝ) :
    paperMu c r = bipartiteWalk (paperFrameA c) (paperFrameB r) :=
  (szegedyDefOneQuantizedWalk I J c r).1

theorem source_definition_one_chain_walk
    (K : Type) [Fintype K] [DecidableEq K] (P : K → K → ℝ) :
    paperMu P P = SzegedyWalk P :=
  (szegedyDefOneQuantizedWalk K K P P).2 K P

theorem source_definition_two_frame_gram
    (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (c : I → J → ℝ) (r : J → I → ℝ) (h : IsPaperBipartiteWalk c r) :
    IsIsometry (paperFrameA c) ∧ IsIsometry (paperFrameB r) ∧
    (∀ i j, ((paperFrameA c)ᴴ * paperFrameB r) i j = (Real.sqrt (c i j * r j i) : ℂ)) ∧
    (bipartiteTilde (paperFrameA c) (paperFrameB r))ᴴ *
        bipartiteTilde (paperFrameA c) (paperFrameB r) =
      1 + bipartiteDiscriminant (paperFrameA c) (paperFrameB r) := by
  obtain ⟨hA, hB, hG, hT, -⟩ := szegedyDefTwoDiscriminant I J c r h
  exact ⟨hA, hB, hG, hT⟩

theorem source_definition_two_chain_discriminant
    (K : Type) [Fintype K] [DecidableEq K] (P : K → K → ℝ) (hP : IsTransitionMatrix P) :
    paperFrameA P = SzegedyIsometry P ∧ paperFrameB P = SzegedyIsometryB P ∧
    bipartiteDiscriminant (SzegedyIsometry P) (SzegedyIsometryB P) =
      Matrix.fromBlocks 0 ((SzegedyDiscriminant P).map Complex.ofReal)
        ((SzegedyDiscriminant P).map Complex.ofReal) 0 := by
  have hwalk : IsPaperBipartiteWalk P P := ⟨hP.1, hP.2, hP.1, hP.2⟩
  exact (szegedyDefTwoDiscriminant K K P P hwalk).2.2.2.2 K P hP

theorem source_definition_three_idle_sector
    (I J K : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K]
    (A : Matrix K I ℂ) (B : Matrix K J ℂ) (w : QState K)
    (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1)
    (hwa : Aᴴ *ᵥ w = 0) (hwb : Bᴴ *ᵥ w = 0) :
    ReflectionAbout (A * Aᴴ) *ᵥ w = -w ∧
    ReflectionAbout (B * Bᴴ) *ᵥ w = -w ∧
    (ReflectionAbout (B * Bᴴ) * ReflectionAbout (A * Aᴴ)) *ᵥ w = w :=
  two_isometry_idle_sector_fixed I J K A B w hA hB hwa hwb

theorem source_definition_four_busy_tilde_coordinates
    (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) :
    (bipartiteDiscriminant A B).IsHermitian ∧
    (bipartiteTilde A B)ᴴ * bipartiteTilde A B = 1 + bipartiteDiscriminant A B ∧
    bipartiteWalk A B ∈ Matrix.unitaryGroup H ℂ :=
  bipartite_discriminant_tilde_bridge H I J A B hA hB

theorem source_definition_five_general_discriminant
    (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) :
    (bipartiteDiscriminant A B).IsHermitian ∧
    (bipartiteTilde A B)ᴴ * bipartiteTilde A B = 1 + bipartiteDiscriminant A B ∧
    bipartiteWalk A B ∈ Matrix.unitaryGroup H ℂ :=
  bipartite_discriminant_tilde_bridge H I J A B hA hB

end Qatlib.Papers.QWalkSpectra04.WalkDefinition.Definitions
