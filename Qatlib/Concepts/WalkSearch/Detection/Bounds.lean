/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.ProjectorCS
import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector
import Qatlib.Concepts.WalkSearch.FrameSpectral.SpectralBounds

/-!
# Spectral and displacement bounds for detection

The module connects the unmarked row-frame Gram matrix to `unmarkedPrincipal` and bounds its
operator norm using the symmetric-chain gap. It also exposes threshold-mass and average
squared-displacement estimates for the corrected marked walk. See [Szegedy2004] for the
mathematical background.

## Main statements

* `source_lemma_two_principal_gram`: the frame identity and norm gap.
* `source_lemma_three_threshold_mass`: threshold bounds for two walk formulations.
* `source_lemma_three_busy_difference`: average squared displacement.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.FrameSpectral
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open scoped Classical BigOperators Kronecker Matrix.Norms.L2Operator

namespace Qatlib.Concepts.WalkSearch.Detection.Bounds

/-- Under the stated gap assumptions, the unmarked row frame is an isometry, its swapped Gram
matrix is `unmarkedPrincipal P S`, and the principal matrix has norm at most `1 - δ *
markedFraction S`. See [Szegedy2004]. -/
theorem source_lemma_two_principal_gram
    (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : SymmetricChainGap P δ) :
    IsIsometry (unmarkedRowFrame P S) ∧
    (unmarkedRowFrame P S)ᴴ * (SwapGate : Matrix (I × I) (I × I) ℂ) * (unmarkedRowFrame P S) =
      unmarkedPrincipal P S ∧
    ‖unmarkedPrincipal P S‖ ≤ 1 - δ * markedFraction S :=
  unmarked_principal_gram_and_gap I P S δ hδ hδ1 hgap

/-- Under the stated gap and marked-fraction assumptions, the unmarked principal matrix has
operator norm at most `1 - δ * ε / 2`. See [Szegedy2004]. -/
theorem source_lemma_two_spectral_radius
    (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ ε : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : SymmetricChainGap P δ)
    (hε : 0 < ε) (hεp : ε ≤ markedFraction S) :
    ‖unmarkedPrincipal P S‖ ≤ 1 - δ * ε / 2 := by
  have h := (unmarked_principal_gram_and_gap I P S δ hδ hδ1 hgap).2.2
  have hde : 0 < δ * ε := mul_pos hδ hε
  have hle : δ * ε ≤ δ * markedFraction S := mul_le_mul_of_nonneg_left hεp hδ.le
  linarith

/-- Under the stated gap assumptions and positive marked fraction, `lemma3Length` is positive,
is at least `1000 / sqrt (δ * markedFraction S)`, and gives threshold mass at least `1 / 6`
for both the corrected and absorbing walk formulations. See [Szegedy2004]. -/
theorem source_lemma_three_threshold_mass
    (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : SymmetricChainGap P δ)
    (ha : 0 < markedFraction S) :
    0 < lemma3Length δ (markedFraction S) ∧
    1000 / Real.sqrt (δ * markedFraction S) ≤ (lemma3Length δ (markedFraction S) : ℝ) ∧
    (1 / 6 : ℝ) ≤ lemma3ThresholdMass (correctedMarkedWalk P S)
      (detectionUnmarkedInitial P S) (lemma3Length δ (markedFraction S)) ∧
    (1 / 6 : ℝ) ≤ lemma3ThresholdMass (lemma3AbsorbingWalk P S)
      (detectionUnmarkedInitial P S) (lemma3Length δ (markedFraction S)) := by
  have hth := lemma3_threshold_event P S δ (lemma3Length δ (markedFraction S))
    hδ hδ1 hgap ha rfl
  have hLpos : 0 < lemma3Length δ (markedFraction S) := hth.1
  have hLpos' : (0 : ℝ) < (lemma3Length δ (markedFraction S) : ℝ) := by
    exact_mod_cast hLpos
  have hb := lemma3Length_bounds δ (markedFraction S) hδ ha
  have hmass : (1 / 6 : ℝ) ≤ lemma3ThresholdMass (correctedMarkedWalk P S)
      (detectionUnmarkedInitial P S) (lemma3Length δ (markedFraction S)) := by
    unfold lemma3ThresholdMass
    rw [le_div_iff₀ hLpos']
    have hring : (1 / 6 : ℝ) * ((lemma3Length δ (markedFraction S) : ℝ)) =
        ((lemma3Length δ (markedFraction S) : ℝ)) / 6 := by ring
    rw [hring]
    exact hth.2
  exact ⟨hLpos, hb.2.1, hmass,
    by rw [lemma3_absorbing_threshold_mass_eq P S (lemma3Length δ (markedFraction S))]; exact hmass⟩

/-- Under the stated gap and positivity assumptions, the unmarked initial state's squared norm
is `1 - markedFraction S`, and its average squared displacement over powers 1 through `L` is
at least the displayed gap-dependent bound. See [Szegedy2004]. -/
theorem source_lemma_three_busy_difference
    (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ : ℝ) (L : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : SymmetricChainGap P δ)
    (hp : 0 < markedFraction S) (hL : 0 < L) :
    ‖toEuclidean_fromVec (detectionUnmarkedInitial P S)‖ ^ 2 = 1 - markedFraction S ∧
    (∑ k : Fin L, ‖toEuclidean_fromVec
      ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S -
        detectionUnmarkedInitial P S)‖ ^ 2) / (L : ℝ) ≥
      2 * (1 - 1 / ((L : ℝ) * Real.sqrt (δ * markedFraction S))) *
        (1 - markedFraction S) :=
  corrected_szegedy_busy_random_power_difference I P S δ L hδ hδ1 hgap hp hL

end Qatlib.Concepts.WalkSearch.Detection.Bounds
