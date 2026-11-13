/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector
import Qatlib.Concepts.WalkSearch.ProjectorCS
import Qatlib.Concepts.WalkSearch.FrameSpectral.SpectralBounds
import Qatlib.Concepts.WalkSearch.TwoLevelLower

/-!
# Szegedy walk detection bounds

This module presents the uniform fixed state, unmarked spectral norm bound, and averaged
detection guarantee for symmetric chains. It also defines `ampK` and bounds the fraction of walk
times at which this squared norm is at most three. See [Szegedy2004].

## Main statements

* `szegedyLemma1_uniform_fixpoint`: For a symmetric transition matrix, the embedded uniform
  state is normalized and fixed by both the Szegedy walk and the swap gate.
* `szegedyTheorem2_detection`: Under the gap, marked fraction, and preparation hypotheses, empty
  marked sets are never detected and the average detection probability is at least `1 / 1000`
  when `L ≥ 1000 / √(δ * ε)`.
* `szegedyLemma3_amp_bound`: For a symmetric chain with positive gap and marked fraction, at
  least a fraction `1 / 6` of the prescribed walk times satisfy `ampK ≤ 3`.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.FrameSpectral
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.PhaseGeometry.Phase
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.QuantWalkSpec04.MainResults.Detection

/-- For a symmetric transition matrix, the embedded uniform state is normalized and fixed by
both the Szegedy walk and the swap gate. -/
theorem szegedyLemma1_uniform_fixpoint
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (P : I → I → ℝ)
    (hP : IsTransitionMatrix P) (hsymm : ∀ x y, P x y = P y x) :
    Normalized (SzegedyEmbedState P (fun _ => (Fintype.card I : ℝ)⁻¹)) ∧
    SzegedyWalk P *ᵥ SzegedyEmbedState P (fun _ => (Fintype.card I : ℝ)⁻¹) =
      SzegedyEmbedState P (fun _ => (Fintype.card I : ℝ)⁻¹) ∧
    SwapGate *ᵥ SzegedyEmbedState P (fun _ => (Fintype.card I : ℝ)⁻¹) =
      SzegedyEmbedState P (fun _ => (Fintype.card I : ℝ)⁻¹) := by
  let c : ℝ := (Fintype.card I : ℝ)⁻¹
  have hcpos : 0 < c := by
    dsimp [c]
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hsum : ∑ _x : I, c = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp [c]
    exact mul_inv_cancel₀ (ne_of_gt (by exact_mod_cast Fintype.card_pos))
  have hrev : IsReversible P (fun _ => c) := by
    intro x y
    show c * P x y = c * P y x
    rw [hsymm x y]
  have hswap : SwapGate *ᵥ SzegedyEmbedState P (fun _ => c) =
      SzegedyEmbedState P (fun _ => c) := by
    set Φ : QState (I × I) := SzegedyEmbedState P (fun _ => c) with hΦ
    have hmain : SwapGate *ᵥ Φ = Φ := by
      funext p
      obtain ⟨x, y⟩ := p
      have h1 : (SwapGate *ᵥ Φ) (x, y) = Φ (y, x) := by
        rw [applyGate_swapGate Φ]
        exact congrArg Φ Prod.swap_prod_mk
      rw [h1, hΦ, szegedyEmbedState_apply P (fun _ => c) y x,
        szegedyEmbedState_apply P (fun _ => c) x y]
      have hrev' : c * P y x = c * P x y := (hrev x y).symm
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj,
        ← Real.sqrt_mul (hP.1 y x) c, ← Real.sqrt_mul (hP.1 x y) c,
        mul_comm (P y x) c, hrev', mul_comm (P x y) c]
    rwa [hΦ] at hmain
  exact ⟨normalized_szegedyEmbedState P hP (fun _ => hcpos.le) hsum,
    szegedyWalk_fixes_stationary P hP hrev, hswap⟩

/-- Under the gap, marked fraction, and preparation hypotheses, empty marked sets are never
detected and the average detection probability is at least `1 / 1000` when `L ≥ 1000 / √(δ *
ε)`. See [Szegedy2004]. -/
theorem szegedyTheorem2_detection
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ ε : ℝ) (L : ℕ) (j : I)
    (U : Matrix (I × I) (I × I) ℂ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : SymmetricChainGap P δ)
    (hε : 0 < ε) (hεS : ε ≤ markedFraction S)
    (hL : 0 < L) (hscale : 1000 / Real.sqrt (δ * ε) ≤ (L : ℝ))
    (hU : U ∈ Matrix.unitaryGroup (I × I) ℂ)
    (hprep : ∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) :
    (∀ K : ℕ, detectionProbability U ∅ j K = 0) ∧
    (1 / 1000 : ℝ) ≤
      (∑ k : Fin L, detectionProbability U S j (k.val + 1)) / (L : ℝ) := by
  refine ⟨fun K => corrected_szegedy_empty_mark_one_sided I P j U K
    hgap.1 hgap.2.1 hU hprep, ?_⟩
  have hdet := (corrected_szegedy_actual_random_power_detection I P S δ ε L j U
    hδ hδ1 hgap hε hεS hL hscale hU hprep).1
  linarith

/-- Under the stated symmetric chain gap and marked fraction hypotheses, the norm of
`unmarkedPrincipal P S` is at most `1 - δ * ε / 2`. -/
theorem szegedyLemma2_spectral_radius
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ ε : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : SymmetricChainGap P δ)
    (hε : 0 < ε) (hεS : ε ≤ markedFraction S) :
    ‖unmarkedPrincipal P S‖ ≤ 1 - δ * ε / 2 := by
  have hnorm := (unmarked_principal_gram_and_gap I P S δ hδ hδ1 hgap).2.2
  have hmul : δ * ε ≤ δ * markedFraction S :=
    mul_le_mul_of_nonneg_left hεS hδ.le
  nlinarith [hnorm, hmul, mul_nonneg hδ.le hε.le]

/-- The squared Euclidean norm of the sum of the unmarked initial state and its image after `K`
corrected marked walk steps. -/
noncomputable def ampK {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) (K : ℕ) : ℝ :=
  ‖toEuclidean_fromVec (detectionUnmarkedInitial P S +
    ((correctedMarkedWalk P S) ^ K) *ᵥ detectionUnmarkedInitial P S)‖ ^ 2

/-- For a symmetric chain with positive gap and marked fraction, at least a fraction `1 / 6` of
the prescribed walk times satisfy `ampK ≤ 3`. -/
theorem szegedyLemma3_amp_bound
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : SymmetricChainGap P δ)
    (hG : 0 < markedFraction S) :
    (1 / 6 : ℝ) ≤
      (∑ k : Fin (lemma3Length δ (markedFraction S)),
        if ampK P S (k.val + 1) ≤ 3 then (1 : ℝ) else 0) /
        ((lemma3Length δ (markedFraction S) : ℝ)) := by
  obtain ⟨hL, hcard⟩ := lemma3_threshold_event P S δ
    (lemma3Length δ (markedFraction S)) hδ hδ1 hgap hG rfl
  have hLpos : (0 : ℝ) < ((lemma3Length δ (markedFraction S) : ℝ)) := by
    exact_mod_cast hL
  have hmass : (1 / 6 : ℝ) ≤
      lemma3ThresholdMass (correctedMarkedWalk P S) (detectionUnmarkedInitial P S)
        (lemma3Length δ (markedFraction S)) := by
    unfold lemma3ThresholdMass
    rw [le_div_iff₀ hLpos]
    have hring : (1 / 6 : ℝ) * ((lemma3Length δ (markedFraction S) : ℝ)) =
        ((lemma3Length δ (markedFraction S) : ℝ)) / 6 := by ring
    rw [hring]
    exact hcard
  have hnum : ((Finset.univ.filter (fun k : Fin (lemma3Length δ (markedFraction S)) =>
        ampK P S (k.val + 1) ≤ 3)).card : ℝ) =
      ∑ k : Fin (lemma3Length δ (markedFraction S)),
        if ampK P S (k.val + 1) ≤ 3 then (1 : ℝ) else 0 := by
    rw [Finset.card_filter]
    push_cast
    simp
  rw [← hnum]
  unfold lemma3ThresholdMass at hmass
  simpa only [ampK] using! hmass

end Qatlib.Papers.QuantWalkSpec04.MainResults.Detection
