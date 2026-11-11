/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TwoLevelLower
import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
import Qatlib.Concepts.SpectralFilter.PhaseReadout.CountedPhaseReflection
import Qatlib.Concepts.WalkFind.UniformThree.PhaseReflectionSearch
import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector
import Qatlib.Concepts.WalkSearch.ProjectorCS
import Qatlib.Concepts.WalkSearch.MultiBandFilter.MultiBandPhaseFilter
import Qatlib.Concepts.WalkSearch.MultiBandFilter.MultiBandFilterConsumers
import Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter.DegeneratePhaseFilter
import Qatlib.Concepts.WalkSearch.Spectral.Approximation
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
import Qatlib.Concepts.HspRecovery.SieveLaw.SharpSelectiveStability
import Qatlib.Concepts.WalkSearch.MnrsAmplify.Theorem3
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3
import Qatlib.Concepts.WalkSearch.ClassicalStop.SzegedyClassicalStopComparisonStat
import Qatlib.Concepts.HspRecovery.KitaevReadout.EigenphaseEstimateSubgoalQuan
import Qatlib.Concepts.HspRecovery.KitaevReadout.EigenphaseEstimateSubgoalStat

/-!
# Spectral filtering and absorbing walk specifications

This module defines the spectral bundles used for phase reflection, amplification, sine envelope
filtering, band selection, and postselection stability. It also introduces the absorbing walk,
its trap complement, and a threshold mass based on sampled walk powers.

`lemma3Length` chooses the natural ceiling of `1000 / sqrt (δ * ε)`. The threshold counting
argument gives a fraction of at least one sixth at this length, as required by
`WalkSpectralClause38FullEndpoint`. The quantum walk spectral framework is developed in
[Szegedy2004].

## Main statements

* `lemma3TrapComplement`: States vanishing on marked diagonal coordinates.
* `lemma3_threshold_event`: A lower bound on the number of sampled powers satisfying the
  threshold.
* `WalkSpectralClause38FullEndpoint`: The combined absorbing walk endpoint specification.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.WalkSearch.MultiBandFilter
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.HspRecovery.SieveLaw
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

open Matrix
open Qatlib
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkSearch.ClassicalStop
open Qatlib
open Qatlib.Concepts.HspRecovery.KitaevReadout
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- For `M ≥ 2`, positive phase gap `η`, and `M * η ≥ 1`, the sine envelope zero-label
probability is at most `10 / (M^2 * η^2)^2`. -/
theorem sin_envelope_zero_label_gap_bound (M : ℕ) (hM : 2 ≤ M) (φ η : ℝ)
    (hη : 0 < η) (hfar : 1 ≤ (M : ℝ) * η) (hgap : η ≤ phaseDistance φ 0) :
    ‖sinEnvelopeKernel M φ (⟨0, by omega⟩ : Fin M)‖^2 ≤
      10 / ((M : ℝ)^2 * η^2)^2 := by
  have h0z : (((⟨0, by omega⟩ : Fin M).val : ℝ) / (M : ℝ)) = 0 := by simp
  have hr : 1 / (M : ℝ) ≤ phaseDistance φ (((⟨0, by omega⟩ : Fin M).val : ℝ) / (M : ℝ)) := by
    rw [h0z]
    have h1 : 1 / (M : ℝ) ≤ η := by
      rw [div_le_iff₀ (by positivity)]
      linarith [hfar]
    exact h1.trans hgap
  have ht := sin_envelope_kernel_far_label_tail M φ ⟨0, by omega⟩ hM hr
  have hdist : η ≤ phaseDistance φ (((⟨0, by omega⟩ : Fin M).val : ℝ) / (M : ℝ)) := by
    rwa [h0z]
  have hdist4 : η^4 ≤ phaseDistance φ (((⟨0, by omega⟩ : Fin M).val : ℝ) / (M : ℝ))^4 := by
    have h0 : 0 ≤ η := by linarith
    exact pow_le_pow_left₀ h0 hdist 4
  have hdenom : (M : ℝ)^4 * η^4 ≤ (M : ℝ)^4 * phaseDistance φ (((⟨0, by omega⟩ : Fin M).val : ℝ) / (M : ℝ))^4 := by
    apply mul_le_mul_of_nonneg_left hdist4 (by positivity)
  have hle : 10 / ((M : ℝ)^4 * phaseDistance φ (((⟨0, by omega⟩ : Fin M).val : ℝ) / (M : ℝ))^4) ≤
      10 / ((M : ℝ)^4 * η^4) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hdenom
  have hrew : (M : ℝ)^4 * η^4 = ((M : ℝ)^2 * η^2)^2 := by ring
  rw [hrew] at hle
  exact ht.trans hle

/-- Making the states in `S` absorbing preserves the transition matrix property. -/
theorem absorbingKernel_isTransitionMatrix {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) (hP : IsTransitionMatrix P) :
    IsTransitionMatrix (absorbingKernel P S) := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · simp only [absorbingKernel]
    split_ifs <;> [norm_num; norm_num; exact hP.1 x y]
  · simp only [absorbingKernel]
    by_cases hx : x ∈ S
    · simp only [hx, ite_true]
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _ hy
        rw [if_neg (show ¬ (y = x) from hy)]
      · intro hcon
        exact absurd (Finset.mem_univ x) hcon
    · simp only [hx, ite_false]
      exact hP.2 x

/-- The condition that a state vanishes at `(i, i)` for every marked vertex `i`. -/
def lemma3TrapComplement {I : Type} [DecidableEq I] (S : Finset I)
    (z : QState (I × I)) : Prop := ∀ i ∈ S, z (i, i) = 0

/-- The Szegedy walk associated with the transition kernel obtained by making `S` absorbing. -/
noncomputable def lemma3AbsorbingWalk {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) : Matrix (I × I) (I × I) ℂ :=
  SzegedyWalk (absorbingKernel P S)

/-- The fraction of sampled powers `1, …, L` for which the squared Euclidean norm of `u + W^k u`
is at most three. -/
noncomputable def lemma3ThresholdMass {I : Type} [Fintype I] [DecidableEq I]
    (W : Matrix (I × I) (I × I) ℂ) (u : QState (I × I)) (L : ℕ) : ℝ :=
  ((Finset.univ.filter (fun k : Fin L =>
      ‖toEuclidean_fromVec (u + W ^ (k.val + 1) *ᵥ u)‖ ^ 2 ≤ 3)).card : ℝ) / (L : ℝ)

/-- The unmarked detection initial state vanishes at every marked diagonal coordinate. -/
theorem detectionUnmarkedInitial_trapComplement {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) :
    lemma3TrapComplement S (detectionUnmarkedInitial P S) := by
  intro i hi
  simp only [detectionUnmarkedInitial, collapse_apply]
  have hnot : ¬ ((i, i) ∈ Finset.univ.filter (fun xy : I × I => xy.1 ∉ S)) := by
    simp [hi]
  rw [if_neg hnot]

/-- The natural ceiling of `1000 / sqrt (δ * ε)`, used as the sampling length for the threshold
estimate. -/
noncomputable def lemma3Length (δ ε : ℝ) : ℕ := ⌈1000 / Real.sqrt (δ * ε)⌉₊

/-- For positive `δ` and `ε`, the sampling length is positive and lies between `1000 / sqrt (δ *
ε)` and that quantity plus one, with a strict upper bound. -/
theorem lemma3Length_bounds (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    let L := lemma3Length δ ε
    0 < L ∧
    1000 / Real.sqrt (δ * ε) ≤ (L : ℝ) ∧
    (L : ℝ) < 1000 / Real.sqrt (δ * ε) + 1 := by
  intro L
  have hpos : 0 < 1000 / Real.sqrt (δ * ε) := by
    have hde : 0 < δ * ε := mul_pos hδ hε
    positivity
  have h1 : 1000 / Real.sqrt (δ * ε) ≤ (L : ℝ) := Nat.le_ceil _
  have h2 : (L : ℝ) < 1000 / Real.sqrt (δ * ε) + 1 := Nat.ceil_lt_add_one hpos.le
  have h0 : 0 < L := by
    by_contra hc
    have hz : L = 0 := by omega
    rw [hz, Nat.cast_zero] at h1
    linarith
  exact ⟨h0, h1, h2⟩

/-- Under the stated average lower bound and pointwise upper bound, at least `L / 6` indices
satisfy `1 - 4 * a ≤ X k`. -/
private theorem lemma3_threshold_counting {L : ℕ} (X : Fin L → ℝ) (a η : ℝ)
    (hL : 0 < L) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hη : 0 ≤ η) (hη1 : η ≤ 1 / 1000)
    (havg : (∑ k : Fin L, X k) / (L : ℝ) ≥ 2 * (1 - η) * (1 - a))
    (hXle : ∀ k : Fin L, X k ≤ 4 * (1 - a)) :
    (L : ℝ) / 6 ≤
      (Finset.univ.filter (fun k : Fin L => 1 - 4 * a ≤ X k)).card := by
  have hLR : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  have hbad_le : (Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card ≤ L :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (by rw [Finset.card_univ, Fintype.card_fin])
  have hsplit : (∑ k ∈ Finset.univ \ Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a), X k)
        + (∑ k ∈ Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a), X k)
      = (∑ k : Fin L, X k) :=
    Finset.sum_sdiff (Finset.filter_subset _ _)
  have hcard_sub : (Finset.univ \ Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card
      = L - (Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
      Fintype.card_fin]
  have hsum_bad : (∑ k ∈ Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a), X k)
      ≤ ((Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card : ℝ) * (1 - 4 * a) := by
    have h := Finset.sum_le_card_nsmul
      (Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)) X (1 - 4 * a)
      (fun k hk => le_of_lt (Finset.mem_filter.mp hk).2)
    rwa [nsmul_eq_mul] at h
  have hsum_good : (∑ k ∈ Finset.univ \ Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a), X k)
      ≤ (((Finset.univ \ Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card : ℕ) : ℝ)
          * (4 * (1 - a)) := by
    have h := Finset.sum_le_card_nsmul
      (Finset.univ \ Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)) X (4 * (1 - a))
      (fun k _ => hXle k)
    rwa [nsmul_eq_mul] at h
  have hNge : (L : ℝ) * (2 * (1 - η) * (1 - a)) ≤ (∑ k : Fin L, X k) := by
    have h := (le_div_iff₀ hLR).mp havg
    nlinarith
  have hNle : (∑ k : Fin L, X k)
      ≤ (((Finset.univ \ Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card : ℕ) : ℝ)
          * (4 * (1 - a))
        + ((Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card : ℝ) * (1 - 4 * a) := by
    rw [← hsplit]
    exact add_le_add hsum_good hsum_bad
  have hexpand :
      (((Finset.univ \ Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card : ℕ) : ℝ)
          * (4 * (1 - a))
        + ((Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card : ℝ) * (1 - 4 * a)
      = 4 * (L : ℝ) * (1 - a)
          - 3 * ((Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card : ℝ) := by
    rw [hcard_sub, Nat.cast_sub hbad_le]
    ring
  have hcount : (L : ℝ) * (2 * (1 - η) * (1 - a))
      ≤ 4 * (L : ℝ) * (1 - a)
          - 3 * ((Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card : ℝ) :=
    hNge.trans (hNle.trans (le_of_eq hexpand))
  have hprod : (1 - a) * (1 + η) ≤ 5 / 4 := by
    have h1 : (1:ℝ) - a ≤ 1 := by linarith
    have h2 : 0 ≤ (1:ℝ) - a := by linarith
    have h3 : 0 ≤ (1:ℝ) + η := by linarith
    have h4 : (1 - a) * (1 + η) ≤ 1 * (1 + η) := by nlinarith
    have h5 : (1:ℝ) + η ≤ 1 + 1 / 1000 := by linarith
    have h6 : (1:ℝ) + 1 / 1000 ≤ 5 / 4 := by norm_num
    linarith
  have h3c : 3 * ((Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card : ℝ)
      ≤ 2 * (L : ℝ) * (1 - a) * (1 + η) := by
    have h : 4 * (L : ℝ) * (1 - a) - (L : ℝ) * (2 * (1 - η) * (1 - a))
        = 2 * (L : ℝ) * (1 - a) * (1 + η) := by ring
    linarith
  have hm := mul_le_mul_of_nonneg_left hprod
    (show (0:ℝ) ≤ 2 * (L : ℝ) by nlinarith)
  have h2L : (2:ℝ) * (L : ℝ) * ((1 - a) * (1 + η)) = 2 * (L : ℝ) * (1 - a) * (1 + η) := by ring
  have h2L5 : (2:ℝ) * (L : ℝ) * (5 / 4) = 5 / 2 * (L : ℝ) := by ring
  have h7 : 3 * ((Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card : ℝ)
      ≤ 5 / 2 * (L : ℝ) := by
    linarith
  have hdiv : ((Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card : ℝ)
      ≤ 5 / 2 * (L : ℝ) / 3 := by
    have hh := (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 3)).mpr h7
    have hc : (3:ℝ) * ((Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card : ℝ) / 3
        = ((Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card : ℝ) := by ring
    rwa [hc] at hh
  have h56 : (5:ℝ) / 2 * (L : ℝ) / 3 = 5 / 6 * (L : ℝ) := by ring
  have hcle : ((Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card : ℝ)
      ≤ 5 / 6 * (L : ℝ) := by
    rwa [← h56]
  have hset : Finset.univ.filter (fun k : Fin L => 1 - 4 * a ≤ X k)
      = Finset.univ \ Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_lt]
  have hgood : (Finset.univ.filter (fun k : Fin L => 1 - 4 * a ≤ X k)).card
      = L - (Finset.univ.filter (fun k : Fin L => X k < 1 - 4 * a)).card := by
    rw [hset, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
      Fintype.card_fin]
  rw [hgood, Nat.cast_sub hbad_le]
  linarith

/-- For a symmetric chain with positive gap and marked fraction, at least `L / 6` sampled powers
satisfy the squared norm threshold three when `L` is the prescribed sampling length
[Szegedy2004]. -/
theorem lemma3_threshold_event
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ : ℝ) (L : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : SymmetricChainGap P δ)
    (ha : 0 < markedFraction S) (hL : L = lemma3Length δ (markedFraction S)) :
    0 < L ∧
    (L : ℝ) / 6 ≤
      (Finset.univ.filter (fun k : Fin L =>
        ‖toEuclidean_fromVec (detectionUnmarkedInitial P S +
          (correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S)‖ ^ 2
          ≤ 3)).card := by
  have hIsTrans : IsTransitionMatrix P := hgap.1
  have ha0 : 0 ≤ markedFraction S := ha.le
  have ha1 : markedFraction S ≤ 1 := (markedFraction_mem_Icc S).2
  have hLb := lemma3Length_bounds δ (markedFraction S) hδ ha
  have hLpos : 0 < L := by rw [hL]; exact hLb.1
  have hLge : 1000 / Real.sqrt (δ * markedFraction S) ≤ (L : ℝ) := by rw [hL]; exact hLb.2.1
  have hbusy := corrected_szegedy_busy_random_power_difference I P S δ L hδ hδ1 hgap ha hLpos
  have hmass : ‖toEuclidean_fromVec (detectionUnmarkedInitial P S)‖ ^ 2 = 1 - markedFraction S :=
    hbusy.1
  have havg : (∑ k : Fin L, ‖toEuclidean_fromVec
        ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S -
          detectionUnmarkedInitial P S)‖ ^ 2) / (L : ℝ) ≥
      2 * (1 - 1 / ((L : ℝ) * Real.sqrt (δ * markedFraction S))) * (1 - markedFraction S) :=
    hbusy.2

  have hunit : correctedMarkedWalk P S ∈ unitaryGroup (I × I) ℂ :=
    correctedMarkedWalk_unitary P S hIsTrans
  have hpow (n : ℕ) : IsIsometry ((correctedMarkedWalk P S) ^ n) := by
    have h := (unitaryGroup (I × I) ℂ).pow_mem hunit n
    simpa only [IsIsometry, Matrix.star_eq_conjTranspose] using! h.1
  have hnorm (n : ℕ) :
      ‖toEuclidean_fromVec ((correctedMarkedWalk P S) ^ n *ᵥ detectionUnmarkedInitial P S)‖ =
        ‖toEuclidean_fromVec (detectionUnmarkedInitial P S)‖ :=
    isometry_mulVec_norm (hpow n) _

  have hpol (k : Fin L) :
      ‖toEuclidean_fromVec (detectionUnmarkedInitial P S +
          (correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S)‖ ^ 2 +
        ‖toEuclidean_fromVec ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ
          detectionUnmarkedInitial P S - detectionUnmarkedInitial P S)‖ ^ 2
      = 4 * (1 - markedFraction S) := by
    have hadd : toEuclidean_fromVec (detectionUnmarkedInitial P S +
            (correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S)
        = toEuclidean_fromVec (detectionUnmarkedInitial P S) +
          toEuclidean_fromVec ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ
            detectionUnmarkedInitial P S) := rfl
    have hsub : toEuclidean_fromVec ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ
            detectionUnmarkedInitial P S - detectionUnmarkedInitial P S)
        = toEuclidean_fromVec ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ
            detectionUnmarkedInitial P S) -
          toEuclidean_fromVec (detectionUnmarkedInitial P S) := rfl
    rw [hadd, hsub]
    have hrev : ‖toEuclidean_fromVec ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ
            detectionUnmarkedInitial P S) - toEuclidean_fromVec (detectionUnmarkedInitial P S)‖
        = ‖toEuclidean_fromVec (detectionUnmarkedInitial P S) -
            toEuclidean_fromVec ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ
              detectionUnmarkedInitial P S)‖ :=
      norm_sub_rev _ _
    rw [hrev, parallelogram_law_with_norm (𝕜 := ℂ), hnorm (k.val + 1), hmass]
    ring
  have hevt (k : Fin L) :
      (‖toEuclidean_fromVec (detectionUnmarkedInitial P S +
          (correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S)‖ ^ 2 ≤ 3)
      ↔ (1 - 4 * markedFraction S ≤
          ‖toEuclidean_fromVec ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ
            detectionUnmarkedInitial P S - detectionUnmarkedInitial P S)‖ ^ 2) := by
    have hp := hpol k
    constructor <;> intro h <;> linarith

  have hXle (k : Fin L) : ‖toEuclidean_fromVec
      ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S -
        detectionUnmarkedInitial P S)‖ ^ 2 ≤ 4 * (1 - markedFraction S) := by
    have htri : ‖toEuclidean_fromVec
        ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S -
          detectionUnmarkedInitial P S)‖ ≤
        ‖toEuclidean_fromVec ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ
          detectionUnmarkedInitial P S)‖ + ‖toEuclidean_fromVec (detectionUnmarkedInitial P S)‖ := by
      have hsub : toEuclidean_fromVec
          ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S -
            detectionUnmarkedInitial P S)
          = toEuclidean_fromVec ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ
              detectionUnmarkedInitial P S) -
            toEuclidean_fromVec (detectionUnmarkedInitial P S) := rfl
      rw [hsub]
      exact norm_sub_le _ _
    have hz := hnorm (k.val + 1)
    have hv := hmass
    have hnn : 0 ≤ ‖toEuclidean_fromVec (detectionUnmarkedInitial P S)‖ :=
      norm_nonneg _
    have hnn2 : 0 ≤ ‖toEuclidean_fromVec
        ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S -
          detectionUnmarkedInitial P S)‖ := norm_nonneg _
    have hle : ‖toEuclidean_fromVec
        ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S -
          detectionUnmarkedInitial P S)‖ ^ 2 ≤
        (‖toEuclidean_fromVec
          ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S)‖ +
          ‖toEuclidean_fromVec (detectionUnmarkedInitial P S)‖) ^ 2 :=
      pow_le_pow_left₀ hnn2 htri 2
    nlinarith [sq_nonneg (‖toEuclidean_fromVec (detectionUnmarkedInitial P S)‖)]

  have hη : (0:ℝ) ≤ 1 / ((L : ℝ) * Real.sqrt (δ * markedFraction S)) := by
    positivity
  have hη1 : (1:ℝ) / ((L : ℝ) * Real.sqrt (δ * markedFraction S)) ≤ 1 / 1000 := by
    have hsq : 0 < Real.sqrt (δ * markedFraction S) := Real.sqrt_pos.mpr (mul_pos hδ ha)
    have hLR : 0 < (L : ℝ) := Nat.cast_pos.mpr hLpos
    have h1000 : (1000:ℝ) ≤ (L : ℝ) * Real.sqrt (δ * markedFraction S) :=
      (div_le_iff₀ hsq).mp hLge
    apply (div_le_div_iff₀ (mul_pos hLR hsq) (by norm_num)).mpr
    linarith
  refine ⟨hLpos, ?_⟩
  have hcard_evt : (Finset.univ.filter (fun k : Fin L =>
        ‖toEuclidean_fromVec (detectionUnmarkedInitial P S +
          (correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S)‖ ^ 2 ≤ 3)).card
      = (Finset.univ.filter (fun k : Fin L =>
        1 - 4 * markedFraction S ≤
          ‖toEuclidean_fromVec ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ
            detectionUnmarkedInitial P S - detectionUnmarkedInitial P S)‖ ^ 2)).card :=
    congrArg Finset.card (Finset.filter_congr (fun k _ => hevt k))
  rw [hcard_evt]
  exact lemma3_threshold_counting
    (fun k : Fin L => ‖toEuclidean_fromVec
      ((correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S -
        detectionUnmarkedInitial P S)‖ ^ 2)
    (markedFraction S) (1 / ((L : ℝ) * Real.sqrt (δ * markedFraction S)))
    hLpos ha0 ha1 hη hη1 havg hXle

/-- The conjunction of reversible stationary state facts, Szegedy walk geometry and unitarity,
approximate phase reflection bounds, and phase reflection and search circuit counts. -/
def WalkSpectralClause6Prop : Prop :=
  (∀ {I : Type} [Fintype I] [DecidableEq I] {P : I → I → ℝ}
      (hP : IsTransitionMatrix P) {π : I → ℝ}
      (hπ : (∀ x, 0 ≤ π x) ∧ ∑ x, π x = 1) (hrev : IsReversible P π),
    IsStationary P π) ∧
  (∀ {I : Type} [Fintype I] [DecidableEq I] (P : I → I → ℝ)
      (hP : IsTransitionMatrix P) {π : I → ℝ} (hrev : IsReversible P π),
    SzegedyWalk P *ᵥ SzegedyEmbedState P π = SzegedyEmbedState P π) ∧
  (∀ {I : Type} [Fintype I] [DecidableEq I] (P : I → I → ℝ)
      (hP : IsTransitionMatrix P) {v : I → ℝ} (hv : ∀ x, 0 ≤ v x) (hsum : ∑ x, v x = 1),
    Normalized (SzegedyEmbedState P v)) ∧
  (∀ {I : Type} [Fintype I] [DecidableEq I] (P : I → I → ℝ) (hP : IsTransitionMatrix P),
    SzegedyWalk P = ReflectionAbout (SzegedyIsometryB P * (SzegedyIsometryB P)ᴴ) *
      ReflectionAbout (SzegedyIsometry P * (SzegedyIsometry P)ᴴ)) ∧
  (∀ {I : Type} [Fintype I] [DecidableEq I] (P : I → I → ℝ) (hP : IsTransitionMatrix P),
    SzegedyWalk P ∈ Matrix.unitaryGroup (I × I) ℂ) ∧
  (∀ {I : Type} [Fintype I] [DecidableEq I] (P : I → I → ℝ) (hP : IsTransitionMatrix P)
      (v : I → ℝ) (hv : ∑ i, v i ^ 2 = 1) (θ : ℝ) (hs : Real.sin θ ≠ 0)
      (hvD : SzegedyDiscriminant P *ᵥ v = (Real.cos θ) • v),
    ∃ (w₀ w₁ : QState (I × I)), Normalized w₀ ∧ Normalized w₁ ∧ Inner w₀ w₁ = 0 ∧
      SzegedyWalk P *ᵥ w₀
        = (((Real.cos (2 * θ) : ℝ)) : ℂ) • w₀ + (((Real.sin (2 * θ) : ℝ)) : ℂ) • w₁ ∧
      SzegedyWalk P *ᵥ w₁
        = (-(((Real.sin (2 * θ) : ℝ)) : ℂ)) • w₀ + (((Real.cos (2 * θ) : ℝ)) : ℂ) • w₁) ∧
  (∀ {I : Type} [Fintype I] [DecidableEq I] (J : Type) [Fintype J] [DecidableEq J]
      (j0 : J) (v : J → QState I) (p : J → ℝ) (W : Matrix I I ℂ) (M k : ℕ) (η : ℝ)
      (hM : 2 ≤ M) (hη : 0 < η) (hW : W ∈ Matrix.unitaryGroup I ℂ)
      (hv : ∀ a b, Inner (v a) (v b) = if a = b then 1 else 0)
      (heigen : ∀ a, ApplyGate W (v a) = Complex.exp (2 * Real.pi * Complex.I * p a) • v a)
      (hp0 : p j0 = 0) (hgap : ∀ a, a ≠ j0 → η ≤ phaseDistance (p a) 0) (c : J → ℂ),
    let ψ := ∑ a, c a • v a
    ‖toEuclidean_fromVec (phaseReflectionState W M k ψ -
      phaseReflectionEmbed M k (ApplyGate (ReflectionAbout (outerProduct (v j0))) ψ))‖ ≤
        2 * (1 / (2 * (M : ℝ) * η)) ^ k * ‖toEuclidean_fromVec ψ‖) ∧
  (∀ (M k : ℕ) (hM : 2 ≤ M),
    WellFormedAdjointCircuit (phaseReflectionWord (I := Unit) M k) ∧
      adjointQueryCount (phaseReflectionWord (I := Unit) M k) = 2 * k * (M - 1) ∧
      adjointGateCount (phaseReflectionWord (I := Unit) M k) = 4 * k * (M - 1) + 4 * k + 1) ∧
  (∀ (M k t : ℕ) (hM : 2 ≤ M),
    phaseSearchLedger M k t = (2 * k * t * (M - 1), t, 1))

/-- The conjunction of local amplification, its explicit cost bound, approximate phase search
success and norm preservation, and the phase search ledger. -/
def WalkSpectralClause32Prop : Prop :=
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3.{0} ∧
  (∀ (ε c₁ c₂ U C δ : ℝ) (tMax : ℕ)
      (hε : 0 < ε) (hε1 : ε ≤ 1) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
      (hmax : (3 : ℝ)^tMax*Real.arcsin (Real.sqrt ε) ≤ 3*Real.pi/4)
      (hδ : 0 < δ) (hC : 0 ≤ C) (hcU : c₁ ≤ 2*U/Real.sqrt δ) (hcc : c₂ ≤ C),
    2*(3 : ℝ)^tMax*(c₁*(Real.log 72+3)+c₂) ≤
      99*(1/Real.sqrt ε)*((1/Real.sqrt δ)*U+C)) ∧
  (∀ {I : Type} [Fintype I] [DecidableEq I] (J : Type) [Fintype J] [DecidableEq J]
      (j0 : J) (v : J → QState I) (p : J → ℝ) (W : Matrix I I ℂ) (S : Finset I)
      (M k t : ℕ) (η θ : ℝ) (hM : 2 ≤ M) (hη : 0 < η)
      (hW : W ∈ Matrix.unitaryGroup I ℂ)
      (hv : ∀ a b, Inner (v a) (v b) = if a = b then 1 else 0)
      (heigen : ∀ a, ApplyGate W (v a) = Complex.exp (2 * Real.pi * Complex.I * p a) • v a)
      (hp0 : p j0 = 0) (hgap : ∀ a, a ≠ j0 → η ≤ phaseDistance (p a) 0)
      (hmark : ∀ c : J → ℂ, ∃ d : J → ℂ,
        ApplyGate (preparedMark S) (∑ a, c a • v a) = ∑ a, d a • v a)
      (hθ : 0 < θ) (hθ1 : θ < Real.pi / 2) (hp : MeasureProb (v j0) S = (Real.sin θ) ^ 2),
    MeasureProb (phaseSearchState W (v j0) S M k t)
      (Finset.univ.filter (fun q => q.2.2 ∈ S)) ≥
      (Real.sin ((2 * (t : ℝ) + 1) * θ)) ^ 2 -
        4 * (t : ℝ) * (1 / (2 * (M : ℝ) * η)) ^ k) ∧
  (∀ {I : Type} [Fintype I] [DecidableEq I] (W : Matrix I I ℂ) (ψ : QState I)
      (S : Finset I) (M k t : ℕ) (hW : W ∈ Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M),
    ‖toEuclidean_fromVec (phaseSearchState W ψ S M k t)‖ =
      ‖toEuclidean_fromVec ψ‖) ∧
  (∀ (M k t : ℕ) (hM : 2 ≤ M),
    phaseSearchLedger M k t = (2 * k * t * (M - 1), t, 1))

/-- The conjunction of sine envelope preparation and probability tail bounds with the specified
forward, HHL, and amplified query estimates. -/
def WalkSpectralClause33Prop : Prop :=
  (∀ (M : ℕ) (hM : 2 ≤ M),
    (∑ τ, ‖sinEnvelopeState M τ‖^2 = 1) ∧
      sinEnvelopePrep M hM ∈ Matrix.unitaryGroup (Fin M) ℂ ∧
      sinEnvelopePrep M hM *ᵥ Ket (⟨0, by omega⟩ : Fin M) = sinEnvelopeState M) ∧
  (∀ (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 2 ≤ M)
      (hr : 1/(M:ℝ) ≤ phaseDistance φ ((z.val:ℝ)/(M:ℝ))),
    ‖sinEnvelopeKernel M φ z‖^2 ≤
      10/((M:ℝ)^4*phaseDistance φ ((z.val:ℝ)/(M:ℝ))^4)) ∧
  (∀ (M : ℕ) (hM : 2 ≤ M) (φ η : ℝ)
      (hη : 0 < η) (hfar : 1 ≤ (M : ℝ) * η) (hgap : η ≤ phaseDistance φ 0),
    ‖sinEnvelopeKernel M φ (⟨0, by omega⟩ : Fin M)‖^2 ≤
      10 / ((M : ℝ)^2 * η^2)^2) ∧
  (∀ {I : Type} [Fintype I] [DecidableEq I] (M : ℕ) (hM : 2 ≤ M),
    adjointQueryCount (sinEnvelopeForwardWord (I := I) M hM) = M - 1 ∧
      adjointGateCount (sinEnvelopeForwardWord (I := I) M hM) = 2 * (M - 1) + 2) ∧
  (∀ (D M : ℕ) (hM : 2 ≤ M) (d : ℝ) (hd : 0 < d) (B U : Operator D)
      (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ)
      (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ),
    WellFormedAdjointCircuit (sinEnvelopeHHLWord M hM d B) ∧
      evaluate (sinEnvelopeOracleLift (D := D) (M := M) U) (sinEnvelopeHHLWord M hM d B)
        ∈ Matrix.unitaryGroup _ ℂ ∧
      adjointQueryCount (sinEnvelopeHHLWord M hM d B) = 2 * (M - 1) ∧
      adjointGateCount (sinEnvelopeHHLWord M hM d B) = 4 * (M - 1) + 6) ∧
  (∀ (M : ℕ) (hM : 2 ≤ M) (d : ℝ) (k : ℕ)
      (hk : k ≤ Nat.ceil (1 / (5 * d)) + 1),
    (2 * (k : ℝ) + 1) * (2 * ((M : ℝ) - 1)) + (k : ℝ) ≤
      (2 * ((Nat.ceil (1 / (5 * d)) : ℝ) + 1) + 1) * (2 * (M : ℝ)) +
        ((Nat.ceil (1 / (5 * d)) : ℝ) + 1))

/-- The conjunction of phase band classification, accepted and reflected state error estimates,
normalized branch guarantees, band sign unitarity, and reflection circuit counts. -/
def WalkSpectralTunableQueryProp : Prop :=
  (∀ (J : Type) [Fintype J] [DecidableEq J] (M : ℕ) (bands : List (ℚ × ℚ))
      (phi : J → ℝ) (eta : ℝ), 2 ≤ M → 0 < eta → eta ≤ 1/16 →
      (∀ j, |phi j| ≤ 1/4) → (∀ b ∈ bands, -1/4 ≤ (b.1:ℝ) ∧ (b.2:ℝ) ≤ 1/4) →
      (∀ j b, b∈bands → ((b.1:ℝ)+2*eta ≤ phi j ∧ phi j ≤ (b.2:ℝ)-2*eta) ∨
        (phi j ≤ (b.1:ℝ)-2*eta ∨ (b.2:ℝ)+2*eta ≤ phi j)) →
      bandClassificationGap M (bandLabels M bands) phi
        (Finset.univ.filter (fun j => bandContains bands (phi j))) eta) ∧
  (∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (U : Matrix I I ℂ) (M : ℕ) (hM : 2 ≤ M) (S : Finset (Fin M)) (v : J → QState I)
      (c : J → ℂ) (phi : J → ℝ) (T : Finset J) (eta : ℝ),
      U∈Matrix.unitaryGroup I ℂ → 0 < eta → eta ≤ 1/2 → bandClassificationGap M S phi T eta →
      (∀ j l, Inner (v j) (v l)=if j=l then 1 else 0) → (∑ j, ‖c j‖^2)=1 →
      (∀ j, U*ᵥ v j=Complex.exp (2*Real.pi*Complex.I*(phi j:ℂ)) • v j) →
    ‖toEuclidean_fromVec (bandAccepted U M (by omega) S (∑ j,c j • v j)-
      bandEmbed M (by omega) (spectralTargetState v c T))‖ ≤ 1/(2*Real.sqrt M*eta)) ∧
  (∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (U : Matrix I I ℂ) (M : ℕ) (hM : 2 ≤ M) (S : Finset (Fin M)) (v : J → QState I)
      (c : J → ℂ) (phi : J → ℝ) (T : Finset J) (eta : ℝ),
      U∈Matrix.unitaryGroup I ℂ → 0 < eta → eta ≤ 1/2 → bandClassificationGap M S phi T eta →
      (∀ j l, Inner (v j) (v l)=if j=l then 1 else 0) → (∑ j, ‖c j‖^2)=1 →
      (∀ j, U*ᵥ v j=Complex.exp (2*Real.pi*Complex.I*(phi j:ℂ)) • v j) →
    ‖toEuclidean_fromVec (bandReflected U M (by omega) S (∑ j,c j • v j)-
      bandEmbed M (by omega) (∑ j,(if j∈T then c j else -c j) • v j))‖ ≤ 1/(Real.sqrt M*eta)) ∧
  (∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (U : Matrix I I ℂ) (M : ℕ) (hM : 2 ≤ M) (S : Finset (Fin M)) (v : J → QState I)
      (c : J → ℂ) (phi : J → ℝ) (T : Finset J) (eta : ℝ),
      U∈Matrix.unitaryGroup I ℂ → 0 < eta → eta ≤ 1/2 → bandClassificationGap M S phi T eta →
      (∀ j l, Inner (v j) (v l)=if j=l then 1 else 0) → (∑ j, ‖c j‖^2)=1 →
      (∀ j, U*ᵥ v j=Complex.exp (2*Real.pi*Complex.I*(phi j:ℂ)) • v j) →
      let a := ∑ j∈T, ‖c j‖^2
      let e := 1/(2*Real.sqrt M*eta)
      let z := bandAccepted U M (by omega) S (∑ j,c j • v j)
      e < Real.sqrt a → (Real.sqrt a-e)^2 ≤ ‖toEuclidean_fromVec z‖^2 ∧
      ‖NormedSpace.normalize (toEuclidean_fromVec z)-
        NormedSpace.normalize (toEuclidean_fromVec (bandEmbed M (by omega) (spectralTargetState v c T)))‖ ≤
        2*e/Real.sqrt a) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (M : ℕ) (S : Finset (Fin M)),
    bandSign (I := I) M S ∈ Matrix.unitaryGroup _ ℂ) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (M : ℕ) (S : Finset (Fin M)), 2 ≤ M →
    WellFormedAdjointCircuit (bandReflectionWord (I:=I) M S) ∧
      adjointQueryCount (bandReflectionWord (I:=I) M S) = 2*(M-1) ∧
      adjointGateCount (bandReflectionWord (I:=I) M S) = 4 * (M - 1) + 5)

/-- The conjunction of band reflection perturbation bounds, accepted branch mass and
normalization estimates, and norm and isometry properties of orthonormal basis columns. -/
def WalkSpectralOptimizedTunableProp : Prop :=
  (∀ (I : Type) [Fintype I] [DecidableEq I] (M : ℕ) (hM : 2 ≤ M) (S : Finset (Fin M))
      (U W : Matrix I I ℂ) (psi : QState I),
    U∈Matrix.unitaryGroup I ℂ → W∈Matrix.unitaryGroup I ℂ → Normalized psi →
    ‖toEuclidean_fromVec (bandReflected U M (by omega) S psi-bandReflected W M (by omega) S psi)‖ ≤
      2*(M-1)*‖U-W‖) ∧
  (∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (U : Matrix I I ℂ) (M : ℕ) (hM : 2 ≤ M) (S : Finset (Fin M)) (v : J → QState I)
      (c : J → ℂ) (phi : J → ℝ) (T : Finset J) (eta : ℝ),
      U∈Matrix.unitaryGroup I ℂ → 0 < eta → eta ≤ 1/2 → bandClassificationGap M S phi T eta →
      (∀ j l, Inner (v j) (v l)=if j=l then 1 else 0) → (∑ j, ‖c j‖^2)=1 →
      (∀ j, U*ᵥ v j=Complex.exp (2*Real.pi*Complex.I*(phi j:ℂ)) • v j) →
      let a := ∑ j∈T, ‖c j‖^2
      let e := 1/(2*Real.sqrt M*eta)
      let z := bandAccepted U M (by omega) S (∑ j,c j • v j)
      e < Real.sqrt a → (Real.sqrt a-e)^2 ≤ ‖toEuclidean_fromVec z‖^2 ∧
      ‖NormedSpace.normalize (toEuclidean_fromVec z)-
        NormedSpace.normalize (toEuclidean_fromVec (bandEmbed M (by omega) (spectralTargetState v c T)))‖ ≤
        2*e/Real.sqrt a) ∧
  (∀ (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I)),
    ‖basisColumns b‖ ≤ 1) ∧
  (∀ (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I)),
    (basisColumns b)ᴴ * basisColumns b = 1)

/-- Selective outcome probability and normalized positive branch stability estimates in trace
norm for equal-trace positive inputs, allowing an arbitrary reference system. -/
def WalkSpectralClause36Prop : Prop :=
  (∀ {O : Type} [Fintype O] {D E R : ℕ} (J : Instrument O D E) (S : Finset O)
      (ρ τ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ)
      (hρ : ρ.PosSemidef) (hτ : τ.PosSemidef)
      (hequal : (Matrix.trace ρ).re = (Matrix.trace τ).re),
    |(Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re
        - (Matrix.trace (tensorLeft (selectiveMap J S) τ)).re|
      ≤ Matrix.traceNorm (ρ - τ) / 2) ∧
  (∀ (O : Type) [Fintype O] (D E R : ℕ) (J : Instrument O D E) (S : Finset O)
      (ρ τ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ),
      ρ.PosSemidef → τ.PosSemidef → (Matrix.trace ρ).re = (Matrix.trace τ).re →
      let A := tensorLeft (selectiveMap J S) ρ
      let B := tensorLeft (selectiveMap J S) τ
      0 < (Matrix.trace A).re → 0 < (Matrix.trace B).re →
      Matrix.traceNorm (normalizedPositiveBranch A - normalizedPositiveBranch B) ≤
        Matrix.traceNorm (ρ - τ) / max (Matrix.trace A).re (Matrix.trace B).re) ∧
  (∀ {O : Type} [Fintype O] {D E R : ℕ} (J : Instrument O D E) (S : Finset O)
      (ρ τ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) (η : ℝ),
      ρ.PosSemidef → τ.PosSemidef → (Matrix.trace ρ).re = (Matrix.trace τ).re →
      0 ≤ η → Matrix.traceNorm (ρ - τ) ≤ η →
      η / 2 < (Matrix.trace (tensorLeft (selectiveMap J S) τ)).re →
      0 < (Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re ∧
      Matrix.traceNorm (normalizedPositiveBranch (tensorLeft (selectiveMap J S) ρ)
        - normalizedPositiveBranch (tensorLeft (selectiveMap J S) τ)) ≤
        η / (Matrix.trace (tensorLeft (selectiveMap J S) τ)).re)

/-- The conjunction of degenerate zero phase detection probability and postselection bounds,
postmeasurement norm control, and phase kernel expansions. -/
def WalkSpectralClause37Prop : Prop :=
  (∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (W : Matrix I I ℂ) (M k : ℕ) (hM : 2 ≤ M) (v : J → QState I) (c : J → ℂ)
      (φ : J → ℝ) (T : Finset J) (η : ℝ),
      W ∈ Matrix.unitaryGroup I ℂ → 0 < η →
      (∀ j l, Inner (v j) (v l) = if j = l then 1 else 0) →
      (∑ j, ‖c j‖ ^ 2) = 1 →
      (∀ j, W *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ)) • v j) →
      (∀ j ∈ T, phaseDistance (φ j) 0 = 0) →
      (∀ j, j ∉ T → η ≤ phaseDistance (φ j) 0) →
    let ψ := ∑ j, c j • v j
    let a := ∑ j ∈ T, ‖c j‖ ^ 2
    let p := MeasureProb (degenerateDetectionState W M k ψ) (phaseZeroEvent M k)
    a ≤ p ∧ p ≤ a + (1 / (2 * (M : ℝ) * η)) ^ (2 * k) * (1 - a) ∧
      ‖toEuclidean_fromVec (degenerateZeroBranch W M k (by omega) ψ -
        spectralTargetState v c T)‖ ≤
        (1 / (2 * (M : ℝ) * η)) ^ k * Real.sqrt (1 - a)) ∧
  (∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (W : Matrix I I ℂ) (M k : ℕ) (hM : 2 ≤ M) (v : J → QState I) (c : J → ℂ)
      (φ : J → ℝ) (T : Finset J) (η : ℝ) (hW : W ∈ Matrix.unitaryGroup I ℂ)
      (hη : 0 < η) (hv : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
      (hc : (∑ j, ‖c j‖ ^ 2) = 1)
      (he : ∀ j, W *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ)) • v j)
      (ht : ∀ j ∈ T, phaseDistance (φ j) 0 = 0)
      (hg : ∀ j, j ∉ T → η ≤ phaseDistance (φ j) 0),
    let a := ∑ j ∈ T, ‖c j‖ ^ 2
    0 < a → ‖toEuclidean_fromVec
      (PostMeasure (degenerateZeroBranch W M k (by omega) (∑ j, c j • v j)) Finset.univ -
        PostMeasure (spectralTargetState v c T) Finset.univ)‖ ≤
      2 * (1 / (2 * (M : ℝ) * η)) ^ k * Real.sqrt (1 - a) / Real.sqrt a) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (ψ : QState I) (S : Finset I),
    ‖toEuclidean_fromVec (PostMeasure ψ S)‖ ≤ 1) ∧
  (∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (W : Matrix I I ℂ) (M k : ℕ) (hM : 0 < M)
      (v : J → QState I) (c : J → ℂ) (φ : J → ℝ)
      (he : ∀ j, W *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ)) • v j),
    degenerateDetectionState W M k (∑ j, c j • v j) =
        ∑ j, c j • phaseKernelPacket M k (φ j) (v j) ∧
      degenerateZeroBranch W M k hM (∑ j, c j • v j) =
        ∑ j, (c j * (qpeKernel M (φ j) (⟨0, hM⟩ : Fin M)) ^ k) • v j)

/-- The conjunction of the corrected walk random power estimate, unmarked initial state and
absorbing kernel properties, sampling length bounds, and the threshold event count. -/
def WalkSpectralClause38Prop : Prop :=
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (P : I→I→ℝ) (S : Finset I) (δ : ℝ) (L : ℕ),
    0<δ → δ≤1 → SymmetricChainGap P δ → 0 < markedFraction S → 0<L →
    ‖toEuclidean_fromVec (detectionUnmarkedInitial P S)‖^2=1-markedFraction S ∧
    (∑ k : Fin L,‖toEuclidean_fromVec
      ((correctedMarkedWalk P S)^(k.val+1)*ᵥdetectionUnmarkedInitial P S-
        detectionUnmarkedInitial P S)‖^2)/(L:ℝ) ≥
      2*(1-1/((L:ℝ)*Real.sqrt (δ*markedFraction S)))*(1-markedFraction S)) ∧
  (∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (P : I → I → ℝ) (S : Finset I)
      (hP : IsTransitionMatrix P),
    ‖toEuclidean_fromVec (detectionUnmarkedInitial P S)‖^2 = 1 - markedFraction S) ∧
  (∀ {I : Type} [Fintype I] [DecidableEq I] (P : I → I → ℝ) (S : Finset I),
    lemma3TrapComplement S (detectionUnmarkedInitial P S)) ∧
  (∀ {I : Type} [Fintype I] [DecidableEq I] (P : I → I → ℝ) (S : Finset I)
      (hP : IsTransitionMatrix P),
    IsTransitionMatrix (absorbingKernel P S)) ∧
  (∀ (δ ε : ℝ), 0 < δ → 0 < ε →
    let L := lemma3Length δ ε
    0 < L ∧
    1000 / Real.sqrt (δ * ε) ≤ (L : ℝ) ∧
    (L : ℝ) < 1000 / Real.sqrt (δ * ε) + 1) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (P : I → I → ℝ) (S : Finset I) (δ : ℝ) (L : ℕ),
    0 < δ → δ ≤ 1 → SymmetricChainGap P δ → 0 < markedFraction S →
      L = lemma3Length δ (markedFraction S) →
    0 < L ∧
    (L : ℝ) / 6 ≤
      (Finset.univ.filter (fun k : Fin L =>
        ‖toEuclidean_fromVec (detectionUnmarkedInitial P S +
          (correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S)‖ ^ 2
          ≤ 3)).card)

/-- The absorbing walk endpoint statement for marked fraction at most `1 / 8`, requiring the
trap complement bridge, initial mass and length bounds, and threshold mass at least `1 / 6`
for both walks. -/
def WalkSpectralClause38FullEndpoint : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ : ℝ),
    0 < δ → δ ≤ 1 → SymmetricChainGap P δ →
    0 < markedFraction S → markedFraction S ≤ 1 / 8 →
    let ε := markedFraction S
    let L := lemma3Length δ ε
    let u := detectionUnmarkedInitial P S
    IsTransitionMatrix (absorbingKernel P S) ∧
    lemma3TrapComplement S u ∧
    (∀ z : QState (I × I), lemma3TrapComplement S z →
      ∀ K : ℕ,
        lemma3TrapComplement S ((lemma3AbsorbingWalk P S) ^ K *ᵥ z) ∧
        (lemma3AbsorbingWalk P S) ^ K *ᵥ z =
          (correctedMarkedWalk P S) ^ K *ᵥ z) ∧
    ‖toEuclidean_fromVec u‖ ^ 2 = 1 - ε ∧
    0 < L ∧
    1000 / Real.sqrt (δ * ε) ≤ (L : ℝ) ∧
    (L : ℝ) < 1000 / Real.sqrt (δ * ε) + 1 ∧
    (1 / 6 : ℝ) ≤ lemma3ThresholdMass (correctedMarkedWalk P S) u L ∧
    (1 / 6 : ℝ) ≤ lemma3ThresholdMass (lemma3AbsorbingWalk P S) u L

/-- The conjunction of the eigenphase estimation subgoal, exact controlled power action on
root-of-unity eigenstates, and a bound on phase decoding failure. -/
def WalkSpectralClause39Prop : Prop :=
  EigenphaseEstimateSubgoal ∧
  (∀ {M : ℕ} {I : Type} [Fintype I] [DecidableEq I] {U : Matrix I I ℂ}
      {ψ : QState I} {k : ℕ} (hψ : U *ᵥ ψ = (primRoot M ^ ((k : ℤ))) • ψ),
    ControlledPowers U M *ᵥ TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ
      = TensorState (PhaseState M k) ψ) ∧
  (∀ (δ ε : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hε : 0 < ε) (hε1 : ε < 1)
      (I : Type) [Fintype I] [DecidableEq I] (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ)
      (heig : U *ᵥ ψ = eigenPhase φ • ψ) (s : ℕ)
      (hs : 36 * Real.log (4 / ε) / (Real.sin (Real.pi * δ)) ^ 2 ≤ s),
    (eigenphaseSampleLaw φ s).probEvent (L := 1)
        (fun ω => ¬ ∃ m : ℤ, |eigenphaseDecode s (ω 0) - φ + m| ≤ δ) ≤ ε)

end Qatlib.Concepts.WalkSearch.FrameSpectral
