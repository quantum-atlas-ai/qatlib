/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.SignedReadout.Sampling
public import Qatlib.Concepts.QRAM.SignedReadout.EmbeddedReference
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDistTV
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.PureStateTV
public import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesExt

@[expose] public section

/-!
# Stability of a signed tomography basis shot

A normalized complex output may occupy additional workspace labels.
Reading a physical address is a deterministic function of the measured
basis label. The same function is applied to the ideal embedded real
state, which has zero amplitude outside the intended address labels.
The resulting shot laws have total variation bounded by the state error.
This supplies a workspace readout bound for the basis sampling used in
[KerenidisLandmanPrakash2020], Appendix G.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.QRAM.SignedReadout

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesExt (observe observe_mass)
open Qatlib.Foundations.PureStateMath (QState BornProb Normalized ApplyGate Inner bornProb_nonneg)
open Qatlib.Foundations.PureStateMath.BornBridge
  (relabelState toEuclidean_fromVec normalized_iff_norm_toEuclidean_fromVec inner_euclidean_fromVec)
open Qatlib.Foundations.QramData.SquaredNormTree (Address)
open scoped BigOperators Classical

/-- Deterministic relabeling cannot increase the sum of absolute mass differences. -/
private theorem push_mass_difference_le {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (p q : FinDist I) (label : I → J) :
    (∑ j, |(observe p label).prob j - (observe q label).prob j|) ≤
      ∑ i, |p.prob i - q.prob i| := by
  have hDiff (j : J) :
      (observe p label).prob j - (observe q label).prob j =
        ∑ i, if label i = j then p.prob i - q.prob i else 0 := by
    simp only [observe_mass, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  calc
    _ = ∑ j, |∑ i, if label i = j then p.prob i - q.prob i else 0| := by simp only [hDiff]
    _ ≤ ∑ j, ∑ i, |if label i = j then p.prob i - q.prob i else 0| :=
      Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [apply_ite abs, abs_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Apply a deterministic classical label function to the Born measurement of
a normalized quantum state. -/
def bornReadoutLaw {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (state : QState I) (hState : Normalized state) (label : I → J) : FinDist J :=
  observe ⟨BornProb state, bornProb_nonneg state, hState⟩ label

/-- Reading labels from normalized quantum states transfers their Euclidean
distance to a bound on the total variation of the resulting shot laws. -/
theorem born_readout_tv_le {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (state ideal : QState I) (hState : Normalized state) (hIdeal : Normalized ideal)
    (label : I → J) :
    tvDist (bornReadoutLaw state hState label) (bornReadoutLaw ideal hIdeal label) ≤
      ‖toEuclidean_fromVec (state - ideal)‖ := by
  have hBorn := pureState_born_tv_le_sqrt_fidelity (1 : Matrix I I ℂ)
    (Matrix.unitaryGroup I ℂ).one_mem state ideal hState hIdeal
  simp only [ApplyGate, Matrix.one_mulVec] at hBorn
  have hStateNorm := (normalized_iff_norm_toEuclidean_fromVec state).1 hState
  have hIdealNorm := (normalized_iff_norm_toEuclidean_fromVec ideal).1 hIdeal
  have hNorm : Real.sqrt (1 - ‖Inner state ideal‖ ^ 2) ≤ ‖toEuclidean_fromVec (state - ideal)‖ := by
    apply (Real.sqrt_le_left (norm_nonneg _)).2
    rw [show toEuclidean_fromVec (state - ideal) =
        toEuclidean_fromVec state - toEuclidean_fromVec ideal from rfl,
      norm_sub_sq (𝕜 := ℂ), inner_euclidean_fromVec, hStateNorm, hIdealNorm]
    change 1 - ‖Inner state ideal‖ ^ 2 ≤ (1 : ℝ) ^ 2 - 2 * (Inner state ideal).re + 1 ^ 2
    nlinarith [Complex.re_le_norm (Inner state ideal), sq_nonneg (‖Inner state ideal‖ - 1)]
  unfold tvDist
  refine (mul_le_mul_of_nonneg_left (push_mass_difference_le
    ⟨BornProb state, bornProb_nonneg state, hState⟩
    ⟨BornProb ideal, bornProb_nonneg ideal, hIdeal⟩ label) (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans ?_
  exact hBorn.trans hNorm

variable {depth : ℕ} {I : Type} [Fintype I] [DecidableEq I]

/-- Pad physical-address amplitudes with zeros and place them on the indicated labels. -/
def embeddedDirection (place : Address depth ↪ I) (direction : Address depth → ℝ) : QState I :=
  relabelState (referenceWorkspaceEquiv place) (Sum.elim (fun a => (direction a : ℂ)) 0)

omit [Fintype I] in
/-- Each embedded amplitude is the coefficient of the unique matching address,
with zero amplitude at all other workspace labels. -/
theorem embedded_direction_apply (place : Address depth ↪ I)
    (direction : Address depth → ℝ) (i : I) :
    embeddedDirection place direction i =
      ∑ a, if i = place a then (direction a : ℂ) else 0 := by
  let e := referenceWorkspaceEquiv place
  obtain ⟨v, rfl⟩ := e.surjective i
  change (Sum.elim (fun a => (direction a : ℂ)) 0) (e.symm (e v)) = _
  rw [Equiv.symm_apply_apply]
  have hAddress (a : Address depth) : e v = place a ↔ v = Sum.inl a := by
    rw [← reference_workspace_inl place a]
    exact e.injective.eq_iff
  simp_rw [hAddress]
  cases v <;> simp

/-- Read a placed address using the supplied default for the other workspace labels. -/
def readPlacedAddress (place : Address depth ↪ I) (fallback : Address depth) (i : I) :
    Address depth :=
  Sum.elim id (fun _ => fallback) ((referenceWorkspaceEquiv place).symm i)

omit [Fintype I] in
/-- A placed basis label recovers its physical address. -/
theorem read_placed_address (place : Address depth ↪ I) (fallback a : Address depth) :
    readPlacedAddress place fallback (place a) = a := by
  simp only [readPlacedAddress, ← reference_workspace_inl place a, Equiv.symm_apply_apply,
    Sum.elim_inl, id_eq]

/-- The zero-padded direction has the same total Born mass as the original direction. -/
theorem embedded_direction_normalized (place : Address depth ↪ I)
    (direction : Address depth → ℝ) (hDirection : ∑ a, direction a ^ 2 = 1) :
    Normalized (embeddedDirection place direction) := by
  let e := referenceWorkspaceEquiv place
  change ∑ i, BornProb (embeddedDirection place direction) i = 1
  rw [← e.sum_comp (BornProb (embeddedDirection place direction)), Fintype.sum_sum_type]
  simpa [embeddedDirection, e, relabelState, Function.comp_apply, BornProb,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] using hDirection

/-- A label function that recovers each placed address gives exactly the real
basis law when its input is the corresponding ideal embedded direction. -/
theorem embedded_direction_basis_law (place : Address depth ↪ I)
    (direction : Address depth → ℝ) (hDirection : ∑ a, direction a ^ 2 = 1)
    (label : I → Address depth) (hLabel : ∀ a, label (place a) = a) :
    bornReadoutLaw (embeddedDirection place direction)
      (embedded_direction_normalized place direction hDirection) label =
      basisSampleLaw direction hDirection := by
  let e := referenceWorkspaceEquiv place
  have hPlaced (a : Address depth) : label (e (Sum.inl a)) = a := hLabel a
  apply Qatlib.Concepts.ProbabilityCore.Concentration.FinDist.ext
  intro a
  rw [bornReadoutLaw, observe_mass]
  change (∑ i, if label i = a then BornProb (embeddedDirection place direction) i else 0) = direction a ^ 2
  rw [← e.sum_comp (fun i => if label i = a then BornProb (embeddedDirection place direction) i else 0),
    Fintype.sum_sum_type]
  simp only [hPlaced]
  simp [embeddedDirection, e, relabelState, BornProb,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The distance from the decoded state to the embedded ideal direction bounds
the error in the basis-shot law, allowing arbitrary labels for other outcomes. -/
theorem measured_basis_shot_tv_le (place : Address depth ↪ I)
    (state : QState I) (hState : Normalized state) (direction : Address depth → ℝ)
    (hDirection : ∑ a, direction a ^ 2 = 1) (label : I → Address depth)
    (hLabel : ∀ a, label (place a) = a) :
    tvDist (bornReadoutLaw state hState label) (basisSampleLaw direction hDirection) ≤
      ‖toEuclidean_fromVec (state - embeddedDirection place direction)‖ := by
  rw [← embedded_direction_basis_law place direction hDirection label hLabel]
  exact born_readout_tv_le state _ hState _ label

end Qatlib.Concepts.QRAM.SignedReadout
