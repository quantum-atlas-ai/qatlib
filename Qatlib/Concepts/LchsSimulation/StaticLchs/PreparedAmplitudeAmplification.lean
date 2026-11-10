/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedQueryCircuit
import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError
import Qatlib.Concepts.LchsSimulation.StaticLchs.ReadoutError
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
open Qatlib.Foundations.PureStateMath.Reflection
set_option warningAsError false
open Qatlib.Concepts.PhaseGeometry.Phase

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Foundations.PureStateMath.BornBridge


namespace Qatlib.Concepts.LchsSimulation.StaticLchs

open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open scoped Matrix.Norms.L2Operator

noncomputable def preparedAAState {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) : QState I := ApplyGate A (Ket j₀)

noncomputable def preparedMark {I : Type} [Fintype I] [DecidableEq I] (S : Finset I) :
    Matrix I I ℂ := 1 - (2 : ℂ) • Projector S

noncomputable def preparedAAIterate {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) : Matrix I I ℂ :=
  A * ReflectionAbout (outerProduct (Ket j₀)) * Aᴴ * preparedMark S

noncomputable def preparedAACircuit {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (k : ℕ) : Circuit I :=
  [Step.gate A] ++ RepeatCircuit
    [Step.query, Step.gate Aᴴ, Step.gate (ReflectionAbout (outerProduct (Ket j₀))),
      Step.gate A] k

noncomputable def preparedAAWord {I : Type} [Fintype I] [DecidableEq I] (j₀ : I) (k : ℕ) :
    List (PreparedStep I) :=
  (List.replicate k
    [PreparedStep.prepareForward, .gate (ReflectionAbout (outerProduct (Ket j₀))),
      .prepareBackward, .dataForward]).flatten ++ [.prepareForward]

section Helpers

variable {I : Type} [Fintype I] [DecidableEq I]

private theorem inner_add_left' (ψ φ χ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (ψ + φ) χ = Qatlib.Foundations.PureStateMath.Inner ψ χ + Qatlib.Foundations.PureStateMath.Inner φ χ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.add_apply, Pi.star_apply, RCLike.star_def, map_add,
    add_mul, Finset.sum_add_distrib]

private theorem inner_neg_right' (ψ φ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner ψ (-φ) = -(Qatlib.Foundations.PureStateMath.Inner ψ φ) := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem inner_conj_symm' (ψ φ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner ψ φ = star (Qatlib.Foundations.PureStateMath.Inner φ ψ) := by
  rw [inner_apply, inner_apply, star_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Complex.star_def, map_mul, starRingEnd_self_apply, mul_comm]

private theorem inner_mulVec_conjTranspose_right' (A : Matrix I I ℂ) (ψ φ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner ψ (A *ᵥ φ) = Qatlib.Foundations.PureStateMath.Inner (Aᴴ *ᵥ ψ) φ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner]
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

private theorem outerProduct_conj (A : Matrix I I ℂ) (φ : QState I) :
    A * outerProduct φ * Aᴴ = outerProduct (A *ᵥ φ) := by
  ext i j
  simp only [outerProduct, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    starRingEnd_apply, Matrix.mulVec, dotProduct]
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  conv_rhs => rw [star_mul]
  ring

private theorem applyGate_outerProduct (ψ φ : QState I) :
    ApplyGate (outerProduct ψ) φ = Qatlib.Foundations.PureStateMath.Inner ψ φ • ψ :=
  outerProduct_mulVec ψ φ

private theorem collapse_mulVec (x : QState I) (S : Finset I) :
    Collapse x S = (Projector S) *ᵥ x := rfl

private theorem applyGate_add (U : Matrix I I ℂ) (x y : QState I) :
    ApplyGate U (x + y) = ApplyGate U x + ApplyGate U y := Matrix.mulVec_add U x y

private theorem applyGate_smul (U : Matrix I I ℂ) (c : ℂ) (x : QState I) :
    ApplyGate U (c • x) = c • ApplyGate U x := Matrix.mulVec_smul U c x

private theorem preparedMark_unitary (S : Finset I) :
    preparedMark S ∈ Matrix.unitaryGroup I ℂ := by
  have hR : ReflectionAbout (Projector S) ∈ Matrix.unitaryGroup I ℂ :=
    reflectionAbout_unitary (projector_isOrthogonalProjector S)
  have hneg : preparedMark S = -(ReflectionAbout (Projector S)) := by
    unfold preparedMark ReflectionAbout
    module
  rw [hneg, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_neg, neg_mul_neg]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hR
  exact hR

private theorem preparedMark_apply (S : Finset I) (x : QState I) :
    ApplyGate (preparedMark S) x = x - (2 : ℂ) • Collapse x S := by
  simp only [ApplyGate, preparedMark, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Collapse]

private theorem normalized_preparedAAState (A : Matrix I I ℂ) (j₀ : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) : Normalized (preparedAAState A j₀) :=
  normalized_applyGate hA (normalized_ket j₀)

private theorem unitary_mul_conjTranspose {A : Matrix I I ℂ}
    (hA : A ∈ Matrix.unitaryGroup I ℂ) : A * Aᴴ = 1 := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hA
  exact mul_eq_one_comm.mp hA

private theorem compl_projector (S : Finset I) : 1 - Projector S = Projector Sᶜ := by
  ext i j
  simp only [Matrix.one_apply, Matrix.sub_apply]
  by_cases h : i = j
  · subst h
    simp only [Projector, Matrix.diagonal_apply]
    by_cases hs : i ∈ S <;> simp [hs, Finset.mem_compl]
  · simp [Projector, h]

private theorem projector_mul_compl (S : Finset I) : Projector S * Projector Sᶜ = 0 := by
  rw [← compl_projector, mul_sub, mul_one, projector_mul_self, sub_self]

private theorem projector_compl_mul (S : Finset I) : Projector Sᶜ * Projector S = 0 := by
  rw [← compl_projector, sub_mul, one_mul, projector_mul_self, sub_self]

private theorem collapse_idem (ψ : QState I) (S : Finset I) :
    Collapse (Collapse ψ S) S = Collapse ψ S := by
  rw [collapse_mulVec, collapse_mulVec, Matrix.mulVec_mulVec, projector_mul_self]

private theorem collapse_sub (ψ : QState I) (S : Finset I) :
    Collapse (ψ - Collapse ψ S) S = 0 := by
  rw [collapse_mulVec, collapse_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    projector_mul_self, sub_self]

private theorem collapse_compl (ψ : QState I) (S : Finset I) :
    ψ - Collapse ψ S = Collapse ψ Sᶜ := by
  rw [collapse_mulVec, collapse_mulVec, ← compl_projector, Matrix.sub_mulVec,
    Matrix.one_mulVec]

private theorem inner_bad_good (ψ : QState I) (S : Finset I) :
    Qatlib.Foundations.PureStateMath.Inner (Collapse ψ S) (ψ - Collapse ψ S) = 0 := by
  rw [collapse_compl, collapse_mulVec, collapse_mulVec,
    inner_mulVec_conjTranspose_right', Matrix.mulVec_mulVec, projector_conjTranspose,
    projector_compl_mul, Matrix.zero_mulVec]
  simp [Qatlib.Foundations.PureStateMath.Inner]

private theorem inner_self_good (ψ : QState I) (S : Finset I) :
    Qatlib.Foundations.PureStateMath.Inner (Collapse ψ S) (Collapse ψ S) = ((MeasureProb ψ S : ℝ) : ℂ) := by
  rw [inner_self, ← Complex.ofReal_sum, ← sum_normSq_collapse]

private theorem measureProb_compl {ψ : QState I} (hψ : Normalized ψ) (S : Finset I) :
    MeasureProb ψ Sᶜ = 1 - MeasureProb ψ S := by
  have h1 : MeasureProb ψ S + MeasureProb ψ Sᶜ = 1 := by
    rw [← measureProb_union ψ disjoint_compl_right, Finset.union_compl,
      measureProb_univ hψ]
  linarith

private theorem inner_split (ψ good bad : QState I) (hsum : good + bad = ψ)
    (horth : Qatlib.Foundations.PureStateMath.Inner good bad = 0) :
    Qatlib.Foundations.PureStateMath.Inner ψ good = Qatlib.Foundations.PureStateMath.Inner good good ∧ Qatlib.Foundations.PureStateMath.Inner ψ bad = Qatlib.Foundations.PureStateMath.Inner bad bad := by
  have hbg : Qatlib.Foundations.PureStateMath.Inner bad good = 0 := by
    rw [inner_conj_symm' bad good, horth, star_zero]
  constructor
  · rw [← hsum, inner_add_left', hbg, add_zero]
  · rw [← hsum, inner_add_left', horth, zero_add]

private theorem collapse_eq_zero_of_measureProb_zero {ψ : QState I} {S : Finset I}
    (h : MeasureProb ψ S = 0) : Collapse ψ S = 0 := by
  have hsum := sum_normSq_collapse ψ S
  rw [h] at hsum
  have hz : ∀ i : I, ‖Collapse ψ S i‖ ^ 2 = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg (‖Collapse ψ S j‖))).mp hsum i (Finset.mem_univ i)
  funext i
  have hi2 : ‖Collapse ψ S i‖ ^ 2 = 0 := hz i
  have hi : Collapse ψ S i = 0 := by
    apply norm_eq_zero.mp
    exact pow_eq_zero_iff (two_ne_zero) |>.mp hi2
  rw [hi]
  rfl

end Helpers

theorem prepared_aa_reflection_and_access {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    preparedMark S ∈ Matrix.unitaryGroup I ℂ ∧ Normalized (preparedAAState A j₀) ∧
    A * ReflectionAbout (outerProduct (Ket j₀)) * Aᴴ =
      ReflectionAbout (outerProduct (preparedAAState A j₀)) ∧
    preparedAAIterate A j₀ S ∈ Matrix.unitaryGroup I ℂ := by
  have hAA : A * Aᴴ = 1 := unitary_mul_conjTranspose hA
  have hconj : A * ReflectionAbout (outerProduct (Ket j₀)) * Aᴴ
      = ReflectionAbout (outerProduct (preparedAAState A j₀)) := by
    show A * ((2 : ℂ) • outerProduct (Ket j₀) - 1) * Aᴴ
        = (2 : ℂ) • outerProduct (A *ᵥ Ket j₀) - (1 : Matrix I I ℂ)
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hAA, outerProduct_conj]
  refine ⟨preparedMark_unitary S, normalized_preparedAAState A j₀ hA, hconj, ?_⟩
  have hsplit : preparedAAIterate A j₀ S
      = ReflectionAbout (outerProduct (preparedAAState A j₀)) * preparedMark S := by
    unfold preparedAAIterate
    rw [hconj]
  rw [hsplit]
  exact (Matrix.unitaryGroup I ℂ).mul_mem
    (outerProduct_reflection_unitary (normalized_preparedAAState A j₀ hA))
    (preparedMark_unitary S)

private theorem iterate_split {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    preparedAAIterate A j₀ S
      = ReflectionAbout (outerProduct (preparedAAState A j₀)) * preparedMark S := by
  have hconj := (prepared_aa_reflection_and_access A j₀ S hA).2.2.1
  unfold preparedAAIterate
  rw [hconj]

section RunHelpers

variable {I : Type} [Fintype I] [DecidableEq I]

private theorem run_preparedBlock (M A R₀ : Matrix I I ℂ) (ψ : QState I) :
    Run M [Step.query, Step.gate Aᴴ, Step.gate R₀, Step.gate A] ψ =
      (A * R₀ * Aᴴ * M) *ᵥ ψ := by
  show A *ᵥ (R₀ *ᵥ (Aᴴ *ᵥ (M *ᵥ ψ))) = (A * R₀ * Aᴴ * M) *ᵥ ψ
  simp only [Matrix.mulVec_mulVec]
  simp only [← Matrix.mul_assoc]

private theorem run_repeat_preparedBlock (M A R₀ : Matrix I I ℂ) (k : ℕ) (ψ : QState I) :
    Run M (RepeatCircuit [Step.query, Step.gate Aᴴ, Step.gate R₀, Step.gate A] k) ψ =
      ((A * R₀ * Aᴴ * M) ^ k) *ᵥ ψ := by
  induction k generalizing ψ with
  | zero => simp [RepeatCircuit]
  | succ k ih =>
      rw [RepeatCircuit, run_append, run_preparedBlock, ih, ← Matrix.mulVec_mulVec,
        pow_succ]
      simp only [← Matrix.mulVec_mulVec]

end RunHelpers

theorem prepared_aa_actual_circuit {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    IsUnitaryCircuit (preparedAACircuit A j₀ k) ∧
    QueryCount (preparedAACircuit A j₀ k) = k ∧ GateCount (preparedAACircuit A j₀ k) = 3*k+1 ∧
    Run (preparedMark S) (preparedAACircuit A j₀ k) (Ket j₀) =
      ApplyGate ((preparedAAIterate A j₀ S)^k) (preparedAAState A j₀) := by
  have hblock : IsUnitaryCircuit
      [Step.query, Step.gate Aᴴ, Step.gate (ReflectionAbout (outerProduct (Ket j₀))),
        Step.gate A] := by
    rw [isUnitaryCircuit_query, isUnitaryCircuit_gate, isUnitaryCircuit_gate,
      isUnitaryCircuit_gate]
    exact ⟨adjoint_unitary hA, outerProduct_reflection_unitary (normalized_ket j₀),
      hA, isUnitaryCircuit_nil⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [preparedAACircuit, isUnitaryCircuit_append, isUnitaryCircuit_gate]
    exact ⟨⟨hA, isUnitaryCircuit_nil⟩, hblock.repeatCircuit k⟩
  · rw [preparedAACircuit, queryCount_append, queryCount_repeatCircuit]
    simp
  · rw [preparedAACircuit, gateCount_append]
    simp only [gateCount_gate, gateCount_repeatCircuit]
    norm_num
    omega
  · rw [preparedAACircuit, run_append, run_gate, run_nil, run_repeat_preparedBlock]
    rfl

theorem prepared_aa_good_bad_geometry {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    let ψ := preparedAAState A j₀
    let good := Collapse ψ S
    let bad := ψ-good
    good+bad = ψ ∧ Qatlib.Foundations.PureStateMath.Inner good bad = 0 ∧
    ‖toEuclidean_fromVec good‖^2 = MeasureProb ψ S ∧
    ‖toEuclidean_fromVec bad‖^2 = 1-MeasureProb ψ S ∧ 0 ≤ MeasureProb ψ S ∧ MeasureProb ψ S ≤ 1 := by
  have hψ : Normalized (preparedAAState A j₀) := normalized_preparedAAState A j₀ hA
  refine ⟨add_sub_cancel _ _, inner_bad_good _ S, ?_, ?_, measureProb_nonneg _ S,
    measureProb_le_one hψ S⟩
  · rw [norm_toEuclidean_fromVec_sq]
    exact sum_normSq_collapse _ S
  · rw [collapse_compl, norm_toEuclidean_fromVec_sq, sum_normSq_collapse,
      measureProb_compl hψ S]

private theorem reflection_mark_action {I : Type} [Fintype I] [DecidableEq I]
    (ψ good bad : QState I) (S : Finset I)
    (hsum : good + bad = ψ) (hcb : Collapse bad S = 0) (hcg : Collapse good S = good)
    (hig hib : ℂ) (higEq : Qatlib.Foundations.PureStateMath.Inner ψ good = hig) (hibEq : Qatlib.Foundations.PureStateMath.Inner ψ bad = hib) :
    ApplyGate (ReflectionAbout (outerProduct ψ) * preparedMark S) bad
      = (2 * hib - 1) • bad + (2 * hib) • good ∧
    ApplyGate (ReflectionAbout (outerProduct ψ) * preparedMark S) good
      = (-2 * hig) • bad + (1 - 2 * hig) • good := by
  have hMb : ApplyGate (preparedMark S) bad = bad := by
    rw [preparedMark_apply, hcb, smul_zero, sub_zero]
  have hMg : ApplyGate (preparedMark S) good = -good := by
    rw [preparedMark_apply, hcg]
    module
  constructor
  · rw [applyGate_mul, hMb, applyGate_reflectionAbout, applyGate_outerProduct, hibEq,
      ← hsum]
    module
  · rw [applyGate_mul, hMg, applyGate_reflectionAbout, applyGate_outerProduct,
      inner_neg_right', higEq, ← hsum]
    module

private theorem iterate_two_component {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    ApplyGate (preparedAAIterate A j₀ S)
        (preparedAAState A j₀ - Collapse (preparedAAState A j₀) S) =
      (((1 - 2 * MeasureProb (preparedAAState A j₀) S : ℝ) : ℂ)) •
        (preparedAAState A j₀ - Collapse (preparedAAState A j₀) S) +
      (((2 * (1 - MeasureProb (preparedAAState A j₀) S) : ℝ) : ℂ)) •
        Collapse (preparedAAState A j₀) S ∧
    ApplyGate (preparedAAIterate A j₀ S) (Collapse (preparedAAState A j₀) S) =
      (((-2 * MeasureProb (preparedAAState A j₀) S : ℝ) : ℂ)) •
        (preparedAAState A j₀ - Collapse (preparedAAState A j₀) S) +
      (((1 - 2 * MeasureProb (preparedAAState A j₀) S : ℝ) : ℂ)) •
        Collapse (preparedAAState A j₀) S := by
  have hnorm : Normalized (preparedAAState A j₀) := normalized_preparedAAState A j₀ hA
  have hsum : Collapse (preparedAAState A j₀) S +
      (preparedAAState A j₀ - Collapse (preparedAAState A j₀) S)
      = preparedAAState A j₀ := add_sub_cancel _ _
  have hor : Qatlib.Foundations.PureStateMath.Inner (Collapse (preparedAAState A j₀) S)
      (preparedAAState A j₀ - Collapse (preparedAAState A j₀) S) = 0 :=
    inner_bad_good _ S
  have hin := inner_split (preparedAAState A j₀) (Collapse (preparedAAState A j₀) S)
    (preparedAAState A j₀ - Collapse (preparedAAState A j₀) S) hsum hor
  have hgg : Qatlib.Foundations.PureStateMath.Inner (Collapse (preparedAAState A j₀) S) (Collapse (preparedAAState A j₀) S)
      = ((MeasureProb (preparedAAState A j₀) S : ℝ) : ℂ) := inner_self_good _ S
  have hbb : Qatlib.Foundations.PureStateMath.Inner (preparedAAState A j₀ - Collapse (preparedAAState A j₀) S)
      (preparedAAState A j₀ - Collapse (preparedAAState A j₀) S)
      = ((1 - MeasureProb (preparedAAState A j₀) S : ℝ) : ℂ) := by
    rw [collapse_compl, inner_self_good, measureProb_compl hnorm S]
  have hact := reflection_mark_action (preparedAAState A j₀)
    (Collapse (preparedAAState A j₀) S)
    (preparedAAState A j₀ - Collapse (preparedAAState A j₀) S) S hsum
    (collapse_sub _ S) (collapse_idem _ S)
    (((MeasureProb (preparedAAState A j₀) S : ℝ) : ℂ))
    (((1 - MeasureProb (preparedAAState A j₀) S : ℝ) : ℂ))
    (hin.1.trans hgg) (hin.2.trans hbb)
  constructor
  · rw [iterate_split A j₀ S hA, hact.1]
    have hc1 : (((1 - 2 * MeasureProb (preparedAAState A j₀) S : ℝ) : ℂ))
        = 2 * (((1 - MeasureProb (preparedAAState A j₀) S : ℝ) : ℂ)) - 1 := by
      push_cast
      ring
    have hc2 : (((2 * (1 - MeasureProb (preparedAAState A j₀) S) : ℝ) : ℂ))
        = 2 * (((1 - MeasureProb (preparedAAState A j₀) S : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [hc1, hc2]
  · rw [iterate_split A j₀ S hA, hact.2]
    have hc3 : (((-2 * MeasureProb (preparedAAState A j₀) S : ℝ) : ℂ))
        = -2 * (((MeasureProb (preparedAAState A j₀) S : ℝ) : ℂ)) := by
      push_cast
      ring
    have hc1' : (((1 - 2 * MeasureProb (preparedAAState A j₀) S : ℝ) : ℂ))
        = 1 - 2 * (((MeasureProb (preparedAAState A j₀) S : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [hc3, hc1']

theorem prepared_aa_two_component_step {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    let ψ := preparedAAState A j₀
    let good := Collapse ψ S
    let bad := ψ-good
    let a := MeasureProb ψ S
    ApplyGate (preparedAAIterate A j₀ S) bad = ((1-2*a : ℝ) : ℂ) • bad + ((2*(1-a) : ℝ) : ℂ) • good ∧
    ApplyGate (preparedAAIterate A j₀ S) good = ((-2*a : ℝ) : ℂ) • bad + ((1-2*a : ℝ) : ℂ) • good :=
  iterate_two_component A j₀ S hA

private theorem two_component_comb {V : Type} [AddCommMonoid V] [Module ℂ V]
    (bad good : V) (r1 r2 c1 c2 c3 c4 α' β' : ℂ)
    (h1 : r1 * c1 + r2 * c3 = α') (h2 : r1 * c2 + r2 * c4 = β') :
    r1 • (c1 • bad + c2 • good) + r2 • (c3 • bad + c4 • good) = α' • bad + β' • good := by
  have hsplit : r1 • (c1 • bad + c2 • good) + r2 • (c3 • bad + c4 • good)
      = (r1 * c1 + r2 * c3) • bad + (r1 * c2 + r2 * c4) • good := by
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul, add_smul,
      add_smul]
    abel
  rw [hsplit, h1, h2]

private theorem orbit_coef_bad (θ x : ℝ) (_hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) :
    (Real.cos x / Real.cos θ) * (1 - 2*(Real.sin θ)^2)
      + (Real.sin x / Real.sin θ) * (-2*(Real.sin θ)^2)
      = Real.cos (x + 2*θ) / Real.cos θ := by
  have h1 : 1 - 2*(Real.sin θ)^2 = 2*(Real.cos θ)^2 - 1 := by
    have := Real.sin_sq_add_cos_sq θ
    linarith
  field_simp
  rw [Real.cos_add, Real.cos_two_mul, Real.sin_two_mul, h1]
  ring

private theorem orbit_coef_good (θ x : ℝ) (hs : Real.sin θ ≠ 0) (_hc : Real.cos θ ≠ 0) :
    (Real.cos x / Real.cos θ) * (2*(1 - (Real.sin θ)^2))
      + (Real.sin x / Real.sin θ) * (1 - 2*(Real.sin θ)^2)
      = Real.sin (x + 2*θ) / Real.sin θ := by
  have h1 : 1 - 2*(Real.sin θ)^2 = 2*(Real.cos θ)^2 - 1 := by
    have := Real.sin_sq_add_cos_sq θ
    linarith
  have h2 : 1 - (Real.sin θ)^2 = (Real.cos θ)^2 := by
    have := Real.sin_sq_add_cos_sq θ
    linarith
  field_simp
  rw [Real.sin_add, Real.cos_two_mul, Real.sin_two_mul, h1, h2]
  ring

private theorem cos_pos_of_lt_half_pi {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    0 < Real.cos θ := by
  have hsin : 0 < Real.sin (Real.pi / 2 - θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [Real.sin_pi_div_two_sub θ] at hsin
  exact hsin

private theorem iterate_orbit {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (θ : ℝ) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hprob : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2) :
    ApplyGate ((preparedAAIterate A j₀ S)^k) (preparedAAState A j₀) =
    (((Real.cos ((2*(k:ℝ)+1)*θ) / Real.cos θ : ℝ)) : ℂ) •
      (preparedAAState A j₀ - Collapse (preparedAAState A j₀) S) +
    (((Real.sin ((2*(k:ℝ)+1)*θ) / Real.sin θ : ℝ)) : ℂ) •
      Collapse (preparedAAState A j₀) S := by
  have hs : Real.sin θ ≠ 0 := by
    have := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
    positivity
  have hc : Real.cos θ ≠ 0 := by
    have := cos_pos_of_lt_half_pi hθ0 hθ1
    positivity
  induction k with
  | zero =>
      rw [pow_zero, applyGate_one]
      have h0 : (2*((0:ℕ):ℝ)+1)*θ = θ := by norm_num
      rw [h0, div_self hc, div_self hs]
      module
  | succ k ih =>
      obtain ⟨hbadstep, hgoodstep⟩ := iterate_two_component A j₀ S hA
      have hang : (2*((k+1 : ℕ):ℝ)+1)*θ = (2*(k:ℝ)+1)*θ + 2*θ := by
        push_cast
        ring
      rw [hang, pow_succ', applyGate_mul, ih, applyGate_add, applyGate_smul,
        applyGate_smul, hbadstep, hgoodstep, hprob]
      refine two_component_comb _ _ _ _ _ _ _ _ _ _ ?_ ?_
      · exact_mod_cast orbit_coef_bad θ ((2*(k:ℝ)+1)*θ) hs hc
      · exact_mod_cast orbit_coef_good θ ((2*(k:ℝ)+1)*θ) hs hc

theorem prepared_aa_actual_rotation {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (θ : ℝ) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    0 < θ → θ < Real.pi/2 → MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2 →
    Run (preparedMark S) (preparedAACircuit A j₀ k) (Ket j₀) =
    ((Real.cos ((2*(k:ℝ)+1)*θ) / Real.cos θ : ℝ) : ℂ) •
      (preparedAAState A j₀ - Collapse (preparedAAState A j₀) S) +
    ((Real.sin ((2*(k:ℝ)+1)*θ) / Real.sin θ : ℝ) : ℂ) •
      Collapse (preparedAAState A j₀) S := by
  intro hθ0 hθ1 hprob
  rw [(prepared_aa_actual_circuit A j₀ S k hA).2.2.2]
  exact iterate_orbit A j₀ S θ k hA hθ0 hθ1 hprob

theorem prepared_aa_born_success {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (θ : ℝ) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    0 < θ → θ < Real.pi/2 → MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2 →
    MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k) (Ket j₀)) S =
    (Real.sin ((2*(k:ℝ)+1)*θ))^2 := by
  intro hθ0 hθ1 hprob
  have hs : Real.sin θ ≠ 0 := by
    have := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
    positivity
  rw [(prepared_aa_actual_circuit A j₀ S k hA).2.2.2,
    iterate_orbit A j₀ S θ k hA hθ0 hθ1 hprob, ← sum_normSq_collapse]
  have hcol : ∀ (c d : ℂ) (u v : QState I),
      Collapse (c • u + d • v) S = c • Collapse u S + d • Collapse v S := by
    intro c d u v
    rw [collapse_mulVec, collapse_mulVec, collapse_mulVec, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hbad0 : Collapse (preparedAAState A j₀ - Collapse (preparedAAState A j₀) S) S = 0 :=
    collapse_sub _ S
  have hgood : Collapse (Collapse (preparedAAState A j₀) S) S
      = Collapse (preparedAAState A j₀) S := collapse_idem _ S
  have hsq : ∀ (r : ℝ) (v : QState I),
      ∑ i, ‖((((r : ℝ) : ℂ) • v) i)‖^2 = r^2 * ∑ i, ‖v i‖^2 := by
    intro r v
    have hentry : ∀ i : I, ‖((((r : ℝ) : ℂ) • v) i)‖^2 = r^2 * ‖v i‖^2 := by
      intro i
      have h1 : (((r : ℝ) : ℂ) • v) i = ((r : ℝ) : ℂ) * v i := rfl
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [Finset.sum_congr rfl (fun i _ => hentry i), Finset.mul_sum]
  rw [hcol _ _ _ _, hbad0, hgood, smul_zero, zero_add, hsq, sum_normSq_collapse,
    hprob]
  field_simp

section FixHelpers

variable {I : Type} [Fintype I] [DecidableEq I]

private theorem pow_mulVec_fix (Q : Matrix I I ℂ) (x : QState I) (h : Q *ᵥ x = x) :
    ∀ k : ℕ, Q^k *ᵥ x = x := by
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, h]

private theorem pow_mulVec_neg (Q : Matrix I I ℂ) (x : QState I) (h : Q *ᵥ x = -x) :
    ∀ k : ℕ, Q^k *ᵥ x = ((-1:ℂ)^k) • x := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h,
        ← neg_one_smul ℂ x, smul_smul, ← pow_succ]

end FixHelpers

theorem prepared_aa_endpoint_states {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    (MeasureProb (preparedAAState A j₀) S = 0 →
      Run (preparedMark S) (preparedAACircuit A j₀ k) (Ket j₀) = preparedAAState A j₀) ∧
    (MeasureProb (preparedAAState A j₀) S = 1 →
      Run (preparedMark S) (preparedAACircuit A j₀ k) (Ket j₀) =
        ((-1:ℂ)^k) • preparedAAState A j₀) := by
  have hnorm : Normalized (preparedAAState A j₀) := normalized_preparedAAState A j₀ hA
  have hrun := (prepared_aa_actual_circuit A j₀ S k hA).2.2.2
  constructor
  · intro ha
    have hg0 : Collapse (preparedAAState A j₀) S = 0 :=
      collapse_eq_zero_of_measureProb_zero ha
    have hbad : preparedAAState A j₀ - Collapse (preparedAAState A j₀) S
        = preparedAAState A j₀ := by rw [hg0, sub_zero]
    have hstep : preparedAAIterate A j₀ S *ᵥ preparedAAState A j₀
        = preparedAAState A j₀ := by
      have h1 := (iterate_two_component A j₀ S hA).1
      rw [ha, hbad, hg0, smul_zero, add_zero] at h1
      have hcoef : (((1 - 2 * 0 : ℝ) : ℂ)) = 1 := by norm_num
      rw [hcoef, one_smul] at h1
      exact h1
    rw [hrun]
    exact pow_mulVec_fix _ _ hstep k
  · intro ha
    have hbad0 : preparedAAState A j₀ - Collapse (preparedAAState A j₀) S = 0 := by
      have hc : MeasureProb (preparedAAState A j₀) Sᶜ = 0 := by
        rw [measureProb_compl hnorm S, ha, sub_self]
      rw [collapse_compl, collapse_eq_zero_of_measureProb_zero hc]
    have hgood : Collapse (preparedAAState A j₀) S = preparedAAState A j₀ :=
      (sub_eq_zero.mp hbad0).symm
    have hstep : preparedAAIterate A j₀ S *ᵥ preparedAAState A j₀
        = -(preparedAAState A j₀) := by
      have h2 := (iterate_two_component A j₀ S hA).2
      rw [ha, hbad0, hgood] at h2
      have hcoef : (((1 - 2 * 1 : ℝ) : ℂ)) = -1 := by norm_num
      rw [hcoef, smul_zero, zero_add, neg_one_smul] at h2
      exact h2
    rw [hrun]
    exact pow_mulVec_neg _ _ hstep k

theorem prepared_aa_oracle_error {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (O : Matrix I I ℂ) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ) :
    ‖toEuclidean_fromVec (Run O (preparedAACircuit A j₀ k) (Ket j₀) -
      Run (preparedMark S) (preparedAACircuit A j₀ k) (Ket j₀))‖ ≤ (k:ℝ)*‖O-preparedMark S‖ ∧
    |MeasureProb (Run O (preparedAACircuit A j₀ k) (Ket j₀)) S -
      MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k) (Ket j₀)) S| ≤
      2*(k:ℝ)*‖O-preparedMark S‖ := by
  have hC := (prepared_aa_actual_circuit A j₀ S k hA).1
  have hM := preparedMark_unitary S
  have h1 := norm_run_sub_run_le_queryCount O (preparedMark S) (preparedAACircuit A j₀ k)
    (Ket j₀) hO hM hC
  rw [(normalized_iff_norm_toEuclidean_fromVec (Ket j₀)).mp (normalized_ket j₀), mul_one,
    (prepared_aa_actual_circuit A j₀ S k hA).2.1] at h1
  refine ⟨h1, ?_⟩
  have h2 := measureProb_run_sub_le_queryCount O (preparedMark S)
    (preparedAACircuit A j₀ k) (Ket j₀) S hO hM hC (normalized_ket j₀)
  rw [(prepared_aa_actual_circuit A j₀ S k hA).2.1] at h2
  exact h2

section Word

variable {I : Type} [Fintype I] [DecidableEq I]

private theorem evaluatePrepared_flatten_replicate (U B : Matrix I I ℂ)
    (block : List (PreparedStep I)) (k : ℕ) :
    evaluatePrepared U B (List.replicate k block |>.flatten)
      = (evaluatePrepared U B block)^k := by
  induction k with
  | zero => simp [evaluatePrepared]
  | succ k ih =>
      rw [List.replicate_succ, List.flatten_cons, evaluatePrepared_append, ih, pow_succ']

private theorem counts_flatten_replicate (block : List (PreparedStep I)) (k : ℕ) :
    preparedDataQueries (List.replicate k block |>.flatten)
      = k * preparedDataQueries block ∧
    preparedInputQueries (List.replicate k block |>.flatten)
      = k * preparedInputQueries block ∧
    preparedFixedGates (List.replicate k block |>.flatten)
      = k * preparedFixedGates block := by
  induction k with
  | zero => simp [preparedDataQueries, preparedInputQueries, preparedFixedGates]
  | succ k ih =>
      rw [List.replicate_succ, List.flatten_cons]
      obtain ⟨e1, e2, e3⟩ := preparedCounts_append block (List.replicate k block).flatten
      obtain ⟨d1, i1, f1⟩ := ih
      rw [e1, e2, e3, d1, i1, f1]
      exact ⟨by ring, by ring, by ring⟩

theorem prepared_aa_separate_access_word {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    PreparedCircuitValid (preparedAAWord j₀ k) ∧ preparedDataQueries (preparedAAWord j₀ k) = k ∧
    preparedInputQueries (preparedAAWord j₀ k) = 2*k+1 ∧ preparedFixedGates (preparedAAWord j₀ k) = k ∧
    evaluatePrepared (preparedMark S) A (preparedAAWord j₀ k) = (preparedAAIterate A j₀ S)^k * A ∧
    ApplyGate (evaluatePrepared (preparedMark S) A (preparedAAWord j₀ k)) (Ket j₀) =
      Run (preparedMark S) (preparedAACircuit A j₀ k) (Ket j₀) := by
  have hwordeq : preparedAAWord j₀ k
      = (List.replicate k
          [PreparedStep.prepareForward, .gate (ReflectionAbout (outerProduct (Ket j₀))),
            .prepareBackward, .dataForward]).flatten ++ [.prepareForward] := rfl
  have hblockEval : evaluatePrepared (preparedMark S) A
      [PreparedStep.prepareForward, .gate (ReflectionAbout (outerProduct (Ket j₀))),
        .prepareBackward, .dataForward]
      = preparedAAIterate A j₀ S := by
    simp only [evaluatePrepared, preparedInstruction]
    rw [Matrix.mul_one]
    simp only [← Matrix.mul_assoc]
    rfl
  have hblockData : preparedDataQueries
      ([PreparedStep.prepareForward, .gate (ReflectionAbout (outerProduct (Ket j₀))),
        .prepareBackward, .dataForward] : List (PreparedStep I)) = 1 := rfl
  have hblockInput : preparedInputQueries
      ([PreparedStep.prepareForward, .gate (ReflectionAbout (outerProduct (Ket j₀))),
        .prepareBackward, .dataForward] : List (PreparedStep I)) = 2 := rfl
  have hblockFixed : preparedFixedGates
      ([PreparedStep.prepareForward, .gate (ReflectionAbout (outerProduct (Ket j₀))),
        .prepareBackward, .dataForward] : List (PreparedStep I)) = 1 := rfl
  obtain ⟨q1, q2, q3⟩ := counts_flatten_replicate
    ([PreparedStep.prepareForward, .gate (ReflectionAbout (outerProduct (Ket j₀))),
      .prepareBackward, .dataForward] : List (PreparedStep I)) k
  have hlastData : preparedDataQueries
      ([PreparedStep.prepareForward] : List (PreparedStep I)) = 0 := rfl
  have hlastInput : preparedInputQueries
      ([PreparedStep.prepareForward] : List (PreparedStep I)) = 1 := rfl
  have hlastFixed : preparedFixedGates
      ([PreparedStep.prepareForward] : List (PreparedStep I)) = 0 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨t, ht, hct⟩ := List.mem_flatten.mp hc
      have htb : t = [PreparedStep.prepareForward,
          .gate (ReflectionAbout (outerProduct (Ket j₀))), .prepareBackward,
          .dataForward] := (List.mem_replicate.mp ht).2
      rw [htb] at hct
      rcases List.mem_cons.mp hct with h | h
      · subst h; trivial
      · rcases List.mem_cons.mp h with h | h
        · subst h
          exact outerProduct_reflection_unitary (normalized_ket j₀)
        · rcases List.mem_cons.mp h with h | h
          · subst h; trivial
          · rcases List.mem_cons.mp h with h | h
            · subst h; trivial
            · simp at h
    · have hc' : c = PreparedStep.prepareForward := List.mem_singleton.mp hc
      subst hc'
      trivial
  · rw [hwordeq]
    obtain ⟨e1, _, _⟩ := preparedCounts_append
      ((List.replicate k
          [PreparedStep.prepareForward, .gate (ReflectionAbout (outerProduct (Ket j₀))),
            .prepareBackward, .dataForward]).flatten)
      [PreparedStep.prepareForward]
    rw [e1, q1, hblockData, hlastData]
    simp
  · rw [hwordeq]
    obtain ⟨_, e2, _⟩ := preparedCounts_append
      ((List.replicate k
          [PreparedStep.prepareForward, .gate (ReflectionAbout (outerProduct (Ket j₀))),
            .prepareBackward, .dataForward]).flatten)
      [PreparedStep.prepareForward]
    rw [e2, q2, hblockInput, hlastInput]
    omega
  · rw [hwordeq]
    obtain ⟨_, _, e3⟩ := preparedCounts_append
      ((List.replicate k
          [PreparedStep.prepareForward, .gate (ReflectionAbout (outerProduct (Ket j₀))),
            .prepareBackward, .dataForward]).flatten)
      [PreparedStep.prepareForward]
    rw [e3, q3, hblockFixed, hlastFixed]
    simp
  · rw [hwordeq, evaluatePrepared_append, evaluatePrepared_flatten_replicate, hblockEval]
    simp [evaluatePrepared, preparedInstruction]
  · rw [hwordeq, evaluatePrepared_append, evaluatePrepared_flatten_replicate, hblockEval]
    simp only [evaluatePrepared, preparedInstruction, Matrix.mul_one]
    rw [(prepared_aa_actual_circuit A j₀ S k hA).2.2.2, applyGate_mul]
    rfl

end Word

end Qatlib.Concepts.LchsSimulation.StaticLchs
