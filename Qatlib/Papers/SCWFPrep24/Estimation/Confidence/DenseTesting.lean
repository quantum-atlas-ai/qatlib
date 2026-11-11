/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalReadout
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.DenseFamily

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Dense Testing

The constant and dense witnesses occupy two literal points of the same actual input family.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix ComplexOrder MatrixOrder

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.DenseTesting
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
open Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Concepts.MbqcFlow.FlowDecision
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.MixedFidelity.FidelityMetric.EventReadout
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalReadout
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.DenseFamily
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.DenseOverlap
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridMatching
open Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin

/-- The constant and dense witnesses occupy two literal points of the same actual input family. -/
def denseLabel (d N Q : ℕ) (k : Fin 4) : InputLabel d N Q := (fun _ => k,fun _ => 0)

/-- The original full known basis preserves the actual inner product, including both unknown spin amplitudes at every original address. -/
theorem original_inner (d N : ℕ) (h4 : 4∣N) (b : ℝ) (Q : ℕ) (x y : InputLabel d N Q) :
    Inner (encodedOriginalInput d N h4 b Q x) (encodedOriginalInput d N h4 b Q y)=
      Inner (originalInput d N h4 b Q x) (originalInput d N h4 b Q y) := by
  simp only [inner_apply,encodedOriginalInput]
  exact Equiv.sum_comp (originalFiniteBasis d N h4 Q)
    (fun a => (starRingEnd ℂ) (originalInput d N h4 b Q x a)*originalInput d N h4 b Q y a)

/-- The same actual dense and constant family points have the source's exact complete Q-copy squared fidelity. -/
theorem actual_dense_fidelity (d N : ℕ) [NeZero N] (h4 : 4∣N) (b : ℝ)
    (hb0 : 0≤b) (hb1 : b≤1) (Q : ℕ) :
    (Froot (outerProduct (encodedOriginalInput d N h4 b Q (denseLabel d N Q 3)))
      (outerProduct (encodedOriginalInput d N h4 b Q (denseLabel d N Q 1))))^2=(1-b)^(2*Q) := by
  let ψ := encodedOriginalInput d N h4 b Q (denseLabel d N Q 3)
  let φ := encodedOriginalInput d N h4 b Q (denseLabel d N Q 1)
  have hp : Normalized ψ := encodedOriginalInput_normalized d N h4 b hb0 hb1 Q _
  have hq : Normalized φ := encodedOriginalInput_normalized d N h4 b hb0 hb1 Q _
  have h := (g1 _ _ _ (Qatlib.Foundations.PureStateMath.BornBridge.outerProduct_density hp)
    (Qatlib.Foundations.PureStateMath.BornBridge.outerProduct_density hq)).2.2.2.2.1 ψ φ hp hq
  change (Froot (outerProduct ψ) (outerProduct φ))^2=_
  rw [h]
  change ‖Inner (encodedOriginalInput d N h4 b Q (denseLabel d N Q 3))
    (encodedOriginalInput d N h4 b Q (denseLabel d N Q 1))‖^2=_
  rw [original_inner]
  have hc : (fun a => pairedWeakSpin b (fun _ : PairLabels d N => 3) (originalGrid d N h4 a))=
      (fun _a : Fin (d+1) → Fin N => weakSpin b 1) := by
    funext a
    change weakSpin b (siteSign (fun _ => 3) (originalGrid d N h4 a))=_
    rw [sign_three]
  change ‖Inner (originalSuppliedCopies (fun a => pairedWeakSpin b (fun _ : PairLabels d N => 3) (originalGrid d N h4 a)) Q (fun _ => 0))
    (originalSuppliedCopies (fun a => weakSpin b (denseSign d N h4 a)) Q (fun _ => 0))‖^2=_
  rw [hc,dense_copies_inner b _ hb0 hb1 (denseSign_sum d N h4) Q]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (by linarith : 0≤1-b) Q)]
  rw [←pow_mul]
  congr 1
  omega

/-- The original family guarantee controls the dense witnesses' true real threshold errors, paying their full original loss and all copies. -/
theorem actual_dense_testing (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N)
    (δ : ℝ) (Q K : ℕ) (T : QuantumChannel (InputDim d N Q) K) (P : EventPOVM K ℝ)
    (hacc : FamilyAccurate d N h4 Q K T P δ) :
    (1-128/((N : ℝ)^2))^(2*Q)≤4*δ := by
  let b : ℝ := 128/((N : ℝ)^2)
  let η : ℝ := (N : ℝ)^2
  let z0 := denseLabel d N Q 3
  let z1 := denseLabel d N Q 1
  let ψ := encodedOriginalInput d N h4 b Q z0
  let φ := encodedOriginalInput d N h4 b Q z1
  let A := outerProduct ψ
  let B := outerProduct φ
  have hb := original_weak_excitation N hN
  have hp : IsDensityOperator A := Qatlib.Foundations.PureStateMath.BornBridge.outerProduct_density
    (encodedOriginalInput_normalized d N h4 b hb.1 (by linarith [hb.2]) Q z0)
  have hq : IsDensityOperator B := Qatlib.Foundations.PureStateMath.BornBridge.outerProduct_density
    (encodedOriginalInput_normalized d N h4 b hb.1 (by linarith [hb.2]) Q z1)
  have hh : 2*Real.pi/(N : ℝ)≠0 := div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    (by exact_mod_cast (NeZero.ne N))
  have hl0 : originalFieldLoss d N h4 b z0.1 Q z0.2 (2*Real.pi/N) N=0 :=
    constant_family_full_loss d N h4 b hb.1 (by linarith [hb.2]) Q _ _ hh
  have hl1 : 2*η<originalFieldLoss d N h4 b z1.1 Q z1.2 (2*Real.pi/N) N := by
    change 2*η<originalFieldLoss d N h4 b (fun _ => 1) Q (fun _ => 0) (2*Real.pi/N) N
    rw [dense_family_full_loss d N hN h4 b hb.1 (by linarith [hb.2]) Q _ _ hh]
    exact original_dense_loss_gap N hN
  have h0 : P.born (T.map A) (Set.Ioi η)≤δ := by
    apply le_trans (P.born_mono _ (T.preservesDensity hp) _ _ measurableSet_Ioi
      (estimationFailure_measurable _ _) ?_) (hacc z0)
    intro x hx
    change η< |x-originalFieldLoss d N h4 b z0.1 Q z0.2 (2*Real.pi/N) N|
    rw [hl0,sub_zero]
    exact lt_of_lt_of_le hx (le_abs_self x)
  have h1 : P.born (T.map B) (Set.Ioi η)ᶜ≤δ := by
    apply le_trans (P.born_mono _ (T.preservesDensity hq) _ _ measurableSet_Ioi.compl
      (estimationFailure_measurable _ _) ?_) (hacc z1)
    intro x hx
    have hx' : x≤η := le_of_not_gt hx
    change η< |x-originalFieldLoss d N h4 b z1.1 Q z1.2 (2*Real.pi/N) N|
    nlinarith [neg_le_abs (x-originalFieldLoss d N h4 b z1.1 Q z1.2 (2*Real.pi/N) N)]
  have he := P.error_after_channel T A B hp hq (Set.Ioi η) measurableSet_Ioi
  have hf := actual_dense_fidelity d N h4 b hb.1 (by linarith [hb.2]) Q
  change (Froot A B)^2=(1-b)^(2*Q) at hf
  rw [hf] at he
  change (1-b)^(2*Q)≤4*δ
  linarith

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.DenseTesting
