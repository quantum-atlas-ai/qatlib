/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalQuantum
import Qatlib.Concepts.MixedFidelity.FidelityMetric.EventReadout

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Original Readout

The complete original input dimension in the one known full basis; no hidden sign or phase register is supplied.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix ComplexOrder MatrixOrder

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalReadout
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.MixedFidelity.FidelityMetric.EventReadout
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PriorBasis

/-- The complete original input dimension in the one known full basis; no hidden sign or phase register is supplied. -/
abbrev InputDim (d N Q : ℕ) := Fintype.card (Fin Q → (PairLabels d N × Bool) × Bool)

/-- The actual classical prior points label the physical input ensemble, not extra accessible quantum registers. -/
abbrev InputLabel (d N Q : ℕ) := (PairLabels d N → Fin 4) × ((Fin (d+1) → Fin N) → Fin (Q+1))

/-- Actual real-output accuracy on the original physical weak-input family after arbitrary common quantum processing. -/
def FamilyAccurate (d N : ℕ) [NeZero N] (h4 : 4∣N) (Q K : ℕ) (T : QuantumChannel (InputDim d N Q) K)
    (P : EventPOVM K ℝ) (δ : ℝ) : Prop :=
  ∀ z : InputLabel d N Q,P.born (T.map (outerProduct (encodedOriginalInput d N h4 (128/((N : ℝ)^2)) Q z)))
    (estimationFailure (originalFieldLoss d N h4 (128/((N : ℝ)^2)) z.1 Q z.2 (2*Real.pi/N) N) ((N : ℝ)^2))≤δ

/-- The actual common channel maps the same full original quantum prior to the same weighted processed physical component states. -/
theorem processed_prior_mixture (d N : ℕ) (h4 : 4∣N) (b ρ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1)
    (Q K : ℕ) (T : QuantumChannel (InputDim d N Q) K) :
    (∑ z : InputLabel d N Q,((originalPriorLaw d N ρ hlo hhi Q).prob z : ℂ) •
      T.map (outerProduct (encodedOriginalInput d N h4 b Q z)))=
    T.map (encodedGridPrior (GridMatching.originalGrid d N h4) b ρ Q) := by
  rw [original_quantum_prior_mixture d N h4 b ρ hlo hhi Q]
  simp only [map_sum,map_smul]

/-- The genuine original low-loss prior's real threshold error is at most twice delta, including its same actual full-loss bad-input mass. -/
theorem actual_low_error (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N) (hd : d+1=2 ∨ d+1=3)
    (δ : ℝ) (hδ : 0<δ) (hmax : δ≤1/10) (hL : Real.log (1/δ)≤(N^(d+1) : ℕ)/(N : ℝ)^2)
    (Q K : ℕ) (T : QuantumChannel (InputDim d N Q) K) (P : EventPOVM K ℝ)
    (hacc : FamilyAccurate d N h4 Q K T P δ) :
    P.born (T.map (encodedGridPrior (GridMatching.originalGrid d N h4) (128/((N : ℝ)^2)) (3/4) Q))
      (Set.Ici (physicalThreshold (d+1) N))≤2*δ := by
  let p := originalPriorLaw d N (3/4) (by norm_num) (by norm_num) Q
  let A := fun z : InputLabel d N Q => T.map (outerProduct (encodedOriginalInput d N h4 (128/((N : ℝ)^2)) Q z))
  let bad := fun z : InputLabel d N Q => badFieldLoss d N h4 (128/((N : ℝ)^2)) ((N : ℝ)^2) (3/4) (2*Real.pi/N) N Q z.2 z.1
  let failure := fun z : InputLabel d N Q => estimationFailure
    (originalFieldLoss d N h4 (128/((N : ℝ)^2)) z.1 Q z.2 (2*Real.pi/N) N) ((N : ℝ)^2)
  have hb := original_weak_excitation N hN
  have hA (z : InputLabel d N Q) : IsDensityOperator (A z) := T.preservesDensity
    (Qatlib.Foundations.PureStateMath.BornBridge.outerProduct_density
      (encodedOriginalInput_normalized d N h4 _ hb.1 (by linarith [hb.2]) Q z))
  have hinc (z : InputLabel d N Q) (hz : ¬bad z) : Set.Ici (physicalThreshold (d+1) N)⊆failure z := by
    intro x hx
    change (N : ℝ)^2 < |x-originalFieldLoss d N h4 (128/((N : ℝ)^2)) z.1 Q z.2 (2*Real.pi/N) N|
    by_contra he
    have h := original_low_threshold d N hN h4 (by omega) z.1 Q z.2 x hz (le_of_not_gt he)
    exact (not_lt_of_ge hx) h
  have hp := P.prior_event_upper p A hA bad (Set.Ici (physicalThreshold (d+1) N)) measurableSet_Ici
    failure (fun _ => estimationFailure_measurable _ _) δ hδ.le hacc hinc
  rw [processed_prior_mixture] at hp
  have hm := original_joint_bad_prior_paid d N hN h4 hd (3/4) δ (by norm_num) (by norm_num) hδ hmax hL Q
  change (∑ z ∈ Finset.univ.filter bad,p.prob z)≤δ at hm
  exact hp.trans (by linarith [hm])

/-- The genuine original high-loss prior's real threshold error is at most twice delta under the same arbitrary quantum processing and original accuracy guarantee. -/
theorem actual_high_error (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N) (hd : d+1=2 ∨ d+1=3)
    (δ : ℝ) (hδ : 0<δ) (hmax : δ≤1/10) (hL : Real.log (1/δ)≤(N^(d+1) : ℕ)/(N : ℝ)^2)
    (Q K : ℕ) (T : QuantumChannel (InputDim d N Q) K) (P : EventPOVM K ℝ)
    (hacc : FamilyAccurate d N h4 Q K T P δ) :
    P.born (T.map (encodedGridPrior (GridMatching.originalGrid d N h4) (128/((N : ℝ)^2)) (-3/4) Q))
      (Set.Iio (physicalThreshold (d+1) N))≤2*δ := by
  let p := originalPriorLaw d N (-3/4) (by norm_num) (by norm_num) Q
  let A := fun z : InputLabel d N Q => T.map (outerProduct (encodedOriginalInput d N h4 (128/((N : ℝ)^2)) Q z))
  let bad := fun z : InputLabel d N Q => badFieldLoss d N h4 (128/((N : ℝ)^2)) ((N : ℝ)^2) (-3/4) (2*Real.pi/N) N Q z.2 z.1
  let failure := fun z : InputLabel d N Q => estimationFailure
    (originalFieldLoss d N h4 (128/((N : ℝ)^2)) z.1 Q z.2 (2*Real.pi/N) N) ((N : ℝ)^2)
  have hb := original_weak_excitation N hN
  have hA (z : InputLabel d N Q) : IsDensityOperator (A z) := T.preservesDensity
    (Qatlib.Foundations.PureStateMath.BornBridge.outerProduct_density
      (encodedOriginalInput_normalized d N h4 _ hb.1 (by linarith [hb.2]) Q z))
  have hinc (z : InputLabel d N Q) (hz : ¬bad z) : Set.Iio (physicalThreshold (d+1) N)⊆failure z := by
    intro x hx
    change (N : ℝ)^2 < |x-originalFieldLoss d N h4 (128/((N : ℝ)^2)) z.1 Q z.2 (2*Real.pi/N) N|
    by_contra he
    have h := original_high_threshold d N hN h4 (by omega) z.1 Q z.2 x hz (le_of_not_gt he)
    exact (not_lt_of_ge h.le) hx
  have hp := P.prior_event_upper p A hA bad (Set.Iio (physicalThreshold (d+1) N)) measurableSet_Iio
    failure (fun _ => estimationFailure_measurable _ _) δ hδ.le hacc hinc
  rw [processed_prior_mixture] at hp
  have hm := original_joint_bad_prior_paid d N hN h4 hd (-3/4) δ (by norm_num) (by norm_num) hδ hmax hL Q
  change (∑ z ∈ Finset.univ.filter bad,p.prob z)≤δ at hm
  exact hp.trans (by linarith [hm])

/-- True real-output accuracy on the original physical family forces the full original priors' squared fidelity below eight delta, after arbitrary common finite-dimensional quantum processing. -/
theorem actual_prior_fidelity_upper (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N) (hd : d+1=2 ∨ d+1=3)
    (δ : ℝ) (hδ : 0<δ) (hmax : δ≤1/10) (hL : Real.log (1/δ)≤(N^(d+1) : ℕ)/(N : ℝ)^2)
    (Q K : ℕ) (T : QuantumChannel (InputDim d N Q) K) (P : EventPOVM K ℝ)
    (hacc : FamilyAccurate d N h4 Q K T P δ) :
    (Froot
      (encodedGridPrior (GridMatching.originalGrid d N h4) (128/((N : ℝ)^2)) (3/4) Q)
      (encodedGridPrior (GridMatching.originalGrid d N h4) (128/((N : ℝ)^2)) (-3/4) Q))^2≤8*δ := by
  have hl := actual_low_error d N hN h4 hd δ hδ hmax hL Q K T P hacc
  have hh := actual_high_error d N hN h4 hd δ hδ hmax hL Q K T P hacc
  have hA := original_physical_prior_legal d N hN h4 (3/4) (by norm_num) (by norm_num) Q
  have hB := original_physical_prior_legal d N hN h4 (-3/4) (by norm_num) (by norm_num) Q
  have he := P.error_after_channel T _ _ hA hB (Set.Ici (physicalThreshold (d+1) N)) measurableSet_Ici
  rw [Set.compl_Ici] at he
  linarith

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalReadout

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalReadout
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
open Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Concepts.MbqcFlow.FlowDecision
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.MixedFidelity.FidelityMetric.EventReadout
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridLossBridge
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.DenseOverlap
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

/-- The same known full basis encodes Q ordinary copies of any original physical spinor. -/
def encodedOriginalField (d N : ℕ) (h4 : 4∣N) (Q : ℕ)
    (ψ : (Fin (d+1) → Fin N) → Bool → ℂ) : QState (Fin (InputDim d N Q)) :=
  fun i => originalSuppliedCopies ψ Q (fun _ => 0) (originalFiniteBasis d N h4 Q i)

/-- The actual physical field, with its one shared phase assignment, supplies exactly the same complete input used by the prior. -/
theorem encodedOriginalField_eq (d N : ℕ) (h4 : 4∣N) (b : ℝ) (Q : ℕ)
    (z : InputLabel d N Q) :
    encodedOriginalField d N h4 Q (originalField d N h4 b z.1 Q z.2)=encodedOriginalInput d N h4 b Q z := by
  funext i
  change originalSuppliedCopies (sharedPhaseField (fun a => pairedWeakSpin b z.1 (GridMatching.originalGrid d N h4 a)) Q z.2)
    Q (fun _ => 0) (originalFiniteBasis d N h4 Q i)=_
  rw [copies_zero]
  rfl

/-- The original full physical loss uses kappa one, zero forcing, and lambda N on the actual periodic unit shifts. -/
abbrev originalLoss (d N : ℕ) [NeZero N] (ψ : (Fin (d+1) → Fin N) → Bool → ℂ) :=
  spinorDiscreteLoss (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
    (fun _ _ => 0) (periodicUnitShift (d+1) N) (2*Real.pi/N) 1 N

/-- Original full-domain real-output accuracy quantifies over every pointwise unit spinor satisfying every original public Bell promise. -/
def AllOriginalAccurate (d N : ℕ) [NeZero N] (h4 : 4∣N) (Q K : ℕ)
    (T : QuantumChannel (InputDim d N Q) K) (P : EventPOVM K ℝ) (δ : ℝ) : Prop :=
  ∀ ψ : (Fin (d+1) → Fin N) → Bool → ℂ,
    (∀ a,(real0 ψ a)^2+(imag0 ψ a)^2+(real1 ψ a)^2+(imag1 ψ a)^2=1) →
    (∀ j : Fin (d+1),bellMean (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
      (periodicDoubleShift (d+1) N j)≤256/((N : ℝ)^2)) →
    P.born (T.map (outerProduct (encodedOriginalField d N h4 Q ψ)))
      (estimationFailure (originalLoss d N ψ) ((N : ℝ)^2))≤δ

/-- Accuracy for the literal original full domain entails the prior-family guarantee by internally proving the same fields' normalization, public promises, and exact Q-copy identity. -/
theorem allOriginalAccurate_family (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N)
    (Q K : ℕ) (T : QuantumChannel (InputDim d N Q) K) (P : EventPOVM K ℝ) (δ : ℝ)
    (hacc : AllOriginalAccurate d N h4 Q K T P δ) : FamilyAccurate d N h4 Q K T P δ := by
  intro z
  have hb := original_weak_excitation N hN
  have ha := hacc (originalField d N h4 (128/((N : ℝ)^2)) z.1 Q z.2)
    (physicalField_coordinate_mass (GridMatching.originalGrid d N h4) _ hb.1 (by linarith [hb.2]) z.1 Q z.2)
    (original_field_bell_promise d N hN h4 z.1 Q z.2)
  rw [encodedOriginalField_eq] at ha
  exact ha

/-- The literal original full-domain estimation guarantee forces the original priors' whole-input testing fidelity below eight delta. -/
theorem allOriginalAccurate_fidelity_upper (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N)
    (hd : d+1=2 ∨ d+1=3) (δ : ℝ) (hδ : 0<δ) (hmax : δ≤1/10)
    (hL : Real.log (1/δ)≤(N^(d+1) : ℕ)/(N : ℝ)^2)
    (Q K : ℕ) (T : QuantumChannel (InputDim d N Q) K) (P : EventPOVM K ℝ)
    (hacc : AllOriginalAccurate d N h4 Q K T P δ) :
    (Froot (PriorBasis.encodedGridPrior (GridMatching.originalGrid d N h4) (128/((N : ℝ)^2)) (3/4) Q)
      (PriorBasis.encodedGridPrior (GridMatching.originalGrid d N h4) (128/((N : ℝ)^2)) (-3/4) Q))^2≤8*δ :=
  actual_prior_fidelity_upper d N hN h4 hd δ hδ hmax hL Q K T P
    (allOriginalAccurate_family d N hN h4 Q K T P δ hacc)

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalReadout
