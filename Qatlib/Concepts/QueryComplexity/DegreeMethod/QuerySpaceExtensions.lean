/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.InterruptBridge.QuerySpaceExtensionsRefinedDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.StoppingCore.InterruptBridge

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexConjugate

private theorem measureProb_compl {I : Type} [Fintype I] [DecidableEq I]
    {ψ : QState I} (hψ : Normalized ψ) (S : Finset I) :
    MeasureProb ψ Sᶜ = 1 - MeasureProb ψ S := by
  have h1 : MeasureProb ψ S + MeasureProb ψ Sᶜ = 1 := by
    rw [← measureProb_union ψ disjoint_compl_right, Finset.union_compl,
      measureProb_univ hψ]
  linarith

private theorem normalized_deferredObservedInput {n R : ℕ} {W : Type} [Fintype W]
    [DecidableEq W] {ψ : QState ((Fin n × Bool) × W)} (hψ : Normalized ψ) :
    Normalized (deferredObservedInput (R := R) ψ) := by
  have h1 : MeasureProb (deferredObservedInput (R := R) ψ) Finset.univ = 1 := by
    have h := deferredObservedInput_mass (R := R) ψ
    have h2 : MeasureProb (deferredObservedInput (R := R) ψ) Finset.univ
        = MeasureProb ψ Finset.univ := h
    rw [h2, measureProb_univ hψ]
  exact h1

private theorem applyGate_smul_matrix {I : Type} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (c : ℂ) (ψ : QState I) :
    ApplyGate (c • M) ψ = c • ApplyGate M ψ := by
  funext i
  show ∑ j, (c • M) i j * ψ j = c * (∑ j, M i j * ψ j)
  simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem applyGate_phaseOracleOfAngle {I : Type} [Fintype I] [DecidableEq I]
    (θ : I → ℝ) (ψ : QState I) :
    ApplyGate (phaseOracleOfAngle θ) ψ
      = fun i => Complex.exp (Complex.I * (θ i : ℂ)) * ψ i := by
  funext i
  simp only [ApplyGate, phaseOracleOfAngle, Matrix.mulVec_diagonal]

private theorem run_smul_oracle_of_action {I : Type} [Fintype I] [DecidableEq I]
    (O O' : Matrix I I ℂ) (c : ℂ)
    (hact : ∀ ψ : QState I, ApplyGate O' ψ = c • ApplyGate O ψ) :
    ∀ (C : Circuit I) (ψ : QState I),
      Run O' C ψ = c ^ (QueryCount C) • Run O C ψ := by
  intro C
  induction C with
  | nil =>
    intro ψ
    simp [Run, QueryCount]
  | cons s C ih =>
    cases s with
    | gate U =>
      intro ψ
      show Run O' C (ApplyGate U ψ) = c ^ (QueryCount C) • Run O C (ApplyGate U ψ)
      rw [ih]
    | query =>
      intro ψ
      have h1 := ih (ApplyGate O' ψ)
      have h2 : ApplyGate O' ψ = c • ApplyGate O ψ := hact ψ
      have hR : Run O C (ApplyGate O' ψ) = c • Run O C (ApplyGate O ψ) := by
        rw [h2]
        exact Qatlib.Concepts.StoppingCore.InterruptBridge.run_smul O c C (ApplyGate O ψ)
      show Run O' C (ApplyGate O' ψ) = c ^ (QueryCount C + 1) • Run O C (ApplyGate O ψ)
      rw [h1, hR, smul_smul, ← pow_succ]

theorem cleanSpaceScope_transport {I J F : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (O : F → Matrix I I ℂ) (Acc : F → Finset I) (j₀ : J)
    (C : Circuit I) (ψ₀ : QState I) (C' : Circuit (I × J)) (ψ' : QState (I × J))
    (hC : IsUnitaryCircuit C) (hscope : cleanSpaceScope O Acc j₀ C ψ₀ C' ψ') :
    cleanRunTransport O Acc C ψ₀ j₀ C' ψ' := by
  rcases hscope with ⟨hC', hψ', _, hE, hq, hg, hs⟩
  refine ⟨hC', hψ', hq, hg, hs, ?_, hE, ?_⟩
  · rw [hC']
    exact isUnitaryCircuit_liftCircuitTo hC
  · intro f
    rw [hC', hψ']
    show MeasureProb (Run (TensorGate (O f) (1 : Matrix J J ℂ)) (LiftCircuitTo J C)
        (TensorState ψ₀ (Ket j₀))) (ancillaReadout (Acc f))
      = MeasureProb (Run (O f) C ψ₀) (Acc f)
    rw [run_liftCircuitTo_liftedOracle J (O f) C ψ₀ (Ket j₀)]
    exact measureProb_tensorState_left (normalized_ket j₀) (Run (O f) C ψ₀) (Acc f)

theorem cleanSpaceScope_exists {I J F : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (O : F → Matrix I I ℂ) (Acc : F → Finset I) (j₀ : J)
    (C : Circuit I) (ψ₀ : QState I) :
    cleanSpaceScope O Acc j₀ C ψ₀ (LiftCircuitTo J C) (TensorState ψ₀ (Ket j₀)) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    rfl
  · intro f
    exact readoutEffect_ancillaReadout (Acc f)
  · exact queryCount_liftCircuitTo J C
  · exact gateCount_liftCircuitTo J C
  · exact size_liftCircuitTo J C

theorem correctedBridgeAdversaryTransport_fixed {X : Type} [Fintype X] [DecidableEq X]
    [Nonempty X] {n : ℕ} {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
    (input : X → Fin n → Bool) (f : X → Bool) (Γ : Matrix X X ℂ) (ε : ℝ)
    (P : ObservedCircuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W)) :
    correctedBridgeAdversaryTransport input f Γ ε P ψ := by
  intro hn hP hε0 hε1 hψ htree hΓ
  obtain ⟨R, C, hC, hcount, hgate, hfull⟩ :=
    observed_query_same_cost_full_branch_purification n W P hn hP
  have htransport (g : Fin n → Bool) (φ : QState ((Fin n × Bool) × W)) :
      MeasureProb (Run (workspaceBitOracle (W := W × Fin (R + 1) × Bool) g) C
        (deferredObservedInput (R := R) φ)) (adaptiveObservedHistoryEvent P R) =
        observedAcceptance (workspaceBitOracle (W := W) g) P φ := by
    obtain ⟨hlen, hstate⟩ := hfull g φ
    exact observed_full_history_acceptance_transport P R C g φ hlen hstate
  have hnorm : Normalized (deferredObservedInput (R := R) ψ) :=
    normalized_deferredObservedInput hψ
  have hsuccess : ∀ x : X, 1 - ε ≤ MeasureProb
      (Run (workspaceBitOracle (W := W × Fin (R + 1) × Bool) (input x)) C
        (deferredObservedInput (R := R) ψ))
      (if f x then adaptiveObservedHistoryEvent P R
       else (adaptiveObservedHistoryEvent P R)ᶜ) := by
    intro x
    have htr := htransport (input x) ψ
    have htree' := htree x
    by_cases hfx : f x
    · simp only [treeBoundedError, if_pos hfx] at htree'
      simp only [if_pos hfx]
      rw [htr]
      exact htree'
    · simp only [treeBoundedError, if_neg hfx] at htree'
      simp only [if_neg hfx]
      have hrunnorm : Normalized
            (Run (workspaceBitOracle (W := W × Fin (R + 1) × Bool) (input x)) C
              (deferredObservedInput (R := R) ψ)) :=
        hC.normalized_run (workspaceBitOracle_unitary _) hnorm
      have hcompl : MeasureProb
            (Run (workspaceBitOracle (W := W × Fin (R + 1) × Bool) (input x)) C
              (deferredObservedInput (R := R) ψ))
            (adaptiveObservedHistoryEvent P R)ᶜ
          = 1 - MeasureProb
            (Run (workspaceBitOracle (W := W × Fin (R + 1) × Bool) (input x)) C
              (deferredObservedInput (R := R) ψ))
            (adaptiveObservedHistoryEvent P R) :=
        measureProb_compl hrunnorm (adaptiveObservedHistoryEvent P R)
      rw [hcompl, htr]
      linarith
  have hΓh : Γ.IsHermitian ∧ (∀ x y, f x = f y → Γ x y = 0) := hΓ
  have hbound := negative_adversary_actual_bounded_error_circuit_lower_bound
    X (W × Fin (R + 1) × Bool) n input Γ f C (deferredObservedInput (R := R) ψ)
    (adaptiveObservedHistoryEvent P R) ε hΓh.1 hΓh.2
    hC hnorm hε0 hε1 hsuccess
  refine ⟨R, C, ⟨hC, hcount, hgate, ?_⟩, ?_⟩
  · intro g φ
    obtain ⟨hlen, hstate⟩ := hfull g φ
    exact ⟨hlen, observed_full_history_acceptance_transport P R C g φ hlen hstate⟩
  · rw [hcount] at hbound
    exact hbound

theorem unrestrictedAdversaryTransport_false :
    ¬ (unrestrictedAdversaryTransport geInput geF geΓ 0 geP) := by
  intro h
  exact bridgeAdversaryTransport_geP_false h

theorem unrestrictedAdversaryTransport_not_universal :
    ¬ (∀ {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} {W : Type}
        [Fintype W] [DecidableEq W] [Nonempty W]
        (input : X → Fin n → Bool) (f : X → Bool) (Γ : Matrix X X ℂ) (ε : ℝ)
        (P : ObservedCircuit ((Fin n × Bool) × W)),
      unrestrictedAdversaryTransport input f Γ ε P) := by
  intro h
  exact unrestrictedAdversaryTransport_false (h geInput geF geΓ 0 geP)

theorem normalizedTreeAdversaryBound_fixed {X : Type} [Fintype X] [DecidableEq X]
    [Nonempty X] {n : ℕ} {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
    (input : X → Fin n → Bool) (f : X → Bool) (Γ : Matrix X X ℂ) (ε : ℝ)
    (P : ObservedCircuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W)) :
    normalizedTreeAdversaryBound input f Γ ε P ψ := by
  intro hn hP hε0 hε1 hψ htree hΓ
  obtain ⟨R, C, _, hineq⟩ := correctedBridgeAdversaryTransport_fixed
    input f Γ ε P ψ hn hP hε0 hε1 hψ htree hΓ
  exact hineq

theorem generalNoBaselinePhaseToBit_fixed {I : Type} [Fintype I] [DecidableEq I]
    (θ : I → ℝ) (c : ℝ) : generalNoBaselinePhaseToBit θ c := by
  intro C ψ S
  have hact : ∀ φ : QState I,
      ApplyGate (phaseOracleOffset θ c) φ
        = Complex.exp (Complex.I * (c : ℂ)) • ApplyGate (phaseOracleOfAngle θ) φ := by
    intro φ
    funext i
    have hid : Complex.I * ((θ i + c : ℝ) : ℂ)
        = Complex.I * ((θ i : ℝ) : ℂ) + Complex.I * ((c : ℝ) : ℂ) := by
      push_cast
      ring
    have hexp : Complex.exp (Complex.I * ((θ i + c : ℝ) : ℂ))
        = Complex.exp (Complex.I * ((θ i : ℝ) : ℂ))
          * Complex.exp (Complex.I * ((c : ℝ) : ℂ)) := by
      rw [hid]
      exact Complex.exp_add _ _
    simp only [phaseOracleOffset, phaseOracleOfAngle, ApplyGate, Matrix.mulVec_diagonal,
      Pi.smul_apply, smul_eq_mul]
    rw [hexp]
    ring
  have hrun := run_smul_oracle_of_action (phaseOracleOfAngle θ) (phaseOracleOffset θ c)
    (Complex.exp (Complex.I * (c : ℂ))) hact C ψ
  rw [hrun, Qatlib.Foundations.BornMetrics.EventProbability.measureProb_smul]
  have hnorm : ‖(Complex.exp (Complex.I * (c : ℂ)))^(QueryCount C)‖ = 1 := by
    rw [norm_pow, Complex.norm_exp]
    have hre : (Complex.I * (c : ℂ)).re = 0 := by
      rw [Complex.mul_re]
      simp
    rw [hre, Real.exp_zero, one_pow]
  rw [hnorm]
  ring

theorem generalValueReadoutLaw_fixed {X R : Type} [Fintype X] [DecidableEq X]
    [AddCommGroup R] [Fintype R] [DecidableEq R] (v : X → R) (ψ : QState X) (z : R) :
    generalValueReadoutLaw v ψ z := by
  have h1 := addOracle_label_weight v ψ z
  unfold generalValueReadoutLaw valueFiberMass
  rw [h1]
  unfold MeasureProb
  rw [Finset.sum_filter]
  rfl

private theorem one_mem_unitaryGroup {K : Type} [Fintype K] [DecidableEq K] :
    (1 : Matrix K K ℂ) ∈ Matrix.unitaryGroup K ℂ := by
  have h1 : (1 : Matrix K K ℂ) * star (1 : Matrix K K ℂ) = 1 := by
    rw [Matrix.star_eq_conjTranspose]
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  exact Matrix.mem_unitaryGroup_iff.mpr h1

private theorem toEuclidean_fromVec_add {K : Type} [Fintype K] (u v : QState K) :
    toEuclidean_fromVec (u + v) = toEuclidean_fromVec u + toEuclidean_fromVec v := by
  ext i
  simp [toEuclidean_fromVec_apply]

private theorem norm_applyGate_le {K : Type} [Fintype K] [DecidableEq K]
    (A : Matrix K K ℂ) (σ : QState K) :
    ‖toEuclidean_fromVec (ApplyGate A σ)‖ ≤ ‖A‖ * ‖toEuclidean_fromVec σ‖ := by
  simpa [ApplyGate] using! l2_norm_mulVec_fromVec_le A σ

private theorem mulVec_sub_matrix {K : Type} [Fintype K] [DecidableEq K]
    (A B : Matrix K K ℂ) (v : QState K) :
    A *ᵥ v - B *ᵥ v = (A - B) *ᵥ v := by
  symm
  exact Matrix.sub_mulVec A B v

private theorem norm_applyGate_unitary_sub_le {K : Type} [Fintype K] [DecidableEq K]
    [Nonempty K] (U : Matrix K K ℂ) (hU : U ∈ Matrix.unitaryGroup K ℂ) (φ φ' : QState K) :
    ‖toEuclidean_fromVec (ApplyGate U φ) - toEuclidean_fromVec (ApplyGate U φ')‖
      ≤ ‖toEuclidean_fromVec φ - toEuclidean_fromVec φ'‖ := by
  have hnormU : ‖U‖ = 1 := l2_norm_unitary_eq_one hU
  have hsub : toEuclidean_fromVec (ApplyGate U φ) - toEuclidean_fromVec (ApplyGate U φ')
      = toEuclidean_fromVec (ApplyGate U (φ - φ')) := by
    rw [toEuclidean_fromVec_sub]
    congr 1
    simp [ApplyGate, Matrix.mulVec_sub]
  rw [hsub]
  have h := norm_applyGate_le U (φ - φ')
  rw [hnormU] at h
  simpa using! h

private theorem norm_applyGate_oracle_sub_le {K : Type} [Fintype K] [DecidableEq K]
    (A B : Matrix K K ℂ) (φ φ' : QState K) :
    ‖toEuclidean_fromVec (ApplyGate A φ) - toEuclidean_fromVec (ApplyGate B φ')‖
      ≤ ‖A‖ * ‖toEuclidean_fromVec (φ - φ')‖
        + ‖A - B‖ * ‖toEuclidean_fromVec φ'‖ := by
  have hdecomp : ApplyGate A φ - ApplyGate B φ'
      = ApplyGate A (φ - φ') + ApplyGate (A - B) φ' := by
    simp only [ApplyGate]
    rw [Matrix.mulVec_sub A φ φ', Matrix.sub_mulVec A B φ']
    abel
  rw [toEuclidean_fromVec_sub, hdecomp, toEuclidean_fromVec_add]
  calc ‖toEuclidean_fromVec (ApplyGate A (φ - φ'))
        + toEuclidean_fromVec (ApplyGate (A - B) φ')‖
      ≤ ‖toEuclidean_fromVec (ApplyGate A (φ - φ'))‖
        + ‖toEuclidean_fromVec (ApplyGate (A - B) φ')‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖toEuclidean_fromVec (φ - φ')‖
        + ‖A - B‖ * ‖toEuclidean_fromVec φ'‖ :=
        add_le_add (norm_applyGate_le A (φ - φ')) (norm_applyGate_le (A - B) φ')

private theorem normalized_applyGate_unitary {K : Type} [Fintype K] [DecidableEq K]
    (U : Matrix K K ℂ) (hU : U ∈ Matrix.unitaryGroup K ℂ) (σ : QState K)
    (hσ : Normalized σ) : Normalized (ApplyGate U σ) := by
  have h1 : IsUnitaryCircuit [Step.gate U] := by
    rw [isUnitaryCircuit_gate]
    exact ⟨hU, by simp⟩
  have h2 := h1.normalized_run one_mem_unitaryGroup hσ
  simpa [Run] using! h2

private theorem hybrid_aux {K : Type} [Fintype K] [DecidableEq K] [Nonempty K]
    (O O' : Matrix K K ℂ) (hO : O ∈ Matrix.unitaryGroup K ℂ)
    (hO' : O' ∈ Matrix.unitaryGroup K ℂ) :
    ∀ (C : Circuit K) (r : ℝ) (φ φ' : QState K), IsUnitaryCircuit C →
      Normalized φ → Normalized φ' →
      ‖toEuclidean_fromVec φ - toEuclidean_fromVec φ'‖ ≤ r →
      ‖toEuclidean_fromVec (Run O C φ) - toEuclidean_fromVec (Run O' C φ')‖ ≤
        (QueryCount C : ℝ) * ‖O - O'‖ + r := by
  intro C
  induction C with
  | nil =>
    intro r φ φ' hC hφ hφ' hδ
    simpa [Run, QueryCount] using! hδ
  | cons s C ih =>
    cases s with
    | gate U =>
      intro r φ φ' hC hφ hφ' hδ
      have hU : U ∈ Matrix.unitaryGroup K ℂ := by
        rw [isUnitaryCircuit_gate] at hC
        exact hC.1
      have hC' : IsUnitaryCircuit C := by
        rw [isUnitaryCircuit_gate] at hC
        exact hC.2
      have hnormφ : Normalized (ApplyGate U φ) :=
        normalized_applyGate_unitary U hU φ hφ
      have hnormφ' : Normalized (ApplyGate U φ') :=
        normalized_applyGate_unitary U hU φ' hφ'
      have hstep : ‖toEuclidean_fromVec (ApplyGate U φ)
          - toEuclidean_fromVec (ApplyGate U φ')‖ ≤ r := by
        have h1 := norm_applyGate_unitary_sub_le U hU φ φ'
        linarith
      have h := ih r (ApplyGate U φ) (ApplyGate U φ') hC' hnormφ hnormφ' hstep
      calc ‖toEuclidean_fromVec (Run O C (ApplyGate U φ))
          - toEuclidean_fromVec (Run O' C (ApplyGate U φ'))‖
          ≤ (QueryCount C : ℝ) * ‖O - O'‖ + r := h
        _ = (QueryCount (Step.gate U :: C) : ℝ) * ‖O - O'‖ + r := by
            simp [QueryCount]
    | query =>
      intro r φ φ' hC hφ hφ' hδ
      have hC' : IsUnitaryCircuit C := by
        rw [isUnitaryCircuit_query] at hC
        exact hC
      have hnormO : ‖O‖ = 1 := l2_norm_unitary_eq_one hO
      have hnormφ : Normalized (ApplyGate O φ) :=
        normalized_applyGate_unitary O hO φ hφ
      have hnormφ' : Normalized (ApplyGate O' φ') :=
        normalized_applyGate_unitary O' hO' φ' hφ'
      have hstep : ‖toEuclidean_fromVec (ApplyGate O φ)
          - toEuclidean_fromVec (ApplyGate O' φ')‖ ≤ r + ‖O - O'‖ := by
        have h1 := norm_applyGate_oracle_sub_le O O' φ φ'
        have hφ'n : ‖toEuclidean_fromVec φ'‖ = 1 :=
          (normalized_iff_norm_toEuclidean_fromVec φ').mp hφ'
        rw [hφ'n, hnormO] at h1
        have h2 : ‖toEuclidean_fromVec (φ - φ')‖ ≤ r := by
          have hx : ‖toEuclidean_fromVec (φ - φ')‖
              = ‖toEuclidean_fromVec φ - toEuclidean_fromVec φ'‖ := by
            rw [toEuclidean_fromVec_sub]
          rw [hx]
          exact hδ
        linarith
      have h := ih (r + ‖O - O'‖) (ApplyGate O φ) (ApplyGate O' φ') hC' hnormφ hnormφ' hstep
      calc ‖toEuclidean_fromVec (Run O C (ApplyGate O φ))
          - toEuclidean_fromVec (Run O' C (ApplyGate O' φ'))‖
          ≤ (QueryCount C : ℝ) * ‖O - O'‖ + (r + ‖O - O'‖) := h
        _ = (QueryCount (Step.query :: C) : ℝ) * ‖O - O'‖ + r := by
            simp [QueryCount]
            ring

theorem unitaryHybridDistance_fixed {K : Type} [Fintype K] [DecidableEq K]
    [Nonempty K] (O O' : Matrix K K ℂ) (C : Circuit K) (ψ : QState K) (Q : ℕ)
    (hO : O ∈ Matrix.unitaryGroup K ℂ) (hO' : O' ∈ Matrix.unitaryGroup K ℂ)
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ) (hQ : QueryCount C ≤ Q) :
    ‖toEuclidean_fromVec (Run O C ψ) - toEuclidean_fromVec (Run O' C ψ)‖ ≤
      (Q : ℝ) * oracleDistance O O' := by
  have hzero : ‖toEuclidean_fromVec ψ - toEuclidean_fromVec ψ‖ ≤ 0 := by
    rw [sub_self, norm_zero]
  have h := hybrid_aux O O' hO hO' C 0 ψ ψ hC hψ hψ hzero
  calc ‖toEuclidean_fromVec (Run O C ψ) - toEuclidean_fromVec (Run O' C ψ)‖
      ≤ (QueryCount C : ℝ) * ‖O - O'‖ := by linarith [h]
    _ ≤ (Q : ℝ) * ‖O - O'‖ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hQ) (norm_nonneg _)
    _ = (Q : ℝ) * oracleDistance O O' := by rfl

theorem truncatedTailLaw_fixed {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I) :
    truncatedTailLaw O P ψ := by
  intro K
  exact stopJointLaw_fixed O P ψ K

theorem clause1_endpoint :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (J : Type) [Fintype J] [DecidableEq J]
      (F : Type) (O : F → Matrix I I ℂ) (Acc : F → Finset I) (j₀ : J) (Q : ℕ) (p : ℝ),
      cleanUpperTransport O Acc j₀ Q p ∧
      (∀ (C : Circuit I) (ψ₀ : QState I),
        IsUnitaryCircuit C → Normalized ψ₀ → QueryCount C ≤ Q →
        (∀ f : F, p ≤ MeasureProb (Run (O f) C ψ₀) (Acc f)) →
        cleanRunTransport O Acc C ψ₀ j₀ (LiftCircuitTo J C) (TensorState ψ₀ (Ket j₀))) ∧
      (∀ (X : Type) [Fintype X] [DecidableEq X] [Nonempty X] (n : ℕ) (W : Type)
        [Fintype W] [DecidableEq W] [Nonempty W]
        (input : X → Fin n → Bool) (f : X → Bool) (Γ : Matrix X X ℂ) (ε : ℝ)
        (P : ObservedCircuit ((Fin n × Bool) × W))
        (ψ : QState ((Fin n × Bool) × W)),
        correctedBridgeAdversaryTransport input f Γ ε P ψ) ∧
      ¬ (unrestrictedAdversaryTransport geInput geF geΓ 0 geP) := by
  intro I _ _ J _ _ F O Acc j₀ Q p
  refine ⟨cleanUpperTransport_fixed O Acc j₀ Q p, ?_, ?_, ?_⟩
  · intro C ψ₀ hC hψ₀ hQ hacc
    have hscope := cleanSpaceScope_exists O Acc j₀ C ψ₀
    exact cleanSpaceScope_transport O Acc j₀ C ψ₀ (LiftCircuitTo J C)
      (TensorState ψ₀ (Ket j₀)) hC hscope
  · intro X _ _ _ n W _ _ _ input f Γ ε P ψ
    exact correctedBridgeAdversaryTransport_fixed input f Γ ε P ψ
  · exact unrestrictedAdversaryTransport_false

theorem clause2_endpoint :
    ∀ (I : Type) [Fintype I] [DecidableEq I],
      (∀ f : I → Bool, bitValueActionsUnify f ∧ valueBitReadoutUnify f) ∧
      (∀ (W : Type) [Fintype W] [DecidableEq W] (f : I → Bool)
          (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)),
        ∃ (source target : AccessLedger), bitToPhaseSimulation f C ψ source target) ∧
      (∀ (f : I → Bool) (C : Circuit I) (ψ : QState I),
        ∃ (source target : AccessLedger), phaseToBitSimulation f C ψ source target) ∧
      phaseConstantUnidentifiable (I := I) ∧
      (∀ (θ : I → ℝ) (c : ℝ), generalNoBaselinePhaseToBit θ c) ∧
      (∀ ε : ℝ, 0 ≤ ε → ε < 1 / 2 → noBaselinePhaseToBit (I := I) ε) ∧
      (∀ (f : I → Bool) (x xstar : I), baselineExtractsBit f x xstar) ∧
      (∀ (U : Matrix I I ℂ) (L : AccessLedger), chargedCapabilityLaw U L) := by
  intro I _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    exact ⟨bitAction_unify f, valueBitReadoutUnify_fixed f⟩
  · intro W _ _ f C ψ
    exact bitToPhaseSimulation_fixed W f C ψ
  · intro f C ψ
    exact phaseToBitSimulation_fixed f C ψ
  · exact phaseConstantUnidentifiable_fixed
  · intro θ c
    exact generalNoBaselinePhaseToBit_fixed θ c
  · intro ε hε0 hε
    exact noBaselinePhaseToBit_fixed ε hε0 hε
  · intro f x xstar
    exact baselineExtractsBit_fixed f x xstar
  · intro U L
    exact chargedCapabilityLaw_fixed U L

theorem clause3_endpoint :
    (∀ (K : Type) [Fintype K] [DecidableEq K] [Nonempty K]
        (O O' : Matrix K K ℂ) (C : Circuit K) (ψ : QState K) (Q : ℕ),
      unitaryHybridDistance O O' C ψ Q) ∧
    (∀ (X : Type) [Fintype X] [DecidableEq X] [Nonempty X] (n : ℕ) (W : Type)
        [Fintype W] [DecidableEq W] [Nonempty W]
        (input : X → Fin n → Bool) (f : X → Bool) (Γ : Matrix X X ℂ) (ε : ℝ)
        (P : ObservedCircuit ((Fin n × Bool) × W))
        (ψ : QState ((Fin n × Bool) × W)),
      normalizedTreeAdversaryBound input f Γ ε P ψ) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] (O : Matrix I I ℂ)
        (P : ObservedCircuit I) (ψ : QState I), truncatedTailLaw O P ψ) ∧
    (∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
        (next : S → PMF (RandomizedExecution.Configuration S O))
        (cfg : RandomizedExecution.Configuration S O),
      stopTailNeverJointLaw next cfg) ∧
    (∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
        (next : S → PMF (RandomizedExecution.Configuration S O))
        (c : S → ℕ) (cfg : RandomizedExecution.Configuration S O),
      positiveCharge c → weightedExpectedCost next c cfg < ⊤ →
        neverStopMass next cfg = 0) ∧
    zenoZeroCharge zenoNext zenoCharge PUnit.unit ∧
    noUnconditionalPolyRep ∧ (∀ K : ℕ, truncatedSearchPolyRep K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K _ _ _ O O' C ψ Q hO hO' hC hψ hQ
    exact unitaryHybridDistance_fixed O O' C ψ Q hO hO' hC hψ hQ
  · intro X _ _ _ n W _ _ _ input f Γ ε P ψ
    exact normalizedTreeAdversaryBound_fixed input f Γ ε P ψ
  · intro I _ _ O P ψ
    exact truncatedTailLaw_fixed O P ψ
  · intro S _ _ O _ _ next cfg
    exact stopTailNeverJointLaw_fixed next cfg
  · intro S _ _ O _ _ next c cfg hc hcost
    exact positiveCharge_finiteCost_noNontermination next c cfg hc hcost
  · exact zenoZeroCharge_fixed
  · exact noUnconditionalPolyRep_fixed
  · intro K
    exact truncatedSearchPolyRep_fixed K

end Qatlib.Concepts.QueryComplexity.DegreeMethod
