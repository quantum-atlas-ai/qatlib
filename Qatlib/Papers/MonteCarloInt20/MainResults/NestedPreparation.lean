/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.QaeLaw.ActualReadout
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.QuantumPayoffEstimation

/-!
# Coherent preparations for nested amplitude estimation

`innerUnitary` evaluates a counted amplitude-estimation circuit without discarding its
workspace. `samplePreparation` selects these inner circuits over a uniform sample register, and
`outerPreparation` rotates a new flag according to the payoff of the inner estimate.

The marginal and Born-probability identities express the nested flag probability as the sample
average of payoff expectations under the actual inner laws, as required by the scheme of
[KanekoEtAl2020].

## Main statements

* `innerState_marginal`: recovers `aeLaw` by summing over the retained workspace.
* `samplePreparation_born`: factors the joint Born probability into a uniform sample weight and
  an inner probability.
* `nested_flag_born`: identifies the final flag probability with the nested payoff expectation.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn

/-- Evaluate a circuit as a matrix, multiplying each successive operation on the left. -/
def runMatrix {I : Type} [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) : Circuit I → Matrix I I ℂ
  | [] => 1
  | .gate U :: C => runMatrix O C*U
  | .query :: C => runMatrix O C*O

/-- Applying the circuit evaluation matrix to a state equals running the circuit on that state. -/
theorem runMatrix_apply {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (C : Circuit I) (v : QState I) :
    ApplyGate (runMatrix O C) v=Run O C v := by
  induction C generalizing v with
  | nil => simp [runMatrix,Run]
  | cons c C ih => cases c <;> simp only [runMatrix,applyGate_mul,ih,Run]

/-- A unitary circuit evaluated against a unitary oracle has a unitary evaluation matrix. -/
theorem runMatrix_unitary {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (C : Circuit I) (hO : O ∈ unitaryGroup I ℂ)
    (hC : IsUnitaryCircuit C) : runMatrix O C ∈ unitaryGroup I ℂ := by
  induction C with
  | nil => exact (unitaryGroup I ℂ).one_mem
  | cons c C ih =>
    cases c with
    | gate U =>
      have hc := (isUnitaryCircuit_gate U C).mp hC
      exact (unitaryGroup I ℂ).mul_mem (ih hc.2) hc.1
    | query => exact (unitaryGroup I ℂ).mul_mem (ih ((isUnitaryCircuit_query C).mp hC)) hO

/-- The estimate register, Boolean auxiliary register, and retained workspace of inner amplitude
estimation. -/
abbrev Inner (M : ℕ) (I : Type) := Fin M × (Bool × I)

/-- The initial inner configuration with estimate zero, false auxiliary bit, and workspace state
`i₀`. -/
def innerSeed {I : Type} (M : ℕ) (hM : 0 < M) (i₀ : I) : Inner M I := (⟨0,hM⟩,(false,i₀))

/-- The evaluation matrix of the counted amplitude-estimation circuit with its controlled
marking oracle. -/
def innerUnitary {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (A : Matrix I I ℂ) (i₀ : I) (S : Finset I) : Matrix (Inner M I) (Inner M I) ℂ :=
  runMatrix (aeControlledGate M (preparedMark S)) (countedAECircuit M A i₀)

/-- For `M ≥ 2` and unitary `A`, the inner amplitude-estimation matrix is unitary. -/
theorem innerUnitary_unitary {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (i₀ : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) : innerUnitary M A i₀ S ∈ unitaryGroup (Inner M I) ℂ := by
  apply runMatrix_unitary
  · exact tensorGate_unitary (by simp)
      (controlOracle_unitary (prepared_aa_reflection_and_access A i₀ S hA).1)
  · exact (prepared_ae_expanded_access_and_output M hM A i₀ S hA).2.2.1

/-- The state obtained by applying the inner amplitude-estimation matrix to its initial basis
state. -/
def innerState {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 0 < M) (A : Matrix I I ℂ) (i₀ : I) (S : Finset I) : QState (Inner M I) :=
  ApplyGate (innerUnitary M A i₀ S) (Ket (innerSeed M hM i₀))

/-- The inner seed basis vector factors into the zero estimate, false auxiliary bit, and
workspace basis vectors. -/
theorem innerSeed_ket {I : Type} [DecidableEq I] (M : ℕ) (hM : 0 < M) (i₀ : I) :
    Ket (innerSeed M hM i₀)=TensorState (Ket (⟨0,hM⟩ : Fin M)) (TensorState (Ket false) (Ket i₀)) := by
  funext p
  obtain ⟨k,b,i⟩ := p
  simp only [innerSeed,Ket,TensorState,Prod.mk.injEq]
  split_ifs <;> simp_all

/-- For `M ≥ 2` and unitary preparation, summing the inner state's Born probabilities over its
auxiliary bit and workspace gives `aeLaw`. -/
theorem innerState_marginal {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (i₀ : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (k : Fin M) :
    (aeLaw M A i₀ S hA hM).prob k =
      ∑ b : Bool,∑ i : I,BornProb (innerState M (by omega) A i₀ S) (k,(b,i)) := by
  have he : innerState M (by omega) A i₀ S =
      Run (aeControlledGate M (preparedMark S)) (countedAECircuit M A i₀)
      (TensorState (Ket (⟨0,by omega⟩ : Fin M)) (TensorState (Ket false) (Ket i₀))) := by
    rw [innerState,innerSeed_ket,innerUnitary,runMatrix_apply]
  simp only [aeLaw,MeasureProb,Finset.sum_filter,← he,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single k]
  · simp
  · intro q _ hq
    simp [hq]
  · simp

/-- The Born-weighted expectation of any function of the inner estimate equals its expectation
under `aeLaw`. -/
theorem innerState_payoff {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (i₀ : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (f : Fin M → ℝ) :
    (∑ w : Inner M I,BornProb (innerState M (by omega) A i₀ S) w*f w.1)=
      ∑ k,(aeLaw M A i₀ S hA hM).prob k*f k := by
  simp only [Fintype.sum_prod_type,innerState_marginal M hM A i₀ S hA,Finset.sum_mul]

/-- Prepare uniform sample amplitudes and apply the sample-selected inner amplitude-estimation
matrices. -/
def samplePreparation {I : Type} [Fintype I] [DecidableEq I] (n M : ℕ)
    (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I) :
    Matrix (Reg n × Inner M I) (Reg n × Inner M I) ℂ :=
  select (fun j => innerUnitary M (A j) i₀ (S j))*TensorGate (HadamardN n) 1

/-- For `M ≥ 2` and unitary sample preparations, the coherent sample preparation is unitary. -/
theorem samplePreparation_unitary {I : Type} [Fintype I] [DecidableEq I]
    (n M : ℕ) (hM : 2 ≤ M) (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) :
    samplePreparation n M A i₀ S ∈ unitaryGroup (Reg n × Inner M I) ℂ :=
  (unitaryGroup _ ℂ).mul_mem
    (select_unitary _ (fun j => innerUnitary_unitary M hM (A j) i₀ (S j) (hA j)))
    (tensorGate_unitary (hadamardN_unitary n) (by simp))

/-- Applying a matrix to a basis vector selects the corresponding matrix column. -/
theorem apply_ket_column {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (i j : I) : ApplyGate A (Ket j) i=A i j := by
  simp [ApplyGate,Matrix.mulVec,dotProduct,Ket]

/-- Each amplitude of the sample preparation is the sample Hadamard amplitude times the
corresponding inner-state amplitude. -/
theorem samplePreparation_amplitude {I : Type} [Fintype I] [DecidableEq I]
    (n M : ℕ) (hM : 0 < M) (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (j : Reg n) (w : Inner M I) :
    ApplyGate (samplePreparation n M A i₀ S) (Ket (ZeroStr n,innerSeed M hM i₀)) (j,w)=
      HadamardN n j (ZeroStr n)*innerState M hM (A j) i₀ (S j) w := by
  rw [apply_ket_column,innerState,apply_ket_column]
  simp [samplePreparation,Matrix.mul_apply,select,TensorGate,
    Fintype.sum_prod_type,Matrix.one_apply,mul_comm]

/-- Every output amplitude of the `n`-qubit Hadamard transform of the zero word has squared norm
`1 / 2 ^ n`. -/
theorem uniform_hadamard_born (n : ℕ) (j : Reg n) :
    ‖HadamardN n j (ZeroStr n)‖^2=1/(2:ℝ)^n := by
  rw [hadamardN_apply_zero_right,norm_pow,pow_right_comm,norm_inv,inv_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  simp [inv_pow]

/-- The joint Born probability of a sample and inner configuration equals `1 / 2 ^ n` times the
corresponding inner-state Born probability. -/
theorem samplePreparation_born {I : Type} [Fintype I] [DecidableEq I]
    (n M : ℕ) (hM : 0 < M) (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (j : Reg n) (w : Inner M I) :
    BornProb (ApplyGate (samplePreparation n M A i₀ S) (Ket (ZeroStr n,innerSeed M hM i₀))) (j,w)=
      (1/(2:ℝ)^n)*BornProb (innerState M hM (A j) i₀ (S j)) w := by
  rw [BornProb,samplePreparation_amplitude,norm_mul,mul_pow,uniform_hadamard_born]
  rfl

/-- Prepare the sample and inner-estimation registers and rotate a new flag by `g` of the scaled
inner estimate. -/
def outerPreparation {I : Type} [Fintype I] [DecidableEq I] (n M : ℕ)
    (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I) (D : ℝ) (g : ℝ → ℝ) :
    Matrix ((Reg n × Inner M I) × Bool) ((Reg n × Inner M I) × Bool) ℂ :=
  payoffPreparation (samplePreparation n M A i₀ S) (fun p => g (D*aeEstimate M p.2.1))

/-- For `M ≥ 2`, unitary sample preparations, and payoff values in `[0, 1]`, the outer payoff
preparation is unitary. -/
theorem outerPreparation_unitary {I : Type} [Fintype I] [DecidableEq I]
    (n M : ℕ) (hM : 2 ≤ M) (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) (D : ℝ) (g : ℝ → ℝ)
    (hg : ∀ k : Fin M,g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1) :
    outerPreparation n M A i₀ S D g ∈ unitaryGroup ((Reg n × Inner M I) × Bool) ℂ :=
  payoffPreparation_mem_unitaryGroup _ _ (samplePreparation_unitary n M hM A i₀ S hA) (fun p => hg p.2.1)

/-- For unitary sample preparations and payoff values in `[0, 1]`, the outer preparation's
true-flag probability is the uniform sample average of the payoff expectations under the
actual inner estimation laws [KanekoEtAl2020]. -/
theorem nested_flag_born {I : Type} [Fintype I] [DecidableEq I]
    (n M : ℕ) (hM : 2 ≤ M) (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) (D : ℝ) (g : ℝ → ℝ)
    (hg : ∀ k : Fin M,g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1) :
    MeasureProb (ApplyGate (outerPreparation n M A i₀ S D g)
      (Ket ((ZeroStr n,innerSeed M (by omega) i₀),false)))
      (Finset.univ.filter (fun p => p.2=true))=
      (1/(2:ℝ)^n)*∑ j : Reg n,∑ k : Fin M,(aeLaw M (A j) i₀ (S j) (hA j) hM).prob k*g (D*aeEstimate M k) := by
  have hk := (payoff_actual_rotation_and_mean (samplePreparation n M A i₀ S)
    (ZeroStr n,innerSeed M (by omega) i₀) (fun p => g (D*aeEstimate M p.2.1))
    (samplePreparation_unitary n M hM A i₀ S hA) (fun p => hg p.2.1)).2
  change _ = _ at hk
  rw [outerPreparation,hk]
  simp_rw [Fintype.sum_prod_type,samplePreparation_born]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← innerState_payoff M hM (A j) i₀ (S j) (hA j) (fun k => g (D*aeEstimate M k)),Finset.mul_sum]
  simp only [Fintype.sum_prod_type,mul_assoc]

end Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn
