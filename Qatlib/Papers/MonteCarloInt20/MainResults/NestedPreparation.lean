/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.QaeLaw.ActualReadout
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.QuantumPayoffEstimation
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

def runMatrix {I : Type} [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) : Circuit I → Matrix I I ℂ
  | [] => 1
  | .gate U :: C => runMatrix O C*U
  | .query :: C => runMatrix O C*O

theorem runMatrix_apply {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (C : Circuit I) (v : QState I) :
    ApplyGate (runMatrix O C) v=Run O C v := by
  induction C generalizing v with
  | nil => simp [runMatrix,Run]
  | cons c C ih => cases c <;> simp only [runMatrix,applyGate_mul,ih,Run]

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

abbrev Inner (M : ℕ) (I : Type) := Fin M × (Bool × I)

def innerSeed {I : Type} (M : ℕ) (hM : 0 < M) (i₀ : I) : Inner M I := (⟨0,hM⟩,(false,i₀))

def innerUnitary {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (A : Matrix I I ℂ) (i₀ : I) (S : Finset I) : Matrix (Inner M I) (Inner M I) ℂ :=
  runMatrix (aeControlledGate M (preparedMark S)) (countedAECircuit M A i₀)

theorem innerUnitary_unitary {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (i₀ : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) : innerUnitary M A i₀ S ∈ unitaryGroup (Inner M I) ℂ := by
  apply runMatrix_unitary
  · exact tensorGate_unitary (by simp)
      (controlOracle_unitary (prepared_aa_reflection_and_access A i₀ S hA).1)
  · exact (prepared_ae_expanded_access_and_output M hM A i₀ S hA).2.2.1

def innerState {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 0 < M) (A : Matrix I I ℂ) (i₀ : I) (S : Finset I) : QState (Inner M I) :=
  ApplyGate (innerUnitary M A i₀ S) (Ket (innerSeed M hM i₀))

theorem innerSeed_ket {I : Type} [DecidableEq I] (M : ℕ) (hM : 0 < M) (i₀ : I) :
    Ket (innerSeed M hM i₀)=TensorState (Ket (⟨0,hM⟩ : Fin M)) (TensorState (Ket false) (Ket i₀)) := by
  funext p
  obtain ⟨k,b,i⟩ := p
  simp only [innerSeed,Ket,TensorState,Prod.mk.injEq]
  split_ifs <;> simp_all

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

theorem innerState_payoff {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (i₀ : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (f : Fin M → ℝ) :
    (∑ w : Inner M I,BornProb (innerState M (by omega) A i₀ S) w*f w.1)=
      ∑ k,(aeLaw M A i₀ S hA hM).prob k*f k := by
  simp only [Fintype.sum_prod_type,innerState_marginal M hM A i₀ S hA,Finset.sum_mul]

def samplePreparation {I : Type} [Fintype I] [DecidableEq I] (n M : ℕ)
    (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I) :
    Matrix (Reg n × Inner M I) (Reg n × Inner M I) ℂ :=
  select (fun j => innerUnitary M (A j) i₀ (S j))*TensorGate (HadamardN n) 1

theorem samplePreparation_unitary {I : Type} [Fintype I] [DecidableEq I]
    (n M : ℕ) (hM : 2 ≤ M) (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) :
    samplePreparation n M A i₀ S ∈ unitaryGroup (Reg n × Inner M I) ℂ :=
  (unitaryGroup _ ℂ).mul_mem
    (select_unitary _ (fun j => innerUnitary_unitary M hM (A j) i₀ (S j) (hA j)))
    (tensorGate_unitary (hadamardN_unitary n) (by simp))

theorem apply_ket_column {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (i j : I) : ApplyGate A (Ket j) i=A i j := by
  simp [ApplyGate,Matrix.mulVec,dotProduct,Ket]

theorem samplePreparation_amplitude {I : Type} [Fintype I] [DecidableEq I]
    (n M : ℕ) (hM : 0 < M) (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (j : Reg n) (w : Inner M I) :
    ApplyGate (samplePreparation n M A i₀ S) (Ket (ZeroStr n,innerSeed M hM i₀)) (j,w)=
      HadamardN n j (ZeroStr n)*innerState M hM (A j) i₀ (S j) w := by
  rw [apply_ket_column,innerState,apply_ket_column]
  simp [samplePreparation,Matrix.mul_apply,select,TensorGate,
    Fintype.sum_prod_type,Matrix.one_apply,mul_comm]

theorem uniform_hadamard_born (n : ℕ) (j : Reg n) :
    ‖HadamardN n j (ZeroStr n)‖^2=1/(2:ℝ)^n := by
  rw [hadamardN_apply_zero_right,norm_pow,pow_right_comm,norm_inv,inv_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  simp [inv_pow]

theorem samplePreparation_born {I : Type} [Fintype I] [DecidableEq I]
    (n M : ℕ) (hM : 0 < M) (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (j : Reg n) (w : Inner M I) :
    BornProb (ApplyGate (samplePreparation n M A i₀ S) (Ket (ZeroStr n,innerSeed M hM i₀))) (j,w)=
      (1/(2:ℝ)^n)*BornProb (innerState M hM (A j) i₀ (S j)) w := by
  rw [BornProb,samplePreparation_amplitude,norm_mul,mul_pow,uniform_hadamard_born]
  rfl

def outerPreparation {I : Type} [Fintype I] [DecidableEq I] (n M : ℕ)
    (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I) (D : ℝ) (g : ℝ → ℝ) :
    Matrix ((Reg n × Inner M I) × Bool) ((Reg n × Inner M I) × Bool) ℂ :=
  payoffPreparation (samplePreparation n M A i₀ S) (fun p => g (D*aeEstimate M p.2.1))

theorem outerPreparation_unitary {I : Type} [Fintype I] [DecidableEq I]
    (n M : ℕ) (hM : 2 ≤ M) (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) (D : ℝ) (g : ℝ → ℝ)
    (hg : ∀ k : Fin M,g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1) :
    outerPreparation n M A i₀ S D g ∈ unitaryGroup ((Reg n × Inner M I) × Bool) ℂ :=
  payoffPreparation_mem_unitaryGroup _ _ (samplePreparation_unitary n M hM A i₀ S hA) (fun p => hg p.2.1)

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
