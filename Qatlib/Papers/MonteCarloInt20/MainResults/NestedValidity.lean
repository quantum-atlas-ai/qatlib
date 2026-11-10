/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.NestedWord
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open Matrix Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedWord
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Papers.MonteCarloInt20.MainResults.NestedValidity

noncomputable local instance dataDecision (n M : ℕ) (I : Type) [DecidableEq I] :
    DecidableEq ((Reg n × Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn.Inner M I) × Bool) :=
  instDecidableEqProd

noncomputable local instance fullDecision (n M N : ℕ) (I : Type) [DecidableEq I] :
    DecidableEq (Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn.Inner N ((Reg n × Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn.Inner M I) × Bool)) :=
  instDecidableEqProd

def ValidWord {I : Type} [Fintype I] [DecidableEq I] (w : GateWord (Matrix I I ℂ)) : Prop :=
  ∀ a ∈ w,a.2 ∈ unitaryGroup I ℂ

theorem validWord_eval {I : Type} [Fintype I] [DecidableEq I]
    {w : GateWord (Matrix I I ℂ)} (hw : ValidWord w) : wordEval w ∈ unitaryGroup I ℂ := by
  induction w with
  | nil => exact (unitaryGroup I ℂ).one_mem
  | cons a w ih =>
    exact (unitaryGroup I ℂ).mul_mem (ih (fun p hp => hw p (List.mem_cons_of_mem _ hp)))
      (hw a List.mem_cons_self)

theorem validWord_lift {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (f : Matrix I I ℂ → Matrix J J ℂ)
    (hf : ∀ U,U ∈ unitaryGroup I ℂ → f U ∈ unitaryGroup J ℂ)
    {w : GateWord (Matrix I I ℂ)} (hw : ValidWord w) : ValidWord (liftWord f w) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact hf q.2 (hw q hq)

theorem validWord_adjoint {I : Type} [Fintype I] [DecidableEq I]
    {w : GateWord (Matrix I I ℂ)} (hw : ValidWord w) : ValidWord (adjointWord w) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hp)
  exact conjTranspose_mem_unitaryGroup (hw q hq)

theorem stepMatrix_unitary {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (C : Circuit I) (hO : O ∈ unitaryGroup I ℂ) (hC : IsUnitaryCircuit C)
    (s : Step I) (hs : s ∈ C) : stepMatrix O s ∈ unitaryGroup I ℂ := by
  cases s with
  | query => exact hO
  | gate U => exact hC U hs

theorem selectedInnerWord_valid {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : ℕ) (hM : 2 ≤ M) (A : J → Matrix I I ℂ) (i₀ : I) (S : J → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) : ValidWord (I:=J × Inner M I) (selectedInnerWord M A i₀ S) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
  apply select_unitary
  intro j
  apply stepMatrix_unitary (I:=Inner M I) _ (countedAECircuit M (A j) i₀)
  · exact tensorGate_unitary (by simp)
      (controlOracle_unitary (prepared_aa_reflection_and_access (A j) i₀ (S j) (hA j)).1)
  · exact (prepared_ae_expanded_access_and_output M hM (A j) i₀ (S j) (hA j)).2.2.1
  · exact List.mem_map.mpr ⟨a,ha,rfl⟩

theorem preparationWord_valid {I : Type} [Fintype I] [DecidableEq I]
    (n M : ℕ) (hM : 2 ≤ M) (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) (D : ℝ) (g : ℝ → ℝ)
    (hg : ∀ k : Fin M,g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1) :
    ValidWord (I:=((Reg n × Inner M I) × Bool)) (preparationWord n M A i₀ S D g) := by
  intro p hp
  simp only [preparationWord,List.mem_append,List.mem_singleton] at hp
  rcases hp with (rfl | hp) | rfl
  · exact tensorGate_unitary (tensorGate_unitary (hadamardN_unitary n) (by simp)) (by simp)
  · exact validWord_lift (rightSpectatorHom : Matrix (Reg n × Inner M I) (Reg n × Inner M I) ℂ →
      Matrix ((Reg n × Inner M I) × Bool) ((Reg n × Inner M I) × Bool) ℂ)
      (fun U hU => tensorGate_unitary hU (by simp)) (selectedInnerWord_valid M hM A i₀ S hA) p hp
  · exact payoffRotation_mem_unitaryGroup _ (fun p => hg p.2.1)

theorem initializeHom_unitary {I : Type} [Fintype I] [DecidableEq I]
    (N : ℕ) (U : Matrix I I ℂ) (hU : U ∈ unitaryGroup I ℂ) :
    initializeHom N U ∈ unitaryGroup (Inner N I) ℂ :=
  tensorGate_unitary (by simp) (tensorGate_unitary (by simp) hU)

theorem controlledHom_unitary {I : Type} [Fintype I] [DecidableEq I]
    (N : ℕ) (U : Matrix I I ℂ) (hU : U ∈ unitaryGroup I ℂ) :
    controlledHom N U ∈ unitaryGroup (Inner N I) ℂ :=
  tensorGate_unitary (by simp) (controlOracle_unitary hU)

theorem expandedOuterWord_valid {I : Type} [Fintype I] [DecidableEq I]
    (N : ℕ) (hN : 2 ≤ N) (i₀ : I) (S : Finset I)
    (w : GateWord (Matrix I I ℂ)) (hw : ValidWord w) :
    ValidWord (I:=Inner N I) ((aeAccessWord (I:=I) N).flatMap (expandOuterStep N i₀ S w)) := by
  have hP := validWord_eval hw
  have hC := (prepared_ae_expanded_access_and_output N hN (wordEval w) i₀ S hP).2.2.1
  have hO : aeControlledGate N (preparedMark S) ∈ unitaryGroup (Inner N I) ℂ :=
    tensorGate_unitary (by simp) (controlOracle_unitary (prepared_aa_reflection_and_access (wordEval w) i₀ S hP).1)
  intro p hp
  obtain ⟨a,ha,hp⟩ := List.mem_flatMap.mp hp
  have hs : aeAccessInstruction N (wordEval w) i₀ a ∈ countedAECircuit N (wordEval w) i₀ :=
    List.mem_map.mpr ⟨a,ha,rfl⟩
  cases a with
  | «initialize» => exact validWord_lift (initializeHom N) (initializeHom_unitary N) hw p hp
  | prepareForward => exact validWord_lift (controlledHom N) (controlledHom_unitary N) hw p hp
  | prepareBackward => exact validWord_lift (controlledHom N) (controlledHom_unitary N) (validWord_adjoint hw) p hp
  | sourceReflection =>
    simp only [expandOuterStep,List.mem_singleton] at hp
    subst p
    exact stepMatrix_unitary (I:=Inner N I) _ _ hO hC _ hs
  | mark =>
    simp only [expandOuterStep,List.mem_singleton] at hp
    subst p
    exact hO
  | fixed U =>
    simp only [expandOuterStep,List.mem_singleton] at hp
    subst p
    exact stepMatrix_unitary (I:=Inner N I) _ _ hO hC _ hs

theorem nestedWord_valid {I : Type} [Fintype I] [DecidableEq I]
    (n M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) (D : ℝ) (g : ℝ → ℝ)
    (hg : ∀ k : Fin M,g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1) :
    ValidWord (I:=Inner N ((Reg n × Inner M I) × Bool)) (nestedWord n M N (by omega) A i₀ S D g) := by
  exact expandedOuterWord_valid (I:=((Reg n × Inner M I) × Bool)) N hN ((ZeroStr n,innerSeed M (by omega) i₀),false)
    (Finset.univ.filter (fun p => p.2=true)) (preparationWord n M A i₀ S D g)
    (preparationWord_valid n M hM A i₀ S hA D g hg)

end Qatlib.Papers.MonteCarloInt20.MainResults.NestedValidity
