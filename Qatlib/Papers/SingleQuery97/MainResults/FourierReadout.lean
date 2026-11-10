/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermal.FiniteThermalUniformH
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteGateDecisionConsumers
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelianState
import Mathlib.Data.Fintype.EquivFin
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
namespace Qatlib.Papers.SingleQuery97.MainResults.FourierReadout
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
open scoped ENNReal

def dotHom {A m : ℕ} [NeZero A] (z : Fin m → ZMod A) :
    (Fin m → ZMod A) →+ ZMod A where
  toFun s := ∑ i, s i*z i
  map_zero' := by simp
  map_add' s t := by simp [add_mul, Finset.sum_add_distrib]

noncomputable def dotCharacter {A m : ℕ} [NeZero A] (z : Fin m → ZMod A) :
    AddChar (Fin m → ZMod A) ℂ :=
  ZMod.stdAddChar.compAddMonoidHom (dotHom z)

theorem dotCharacter_injective (A m : ℕ) [NeZero A] :
    Function.Injective (dotCharacter (A:=A) (m:=m)) := by
  classical
  intro z w h
  funext i
  have hi := congrArg (fun χ : AddChar (Fin m → ZMod A) ℂ =>
    χ (fun j => if j=i then 1 else 0)) h
  apply ZMod.injective_stdAddChar
  simpa [dotCharacter, dotHom, ite_mul] using hi

noncomputable def dotCharacterEquiv (A m : ℕ) [NeZero A] :
    (Fin m → ZMod A) ≃ AddChar (Fin m → ZMod A) ℂ :=
  Equiv.ofBijective dotCharacter
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨dotCharacter_injective A m, AddChar.card_eq.symm⟩)

theorem vector_character_readout (A m : ℕ) [NeZero A] (z : Fin m → ZMod A) :
    abelianQFT (abelianCharacterState (-dotCharacter z)) = Ket (dotCharacter z) := by
  rw [abelianQFT_characterState, neg_neg]

noncomputable def negativeDotCharacterEquiv (A m : ℕ) [NeZero A] :
    (Fin m → ZMod A) ≃ AddChar (Fin m → ZMod A) ℂ :=
  Equiv.ofBijective (fun z => -dotCharacter z)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨(by intro z w h; exact dotCharacter_injective A m (neg_injective h)), AddChar.card_eq.symm⟩)

theorem actual_positive_fourier_readout (A m : ℕ) [NeZero A] (z : Fin m → ZMod A) :
    Run (1 : Matrix (Fin m → ZMod A) (Fin m → ZMod A) ℂ)
      (Qatlib.Concepts.WalkFind.UniformThree.fourierCircuit (negativeDotCharacterEquiv A m))
      (Qatlib.Concepts.WalkFind.UniformThree.characterState (-dotCharacter z)) = Ket z := by
  funext x
  simp only [Qatlib.Concepts.WalkFind.UniformThree.fourierCircuit, Run,
    Qatlib.Concepts.WalkFind.UniformThree.applyGate_fourierGate,
    Qatlib.Concepts.WalkFind.UniformThree.fourier_characterState]
  change Ket (negativeDotCharacterEquiv A m z) (negativeDotCharacterEquiv A m x) = Ket z x
  simp only [Qatlib.Foundations.PureStateMath.Ket, Equiv.apply_eq_iff_eq]

theorem actual_uniform_h_word (n : ℕ) :
    finiteCodeWordMatrix n (thermalUniformHWord (List.finRange n)) = HadamardN n ∧
    GateCount (finiteCodeCircuit n (thermalUniformHWord (List.finRange n)))=n ∧
    QueryCount (finiteCodeCircuit n (thermalUniformHWord (List.finRange n)))=0 := by
  refine ⟨thermalUniformHWord_all n, ?_, ?_⟩
  · simpa only [List.length_finRange] using (thermalUniformHWord_cost (List.finRange n)).1
  · exact (thermalUniformHWord_cost (List.finRange n)).2

theorem prior_decoder_error_le_tail {Y Z : Type} (p : PMF Y) (code : Y → Z)
    (decoder : Z → Y) (good : Y → Prop)
    (hcorrect : ∀ y, good y → decoder (code y)=y) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (p.map (fun y => (y,decoder (code y)))) (fun q => q.2≠q.1) ≤
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun y => ¬good y) := by
  classical
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_le_of_forall
  intro y
  by_cases hg : good y
  · simp [hg, hcorrect y hg]
  · simp only [hg, not_false_eq_true, ite_true]
    split_ifs <;> simp

end Qatlib.Papers.SingleQuery97.MainResults.FourierReadout
