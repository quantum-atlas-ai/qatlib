/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false
noncomputable section
namespace Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
open Qatlib Matrix
open scoped BigOperators

def thermalToffoliWord (a b t : ℕ) : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode :=
  [.h t, .cx b t, .tdg t, .cx a t, .t t, .cx b t, .tdg t,
   .cx a t, .t b, .t t, .h t, .cx a b, .t a, .tdg b, .cx a b]

theorem thermalToffoliWord_compile (n : ℕ) (a b t : Fin n)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalToffoliWord a.val b.val t.val) =
      Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionCompile (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.toffoliLocalSteps a b t) := by
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hat' : a.val ≠ t.val := fun h => hat (Fin.ext h)
  have hbt' : b.val ≠ t.val := fun h => hbt (Fin.ext h)
  simp [thermalToffoliWord, Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit, Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeMatrix,
    a.isLt, b.isLt, t.isLt, hab', hat', hbt', Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionCompile,
    Qatlib.Concepts.GateVocabulary.LocalReflectionGates.toffoliLocalSteps, Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionGateMatrix]

theorem thermalToffoliWord_exact (n : ℕ) (a b t : Fin n)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordRun n (thermalToffoliWord a.val b.val t.val) (Qatlib.Foundations.PureStateMath.Ket x) =
      some (Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (x a && x b)))) ∧
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalToffoliWord a.val b.val t.val)) = 15 ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalToffoliWord a.val b.val t.val)) = 0 := by
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hat' : a.val ≠ t.val := fun h => hat (Fin.ext h)
  have hbt' : b.val ≠ t.val := fun h => hbt (Fin.ext h)
  have hl : Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalToffoliWord a.val b.val t.val) = true := by
    simp [thermalToffoliWord, Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal, Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal,
      a.isLt, b.isLt, t.isLt, hab', hat', hbt']
  refine ⟨?_, ?_, (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).1⟩
  · simp only [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordRun, hl, if_true]
    rw [thermalToffoliWord_compile n a b t hab hat hbt,
      (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.local_toffoli_fifteen_exact n a b t hab hat hbt).2.2 x]
  · simpa [thermalToffoliWord] using (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n
      (thermalToffoliWord a.val b.val t.val)).2

theorem thermalToffoliWord_coherent (n : ℕ) (a b t : Fin n)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n)) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ)
      (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalToffoliWord a.val b.val t.val)) psi =
      ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • Qatlib.Foundations.PureStateMath.Ket
        (Function.update x t (x t ^^ (x a && x b))) := by
  have he : psi = ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • Qatlib.Foundations.PureStateMath.Ket x := by
    funext z
    simp [Qatlib.Foundations.PureStateMath.Ket, Finset.sum_apply]
  have hk (x : Qatlib.Foundations.PureStateMath.Reg n) : Qatlib.Foundations.PureStateMath.ApplyGate (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionProgramMatrix (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.toffoliLocalSteps a b t))
      (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (x a && x b))) := by
    rw [← Qatlib.Concepts.GateVocabulary.LocalReflectionGates.run_reflectionCompile]
    exact (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.local_toffoli_fifteen_exact n a b t hab hat hbt).2.2 x
  rw [thermalToffoliWord_compile n a b t hab hat hbt,
      Qatlib.Concepts.GateVocabulary.LocalReflectionGates.run_reflectionCompile]
  conv_lhs => rw [he]
  simp only [Qatlib.Foundations.PureStateMath.ApplyGate, Matrix.mulVec_sum, Matrix.mulVec_smul]
  exact Finset.sum_congr rfl (fun x _ => congrArg (fun v => psi x • v) (hk x))

end Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
