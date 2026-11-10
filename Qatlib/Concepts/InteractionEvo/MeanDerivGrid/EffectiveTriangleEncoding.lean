/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveDysonDefinitions
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Matrix

def effectiveToffoliSteps (a b t : ℕ) : List EffectiveStep :=
  [.fixed (.h t),.fixed (.cx b t),.fixed (.tdg t),.fixed (.cx a t),
   .fixed (.t t),.fixed (.cx b t),.fixed (.tdg t),.fixed (.cx a t),
   .fixed (.t b),.fixed (.t t),.fixed (.h t),.fixed (.cx a b),
   .fixed (.t a),.fixed (.tdg b),.fixed (.cx a b)]

def effectiveToffoli (n a b t : ℕ) : EffectiveProgram :=
  ⟨n,effectiveToffoliSteps a b t⟩

theorem effectiveToffoli_counts (n a b t : ℕ) :
    effectiveGates (effectiveToffoli n a b t)=15 ∧
    effectiveQueries (effectiveToffoli n a b t)=0 ∧
    effectivePostselects (effectiveToffoli n a b t)=0 := by
  exact ⟨rfl,rfl,rfl⟩

theorem effectiveToffoli_legal (n a b t : ℕ)
    (ha : a<n) (hb : b<n) (ht : t<n) (hab : a≠b) (hat : a≠t) (hbt : b≠t) :
    effectiveLegal (effectiveToffoli n a b t) := by
  simp [effectiveLegal,effectiveToffoli,effectiveToffoliSteps,effectiveStepLegal,
    finiteCodeLegal,ha,hb,ht,hab,hat,hbt]

theorem effectiveToffoli_coherent (n a b t : ℕ) :
    effectiveCoherent (effectiveToffoli n a b t) := by
  simp [effectiveCoherent,effectiveToffoli,effectiveToffoliSteps]

theorem effectiveToffoli_action (n : ℕ) (a b t : Fin n)
    (hab : a≠b) (hat : a≠t) (hbt : b≠t) (x : Reg n) :
    effectiveMatrix (effectiveToffoli n a.val b.val t.val) (fun _ _ => 1) *ᵥ Ket x =
      Ket (Function.update x t (x t ^^ (x a && x b))) := by
  have habv : a.val≠b.val := fun h => hab (Fin.ext h)
  have hatv : a.val≠t.val := fun h => hat (Fin.ext h)
  have hbtv : b.val≠t.val := fun h => hbt (Fin.ext h)
  have hm : effectiveMatrix (effectiveToffoli n a.val b.val t.val) (fun _ _ => 1) =
      reflectionProgramMatrix (toffoliLocalSteps a b t) := by
    have hr (gs : List (ReflectionGate n)) : reflectionProgramMatrix gs =
        (gs.map reflectionGateMatrix).reverse.prod := by
      induction gs with
      | nil => rfl
      | cons g gs ih => simp [reflectionProgramMatrix,ih]
    rw [hr]
    unfold effectiveMatrix
    congr 2
    simp only [effectiveToffoli,effectiveToffoliSteps,toffoliLocalSteps,List.map_cons,
      List.map_nil,effectiveStepMatrix,reflectionGateMatrix]
    simp [finiteCodeMatrix,a.isLt,b.isLt,t.isLt,habv,hatv,hbtv]

  rw [hm]
  have hh := (local_toffoli_fifteen_exact n a b t hab hat hbt).2.2 x
  rw [run_reflectionCompile] at hh
  exact hh

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
