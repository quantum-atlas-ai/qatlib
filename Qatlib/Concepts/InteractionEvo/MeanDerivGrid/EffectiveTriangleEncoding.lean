/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveDysonDefinitions

/-!
# A finite-gate Toffoli program

This module defines a fifteen-gate Toffoli decomposition as an effective instruction list and
proves its register legality, coherence, and computational-basis action. The construction uses
the finite gate vocabulary for controlled-controlled-X operations discussed in
[NielsenChuang2010].

## Main statements

* `effectiveToffoli_counts`: fifteen gates, zero queries, and zero postselections.
* `effectiveToffoli_action`: flip the target exactly when both control bits are true.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

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

/-- The fifteen fixed-gate instructions implementing a Toffoli operation with controls `a`, `b`
and target `t`. -/
def effectiveToffoliSteps (a b t : ℕ) : List EffectiveStep :=
  [.fixed (.h t),.fixed (.cx b t),.fixed (.tdg t),.fixed (.cx a t),
   .fixed (.t t),.fixed (.cx b t),.fixed (.tdg t),.fixed (.cx a t),
   .fixed (.t b),.fixed (.t t),.fixed (.h t),.fixed (.cx a b),
   .fixed (.t a),.fixed (.tdg b),.fixed (.cx a b)]

/-- The effective program on `n` wires with instruction list `effectiveToffoliSteps a b t`. -/
def effectiveToffoli (n a b t : ℕ) : EffectiveProgram :=
  ⟨n,effectiveToffoliSteps a b t⟩

/-- The Toffoli program contains fifteen gate instructions, no oracle queries, and no
postselections. -/
theorem effectiveToffoli_counts (n a b t : ℕ) :
    effectiveGates (effectiveToffoli n a b t)=15 ∧
    effectiveQueries (effectiveToffoli n a b t)=0 ∧
    effectivePostselects (effectiveToffoli n a b t)=0 := by
  exact ⟨rfl,rfl,rfl⟩

/-- The Toffoli program is legal when both controls and the target are distinct in-range wires. -/
theorem effectiveToffoli_legal (n a b t : ℕ)
    (ha : a<n) (hb : b<n) (ht : t<n) (hab : a≠b) (hat : a≠t) (hbt : b≠t) :
    effectiveLegal (effectiveToffoli n a b t) := by
  simp [effectiveLegal,effectiveToffoli,effectiveToffoliSteps,effectiveStepLegal,
    finiteCodeLegal,ha,hb,ht,hab,hat,hbt]

/-- The Toffoli program is coherent for every choice of register width and wire indices. -/
theorem effectiveToffoli_coherent (n a b t : ℕ) :
    effectiveCoherent (effectiveToffoli n a b t) := by
  simp [effectiveCoherent,effectiveToffoli,effectiveToffoliSteps]

/-- On a computational-basis state with distinct control and target wires, the program flips the
target bit exactly when both control bits are true. -/
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
