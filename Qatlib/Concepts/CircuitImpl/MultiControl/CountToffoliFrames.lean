/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.CountGateMergers
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl.CountToffoliFrames
open Matrix
open scoped Classical BigOperators

private def earlyToffoli {N : ℕ} (a b t : Fin N) : List (ReflectionGate N) :=
  [.inl (t,Hadamard), .inr (b,t), .inl (t,tGateAdj), .inr (a,t), .inl (t,tGate),
    .inr (b,t), .inl (t,tGateAdj), .inr (a,t), .inl (b,tGate), .inl (t,tGate)]

def sourceToffoliMiddle {N : ℕ} (a b t : Fin N) : List (ReflectionGate N) :=
  [.inr (b,t), .inl (t,tGateAdj), .inr (a,t), .inl (t,tGate),
    .inr (b,t), .inl (t,tGateAdj), .inr (a,t), .inl (b,tGate), .inl (t,tGate),
    .inr (a,b), .inl (b,tGateAdj), .inr (a,b)]

def sourceToffoliFramed {N : ℕ} (a b t : Fin N) : List (ReflectionGate N) :=
  [.inl (a,tGate), .inl (t,Hadamard)] ++ sourceToffoliMiddle a b t ++ [.inl (t,Hadamard)]

private theorem singleton_matrix {N : ℕ} (g : ReflectionGate N) :
    reflectionProgramMatrix [g] = reflectionGateMatrix g := by simp [reflectionProgramMatrix]

theorem sourceToffoliFramed_matrix {N : ℕ} (a b t : Fin N)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    reflectionProgramMatrix (sourceToffoliFramed a b t) = reflectionProgramMatrix (toffoliLocalSteps a b t) := by
  let P : ReflectionGate N := .inl (a,tGate)
  let H : ReflectionGate N := .inl (t,Hadamard)
  let tail : List (ReflectionGate N) := [.inr (a,b), P, .inl (b,tGateAdj), .inr (a,b)]
  let xs : List (ReflectionGate N) := earlyToffoli a b t ++ [.inr (a,b)]
  let ys : List (ReflectionGate N) := [.inl (b,tGateAdj), .inr (a,b), H]
  have hOld := toffoliLocalSteps_legal a b t hab hat hbt
  have htail : reflectionLegal tail := by
    intro g hg
    apply hOld g
    simp only [tail, P, toffoliLocalSteps, List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
    tauto
  have hxs : reflectionLegal xs := by
    intro g hg
    apply hOld g
    simp only [xs, earlyToffoli, toffoliLocalSteps, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hg ⊢
    tauto
  have havH : ∀ g ∈ tail, t ∉ reflectionGateWires g := by
    intro g hg
    simp only [tail, P, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;>
      simp [reflectionGateWires, hat.symm, hbt.symm]
  have hcommH : reflectionGateMatrix H * reflectionProgramMatrix tail =
      reflectionProgramMatrix tail * reflectionGateMatrix H :=
    source_wireGate_commute_table t Hadamard tail htail havH
  have hmoveH : reflectionProgramMatrix (earlyToffoli a b t ++ [H] ++ tail) =
      reflectionProgramMatrix (earlyToffoli a b t ++ tail ++ [H]) := by
    simp only [reflectionProgramMatrix_append, singleton_matrix]
    simpa only [Matrix.mul_assoc] using!
      congrArg (fun Q : Matrix (Reg N) (Reg N) ℂ => Q*reflectionProgramMatrix (earlyToffoli a b t)) hcommH.symm
  have havP : ∀ g ∈ xs, match g with
      | .inl (v,_) => a ≠ v
      | .inr (_,z) => a ≠ z := by
    intro g hg
    simp only [xs, earlyToffoli, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals first | exact hat | exact hab
  have hcommP : reflectionGateMatrix P * reflectionProgramMatrix xs =
      reflectionProgramMatrix xs * reflectionGateMatrix P := by
    change wireGate N a tGate * reflectionProgramMatrix xs = reflectionProgramMatrix xs * wireGate N a tGate
    let d : Bool → ℂ := fun q => if q then Complex.exp (((Real.pi/4 : ℝ):ℂ)*Complex.I) else 1
    have hp : tGate = diagonal d := rfl
    rw [hp]
    exact source_controlPhase_commute_table a d xs hxs havP
  calc
    _ = reflectionProgramMatrix ([P] ++ xs ++ ys) := rfl
    _ = reflectionProgramMatrix (xs ++ [P] ++ ys) := (source_slide_gate P xs ys hcommP).symm
    _ = reflectionProgramMatrix (earlyToffoli a b t ++ tail ++ [H]) := rfl
    _ = reflectionProgramMatrix (earlyToffoli a b t ++ [H] ++ tail) := hmoveH.symm
    _ = _ := rfl

theorem sourceToffoliFramed_legal {N : ℕ} (a b t : Fin N)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) : reflectionLegal (sourceToffoliFramed a b t) := by
  intro g hg
  apply toffoliLocalSteps_legal a b t hab hat hbt g
  simp only [sourceToffoliFramed, sourceToffoliMiddle, toffoliLocalSteps,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
  tauto

theorem sourceToffoliMiddle_legal {N : ℕ} (a b t : Fin N)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) : reflectionLegal (sourceToffoliMiddle a b t) := by
  intro g hg
  apply toffoliLocalSteps_legal a b t hab hat hbt g
  simp only [sourceToffoliMiddle, toffoliLocalSteps, List.mem_cons, List.not_mem_nil,
      or_false] at hg ⊢
  tauto

theorem sourceToffoliFramed_ket {N : ℕ} (a b t : Fin N)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (sourceToffoliFramed a b t))
      (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (noWorkToffoliUpdate a b t x) := by
  rw [run_reflectionCompile, sourceToffoliFramed_matrix a b t hab hat hbt, ← run_reflectionCompile]
  exact (local_toffoli_fifteen_exact N a b t hab hat hbt).2.2 x

theorem sourceToffoliUpdate_involutive {N : ℕ} (a b t : Fin N)
    (hat : a ≠ t) (hbt : b ≠ t) : Function.Involutive (noWorkToffoliUpdate a b t) := by
  intro x
  funext k
  by_cases hkt : k = t
  · subst k
    simp [noWorkToffoliUpdate, Function.update_of_ne hat, Function.update_of_ne hbt]
  · simp [noWorkToffoliUpdate, Function.update_of_ne hkt]

theorem sourceToffoliFramed_adjoint_ket {N : ℕ} (a b t : Fin N)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (reflectionAdjoint (sourceToffoliFramed a b t)))
      (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (noWorkToffoliUpdate a b t x) :=
  source_adjoint_involutive_action _ (sourceToffoliFramed_legal a b t hab hat hbt)
    _ (sourceToffoliUpdate_involutive a b t hat hbt) (sourceToffoliFramed_ket a b t hab hat hbt) x

theorem sourceToffoliFramed_counts {N : ℕ} (a b t : Fin N) :
    (sourceToffoliMiddle a b t).length = 12 ∧ (sourceToffoliFramed a b t).length = 15 := by
  exact ⟨rfl,rfl⟩

end Qatlib.Concepts.CircuitImpl.MultiControl.CountToffoliFrames
