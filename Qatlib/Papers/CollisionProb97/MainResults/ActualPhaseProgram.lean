/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.CyclicRecovery.AlgebraicOracle
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
import Qatlib.Concepts.SearchStopping.UnknownCount.Theorem3SourceFamilyTigh
import Qatlib.Concepts.TableAccess.LookupCompile.FiniteTableAccess
import Qatlib.Foundations.QueryWordCore.Circuit
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Classical
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib.Foundations.QueryWordCore.Circuit
namespace Qatlib.Papers.CollisionProb97.MainResults.PhaseCompile
variable {X R:Type} [Fintype X] [DecidableEq X]
 [AddCommGroup R] [Fintype R] [DecidableEq R]

def tableSign (K:Finset X) (T:Finset R) (x:X) (z:R):ℂ :=
 if x∉K ∧ z∈T then -1 else 1

def tablePhase (K:Finset X) (T:Finset R):Matrix (X×R) (X×R) ℂ :=
 Matrix.diagonal (fun p=>tableSign K T p.1 p.2)

def tablePhaseWord (K:Finset X) (T:Finset R):List (AdjointStep (X×R)) :=
 [.backward,.gate (tablePhase K T),.forward]
omit [AddCommGroup R] in

theorem tablePhase_unitary (K:Finset X) (T:Finset R):
 tablePhase K T∈Matrix.unitaryGroup (X×R) ℂ := by
 rw [tablePhase,Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
 simp only [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
 ext p q
 by_cases hpq:p=q
 · subst q
   by_cases h:p.1∉K ∧ p.2∈T <;> simp [tableSign,h]
 · simp [hpq]
omit [Fintype X] [AddCommGroup R] [Fintype R] in

theorem tablePhaseWord_cost (K:Finset X) (T:Finset R):
 adjointQueryCount (tablePhaseWord K T)=2 ∧ adjointGateCount (tablePhaseWord K T)=1 := by
 exact ⟨rfl,rfl⟩

theorem tablePhaseWord_full_state (F:X→R) (K:Finset X) (T:Finset R)
 (ψ:QState (X×R)) (x:X) (z:R):
 ApplyGate (evaluate (AddOracle F) (tablePhaseWord K T)) ψ (x,z)=
 tableSign K T x (z+F x)*ψ (x,z) := by
 simp only [tablePhaseWord,evaluate,instructionMatrix,Matrix.mul_one]
 simp only [applyGate_mul]
 rw [addOracle_conjTranspose,applyGate_addOracle]
 simp only [Pi.neg_apply,sub_neg_eq_add]
 change (tablePhase K T *ᵥ ApplyGate (AddOracle F) ψ) (x,z+F x)=_
 simp only [tablePhase,Matrix.mulVec_diagonal]
 rw [applyGate_addOracle]
 simp

theorem tablePhaseWord_clean (F:X→R) (K:Finset X) (T:Finset R) (ψ:QState X):
 ApplyGate (evaluate (AddOracle F) (tablePhaseWord K T)) (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket 0))=
 TensorState (fun x=>tableSign K T x (F x)*ψ x) (Qatlib.Foundations.PureStateMath.Ket 0) := by
 funext p
 obtain ⟨x,z⟩:=p
 rw [tablePhaseWord_full_state]
 by_cases hz:z=0
 · subst z
   simp [TensorState,Qatlib.Foundations.PureStateMath.Ket]
 · simp [TensorState,Qatlib.Foundations.PureStateMath.Ket,hz]

theorem actual_source_search_fetch_bound {I:Type}[Fintype I][DecidableEq I]
 (l:ℝ) (hl:1<l) (hl4:l<4/3) (A:Finset I) (hA:0<A.card):
 ∃q:ℝ,HasSum (fun x:TerminalTrace I (SourceSizes (Fintype.card I) l)=>
 TerminalMass A (SourceSizes (Fintype.card I) l) x*
 (SourceLookupClock (SourceSizes (Fintype.card I) l) x:ℝ)) q ∧
 0≤q ∧ q≤(1+4*SourcePhaseConstant l)*Real.sqrt ((Fintype.card I:ℝ)/A.card) := by
 exact search_source_terminal_lookup_cost l hl hl4 A hA

omit [AddCommGroup R] in

theorem eval_append (O : Matrix (X × R) (X × R) ℂ)
    (P Q : List (AdjointStep (X × R))) : evaluate O (P ++ Q) = evaluate O P * evaluate O Q := by
  induction P with
  | nil => simp [evaluate]
  | cons g P ih => simp only [List.cons_append, evaluate, ih, Matrix.mul_assoc]

omit [Fintype X] [DecidableEq X] [AddCommGroup R] [Fintype R] [DecidableEq R] in

theorem query_append (P Q : List (AdjointStep (X × R))) :
    adjointQueryCount (P ++ Q) = adjointQueryCount P + adjointQueryCount Q := by
  induction P with
  | nil => simp [adjointQueryCount]
  | cons g P ih => cases g <;> simp [adjointQueryCount, ih, Nat.add_comm, Nat.add_left_comm]

def compile (K : Finset X) (T : Finset R) : Circuit X → List (AdjointStep (X × R))
  | [] => []
  | .gate U :: P => compile K T P ++ [.gate (TensorGate U (1 : Matrix R R ℂ))]
  | .query :: P => compile K T P ++ tablePhaseWord K T

omit [Fintype X] [AddCommGroup R] [Fintype R] in

theorem compile_queries (K : Finset X) (T : Finset R) (P : Circuit X) :
    adjointQueryCount (compile K T P) = 2 * QueryCount P := by
  induction P with
  | nil => rfl
  | cons g P ih =>
    cases g <;> simp only [compile, query_append, ih, adjointQueryCount,
      QueryCount, tablePhaseWord_cost]
    all_goals omega

theorem compile_run (F : X → R) (K : Finset X) (T : Finset R)
    (P : Circuit X) (ψ : QState X) :
    ApplyGate (evaluate (AddOracle F) (compile K T P)) (TensorState ψ (Ket 0)) =
    TensorState (Run (Matrix.diagonal (fun x => tableSign K T x (F x))) P ψ) (Ket 0) := by
  induction P generalizing ψ with
  | nil => simp only [compile, evaluate, applyGate_one, run_nil]
  | cons g P ih =>
    cases g with
    | gate U =>
      rw [compile, eval_append, applyGate_mul]
      simp only [evaluate, instructionMatrix, Matrix.mul_one, applyGate_tensorGate, applyGate_one]
      exact ih (ApplyGate U ψ)
    | query =>
      rw [compile, eval_append, applyGate_mul, tablePhaseWord_clean, ih]
      have hd : ApplyGate (Matrix.diagonal (fun x => tableSign K T x (F x))) ψ =
          fun x => tableSign K T x (F x) * ψ x := by
        funext x
        exact Matrix.mulVec_diagonal _ _ x
      rw [run_query, hd]

end Qatlib.Papers.CollisionProb97.MainResults.PhaseCompile
