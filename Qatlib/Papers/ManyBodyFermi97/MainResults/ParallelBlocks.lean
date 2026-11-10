/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.Defs
import Qatlib.Papers.ManyBodyFermi97.MainResults.OnsiteWord
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.ParallelBlocks
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators Matrix.Norms.L2Operator

def localH (t : ℝ) : Matrix Bool Bool ℂ := (t : ℂ) • PauliX

def blockH (k : ℕ) (t : ℝ) : Matrix (Bool × Fin k) (Bool × Fin k) ℂ :=
  Matrix.blockDiagonal (fun _ : Fin k => localH t)

def localU (t time : ℝ) : Matrix Bool Bool ℂ := HamiltonianEvolution (localH t) time

def blockU (k : ℕ) (t time : ℝ) : Matrix (Bool × Fin k) (Bool × Fin k) ℂ :=
  Matrix.blockDiagonal (fun _ : Fin k => localU t time)

theorem block_evolution (k : ℕ) (t time : ℝ) :
    HamiltonianEvolution (blockH k t) time = blockU k t time := by
  letI : NormedAlgebra ℚ (Matrix Bool Bool ℂ) := .restrictScalars ℚ ℂ _
  unfold blockH blockU localU HamiltonianEvolution
  rw [← Matrix.blockDiagonal_smul,Matrix.exp_blockDiagonal]
  congr 1
  funext i
  exact Pi.coe_exp _ i

theorem localH_hermitian (t : ℝ) : (localH t).IsHermitian := by
  ext b c
  cases b <;> cases c <;> simp [localH,PauliX,permMatrix,Matrix.conjTranspose]

theorem localU_unitary (t time : ℝ) : localU t time ∈ Matrix.unitaryGroup Bool ℂ :=
  hamiltonianEvolution_unitary (localH_hermitian t) time

theorem blockU_unitary (k : ℕ) (t time : ℝ) :
    blockU k t time ∈ Matrix.unitaryGroup (Bool × Fin k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  simp only [blockU,Matrix.star_eq_conjTranspose,Matrix.blockDiagonal_conjTranspose,
    ← Matrix.blockDiagonal_mul]
  have h := (Matrix.mem_unitaryGroup_iff').mp (localU_unitary t time)
  simpa only [Matrix.star_eq_conjTranspose,← Pi.one_def,Matrix.blockDiagonal_one] using! congrArg
    (fun A : Matrix Bool Bool ℂ => Matrix.blockDiagonal (fun _ : Fin k => A)) h

theorem blockU_local (k : ℕ) (t time : ℝ) (x y : Bool × Fin k) :
    blockU k t time x y = if x.2=y.2 then localU t time x.1 y.1 else 0 := by
  simp [blockU,Matrix.blockDiagonal]

def word (k : ℕ) (t time : ℝ) : Circuit (Bool × Fin k) := [.gate (blockU k t time)]

theorem word_correct (k : ℕ) (t time : ℝ) (ψ : QState (Bool × Fin k)) :
    Run 1 (word k t time) ψ = ApplyGate (HamiltonianEvolution (blockH k t) time) ψ ∧
    IsUnitaryCircuit (word k t time) ∧ QueryCount (word k t time)=0 ∧
    GateCount (word k t time)=1 := by
  refine ⟨?_,?_,rfl,rfl⟩
  · rw [block_evolution]
    rfl
  · simp only [word,isUnitaryCircuit_gate,isUnitaryCircuit_nil,and_true]
    exact blockU_unitary k t time

def site {k : ℕ} (x : Bool × Fin k) : Fin (2*k) :=
  ⟨2*x.2.val + if x.1 then 1 else 0, by have h:=x.2.isLt; split <;> omega⟩

theorem site_injective (k : ℕ) : Function.Injective (site (k:=k)) := by
  intro x y h
  have hv:=congrArg Fin.val h
  rcases x with ⟨b,a⟩
  rcases y with ⟨d,c⟩
  cases b <;> cases d <;>
    simp only [site,Bool.false_eq_true,if_false,if_true] at hv
  all_goals first | omega | (have hac : a=c := Fin.ext (by omega); subst c; rfl)

theorem site_surjective (k : ℕ) : Function.Surjective (site (k:=k)) := by
  intro i
  have hq : i.val/2<k := by have h:=i.isLt; omega
  refine ⟨(decide (i.val%2=1),⟨i.val/2,hq⟩),Fin.ext ?_⟩
  by_cases h : i.val%2=1
  · simp only [site,h,decide_true,if_true]
    omega
  · simp only [site,h,decide_false,Bool.false_eq_true,if_false]
    omega

def siteEquiv (k : ℕ) : (Bool × Fin k) ≃ Fin (2*k) :=
  Equiv.ofBijective site ⟨site_injective k,site_surjective k⟩

theorem source_even_blocks (k : ℕ) (t : ℝ) (x y : Bool × Fin k) :
    evenBlocks (2*k) t (site x) (site y) = blockH k t x y := by
  rcases x with ⟨b,a⟩
  rcases y with ⟨d,c⟩
  by_cases hac : a=c
  · subst c
    have hdiv : (2*a.val+1)/2=a.val := by omega
    cases b <;> cases d <;>
      simp [evenBlocks,chainHopping,site,blockH,Matrix.blockDiagonal,localH,PauliX,permMatrix,hdiv]
  · have hv : a.val ≠ c.val := fun h => hac (Fin.ext h)
    have ha : (2*a.val+1)/2=a.val := by omega
    have hc : (2*c.val+1)/2=c.val := by omega
    cases b <;> cases d <;>
      simp [evenBlocks,site,blockH,Matrix.blockDiagonal,localH,PauliX,permMatrix,hac,hv,ha,hc]
end Qatlib.Papers.ManyBodyFermi97.MainResults.ParallelBlocks
