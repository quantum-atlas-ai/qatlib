/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.Defs
import Qatlib.Papers.ManyBodyFermi97.MainResults.OnsiteWord
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Parallel two-level hopping evolution

`blockH` is a direct sum of copies of the two-level hopping Hamiltonian `localH`. Its exact
evolution acts by the same one-qubit matrix on the parity coordinate of each block. `siteEquiv`
identifies this supplied block basis with the even hopping pairs of the open chain.

The mathematical setting is that of [AbramsLloyd1997].

## Main statements

* `block_evolution`: Evolving the block diagonal hopping Hamiltonian gives the block diagonal
  matrix of local evolutions.
* `word_correct`: The block circuit implements exact Hamiltonian evolution, is unitary, uses no
  queries, and contains one gate.
* `source_even_blocks`: Under the site equivalence, the even hopping matrix agrees entrywise
  with the direct sum of two-level hopping blocks.

## References

* [Abrams and Lloyd, 1997][AbramsLloyd1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.ParallelBlocks
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The two-level hopping Hamiltonian `t • PauliX`. -/
def localH (t : ℝ) : Matrix Bool Bool ℂ := (t : ℂ) • PauliX

/-- The block diagonal Hamiltonian consisting of `k` copies of `localH t`. -/
def blockH (k : ℕ) (t : ℝ) : Matrix (Bool × Fin k) (Bool × Fin k) ℂ :=
  Matrix.blockDiagonal (fun _ : Fin k => localH t)

/-- The exact Hamiltonian evolution of the two-level hopping matrix. -/
def localU (t time : ℝ) : Matrix Bool Bool ℂ := HamiltonianEvolution (localH t) time

/-- The block diagonal matrix consisting of `k` copies of the same two-level evolution. -/
def blockU (k : ℕ) (t time : ℝ) : Matrix (Bool × Fin k) (Bool × Fin k) ℂ :=
  Matrix.blockDiagonal (fun _ : Fin k => localU t time)

/-- Evolving the block diagonal hopping Hamiltonian gives the block diagonal matrix of local
evolutions. -/
theorem block_evolution (k : ℕ) (t time : ℝ) :
    HamiltonianEvolution (blockH k t) time = blockU k t time := by
  letI : NormedAlgebra ℚ (Matrix Bool Bool ℂ) := .restrictScalars ℚ ℂ _
  unfold blockH blockU localU HamiltonianEvolution
  rw [← Matrix.blockDiagonal_smul,Matrix.exp_blockDiagonal]
  congr 1
  funext i
  exact Pi.coe_exp _ i

/-- The two-level hopping Hamiltonian is Hermitian for real `t`. -/
theorem localH_hermitian (t : ℝ) : (localH t).IsHermitian := by
  ext b c
  cases b <;> cases c <;> simp [localH,PauliX,permMatrix,Matrix.conjTranspose]

/-- The exact evolution of the two-level hopping Hamiltonian is unitary. -/
theorem localU_unitary (t time : ℝ) : localU t time ∈ Matrix.unitaryGroup Bool ℂ :=
  hamiltonianEvolution_unitary (localH_hermitian t) time

/-- The parallel block evolution is unitary. -/
theorem blockU_unitary (k : ℕ) (t time : ℝ) :
    blockU k t time ∈ Matrix.unitaryGroup (Bool × Fin k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  simp only [blockU,Matrix.star_eq_conjTranspose,Matrix.blockDiagonal_conjTranspose,
    ← Matrix.blockDiagonal_mul]
  have h := (Matrix.mem_unitaryGroup_iff').mp (localU_unitary t time)
  simpa only [Matrix.star_eq_conjTranspose,← Pi.one_def,Matrix.blockDiagonal_one] using! congrArg
    (fun A : Matrix Bool Bool ℂ => Matrix.blockDiagonal (fun _ : Fin k => A)) h

/-- The parallel evolution applies `localU` to the parity coordinate and has zero entries
between distinct block labels. [AbramsLloyd1997] -/
theorem blockU_local (k : ℕ) (t time : ℝ) (x y : Bool × Fin k) :
    blockU k t time x y = if x.2=y.2 then localU t time x.1 y.1 else 0 := by
  simp [blockU,Matrix.blockDiagonal]

/-- The single-gate circuit for parallel two-level evolution in the block and parity basis. -/
def word (k : ℕ) (t time : ℝ) : Circuit (Bool × Fin k) := [.gate (blockU k t time)]

/-- The block circuit implements exact Hamiltonian evolution, is unitary, uses no queries, and
contains one gate. [AbramsLloyd1997] -/
theorem word_correct (k : ℕ) (t time : ℝ) (ψ : QState (Bool × Fin k)) :
    Run 1 (word k t time) ψ = ApplyGate (HamiltonianEvolution (blockH k t) time) ψ ∧
    IsUnitaryCircuit (word k t time) ∧ QueryCount (word k t time)=0 ∧
    GateCount (word k t time)=1 := by
  refine ⟨?_,?_,rfl,rfl⟩
  · rw [block_evolution]
    rfl
  · simp only [word,isUnitaryCircuit_gate,isUnitaryCircuit_nil,and_true]
    exact blockU_unitary k t time

/-- Maps a parity bit and block label to the corresponding site `2 * x.2.val + (if x.1 then 1
else 0)`. -/
def site {k : ℕ} (x : Bool × Fin k) : Fin (2*k) :=
  ⟨2*x.2.val + if x.1 then 1 else 0, by have h:=x.2.isLt; split <;> omega⟩

/-- The block and parity indexing of the chain sites is injective. -/
theorem site_injective (k : ℕ) : Function.Injective (site (k:=k)) := by
  intro x y h
  have hv:=congrArg Fin.val h
  rcases x with ⟨b,a⟩
  rcases y with ⟨d,c⟩
  cases b <;> cases d <;>
    simp only [site,Bool.false_eq_true,if_false,if_true] at hv
  all_goals first | omega | (have hac : a=c := Fin.ext (by omega); subst c; rfl)

/-- Every site of an even chain is represented by a block and parity index. -/
theorem site_surjective (k : ℕ) : Function.Surjective (site (k:=k)) := by
  intro i
  have hq : i.val/2<k := by have h:=i.isLt; omega
  refine ⟨(decide (i.val%2=1),⟨i.val/2,hq⟩),Fin.ext ?_⟩
  by_cases h : i.val%2=1
  · simp only [site,h,decide_true,if_true]
    omega
  · simp only [site,h,decide_false,Bool.false_eq_true,if_false]
    omega

/-- The equivalence between block and parity labels and the `2 * k` chain sites.
[AbramsLloyd1997] -/
def siteEquiv (k : ℕ) : (Bool × Fin k) ≃ Fin (2*k) :=
  Equiv.ofBijective site ⟨site_injective k,site_surjective k⟩

/-- Under the site equivalence, the even hopping matrix agrees entrywise with the direct sum of
two-level hopping blocks. [AbramsLloyd1997] -/
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
