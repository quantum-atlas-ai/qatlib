/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.Lemma5DysonSourceParametersHami
import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorSimulation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
open Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.CoherentSim.FactorialTaylor

namespace Qatlib.Concepts.InteractionEvo.ComputedGrid
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

def computedDysonCutoff (k : ℕ) : ℕ := factorialTaylorCutoff (k + 2)

def computedDysonGridSize (t Λ χ : ℝ) (k : ℕ) : ℕ :=
  max (max 1 ((computedDysonCutoff k) ^ 2))
    (Nat.ceil (16 * t ^ 2 * (χ + Λ ^ 2) * (2 : ℝ) ^ k))

structure ComputedDysonGridRun (I : Type) where
  gridSize : ℕ
  cutoff : ℕ
  increments : List (Matrix I I ℂ)
  approximation : Matrix I I ℂ
  sampleReads : ℕ
  matrixMultiplications : ℕ

def computedDysonGridRun {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t Λ χ : ℝ) (k : ℕ) : ComputedDysonGridRun I :=
  let M := computedDysonGridSize t Λ χ k
  let K := computedDysonCutoff k
  let increments := List.ofFn (fun j : Fin M =>
    -((t / (M : ℝ) : ℝ) : ℂ) • (Complex.I • H (t * j.val / M)))
  { gridSize := M
    cutoff := K
    increments := increments
    approximation := ∑ l ∈ Finset.range (K + 1),
      ((increments.reverse.sublistsLen l).map List.prod).sum
    sampleReads := increments.length
    matrixMultiplications := ((List.range (K + 1)).map
      (fun l => l * (increments.reverse.sublistsLen l).length)).sum }

theorem computedDysonCutoff_tail_and_rate :
    (∀ (k : ℕ) (x : ℝ), 0 ≤  x → x ≤  Real.log 2 →
      (2 : ℝ)*x^(computedDysonCutoff k+1)/(Nat.factorial (computedDysonCutoff k+1):ℝ) ≤
        (1/2:ℝ)^k/2) ∧
    (∃ C m0 : ℕ, 0<C ∧ 2 ≤ m0 ∧ ∀ k : ℕ,m0 ≤ k+2 →
      computedDysonCutoff k*Nat.log 2 (k+2) ≤ C*(k+2)) := by
  constructor
  · intro k x hx hlog
    have hx1 : x ≤ 1 := by
      have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)
      linarith
    have hp : x^(computedDysonCutoff k+1) ≤ 1 := pow_le_one₀ hx hx1
    have hf : (2:ℝ)^(k+2) ≤ (Nat.factorial (computedDysonCutoff k+1):ℝ) := by
      exact_mod_cast (factorial_taylor_native_cutoff_and_rate.1 (k+2)).1
    have hfpos : (0:ℝ)<(Nat.factorial (computedDysonCutoff k+1):ℝ) := by positivity
    calc
      _ ≤  2/(Nat.factorial (computedDysonCutoff k+1):ℝ) := by
        exact div_le_div_of_nonneg_right (by linarith) hfpos.le
      _ ≤  2/(2:ℝ)^(k+2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hf
      _ = _ := by
        simp only [pow_add,pow_two,div_pow,one_pow]
        field_simp
  · obtain ⟨C,m0,hC,hm0,hrate⟩ := factorial_taylor_native_cutoff_and_rate.2
    exact ⟨C,m0,hC,hm0,fun k hk => hrate (k+2) hk⟩

theorem computedDysonGridRun_structure :
    ∀ (I : Type) [Fintype I] [DecidableEq I]
      (H : ℝ → Matrix I I ℂ) (t Λ χ : ℝ) (k : ℕ),
      let r := computedDysonGridRun H t Λ χ k
      1 ≤ r.gridSize ∧ r.cutoff^2 ≤ r.gridSize ∧ r.cutoff=computedDysonCutoff k ∧
      r.increments.length=r.gridSize ∧ r.sampleReads=r.gridSize ∧
      r.approximation=dysonGridTruncatedSum H t r.gridSize r.cutoff ∧
      r.matrixMultiplications=∑ l ∈ Finset.range (r.cutoff+1),l*Nat.choose r.gridSize l := by
  intro I _ _ H t Λ χ k
  have h1 : 1 ≤ computedDysonGridSize t Λ χ k :=
    (le_max_left 1 ((computedDysonCutoff k)^2)).trans (le_max_left _ _)
  have hK : (computedDysonCutoff k)^2 ≤ computedDysonGridSize t Λ χ k :=
    (le_max_right 1 ((computedDysonCutoff k)^2)).trans (le_max_left _ _)
  refine ⟨h1,hK,rfl,?_,?_,rfl,?_⟩
  · simp [computedDysonGridRun]
  · simp [computedDysonGridRun]
  · simp only [computedDysonGridRun,List.length_sublistsLen,List.length_reverse,List.length_ofFn]
    induction computedDysonCutoff k+1 with
    | zero => simp
    | succ m ih =>
      simp only [List.range_succ,List.map_append,List.map_cons,List.map_nil,List.sum_append,
        List.sum_cons,List.sum_nil,add_zero,Finset.sum_range_succ,ih]

end Qatlib.Concepts.InteractionEvo.ComputedGrid
