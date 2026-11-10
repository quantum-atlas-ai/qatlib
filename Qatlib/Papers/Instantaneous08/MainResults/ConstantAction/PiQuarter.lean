/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Instantaneous08.MainResults.ConstantAction.Degenerate
import Qatlib.Papers.Instantaneous08.MainResults.ConstantAction.CodeWeight
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.Instantaneous08.MainResults.ConstantAction

open Qatlib.Papers.Instantaneous08.MainResults.XProgram

attribute [local instance] Classical.propDecidable

def oneVec {n : ℕ} : F2Vec n := fun _ => 1

theorem univ_f2vec_one : (Finset.univ : Finset (F2Vec 1)) = {0, oneVec} := by
  ext x
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro _
    by_cases h : x 0 = 0
    · left
      funext i
      fin_cases i
      exact h
    · right
      have h1 : x 0 = 1 :=
        (ClassicalApprox.zmod2_eq_zero_or_one (x 0)).resolve_left h
      funext i
      fin_cases i
      exact h1
  · intro _; trivial

theorem oneVec_ne_zero : (oneVec : F2Vec 1) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [oneVec] at h0

theorem sum_f2vec_one (f : F2Vec 1 → ℝ) :
    (∑ x : F2Vec 1, f x) = f 0 + f oneVec := by
  have hne : (0 : F2Vec 1) ≠ oneVec := fun h => oneVec_ne_zero h.symm
  rw [univ_f2vec_one, Finset.sum_pair hne]

def oneQubitProg : Fin 1 → F2Vec 1 := fun _ => oneVec

theorem circuit_oneQubitProg_zero :
    circuit 1 oneQubitProg (fun _ => Real.pi / 4) 0 = (Real.cos (Real.pi / 4) : ℂ) := by
  simp only [circuit, oneQubitProg]
  have hne : (oneVec : F2Vec 1) ≠ 0 := oneVec_ne_zero
  simp [xGate, hne]

theorem circuit_oneQubitProg_one :
    circuit 1 oneQubitProg (fun _ => Real.pi / 4) oneVec =
      Complex.I * (Real.sin (Real.pi / 4) : ℂ) := by
  simp only [circuit, oneQubitProg]
  have hne : (oneVec : F2Vec 1) ≠ 0 := oneVec_ne_zero
  have hsum : (oneVec : F2Vec 1) + oneVec = 0 := by
    funext i
    fin_cases i
    decide
  simp [xGate, hne, hsum]

theorem prob_oneQubitProg_zero :
    prob oneQubitProg (fun _ => Real.pi / 4) 0 = 1 / 2 := by
  unfold prob
  rw [circuit_oneQubitProg_zero]
  rw [Complex.normSq_ofReal, Real.cos_pi_div_four]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem prob_oneQubitProg_one :
    prob oneQubitProg (fun _ => Real.pi / 4) oneVec = 1 / 2 := by
  unfold prob
  rw [circuit_oneQubitProg_one, Complex.normSq_mul, Complex.normSq_I, one_mul,
    Complex.normSq_ofReal, Real.sin_pi_div_four]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem collisionProb_pi_div_four_qubit :
    collisionProb oneQubitProg (fun _ => Real.pi / 4) = 1 / 2 := by
  unfold collisionProb
  rw [sum_f2vec_one (fun x => prob oneQubitProg (fun _ => Real.pi / 4) x ^ 2)]
  rw [prob_oneQubitProg_zero, prob_oneQubitProg_one]
  norm_num

theorem actSum_int {n k : ℕ} (p : Fin k → F2Vec n) (a : F2Vec n) :
    ∃ z : ℤ, actSum p a = z := by
  refine ⟨∑ i, if dot (p i) a = 0 then (1 : ℤ) else -1, ?_⟩
  unfold actSum
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : dot (p i) a = 0 <;> simp [rSign, h]

theorem expAction_pi_div_four_pow_eight {n k : ℕ} (p : Fin k → F2Vec n)
    (m : ℤ) (a : F2Vec n) :
    (expAction p ((m : ℝ) * (Real.pi / 4)) a) ^ 8 = 1 := by
  obtain ⟨N, hN⟩ := actSum_int p a
  rw [expAction_eq_exp_actSum, hN]
  have h8 : (Complex.exp (Complex.I * (((m : ℝ) * (Real.pi / 4) : ℝ) : ℂ) *
        ((N : ℝ) : ℂ))) ^ 8 =
      Complex.exp (((m * N : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h8, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

end Qatlib.Papers.Instantaneous08.MainResults.ConstantAction
