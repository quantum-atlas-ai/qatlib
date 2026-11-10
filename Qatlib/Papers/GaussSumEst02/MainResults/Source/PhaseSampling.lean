/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Qatlib.Papers.GaussSumEst02.MainResults.Source.Cost
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.MainResults.Source

def bornPlus (γ φ : ℝ) : ℝ := (1 + Real.cos (γ - φ)) / 2

def bornMinus (γ φ : ℝ) : ℝ := (1 - Real.cos (γ - φ)) / 2

def sign (b : Bool) : ℝ := if b then 1 else -1

theorem bornPlus_add_bornMinus (γ φ : ℝ) : bornPlus γ φ + bornMinus γ φ = 1 := by
  unfold bornPlus bornMinus
  ring

theorem bornPlus_sub_bornMinus (γ φ : ℝ) :
    bornPlus γ φ - bornMinus γ φ = Real.cos (γ - φ) := by
  unfold bornPlus bornMinus
  ring

theorem bornPlus_nonneg (γ φ : ℝ) : 0 ≤ bornPlus γ φ := by
  unfold bornPlus
  nlinarith [Real.neg_one_le_cos (γ - φ)]

theorem bornMinus_nonneg (γ φ : ℝ) : 0 ≤ bornMinus γ φ := by
  unfold bornMinus
  nlinarith [Real.cos_le_one (γ - φ)]

structure SamplingProtocol where
  angle : ℕ → ℝ
  estimate : (t : ℕ) → (Fin t → Bool) → ℝ

def recordProb (γ : ℝ) (P : SamplingProtocol) (t : ℕ) (σ : Fin t → Bool) : ℝ :=
  ∏ i : Fin t, (if σ i then bornPlus γ (P.angle i) else bornMinus γ (P.angle i))

def expectedAngularError (γ : ℝ) (P : SamplingProtocol) (t : ℕ) : ℝ :=
  ∑ σ : Fin t → Bool, recordProb γ P t σ * |P.estimate t σ - γ|

def expectedSignMean (γ : ℝ) (P : SamplingProtocol) (t : ℕ) : ℝ :=
  ∑ σ : Fin t → Bool,
    recordProb γ P t σ * ((t : ℝ)⁻¹ * ∑ i : Fin t, sign (σ i))

theorem fact2_unbiased_sign_mean (γ : ℝ) (P : SamplingProtocol) (t : ℕ) (ht : 0 < t) :
    expectedSignMean γ P t
      = (t : ℝ)⁻¹ * ∑ i : Fin t, Real.cos (γ - P.angle i) := by
  classical

  have hprod : ∀ j : Fin t,
      (∑ σ : Fin t → Bool, recordProb γ P t σ * sign (σ j))
        = Real.cos (γ - P.angle j) := by
    intro j
    have hsplit : ∀ σ : Fin t → Bool,
        recordProb γ P t σ * sign (σ j)
          = ∏ i : Fin t,
              ((if σ i then bornPlus γ (P.angle i) else bornMinus γ (P.angle i))
                * (if i = j then sign (σ i) else 1)) := by
      intro σ
      rw [recordProb, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_ite_eq_of_mem' _ _ _ (Finset.mem_univ j)]
    simp only [hsplit]
    have hpi : Fintype.piFinset (fun _ : Fin t => (Finset.univ : Finset Bool)) = Finset.univ :=
      Fintype.piFinset_univ
    rw [← hpi]
    have hkey :
        (∏ i : Fin t, ∑ b : Bool,
            (if b then bornPlus γ (P.angle i) else bornMinus γ (P.angle i))
              * (if i = j then sign b else 1))
          = ∑ x ∈ Fintype.piFinset (fun _ : Fin t => (Finset.univ : Finset Bool)),
              ∏ i : Fin t,
                (if x i then bornPlus γ (P.angle i) else bornMinus γ (P.angle i))
                  * (if i = j then sign (x i) else 1) :=
      Finset.prod_univ_sum (fun _ : Fin t => (Finset.univ : Finset Bool))
        (fun i b => (if b then bornPlus γ (P.angle i) else bornMinus γ (P.angle i))
          * (if i = j then sign b else 1))
    rw [← hkey]
    have hfac : ∀ i : Fin t,
        (∑ b : Bool, (if b then bornPlus γ (P.angle i) else bornMinus γ (P.angle i))
            * (if i = j then sign b else 1))
          = if i = j then Real.cos (γ - P.angle i) else 1 := by
      intro i
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, Fintype.sum_bool]
        simp only [sign, Bool.false_eq_true, if_true, if_false, mul_neg]
        linarith [bornPlus_sub_bornMinus γ (P.angle i)]
      · rw [if_neg hij, Fintype.sum_bool]
        simp only [sign, Bool.false_eq_true, if_true, if_false, if_neg hij]
        linarith [bornPlus_add_bornMinus γ (P.angle i)]
    trans (∏ i : Fin t, if i = j then Real.cos (γ - P.angle i) else 1)
    · exact Finset.prod_congr rfl fun i _ => hfac i
    · exact Finset.prod_ite_eq_of_mem' (Finset.univ) j
        (fun i => Real.cos (γ - P.angle i)) (Finset.mem_univ j)

  have hpull : expectedSignMean γ P t
      = (t : ℝ)⁻¹ * ∑ σ : Fin t → Bool, ∑ i : Fin t,
          recordProb γ P t σ * sign (σ i) := by
    unfold expectedSignMean
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    calc recordProb γ P t σ * ((t:ℝ)⁻¹ * ∑ i, sign (σ i))
        = (t:ℝ)⁻¹ * (recordProb γ P t σ * ∑ i, sign (σ i)) := by ring
      _ = (t:ℝ)⁻¹ * ∑ i, recordProb γ P t σ * sign (σ i) := by rw [Finset.mul_sum]
  rw [hpull]
  have hinner : (∑ σ : Fin t → Bool, ∑ i : Fin t, recordProb γ P t σ * sign (σ i))
      = ∑ i : Fin t, Real.cos (γ - P.angle i) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => hprod j
  rw [hinner]

def copySampleCount (ε : ℝ) : ℕ := Nat.ceil (1 / ε ^ 2)

theorem copySampleCount_pos (ε : ℝ) (hε : 0 < ε) : 0 < copySampleCount ε := by
  unfold copySampleCount
  apply Nat.ceil_pos.mpr
  positivity

structure PhaseAccessModel where

  protocol : ℝ → SamplingProtocol

  queries : ℝ → ℕ

  queries_pos : ∀ ε : ℝ, 0 < ε → 0 < queries ε

  queries_bound : ∃ C : ℕ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → queries ε ≤ C * sampleCount ε

  accuracy : ∀ γ : ℝ, ∀ ε : ℝ, 0 < ε →
    expectedAngularError γ (protocol ε) (queries ε) < ε

end Qatlib.Papers.GaussSumEst02.MainResults.Source
