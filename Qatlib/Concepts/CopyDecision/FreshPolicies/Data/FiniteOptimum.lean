/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.FreshPolicies.Data.FinitePolicy
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Finite Optimum

Fresh Policies constructions for Copy Decision.
Defines `ignoreCopy`, `uniformGuess`, `ignoredCopies`.
Proves `trine_root_weight_moment`, `finitePolicy_uniform_lower`, `policyError_ignoreCopy`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.FreshPolicies.Data
open Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError

/-- Actual root Born weights satisfy the trine moment inequality. -/
lemma trine_root_weight_moment (A : Qubit →ₗ[ℂ] Qubit) :
    (‖A (trineState 0)‖^2/3)^2+(‖A (trineState 1)‖^2/3)^2+
      (‖A (trineState 2)‖^2/3)^2 ≤
      (‖A (trineState 0)‖^2/3+‖A (trineState 1)‖^2/3+
        ‖A (trineState 2)‖^2/3)^2/2 := by
  letI : InnerProductSpace ℝ Qubit := InnerProductSpace.complexToReal
  have h0 : A (trineState 0)=A basisZero := by
    rw [trineState_eq_input, trineInput_zero]
  have h1 : A (trineState 1)=(-1/2:ℝ) • A basisZero+
      (Real.sqrt 3/2) • A basisOne := by
    rw [trineState_eq_input, trineInput_one]
    change (A.restrictScalars ℝ) _ = _
    simp only [map_add, map_smul]
    rfl
  have h2 : A (trineState 2)=(-1/2:ℝ) • A basisZero+
      (-Real.sqrt 3/2) • A basisOne := by
    rw [trineState_eq_input, trineInput_two]
    change (A.restrictScalars ℝ) _ = _
    simp only [map_add, map_smul]
    rfl
  have hm := (trine_image_moments (A basisZero) (A basisOne)).2
  rw [h0, h1, h2]
  nlinarith only [hm]

/-- Compose actual first-copy geometry with the actual child trees. This is
the stronger root bound, rather than the weaker uniform whole-tree bound. -/
theorem finitePolicy_uniform_lower {n : ℕ} (P : FinitePolicy (n+1)) :
    (1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n) ≤ policyError P (fun _ => 1/3) := by
  cases P with
  | step m A mass gram next =>
    let q : Fin m → Fin 3 → ℝ := fun a i => ‖A a (trineState i)‖^2/3
    let t : ℝ := (1/2:ℝ)^n
    have hb : ∀ a, t^2*((q a 0+q a 1+q a 2)/4) ≤
        (1+t)*policyError (next a) (q a) := by
      intro a
      have hq : ∀ i, 0 ≤ q a i := by intro i; dsimp [q]; positivity
      have hg := harmonic_of_moment (hq 0) (hq 1) (hq 2)
        (trine_root_weight_moment (A a))
      exact (mul_le_mul_of_nonneg_left hg (sq_nonneg t)).trans
        (policy_weighted_bound (next a) (q a) hq)
    have hs : ∑ a, (q a 0+q a 1+q a 2)=1 := by
      dsimp only [q]
      simp only [Finset.sum_add_distrib, ←Finset.sum_div, mass,
        trineState_unit, one_pow]
      norm_num
    have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hb a)
    simp only [←Finset.mul_sum, div_eq_mul_inv, ←Finset.sum_mul, hs] at hsum
    have ht : 0 < 1+t := by dsimp [t]; positivity
    have he : t^2=(1/4:ℝ)^n := by
      dsimp only [t]
      rw [←pow_mul, Nat.mul_comm n 2, pow_mul]
      norm_num
    have hbound : t^2/(4*(1+t)) ≤ ∑ a, policyError (next a) (q a) := by
      apply (div_le_iff₀ (by positivity : 0 < 4*(1+t))).2
      nlinarith only [hsum]
    have hf : t^2/(4*(1+t))=(1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n) := by
      rw [he, pow_succ]
      dsimp only [t]
      field_simp
    rw [hf] at hbound
    simpa only [policyError, one_div_mul_eq_div] using hbound

/-- Ignore a fresh copy; no outcome or quantum output is sent to the child. -/
def ignoreCopy {n : ℕ} (P : FinitePolicy n) : FinitePolicy (n+1) :=
  .step 1 (fun _ => LinearMap.id)
    (by intro x; simp) (by intro x y; simp) (fun _ => P)

/-- The stated copy-decision construction satisfies `policyError_ignoreCopy` with the complete displayed premises. -/
lemma policyError_ignoreCopy {n : ℕ} (P : FinitePolicy n) (q : Fin 3 → ℝ) :
    policyError (ignoreCopy P) q=policyError P q := by
  simp [policyError, ignoreCopy, trineState_unit]

/-- Explicit legal witness at every depth, independent of the unknown label. -/
def uniformGuess : TerminalDecision where
  prob := fun _ => 1/3
  nonneg := by intro k; norm_num
  total := by norm_num [Fin.sum_univ_three]

/-- Definition of ignored Copies in the Fresh Policies construction. -/
def ignoredCopies : (n : ℕ) → FinitePolicy n
  | 0 => .leaf uniformGuess
  | n+1 => ignoreCopy (ignoredCopies n)

/-- ONLY canonical finite trees. Equality to the full original model's optimum
still requires the arbitrary-POVM and measurable-outcome approximation bridges. -/
def finitePolicyRisks (n : ℕ) (q : Fin 3 → ℝ) : Set ℝ :=
  Set.range (fun P : FinitePolicy n => policyError P q)

/-- Definition of finite Policy Optimum in the Fresh Policies construction. -/
def finitePolicyOptimum (n : ℕ) (q : Fin 3 → ℝ) : ℝ :=
  sInf (finitePolicyRisks n q)

/-- The stated copy-decision construction satisfies `finitePolicyRisks_nonempty` with the complete displayed premises. -/
lemma finitePolicyRisks_nonempty (n : ℕ) (q : Fin 3 → ℝ) :
    (finitePolicyRisks n q).Nonempty :=
  ⟨policyError (ignoredCopies n) q, ⟨ignoredCopies n, rfl⟩⟩

/-- The stated copy-decision construction satisfies `finitePolicyRisks_bddBelow` with the complete displayed premises. -/
lemma finitePolicyRisks_bddBelow (n : ℕ) (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) :
    BddBelow (finitePolicyRisks n q) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨P, rfl⟩
  exact policyError_nonneg P q hq

/-- The stated copy-decision construction satisfies `finitePolicyOptimum_nonneg` with the complete displayed premises. -/
lemma finitePolicyOptimum_nonneg (n : ℕ) (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) :
    0 ≤ finitePolicyOptimum n q := by
  apply le_csInf (finitePolicyRisks_nonempty n q)
  rintro _ ⟨P, rfl⟩
  exact policyError_nonneg P q hq

/-- The stated copy-decision construction satisfies `finitePolicyOptimum_le` with the complete displayed premises. -/
lemma finitePolicyOptimum_le {n : ℕ} (P : FinitePolicy n) (q : Fin 3 → ℝ)
    (hq : ∀ i, 0 ≤ q i) : finitePolicyOptimum n q ≤ policyError P q :=
  csInf_le (finitePolicyRisks_bddBelow n q hq) ⟨P, rfl⟩

/-- Uniform lower bound survives the genuine, nonempty policy-risk infimum. -/
theorem finitePolicyOptimum_uniform_lower (n : ℕ) :
    (1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n) ≤ finitePolicyOptimum (n+1) (fun _ => 1/3) := by
  apply le_csInf (finitePolicyRisks_nonempty (n+1) (fun _ => 1/3))
  rintro _ ⟨P, rfl⟩
  exact finitePolicy_uniform_lower P

end Qatlib.Concepts.CopyDecision.FreshPolicies.Data
