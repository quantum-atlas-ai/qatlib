/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.FreshPolicies.Data.GeneralPolicy
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# General Approximation

Fresh Policies constructions for Copy Decision.
Proves `generalPolicy_finite_approximation`, `generalPolicy_uniform_lower`.
-/


set_option autoImplicit false
noncomputable section
universe u
namespace Qatlib.Concepts.CopyDecision.FreshPolicies.Data
open Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError Qatlib.Foundations.DecisionRisk.RiskPartition
open MeasureTheory

/-- Approximate a derived-risk-measurable effect/continuation tree at each
fixed finite copy budget. Original continuation programs are frozen at chosen
histories; their internal posterior/control is never reset to a coarsened one. -/
theorem generalPolicy_finite_approximation {n : ℕ} (P : RawGeneralPolicy.{u} n)
    (hP : GeneralPolicyValid P) (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : FinitePOVMPolicy n,
      |povmPolicyError F q-generalPolicyError P q| ≤ ε*(∑ i, q i) := by
  classical
  induction P generalizing q ε with
  | leaf p =>
    refine ⟨.leaf p, ?_⟩
    simp only [povmPolicyError, generalPolicyError, generalLabelRisk, sub_self, abs_zero]
    exact mul_nonneg hε.le (Finset.sum_nonneg (fun i _ => hq i))
  | @step d Y mY M next ih =>
    letI := mY
    let c : Y → Fin 3 → ℝ := fun y i => generalLabelRisk (next y) i
    have hc : ∀ y i, 0 ≤ c y i ∧ c y i ≤ 1 :=
      fun y i => generalLabelRisk_unit (next y) (hP.1 y) i
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0:ℝ) < ε/2 by positivity)
    have hk' : (1:ℝ)/(k+1:ℕ) ≤ ε/2 := by exact_mod_cast hk.le
    obtain ⟨m, Λ, r, hcoarse⟩ := M.exists_finite_risk_coarsening c (hP.2) hc (k+1) (by omega)
    let w : Fin m → Fin 3 → ℝ := fun a i => q i*qubitBorn (Λ.mats a) (trineState i)
    have hw : ∀ a i, 0 ≤ w a i := fun a i =>
      mul_nonneg (hq i) (qubitBorn_nonneg _ (Λ.nonneg a) _)
    have hchild : ∀ a, ∃ F : FinitePOVMPolicy d,
        |povmPolicyError F (w a)-generalPolicyError (next (r a)) (w a)| ≤
          (ε/2)*(∑ i, w a i) := by
      intro a
      exact ih (r a) (hP.1 (r a)) (w a) (hw a) (ε/2) (by positivity)
    choose F hF using hchild
    have hmass : ∀ i, ∑ a, qubitBorn (Λ.mats a) (trineState i)=1 := by
      intro i
      simp_rw [← povmKraus_born]
      rw [povmKraus_mass, trineState_unit, one_pow]
    have hwtotal : ∑ a, ∑ i, w a i=∑ i, q i := by
      rw [Finset.sum_comm]
      simp only [w, ← Finset.mul_sum, hmass, mul_one]
    let S : ℝ := ∑ a, ∑ i, w a i*c (r a) i
    have hsum : |povmPolicyError (.step m Λ F) q-S| ≤ (ε/2)*(∑ i, q i) := by
      change |(∑ a, povmPolicyError (F a) (w a))-(∑ a, ∑ i, w a i*c (r a) i)| ≤ _
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ a, |povmPolicyError (F a) (w a)-(∑ i, w a i*c (r a) i)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a, (ε/2)*(∑ i, w a i) := Finset.sum_le_sum (fun a _ => hF a)
        _ = (ε/2)*(∑ i, q i) := by rw [← Finset.mul_sum, hwtotal]
    have hQ : 0 ≤ ∑ i, q i := Finset.sum_nonneg (fun i _ => hq i)
    have hcBound : |S-generalPolicyError (.step Y mY M next) q| ≤ (ε/2)*(∑ i, q i) :=
      (hcoarse q hq).trans (mul_le_mul_of_nonneg_right hk' hQ)
    refine ⟨.step m Λ F, ?_⟩
    calc
      _ = |(povmPolicyError (.step m Λ F) q-S)+(S-generalPolicyError (.step Y mY M next) q)| := by
        congr 1
        ring
      _ ≤ |povmPolicyError (.step m Λ F) q-S|+|S-generalPolicyError (.step Y mY M next) q| :=
        abs_add_le _ _
      _ ≤ (ε/2)*(∑ i, q i)+(ε/2)*(∑ i, q i) := add_le_add hsum hcBound
      _ = ε*(∑ i, q i) := by ring

/-- Transfer the UNIFORM finite-tree lower bound to the risk-tree relaxation by epsilon -> zero at each
fixed depth; no optimum/asymptotic interchange or fixed-grid limit is used. -/
theorem generalPolicy_uniform_lower {n : ℕ} (P : RawGeneralPolicy.{u} (n+1))
    (hP : GeneralPolicyValid P) :
    (1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n) ≤ generalPolicyError P (fun _ => 1/3) := by
  by_contra h
  have hgap : 0 < (1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n)-generalPolicyError P (fun _ => 1/3) :=
    sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨F, hF⟩ := generalPolicy_finite_approximation P hP (fun _ => 1/3)
    (by intro i; norm_num)
    (((1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n)-generalPolicyError P (fun _ => 1/3))/2)
    (by positivity)
  have hlow := finitePOVMPolicy_uniform_lower F
  have hu := (abs_le.1 hF).2
  norm_num [Fin.sum_univ_three] at hu
  linarith

end Qatlib.Concepts.CopyDecision.FreshPolicies.Data
