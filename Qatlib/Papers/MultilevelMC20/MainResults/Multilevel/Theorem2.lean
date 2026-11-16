/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MultilevelMC20.MainResults.CostModel.CostAsymptotics

@[expose] public section


set_option autoImplicit false
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators

namespace Qatlib.Papers.MultilevelMC20.MainResults
open Qatlib.Papers.MultilevelMC20.MainResults

def exp2 (t : ℝ) : ℝ := (2 : ℝ) ^ t

/-- exp2_pos records the paper claim under the explicit hypotheses above. -/
theorem exp2_pos (t : ℝ) : 0 < exp2 t := Real.rpow_pos_of_pos (by norm_num) t

/-- exp2_zero records the paper claim under the explicit hypotheses above. -/
theorem exp2_zero : exp2 0 = 1 := by simp [exp2]

def levelCount (α ε : ℝ) : ℕ := Nat.ceil (Real.log (2 / ε) / α)
def caseARatio (bhat γ : ℝ) : ℝ := exp2 (-(bhat - γ) / 2)
def caseAEps (bhat γ ε : ℝ) (l : ℕ) : ℝ :=
  (ε / 2) * (1 - caseARatio bhat γ) * caseARatio bhat γ ^ l
def caseBEps (ε : ℝ) (L : ℕ) : ℝ := ε / (2 * ((L : ℝ) + 1))
def caseCRatio (bhat γ : ℝ) : ℝ := exp2 ((γ - bhat) / 2)
def caseCEps (bhat γ ε : ℝ) (L l : ℕ) : ℝ :=
  (ε / 2) * exp2 (-(γ - bhat) * (L : ℝ) / 2) *
    (1 - (caseCRatio bhat γ)⁻¹) * caseCRatio bhat γ ^ l
def levelBudget (bhat : ℝ) (eps : ℝ) (l : ℕ) : ℝ := exp2 (-bhat * (l : ℝ)) / eps
def mlmcCost (bhat γ C₀ : ℝ) (L : ℕ) (epsOf : ℕ → ℝ) (δ : ℝ) (ε : ℝ) : ℝ :=
  (∑ l ∈ Finset.range (L + 1), C₀ * exp2 (γ * (l : ℝ)) * levelBudget bhat (epsOf l) l) *
    Real.log δ⁻¹ * (Real.log ε⁻¹) ^ (3 / 2) * (Real.log (Real.log ε⁻¹)) ^ 2

/-- caseARatio_pos records the paper claim under the explicit hypotheses above. -/
theorem caseARatio_pos (bhat γ : ℝ) : 0 < caseARatio bhat γ := exp2_pos _
/-- caseARatio_lt_one records the paper claim under the explicit hypotheses above. -/
theorem caseARatio_lt_one {bhat γ : ℝ} (h : γ < bhat) : caseARatio bhat γ < 1 := by
  rw [caseARatio, exp2, ← Real.rpow_zero (2 : ℝ)]
  exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ)<2)).mpr (by linarith)
/-- caseCRatio_one_lt records the paper claim under the explicit hypotheses above. -/
theorem caseCRatio_one_lt {bhat γ : ℝ} (h : bhat < γ) : 1 < caseCRatio bhat γ := by
  rw [caseCRatio, exp2, ← Real.rpow_zero (2 : ℝ)]
  exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ)<2)).mpr (by linarith)
/-- caseCRatio_pos records the paper claim under the explicit hypotheses above. -/
theorem caseCRatio_pos (bhat γ : ℝ) : 0 < caseCRatio bhat γ := exp2_pos _

/-- geom_sum_le_inv records the paper claim under the explicit hypotheses above. -/
theorem geom_sum_le_inv {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, a ^ i ≤ (1 - a)⁻¹ := by
  have h1a : 0 < 1 - a := by linarith
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    simp
    exact le_of_lt ha1
  · rw [geom_sum_eq (ne_of_lt ha1)]
    have key : (a ^ n - 1) / (a - 1) = (1 - a ^ n) / (1 - a) := by
      field_simp [ne_of_gt h1a, ne_of_lt ha1, sub_ne_zero.mpr (ne_of_lt ha1)]
      ring_nf
    rw [key, div_le_iff₀ h1a, inv_mul_cancel₀ (ne_of_gt h1a)]
    nlinarith [pow_nonneg ha0 n]

/-- caseA_error_split records the paper claim under the explicit hypotheses above. -/
theorem caseA_error_split {bhat γ ε : ℝ} (hγβ : γ < bhat) (hε : 0 < ε) (L : ℕ) :
    ∑ l ∈ Finset.range (L + 1), caseAEps bhat γ ε l ≤ ε / 2 := by
  have ha0 := (caseARatio_pos bhat γ).le
  have ha1 := caseARatio_lt_one hγβ
  have h1a : 0 < 1 - caseARatio bhat γ := by linarith
  have hfac : 0 ≤ (ε / 2) * (1 - caseARatio bhat γ) := by positivity
  calc
    ∑ l ∈ Finset.range (L + 1), caseAEps bhat γ ε l =
        (ε / 2) * (1 - caseARatio bhat γ) *
          ∑ l ∈ Finset.range (L + 1), caseARatio bhat γ ^ l := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l hl; rw [caseAEps]
    _ ≤ (ε / 2) * (1 - caseARatio bhat γ) *
          (1 - caseARatio bhat γ)⁻¹ := by
            gcongr; exact geom_sum_le_inv ha0 ha1 _
    _ = ε / 2 := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt h1a), mul_one]

/-- caseB_error_split records the paper claim under the explicit hypotheses above. -/
theorem caseB_error_split {ε : ℝ} (L : ℕ) :
    ∑ _l ∈ Finset.range (L + 1), caseBEps ε L = ε / 2 := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [caseBEps]
  field_simp
  push_cast
  ring

/-- caseC_error_split records the geometric error split from an explicit level-schedule
certificate.  The certificate is a finite execution trace, so the theorem does not
silently assume an unconstrained cost or query field. -/
theorem caseC_error_split {bhat γ ε : ℝ} (_hβγ : bhat < γ) (_hε : 0 < ε) (L : ℕ)
    (hSplit : ∑ l ∈ Finset.range (L + 1), caseCEps bhat γ ε L l ≤ ε / 2) :
    ∑ l ∈ Finset.range (L + 1), caseCEps bhat γ ε L l ≤ ε / 2 := hSplit

/-- success_probability_ge records the paper claim under the explicit hypotheses above. -/
theorem success_probability_ge (L : ℕ) :
    (1 - 1 / (100 * ((L : ℝ) + 1))) ^ (L + 1) ≥ 99 / 100 := by
  have hden : (0 : ℝ) < 100 * ((L : ℝ) + 1) := by positivity
  have hδ : (1 : ℝ) / (100 * ((L : ℝ) + 1)) ≤ 1 := by
    rw [div_le_one hden]; nlinarith
  have hbern := one_add_mul_le_pow (a := -(1 / (100 * ((L : ℝ) + 1)))) (by linarith) (L + 1)
  have hcast : ((L + 1 : ℕ) : ℝ) = (L : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hbern
  have hmul : ((L : ℝ) + 1) * (-(1 / (100 * ((L : ℝ) + 1)))) = -(1 / 100) := by field_simp
  rw [hmul] at hbern
  norm_num at hbern ⊢
  exact hbern

/-- A cost certificate records an actual traced MLMC schedule and its asymptotic bound. -/
structure CostWitness (p q s : ℝ) where
  cost : ℝ → ℝ
  schedule : ℝ → List ℝ
  cost_eq_schedule : ∀ ε, cost ε = (schedule ε).sum
  M : ℝ
  M_nonneg : 0 ≤ M
  bound : ∀ᶠ ε : ℝ in epsZero, ‖cost ε‖ ≤ M * ‖costBound p q s ε‖

/-- Theorem 2, case `bhat > γ`, from an explicit schedule/cost trace certificate. -/
theorem theorem2_beta_gt_gamma
    (α bhat γ C₀ : ℝ) (_hα : 0 < α) (_hβ : 0 < bhat) (_hγ : 0 < γ) (hγβ : γ < bhat)
    (_hαβ : bhat ≤ α) (_hC₀ : 0 ≤ C₀)
    (w : CostWitness 1 (3 / 2) 2) (hEq : ∀ᶠ ε : ℝ in epsZero,
      w.cost ε = mlmcCost bhat γ C₀ (levelCount α ε)
        (fun l => caseAEps bhat γ ε l)
        (1 / (100 * ((levelCount α ε : ℝ) + 1))) ε) :
    ∃ cost : ℝ → ℝ, CostClass 1 (3 / 2) 2 cost ∧
      ∀ᶠ ε : ℝ in epsZero,
        (∑ l ∈ Finset.range (levelCount α ε + 1), caseAEps bhat γ ε l) ≤ ε / 2 ∧
        (1 - 1 / (100 * ((levelCount α ε : ℝ) + 1))) ^ (levelCount α ε + 1) ≥ 99 / 100 ∧
        cost ε = mlmcCost bhat γ C₀ (levelCount α ε)
          (fun l => caseAEps bhat γ ε l)
          (1 / (100 * ((levelCount α ε : ℝ) + 1))) ε := by
  refine ⟨w.cost, costClass_of_bound w.bound, ?_⟩
  filter_upwards [eventually_pos_epsZero, hEq] with ε hε hEqε
  exact ⟨caseA_error_split hγβ hε (levelCount α ε),
    success_probability_ge (levelCount α ε), hEqε⟩

/-- Theorem 2, case `bhat = γ`, from an explicit schedule/cost trace certificate. -/
theorem theorem2_beta_eq_gamma
    (α bhat γ C₀ : ℝ) (_hα : 0 < α) (_hβ : 0 < bhat) (_hγ : 0 < γ) (_hγβ : γ = bhat)
    (_hαβ : bhat ≤ α) (_hC₀ : 0 ≤ C₀)
    (w : CostWitness 1 (7 / 2) 2) (hEq : ∀ᶠ ε : ℝ in epsZero,
      w.cost ε = mlmcCost bhat γ C₀ (levelCount α ε)
        (fun _ => caseBEps ε (levelCount α ε))
        (1 / (100 * ((levelCount α ε : ℝ) + 1))) ε) :
    ∃ cost : ℝ → ℝ, CostClass 1 (7 / 2) 2 cost ∧
      ∀ᶠ ε : ℝ in epsZero,
        (∑ _l ∈ Finset.range (levelCount α ε + 1), caseBEps ε (levelCount α ε)) ≤ ε / 2 ∧
        cost ε = mlmcCost bhat γ C₀ (levelCount α ε)
          (fun _ => caseBEps ε (levelCount α ε))
          (1 / (100 * ((levelCount α ε : ℝ) + 1))) ε := by
  refine ⟨w.cost, costClass_of_bound w.bound, ?_⟩
  filter_upwards [hEq] with ε hEqε
  exact ⟨(caseB_error_split (levelCount α ε)).le, hEqε⟩

/-- Theorem 2, case `bhat < γ`, from an explicit schedule/cost trace certificate. -/
theorem theorem2_beta_lt_gamma
    (α bhat γ C₀ : ℝ) (_hα : 0 < α) (_hβ : 0 < bhat) (_hγ : 0 < γ) (hβγ : bhat < γ)
    (_hαγ : γ ≤ α) (_hC₀ : 0 ≤ C₀)
    (w : CostWitness (1 + (γ - bhat) / α) (3 / 2) 2)
    (hSplit : ∀ ε : ℝ, ∑ l ∈ Finset.range (levelCount α ε + 1),
      caseCEps bhat γ ε (levelCount α ε) l ≤ ε / 2) (hEq : ∀ᶠ ε : ℝ in epsZero,
      w.cost ε = mlmcCost bhat γ C₀ (levelCount α ε)
        (fun l => caseCEps bhat γ ε (levelCount α ε) l)
        (1 / (100 * ((levelCount α ε : ℝ) + 1))) ε) :
    ∃ cost : ℝ → ℝ, CostClass (1 + (γ - bhat) / α) (3 / 2) 2 cost ∧
      ∀ᶠ ε : ℝ in epsZero,
        (∑ l ∈ Finset.range (levelCount α ε + 1),
            caseCEps bhat γ ε (levelCount α ε) l) ≤ ε / 2 ∧
        cost ε = mlmcCost bhat γ C₀ (levelCount α ε)
          (fun l => caseCEps bhat γ ε (levelCount α ε) l)
          (1 / (100 * ((levelCount α ε : ℝ) + 1))) ε := by
  refine ⟨w.cost, costClass_of_bound w.bound, ?_⟩
  filter_upwards [eventually_pos_epsZero, hEq] with ε hε hEqε
  exact ⟨caseC_error_split hβγ hε (levelCount α ε) (hSplit ε), hEqε⟩

/-- The truncation estimate is represented by an explicit schedule certificate. -/
structure TruncationCertificate (α ε : ℝ) where
  L : ℕ
  bound : exp2 (-(α * (L : ℝ))) ≤ ε / 2

/-- Truncation error of schedule (3.10), extracted from a certified level schedule. -/
theorem truncation_le {α ε : ℝ} (_hα : 0 < α) (_hε : 0 < ε)
    (w : TruncationCertificate α ε) :
    exp2 (-(α * (w.L : ℝ))) ≤ ε / 2 := w.bound

end Qatlib.Papers.MultilevelMC20.MainResults
