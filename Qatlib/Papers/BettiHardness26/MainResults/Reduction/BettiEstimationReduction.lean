/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Betti reduction — finite probability skeleton of the planted-clique reduction

Strelchuk, Subramanian, Wesołowski, "Average-case hardness of Betti number estimation",
fixed arXiv:2609.12777v1 (2026-09-11).

This file isolates the *purely probabilistic* core of the reduction from the planted-clique
problem to Betti-number estimation (Section 4, Theorem 2.1). The set of input graphs is a finite
type `Γ`. The null case `G(n, 1/2)` is described by weights `mu0 : Γ → ℝ`, the planted case
`G(n, 1/2, k)` by `mu1 : Γ → ℝ`, with `∑ mu0 = ∑ mu1 = 1`. The balanced mixture
`D_k = ½ G(n,1/2) + ½ G(n,1/2,k)` has success probability `(s0 + s1)/2`.

The main lemma `reduction_threshold` is the proof of Theorem 2.1: an estimator `est` that
estimates the Betti value `beta` to additive error `< η` with success probability `≥ ½ + δ`
over `D_k` yields a *distinguisher* `η ≤ est` whose advantage is at least `δ`, whenever
`β = 0` on the null support and `β ≥ g0 ≥ 2η` on the planted support. The paper's Theorem 2.1
is the case `η = 1/2`, `g0 = 1` (the value gap between `0` and `≥ 1`, Lemmas 4.1–4.2), giving
`advantage ≥ s0 + s1 - 1 ≥ 2δ ≥ δ` (the paper's Eq. (6) and final line, p.10).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BettiHardness26.MainResults.Reduction

open Finset

variable {Γ : Type*} [Fintype Γ]

/-- The `{0,1}`-valued real indicator of a decidable event. -/
def ind (P : Γ → Prop) [DecidablePred P] (g : Γ) : ℝ := if P g then 1 else 0

/-- The natural distinguisher induced by an estimator `est` at threshold `η`: it outputs `1`
when `est ≥ η`. -/
def detector (est : Γ → ℝ) (η : ℝ) : Γ → ℝ := fun g => ind (fun g => η ≤ est g) g

/-- Finite probability mass of an event under weights `mu`. -/
def prob (mu : Γ → ℝ) (P : Γ → Prop) [DecidablePred P] : ℝ :=
  ∑ g, mu g * ind P g

/-- The indicator function is nonnegative. -/
lemma ind_nonneg (P : Γ → Prop) [DecidablePred P] (g : Γ) : 0 ≤ ind P g := by
  unfold ind; split_ifs <;> norm_num

/-- The indicator function is at most one. -/
lemma ind_le_one (P : Γ → Prop) [DecidablePred P] (g : Γ) : ind P g ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

/-- The indicator of a true proposition equals one. -/
lemma ind_of_true (P : Γ → Prop) [DecidablePred P] {g : Γ} (h : P g) : ind P g = 1 := by
  unfold ind; simp [h]

/-- The indicator of a false proposition equals zero. -/
lemma ind_of_false (P : Γ → Prop) [DecidablePred P] {g : Γ} (h : ¬ P g) : ind P g = 0 := by
  unfold ind; simp [h]

/-- The indicator of a complement is one minus the indicator. -/
lemma ind_compl (P : Γ → Prop) [DecidablePred P] (g : Γ) :
    ind (fun g => ¬ P g) g = 1 - ind P g := by
  unfold ind; by_cases h : P g <;> simp [h]

/-- The threshold detector is nonnegative. -/
lemma detector_nonneg (est : Γ → ℝ) (η : ℝ) (g : Γ) : 0 ≤ detector est η g := by
  unfold detector; exact ind_nonneg _ g

/-- The detector equals one when the estimate reaches the threshold. -/
lemma detector_of_ge {est : Γ → ℝ} {η : ℝ} {g : Γ} (h : η ≤ est g) :
    detector est η g = 1 := by
  unfold detector; exact ind_of_true _ h

/-- The detector equals zero when the estimate stays below the threshold. -/
lemma detector_of_lt {est : Γ → ℝ} {η : ℝ} {g : Γ} (h : ¬ η ≤ est g) :
    detector est η g = 0 := by
  unfold detector; exact ind_of_false _ h

/-- The probability of the complement of an event is the total mass minus the
event probability. -/
lemma prob_compl (mu : Γ → ℝ) (P : Γ → Prop) [DecidablePred P] :
    prob mu (fun g => ¬ P g) = (∑ g, mu g) - prob mu P := by
  unfold prob
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [ind_compl]; ring

/-- **Reduction core of Theorem 2.1 (threshold form).** If the Betti value is `0` on the null
support and at least `g0 ≥ 2η` on the planted support, then an estimator achieving additive
error `< η` with success probability `≥ ½ + δ` over the balanced mixture yields a detector
`η ≤ est` with advantage at least `δ`. (Here `0 ≤ δ` is the positive-advantage parameter.) -/
theorem reduction_threshold
    (mu0 mu1 : Γ → ℝ) (hmu0 : ∀ g, 0 ≤ mu0 g) (hmu1 : ∀ g, 0 ≤ mu1 g)
    (hmu0sum : ∑ g, mu0 g = 1) (hmu1sum : ∑ g, mu1 g = 1)
    (beta est : Γ → ℝ) (η g0 δ : ℝ) (hη : 0 ≤ η) (hgap : 2 * η ≤ g0) (hδ : 0 ≤ δ)
    (hNull : ∀ g, mu0 g ≠ 0 → beta g = 0)
    (hPlanted : ∀ g, mu1 g ≠ 0 → g0 ≤ beta g)
    (hHyp : (prob mu0 (fun g => |est g - beta g| < η)
              + prob mu1 (fun g => |est g - beta g| < η)) / 2 ≥ 1/2 + δ) :
    (∑ g, mu1 g * detector est η g) - (∑ g, mu0 g * detector est η g) ≥ δ := by
  set Succ : Γ → Prop := fun g => |est g - beta g| < η with hSucc
  have hstep1 : ∀ g, mu1 g * ind Succ g ≤ mu1 g * detector est η g := by
    intro g
    by_cases hz : mu1 g = 0
    · simp [hz]
    · have hge : g0 ≤ beta g := hPlanted g hz
      have hpt : ind Succ g ≤ detector est η g := by
        by_cases hs : Succ g
        · have hb : |est g - beta g| < η := hs
          rw [abs_lt] at hb
          have hle : η ≤ est g := by linarith [hb.1, hb.2, hge, hgap]
          simp [ind_of_true Succ hs, detector_of_ge hle]
        · rw [ind_of_false Succ hs]
          exact detector_nonneg est η g
      exact mul_le_mul_of_nonneg_left hpt (hmu1 g)
  have hstep2 : ∀ g, mu0 g * detector est η g ≤ mu0 g * ind (fun g => ¬ Succ g) g := by
    intro g
    by_cases hz : mu0 g = 0
    · simp [hz]
    · have hzero : beta g = 0 := hNull g hz
      have hpt : detector est η g ≤ ind (fun g => ¬ Succ g) g := by
        by_cases hd : η ≤ est g
        · have hnotsucc : ¬ Succ g := by
            intro hs
            have hb : |est g - beta g| < η := hs
            rw [hzero, sub_zero, abs_lt] at hb
            linarith [hb.2, hd]
          simp [detector_of_ge hd, ind_of_true (fun g => ¬ Succ g) hnotsucc]
        · rw [detector_of_lt hd]
          exact ind_nonneg _ g
      exact mul_le_mul_of_nonneg_left hpt (hmu0 g)
  have hs1 : prob mu1 Succ ≤ ∑ g, mu1 g * detector est η g := by
    unfold prob
    exact Finset.sum_le_sum (fun g _ => hstep1 g)
  have hs0 : ∑ g, mu0 g * detector est η g ≤ prob mu0 (fun g => ¬ Succ g) := by
    unfold prob
    exact Finset.sum_le_sum (fun g _ => hstep2 g)
  have hcompl : prob mu0 (fun g => ¬ Succ g) = 1 - prob mu0 Succ := by
    rw [prob_compl, hmu0sum]
  have h1 : prob mu0 Succ + prob mu1 Succ ≥ 1 + 2 * δ := by nlinarith [hHyp]
  have h2 : (∑ g, mu1 g * detector est η g) - (∑ g, mu0 g * detector est η g)
      ≥ 2 * δ := by linarith [hs1, hs0, hcompl, h1]
  linarith [h2, hδ]

/-- **Reduction core of Theorem 2.1** (value gap `0` vs `≥ 1`, additive error `½`). -/
theorem estimator_yields_distinguisher
    (mu0 mu1 : Γ → ℝ) (hmu0 : ∀ g, 0 ≤ mu0 g) (hmu1 : ∀ g, 0 ≤ mu1 g)
    (hmu0sum : ∑ g, mu0 g = 1) (hmu1sum : ∑ g, mu1 g = 1)
    (beta est : Γ → ℝ) (delta : ℝ) (hδ : 0 ≤ delta)
    (hNull : ∀ g, mu0 g ≠ 0 → beta g = 0)
    (hPlanted : ∀ g, mu1 g ≠ 0 → 1 ≤ beta g)
    (hHyp : (prob mu0 (fun g => |est g - beta g| < 1/2)
              + prob mu1 (fun g => |est g - beta g| < 1/2)) / 2 ≥ 1/2 + delta) :
    (∑ g, mu1 g * detector est (1/2) g) - (∑ g, mu0 g * detector est (1/2) g)
      ≥ delta :=
  reduction_threshold mu0 mu1 hmu0 hmu1 hmu0sum hmu1sum beta est (1/2) 1 delta
    (by norm_num) (by norm_num) hδ hNull hPlanted hHyp

/-- **Multiplication reduction (paper Corollary 3 proof, §7.2, p.16).** A finite multiplicative
approximation `β/C ≤ est ≤ C β` separates `β = 0` from `β ≥ 1`: with `C ≥ 1` the detector
`1/(2C) ≤ est` is off on the null support and on on the planted support, so its advantage is at
least `δ`. -/
theorem multiplicative_yields_distinguisher
    (mu0 mu1 : Γ → ℝ) (hmu0 : ∀ g, 0 ≤ mu0 g) (hmu1 : ∀ g, 0 ≤ mu1 g)
    (hmu0sum : ∑ g, mu0 g = 1) (hmu1sum : ∑ g, mu1 g = 1)
    (beta est : Γ → ℝ) (C : ℝ) (hC : 1 ≤ C) (delta : ℝ) (hδ : 0 ≤ delta)
    (hNull : ∀ g, mu0 g ≠ 0 → beta g = 0)
    (hPlanted : ∀ g, mu1 g ≠ 0 → 1 ≤ beta g)
    (hHyp : (prob mu0 (fun g => beta g / C ≤ est g ∧ est g ≤ C * beta g)
              + prob mu1 (fun g => beta g / C ≤ est g ∧ est g ≤ C * beta g)) / 2
              ≥ 1/2 + delta) :
    (∑ g, mu1 g * detector est (1 / (2 * C)) g)
      - (∑ g, mu0 g * detector est (1 / (2 * C)) g) ≥ delta := by
  have hCpos : (0 : ℝ) < C := by linarith
  have h2Cpos : (0 : ℝ) < 2 * C := by linarith
  have hhalfpos : (0 : ℝ) < 1 / (2 * C) := by positivity
  have hhalflt : 1 / (2 * C) < 1 / C := by
    rw [one_div, one_div, inv_lt_inv₀ h2Cpos hCpos]; nlinarith
  set Succ : Γ → Prop := fun g => beta g / C ≤ est g ∧ est g ≤ C * beta g with hSucc
  have hstep1 : ∀ g, mu1 g * ind Succ g ≤ mu1 g * detector est (1 / (2 * C)) g := by
    intro g
    by_cases hz : mu1 g = 0
    · simp [hz]
    · have hge : 1 ≤ beta g := hPlanted g hz
      have hpt : ind Succ g ≤ detector est (1 / (2 * C)) g := by
        by_cases hs : Succ g
        · have hleC : (1 : ℝ) / C ≤ est g :=
            le_trans (div_le_div_of_nonneg_right hge (le_of_lt hCpos)) hs.1
          have hle : 1 / (2 * C) ≤ est g := le_trans (le_of_lt hhalflt) hleC
          rw [ind_of_true Succ hs, detector_of_ge hle]
        · rw [ind_of_false Succ hs]
          exact detector_nonneg est (1 / (2 * C)) g
      exact mul_le_mul_of_nonneg_left hpt (hmu1 g)
  have hstep2 : ∀ g, mu0 g * detector est (1 / (2 * C)) g ≤
      mu0 g * ind (fun g => ¬ Succ g) g := by
    intro g
    by_cases hz : mu0 g = 0
    · simp [hz]
    · have hzero : beta g = 0 := hNull g hz
      have hpt : detector est (1 / (2 * C)) g ≤ ind (fun g => ¬ Succ g) g := by
        by_cases hd : 1 / (2 * C) ≤ est g
        · have hnotsucc : ¬ Succ g := by
            intro hs
            have hle : est g ≤ C * beta g := hs.2
            rw [hzero, mul_zero] at hle
            linarith [hd, hle, hhalfpos]
          rw [detector_of_ge hd, ind_of_true (fun g => ¬ Succ g) hnotsucc]
        · rw [detector_of_lt hd]
          exact ind_nonneg _ g
      exact mul_le_mul_of_nonneg_left hpt (hmu0 g)
  have hs1 : prob mu1 Succ ≤ ∑ g, mu1 g * detector est (1 / (2 * C)) g := by
    unfold prob
    exact Finset.sum_le_sum (fun g _ => hstep1 g)
  have hs0 : ∑ g, mu0 g * detector est (1 / (2 * C)) g
      ≤ prob mu0 (fun g => ¬ Succ g) := by
    unfold prob
    exact Finset.sum_le_sum (fun g _ => hstep2 g)
  have hcompl : prob mu0 (fun g => ¬ Succ g) = 1 - prob mu0 Succ := by
    rw [prob_compl, hmu0sum]
  have h1 : prob mu0 Succ + prob mu1 Succ ≥ 1 + 2 * delta := by nlinarith [hHyp]
  have h2 : (∑ g, mu1 g * detector est (1 / (2 * C)) g)
      - (∑ g, mu0 g * detector est (1 / (2 * C)) g) ≥ 2 * delta := by
    linarith [hs1, hs0, hcompl, h1]
  linarith [h2, hδ]

end Qatlib.Papers.BettiHardness26.MainResults.Reduction
