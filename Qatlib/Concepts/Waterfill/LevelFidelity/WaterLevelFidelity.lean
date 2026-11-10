/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtLinearSolve.Waterfill
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.NativeNumerics.WaterFilling

namespace Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity

open scoped BigOperators

noncomputable def levelFill {m : ℕ} (π σ : Fin m → ℚ) (γ : ℝ) (i : Fin m) : ℝ :=
  min (π i : ℝ) (γ * (σ i : ℝ))

noncomputable def levelMass {m : ℕ} (π σ : Fin m → ℚ) (γ : ℝ) : ℝ :=
  ∑ i, (levelFill π σ γ i) ^ 2

noncomputable def levelDot {m : ℕ} (π σ : Fin m → ℚ) (γ : ℝ) : ℝ :=
  ∑ i, (σ i : ℝ) * levelFill π σ γ i

noncomputable def waterPmin {m : ℕ} (π σ : Fin m → ℚ) : ℝ :=
  (∑ i, (π i : ℝ) * (σ i : ℝ)) ^ 2

noncomputable def waterPmax {m : ℕ} (π σ : Fin m → ℚ) : ℝ :=
  ∑ i, if 0 < π i then (σ i : ℝ) ^ 2 else 0
section FidelityHelpers

set_option maxHeartbeats 2000000

theorem levelFill_mono {m : ℕ} (π σ : Fin m → ℚ) (hσ : ∀ i, 0 < σ i) {a b : ℝ}
    (hab : a ≤ b) (i : Fin m) : levelFill π σ a i ≤ levelFill π σ b i :=
  min_le_min (le_refl _)
    (mul_le_mul_of_nonneg_right hab (show (0 : ℝ) ≤ (σ i : ℝ) by exact_mod_cast (hσ i).le))

theorem levelFill_nonneg {m : ℕ} (π σ : Fin m → ℚ) (hπ : ∀ i, 0 ≤ π i)
    (hσ : ∀ i, 0 < σ i) {γ : ℝ} (hγ : 0 ≤ γ) (i : Fin m) : 0 ≤ levelFill π σ γ i :=
  le_min (by exact_mod_cast hπ i) (mul_nonneg hγ (by exact_mod_cast (hσ i).le))

theorem levelMass_mono {m : ℕ} (π σ : Fin m → ℚ) (hπ : ∀ i, 0 ≤ π i)
    (hσ : ∀ i, 0 < σ i) {a b : ℝ} (hγ : 0 ≤ a) (hab : a ≤ b) :
    levelMass π σ a ≤ levelMass π σ b := by
  have per : ∀ i, (levelFill π σ a i) ^ 2 ≤ (levelFill π σ b i) ^ 2 := by
    intro i
    have h1 : (0 : ℝ) ≤ levelFill π σ a i := levelFill_nonneg π σ hπ hσ hγ i
    have h2 : levelFill π σ a i ≤ levelFill π σ b i := levelFill_mono π σ hσ hab i
    nlinarith [h1, h2]
  exact Finset.sum_le_sum fun i _ => per i

private theorem fill_increment_mul {m : ℕ} (π σ : Fin m → ℚ) (hσ : ∀ i, 0 < σ i)
    {a b : ℝ} (hab : a ≤ b) (i : Fin m) :
    levelFill π σ a i * (levelFill π σ b i - levelFill π σ a i) =
      a * (σ i : ℝ) * (levelFill π σ b i - levelFill π σ a i) := by
  by_cases hs : (π i : ℝ) ≤ a * (σ i : ℝ)
  · have hb : (π i : ℝ) ≤ b * (σ i : ℝ) :=
      hs.trans (mul_le_mul_of_nonneg_right hab
        (show (0 : ℝ) ≤ (σ i : ℝ) by exact_mod_cast (hσ i).le))
    rw [show levelFill π σ a i = (π i : ℝ) from min_eq_left hs,
      show levelFill π σ b i = (π i : ℝ) from min_eq_left hb]
    ring
  · rw [show levelFill π σ a i = a * (σ i : ℝ) from min_eq_right (le_of_not_ge hs)]

private theorem mass_increment {m : ℕ} (π σ : Fin m → ℚ) (hσ : ∀ i, 0 < σ i)
    {a b : ℝ} (_ha : 0 ≤ a) (hab : a ≤ b) :
    levelMass π σ b = levelMass π σ a + 2 * a * (levelDot π σ b - levelDot π σ a) +
      ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2 := by
  have per : ∀ i, (levelFill π σ b i) ^ 2 - (levelFill π σ a i) ^ 2 =
      2 * a * ((σ i : ℝ) * levelFill π σ b i - (σ i : ℝ) * levelFill π σ a i) +
        (levelFill π σ b i - levelFill π σ a i) ^ 2 := by
    intro i
    linear_combination 2 * fill_increment_mul π σ hσ hab i
  have hsum : (∑ i, (levelFill π σ b i) ^ 2) - (∑ i, (levelFill π σ a i) ^ 2) =
      2 * a * ((∑ i, (σ i : ℝ) * levelFill π σ b i) -
        (∑ i, (σ i : ℝ) * levelFill π σ a i)) +
        (∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2) := by
    have e1 : (∑ i, (levelFill π σ b i) ^ 2) - (∑ i, (levelFill π σ a i) ^ 2) =
        ∑ i, ((levelFill π σ b i) ^ 2 - (levelFill π σ a i) ^ 2) := by
      rw [Finset.sum_sub_distrib]
    have e2 : (∑ i, (σ i : ℝ) * levelFill π σ b i) -
        (∑ i, (σ i : ℝ) * levelFill π σ a i) =
        ∑ i, ((σ i : ℝ) * levelFill π σ b i - (σ i : ℝ) * levelFill π σ a i) := by
      rw [Finset.sum_sub_distrib]
    have e3 : 2 * a * ∑ i, ((σ i : ℝ) * levelFill π σ b i -
        (σ i : ℝ) * levelFill π σ a i) =
        ∑ i, (2 * a * ((σ i : ℝ) * levelFill π σ b i -
          (σ i : ℝ) * levelFill π σ a i)) := by
      rw [Finset.mul_sum]
    rw [e1, e2, e3, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => per i
  unfold levelMass levelDot
  linarith [hsum]

private theorem mass_le_level_dot {m : ℕ} (π σ : Fin m → ℚ) (hπ : ∀ i, 0 ≤ π i)
    (_hσ : ∀ i, 0 < σ i) {a : ℝ} (_ha : 0 ≤ a) :
    levelMass π σ a ≤ a * levelDot π σ a := by
  have per : ∀ i, (levelFill π σ a i) ^ 2 ≤ a * ((σ i : ℝ) * levelFill π σ a i) := by
    intro i
    have hπ' : (0 : ℝ) ≤ (π i : ℝ) := by exact_mod_cast hπ i
    by_cases hs : (π i : ℝ) ≤ a * (σ i : ℝ)
    · rw [show levelFill π σ a i = (π i : ℝ) from min_eq_left hs]
      nlinarith [mul_nonneg hπ'
        (show (0 : ℝ) ≤ a * (σ i : ℝ) - (π i : ℝ) by linarith)]
    · rw [show levelFill π σ a i = a * (σ i : ℝ) from min_eq_right (le_of_not_ge hs)]
      exact le_of_eq (by ring)
  calc levelMass π σ a ≤ ∑ i, a * ((σ i : ℝ) * levelFill π σ a i) :=
        Finset.sum_le_sum fun i _ => per i
    _ = a * levelDot π σ a := by rw [levelDot, Finset.mul_sum]

private theorem sum_mul_sq_le {m : ℕ} (f g : Fin m → ℝ) :
    (∑ i, f i * g i) ^ 2 ≤ (∑ i, f i ^ 2) * (∑ i, g i ^ 2) := by
  have h1 : |∑ i, f i * g i| ≤
      (‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin m))‖ *
        ‖(WithLp.toLp 2 g : EuclideanSpace ℝ (Fin m))‖) := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, WithLp.ofLp_toLp,
      Pi.star_apply, star_trivial, mul_comm] using!
      abs_real_inner_le_norm (WithLp.toLp 2 f : EuclideanSpace ℝ (Fin m))
        (WithLp.toLp 2 g : EuclideanSpace ℝ (Fin m))
  have h2 : (‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin m))‖ *
      ‖(WithLp.toLp 2 g : EuclideanSpace ℝ (Fin m))‖) ^ 2 =
      (∑ i, f i ^ 2) * (∑ i, g i ^ 2) := by
    have hf : ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin m))‖ ^ 2 = ∑ i, f i ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    have hg : ‖(WithLp.toLp 2 g : EuclideanSpace ℝ (Fin m))‖ ^ 2 = ∑ i, g i ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    nlinarith [norm_nonneg (WithLp.toLp 2 f : EuclideanSpace ℝ (Fin m)),
      norm_nonneg (WithLp.toLp 2 g : EuclideanSpace ℝ (Fin m))]
  rw [← h2]
  refine sq_le_sq.mpr ?_
  rw [abs_of_nonneg (show (0 : ℝ) ≤ ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin m))‖ *
    ‖(WithLp.toLp 2 g : EuclideanSpace ℝ (Fin m))‖ by positivity)]
  exact h1

private theorem dot_increment_bound {m : ℕ} (π σ : Fin m → ℚ) (hπ : ∀ i, 0 ≤ π i)
    (hσ : ∀ i, 0 < σ i) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a * (levelDot π σ b - levelDot π σ a) ^ 2 ≤
      levelDot π σ a * ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2 := by
  have key : ∀ i, a * ((σ i : ℝ) * (levelFill π σ b i - levelFill π σ a i)) =
      levelFill π σ a i * (levelFill π σ b i - levelFill π σ a i) := by
    intro i
    linear_combination (-(fill_increment_mul π σ hσ hab i))
  have hinner : a * (levelDot π σ b - levelDot π σ a) =
      ∑ i, levelFill π σ a i * (levelFill π σ b i - levelFill π σ a i) := by
    unfold levelDot
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by linear_combination (key i)
  have hcs := sum_mul_sq_le (fun i => levelFill π σ a i)
    (fun i => levelFill π σ b i - levelFill π σ a i)
  have hf3 := mass_le_level_dot π σ hπ hσ ha.le
  have hS : (0 : ℝ) ≤ ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : (∑ i, (levelFill π σ a i) ^ 2) = levelMass π σ a := rfl
  have c1 : (a * (levelDot π σ b - levelDot π σ a)) ^ 2 ≤
      (∑ i, (levelFill π σ a i) ^ 2) *
        (∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2) := by
    rw [hinner]
    exact hcs
  have c2 : (∑ i, (levelFill π σ a i) ^ 2) *
      (∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2) ≤
      (a * levelDot π σ a) * ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2 := by
    nlinarith [hf3, hS, hB]
  have c3 : a * (a * (levelDot π σ b - levelDot π σ a) ^ 2) ≤
      a * (levelDot π σ a * ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2) := by
    nlinarith [c1, c2]
  nlinarith [c3, ha]

private theorem fidelity_anti_le {m : ℕ} (π σ : Fin m → ℚ) (hπ : ∀ i, 0 ≤ π i)
    (hσ : ∀ i, 0 < σ i) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    levelDot π σ b ^ 2 * levelMass π σ a ≤ levelDot π σ a ^ 2 * levelMass π σ b := by
  have hinc := mass_increment π σ hσ ha.le hab
  have hf3 := mass_le_level_dot π σ hπ hσ ha.le
  have hcs := dot_increment_bound π σ hπ hσ ha hab
  have hS : (0 : ℝ) ≤ ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hΔ : (0 : ℝ) ≤ levelDot π σ b - levelDot π σ a := by
    have hsum : (0 : ℝ) ≤ ∑ i, (σ i : ℝ) *
        (levelFill π σ b i - levelFill π σ a i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg
        (show (0 : ℝ) ≤ (σ i : ℝ) by exact_mod_cast (hσ i).le)
        (sub_nonneg.mpr (levelFill_mono π σ hσ hab i))
    have heq : ∑ i, (σ i : ℝ) * (levelFill π σ b i - levelFill π σ a i) =
        levelDot π σ b - levelDot π σ a := by
      unfold levelDot
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  have hA : (0 : ℝ) ≤ levelDot π σ a := by
    unfold levelDot
    exact Finset.sum_nonneg fun i _ => mul_nonneg
      (show (0 : ℝ) ≤ (σ i : ℝ) by exact_mod_cast (hσ i).le)
      (levelFill_nonneg π σ hπ hσ ha.le i)
  have hB : (0 : ℝ) ≤ levelMass π σ a :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have key1 : (levelDot π σ b - levelDot π σ a) ^ 2 * levelMass π σ a ≤
      levelDot π σ a ^ 2 * ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2 := by
    have step1 : a * ((levelDot π σ b - levelDot π σ a) ^ 2 * levelMass π σ a) ≤
        (levelDot π σ a * ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2) *
          levelMass π σ a := by
      nlinarith [hcs, hB]
    have hAS : (0 : ℝ) ≤ levelDot π σ a *
        ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2 := mul_nonneg hA hS
    have step2 : (levelDot π σ a * ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2) *
        levelMass π σ a ≤
        a * (levelDot π σ a ^ 2 * ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2) := by
      nlinarith [hf3, hAS]
    nlinarith [step1, step2, ha]
  have t1 : (0 : ℝ) ≤ 2 * levelDot π σ a * (levelDot π σ b - levelDot π σ a) :=
    mul_nonneg (by linarith) hΔ
  have t2 : (0 : ℝ) ≤ a * levelDot π σ a - levelMass π σ a := by linarith
  have term1 : (0 : ℝ) ≤ 2 * levelDot π σ a * (levelDot π σ b - levelDot π σ a) *
      (a * levelDot π σ a - levelMass π σ a) := mul_nonneg t1 t2
  have term2 : (0 : ℝ) ≤ levelDot π σ a ^ 2 *
      ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2 -
      (levelDot π σ b - levelDot π σ a) ^ 2 * levelMass π σ a := by linarith
  have diff : levelDot π σ a ^ 2 * levelMass π σ b - levelDot π σ b ^ 2 * levelMass π σ a =
      2 * levelDot π σ a * (levelDot π σ b - levelDot π σ a) *
        (a * levelDot π σ a - levelMass π σ a) +
      (levelDot π σ a ^ 2 * ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2 -
        (levelDot π σ b - levelDot π σ a) ^ 2 * levelMass π σ a) := by
    have hBb : levelMass π σ b = levelMass π σ a +
        2 * a * (levelDot π σ b - levelDot π σ a) +
        ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2 := hinc
    have hAb : levelDot π σ b =
        levelDot π σ a + (levelDot π σ b - levelDot π σ a) := by ring
    rw [hBb, hAb]
    ring
  linarith [diff, term1, term2]

private theorem fidelity_anti_lt_core {m : ℕ} (π σ : Fin m → ℚ) (hπ : ∀ i, 0 ≤ π i)
    (hσ : ∀ i, 0 < σ i) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (h1 : ∃ j, 0 < (π j : ℝ) ∧ (π j : ℝ) < a * (σ j : ℝ))
    (h2 : ∃ i₁, a * (σ i₁ : ℝ) < (π i₁ : ℝ)) :
    levelDot π σ b ^ 2 * levelMass π σ a < levelDot π σ a ^ 2 * levelMass π σ b := by
  have hinc := mass_increment π σ hσ ha.le hab.le
  have hf3 := mass_le_level_dot π σ hπ hσ ha.le
  have hcs := dot_increment_bound π σ hπ hσ ha hab.le
  have hS : (0 : ℝ) ≤ ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : (0 : ℝ) ≤ levelMass π σ a :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  obtain ⟨j, hjπ, hjsat⟩ := h1
  obtain ⟨i₁, hi₁⟩ := h2
  have hσpos : ∀ i, (0 : ℝ) < (σ i : ℝ) := fun i => by exact_mod_cast hσ i
  have hA : (0 : ℝ) < levelDot π σ a := by
    unfold levelDot
    have heq : levelFill π σ a j = (π j : ℝ) := min_eq_left hjsat.le
    exact Finset.sum_pos' (f := fun i => (σ i : ℝ) * levelFill π σ a i)
      (fun i _ => mul_nonneg (hσpos i).le
        (levelFill_nonneg π σ hπ hσ ha.le i))
      ⟨j, Finset.mem_univ j, by
        show (0 : ℝ) < (σ j : ℝ) * levelFill π σ a j
        rw [heq]
        exact mul_pos (hσpos j) hjπ⟩
  have hΔ : (0 : ℝ) < levelDot π σ b - levelDot π σ a := by
    have hδ₁ : (0 : ℝ) < levelFill π σ b i₁ - levelFill π σ a i₁ := by
      have hεa₁ : levelFill π σ a i₁ = a * (σ i₁ : ℝ) := by
        refine min_eq_right (le_of_not_ge ?_)
        intro hcon
        exact absurd hi₁ (not_lt.mpr hcon)
      have hεb₁ : levelFill π σ b i₁ = min (π i₁ : ℝ) (b * (σ i₁ : ℝ)) := rfl
      rw [hεa₁, hεb₁]
      have hlt := lt_min_iff.mpr ⟨hi₁, mul_lt_mul_of_pos_right hab (hσpos i₁)⟩
      linarith
    have hsum : (0 : ℝ) < ∑ i, (σ i : ℝ) *
        (levelFill π σ b i - levelFill π σ a i) :=
      Finset.sum_pos' (f := fun i => (σ i : ℝ) *
        (levelFill π σ b i - levelFill π σ a i))
        (fun i _ => mul_nonneg (hσpos i).le
          (sub_nonneg.mpr (levelFill_mono π σ hσ hab.le i)))
        ⟨i₁, Finset.mem_univ i₁, mul_pos (hσpos i₁) hδ₁⟩
    have heq : ∑ i, (σ i : ℝ) * (levelFill π σ b i - levelFill π σ a i) =
        levelDot π σ b - levelDot π σ a := by
      unfold levelDot
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  have hf3s : levelMass π σ a < a * levelDot π σ a := by
    have hper : ∀ i, (levelFill π σ a i) ^ 2 - a * ((σ i : ℝ) * levelFill π σ a i) ≤ 0 := by
      intro i
      have hπ' : (0 : ℝ) ≤ (π i : ℝ) := by exact_mod_cast hπ i
      by_cases hs : (π i : ℝ) ≤ a * (σ i : ℝ)
      · rw [show levelFill π σ a i = (π i : ℝ) from min_eq_left hs]
        nlinarith [mul_nonneg hπ'
          (show (0 : ℝ) ≤ a * (σ i : ℝ) - (π i : ℝ) by linarith)]
      · rw [show levelFill π σ a i = a * (σ i : ℝ) from min_eq_right (le_of_not_ge hs)]
        exact le_of_eq (by ring)
    have hsplit : levelMass π σ a - a * levelDot π σ a =
        ((levelFill π σ a j) ^ 2 - a * ((σ j : ℝ) * levelFill π σ a j)) +
        ∑ i ∈ Finset.univ.erase j,
          ((levelFill π σ a i) ^ 2 - a * ((σ i : ℝ) * levelFill π σ a i)) := by
      have hsum : (∑ i ∈ Finset.univ.erase j,
          ((levelFill π σ a i) ^ 2 - a * ((σ i : ℝ) * levelFill π σ a i))) +
          ((levelFill π σ a j) ^ 2 - a * ((σ j : ℝ) * levelFill π σ a j)) =
          ∑ i, ((levelFill π σ a i) ^ 2 - a * ((σ i : ℝ) * levelFill π σ a i)) :=
        Finset.sum_erase_add _ _ (Finset.mem_univ j)
      unfold levelMass levelDot
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← hsum]
      ring
    have hneg : (levelFill π σ a j) ^ 2 - a * ((σ j : ℝ) * levelFill π σ a j) < 0 := by
      rw [show levelFill π σ a j = (π j : ℝ) from min_eq_left hjsat.le]
      have hpos : (0 : ℝ) < a * (σ j : ℝ) - (π j : ℝ) := by linarith
      have hprod : (0 : ℝ) < (π j : ℝ) * (a * (σ j : ℝ) - (π j : ℝ)) := mul_pos hjπ hpos
      nlinarith [hprod]
    have hrest : (∑ i ∈ Finset.univ.erase j,
        ((levelFill π σ a i) ^ 2 - a * ((σ i : ℝ) * levelFill π σ a i))) ≤ 0 :=
      Finset.sum_nonpos fun i _ => hper i
    linarith [hsplit, hneg, hrest]
  have key1 : (levelDot π σ b - levelDot π σ a) ^ 2 * levelMass π σ a ≤
      levelDot π σ a ^ 2 * ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2 := by
    have step1 : a * ((levelDot π σ b - levelDot π σ a) ^ 2 * levelMass π σ a) ≤
        (levelDot π σ a * ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2) *
          levelMass π σ a := by
      nlinarith [hcs, hB]
    have hAS : (0 : ℝ) ≤ levelDot π σ a *
        ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2 := mul_nonneg hA.le hS
    have step2 : (levelDot π σ a * ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2) *
        levelMass π σ a ≤
        a * (levelDot π σ a ^ 2 * ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2) := by
      nlinarith [hf3, hAS]
    nlinarith [step1, step2, ha]
  have term1 : (0 : ℝ) < 2 * levelDot π σ a * (levelDot π σ b - levelDot π σ a) *
      (a * levelDot π σ a - levelMass π σ a) :=
    mul_pos (mul_pos (by linarith) hΔ) (by linarith)
  have term2 : (0 : ℝ) ≤ levelDot π σ a ^ 2 *
      ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2 -
      (levelDot π σ b - levelDot π σ a) ^ 2 * levelMass π σ a := by linarith
  have diff : levelDot π σ a ^ 2 * levelMass π σ b - levelDot π σ b ^ 2 * levelMass π σ a =
      2 * levelDot π σ a * (levelDot π σ b - levelDot π σ a) *
        (a * levelDot π σ a - levelMass π σ a) +
      (levelDot π σ a ^ 2 * ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2 -
        (levelDot π σ b - levelDot π σ a) ^ 2 * levelMass π σ a) := by
    have hBb : levelMass π σ b = levelMass π σ a +
        2 * a * (levelDot π σ b - levelDot π σ a) +
        ∑ i, (levelFill π σ b i - levelFill π σ a i) ^ 2 := hinc
    have hAb : levelDot π σ b =
        levelDot π σ a + (levelDot π σ b - levelDot π σ a) := by ring
    rw [hBb, hAb]
    ring
  linarith [diff, term1, term2]

theorem levelFillCast {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) (i : Fin m) :
    levelFill π σ (γ : ℝ) i = (waterFill π σ γ i : ℝ) := by
  by_cases h : π i ≤ γ * σ i
  · rw [show levelFill π σ (γ : ℝ) i = (π i : ℝ) from
      min_eq_left (by exact_mod_cast h),
      show (waterFill π σ γ i : ℝ) = ((π i : ℚ) : ℝ) from by
        simp [waterFill, min_eq_left h]]
  · rw [show levelFill π σ (γ : ℝ) i = (γ : ℝ) * (σ i : ℝ) from
      min_eq_right (by exact_mod_cast (le_of_not_ge h)),
      show (waterFill π σ γ i : ℝ) = ((γ * σ i : ℚ) : ℝ) from by
        simp [waterFill, min_eq_right (le_of_not_ge h)], Rat.cast_mul]

theorem levelOverlapLe {m : ℕ} (π σ : Fin m → ℚ) (_hσ : ∀ i, 0 < σ i) {γ : ℝ}
    (hγ : 0 < γ) (v : Fin m → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ (π i : ℝ))
    (he : (∑ i, v i ^ 2) ≤ levelMass π σ γ) :
    (∑ i, (σ i : ℝ) * v i) ≤ levelDot π σ γ := by
  have hi (j : Fin m) :
      2 * γ * ((σ j : ℝ) * v j - (σ j : ℝ) * levelFill π σ γ j) ≤
        (v j) ^ 2 - (levelFill π σ γ j) ^ 2 := by
    by_cases hs : (π j : ℝ) ≤ γ * (σ j : ℝ)
    · rw [show levelFill π σ γ j = (π j : ℝ) from min_eq_left hs]
      nlinarith [mul_nonneg (sub_nonneg.mpr (hv j).2)
        (show (0 : ℝ) ≤ 2 * γ * (σ j : ℝ) - (π j : ℝ) - v j by linarith [(hv j).2])]
    · rw [show levelFill π σ γ j = γ * (σ j : ℝ) from min_eq_right (le_of_not_ge hs)]
      nlinarith [sq_nonneg (v j - γ * (σ j : ℝ))]
  have hh := Finset.sum_le_sum (s := Finset.univ) fun j _ => hi j
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hh
  have hmass : (∑ j, (v j) ^ 2) ≤ ∑ j, (levelFill π σ γ j) ^ 2 := he
  unfold levelDot
  nlinarith [hh]

theorem levelFidelityStrictAnti (m : ℕ) (π σ : Fin m → ℚ) (γlo γhi : ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hσ : ∀ i, 0 < σ i) (hlohi : γlo < γhi)
    (hlow : ∀ i, 0 < π i → γlo * (σ i : ℝ) ≤ (π i : ℝ))
    (hwit : ∃ i₀, 0 < π i₀ ∧ γlo * (σ i₀ : ℝ) = (π i₀ : ℝ))
    (_hhigh : ∀ i, (π i : ℝ) ≤ γhi * (σ i : ℝ))
    (hwit2 : ∃ i₁, 0 < π i₁ ∧ (π i₁ : ℝ) = γhi * (σ i₁ : ℝ))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (haglo : γlo ≤ a) (hbhi : b ≤ γhi) :
    levelDot π σ b ^ 2 * levelMass π σ a < levelDot π σ a ^ 2 * levelMass π σ b := by
  obtain ⟨i₀, hπ₀, heq₀⟩ := hwit
  obtain ⟨i₁, hπ₁, heq₁⟩ := hwit2
  have hσpos : ∀ i, (0 : ℝ) < (σ i : ℝ) := fun i => by exact_mod_cast hσ i
  have hπ₀' : (0 : ℝ) < (π i₀ : ℝ) := by exact_mod_cast hπ₀
  have hγlo : (0 : ℝ) < γlo := by
    by_contra hcon
    have hle : γlo ≤ 0 := le_of_not_gt hcon
    have hprod : (0 : ℝ) ≤ (-γlo) * (σ i₀ : ℝ) := mul_nonneg (neg_nonneg.mpr hle) (hσpos i₀).le
    have hle2 : γlo * (σ i₀ : ℝ) ≤ 0 := by nlinarith [hprod]
    rw [heq₀] at hle2
    exact absurd hπ₀' (not_lt.mpr hle2)
  have hstrictpi₀ : ∀ x : ℝ, γlo < x → (π i₀ : ℝ) < x * (σ i₀ : ℝ) := by
    intro x hx
    have h : γlo * (σ i₀ : ℝ) < x * (σ i₀ : ℝ) := mul_lt_mul_of_pos_right hx (hσpos i₀)
    linarith [heq₀]
  have hroom : ∀ x : ℝ, x < γhi → x * (σ i₁ : ℝ) < (π i₁ : ℝ) := by
    intro x hx
    have h1 : x * (σ i₁ : ℝ) < γhi * (σ i₁ : ℝ) := mul_lt_mul_of_pos_right hx (hσpos i₁)
    rwa [← heq₁] at h1
  have hBpos_of : ∀ x : ℝ, γlo ≤ x → (0 : ℝ) < levelMass π σ x := by
    intro x hx
    have hmono : levelFill π σ γlo i₀ ≤ levelFill π σ x i₀ :=
      levelFill_mono π σ hσ hx i₀
    rw [show levelFill π σ γlo i₀ = (π i₀ : ℝ) from min_eq_left heq₀.symm.le] at hmono
    exact Finset.sum_pos' (f := fun i => (levelFill π σ x i) ^ 2)
      (fun _ _ => sq_nonneg _) ⟨i₀, Finset.mem_univ i₀, by nlinarith⟩
  by_cases hx : γlo < a
  · exact fidelity_anti_lt_core π σ hπ hσ ha hab ⟨i₀, hπ₀', hstrictpi₀ a hx⟩
      ⟨i₁, hroom a (hab.trans_le hbhi)⟩
  · have hae : a = γlo := le_antisymm (le_of_not_gt hx) haglo
    subst hae
    have hmid : (0 : ℝ) < (a + b) / 2 := by linarith
    have hcore := fidelity_anti_lt_core π σ hπ hσ hmid
      (show (a + b) / 2 < b by linarith)
      ⟨i₀, hπ₀', hstrictpi₀ _ (show a < (a + b) / 2 by linarith)⟩
      ⟨i₁, hroom ((a + b) / 2) (by linarith : (a + b) / 2 < γhi)⟩
    have hweak := fidelity_anti_le π σ hπ hσ hγlo (show a ≤ (a + b) / 2 by linarith)
    have hB1 := hBpos_of a le_rfl
    have hB2 := hBpos_of ((a + b) / 2) (by linarith)
    have hB3 := hBpos_of b (by linarith)
    nlinarith [hcore, hweak, hB1, hB2, hB3]

end FidelityHelpers

end Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity
