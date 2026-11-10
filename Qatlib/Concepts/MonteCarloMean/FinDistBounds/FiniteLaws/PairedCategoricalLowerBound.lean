/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteAssouad
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.PairedCategoricalLowerBound
open FiniteInformationDivergence FiniteAssouad
open scoped BigOperators Classical
noncomputable section

def pairedLaw (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (theta : Cube m) : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin m × Bool) where
  prob x := (if x.2=theta x.1 then 1+a else 1-a)/(2*(m : ℝ))
  nonneg x := by
    have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    split_ifs <;> positivity
  sum_one := by
    have hmR : (m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
    have hb (i : Fin m) :
        (∑ b : Bool, (if b=theta i then 1+a else 1-a)/(2*(m : ℝ))) = (m : ℝ)⁻¹ := by
      rcases Bool.eq_false_or_eq_true (theta i) with ht | ht <;> simp [ht] <;> field_simp <;> ring
    simp only [Fintype.sum_prod_type, hb, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hmR

theorem paired_positive (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (theta : Cube m) (x : Fin m × Bool) : 0 < (pairedLaw m hm a ha ha1 theta).prob x := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  dsimp [pairedLaw]
  split_ifs <;> positivity

theorem neighbor_kl (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (theta : Cube m) (i : Fin m) :
    kl (pairedLaw m hm a ha ha1 theta) (pairedLaw m hm a ha ha1 (flipAt i theta)) =
      a/(m : ℝ)*(Real.log (1+a)-Real.log (1-a)) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have h1 : Real.log ((1+a)/(2*(m : ℝ))) = Real.log (1+a)-Real.log (2*(m : ℝ)) :=
    Real.log_div (by positivity) (by positivity)
  have h2 : Real.log ((1-a)/(2*(m : ℝ))) = Real.log (1-a)-Real.log (2*(m : ℝ)) :=
    Real.log_div (ne_of_gt (sub_pos.mpr ha1)) (by positivity)
  unfold kl
  simp only [pairedLaw, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp only [flipAt_self]
    rcases Bool.eq_false_or_eq_true (theta i) with ht | ht <;> simp [ht, h1, h2] <;> ring
  · intro j _ hji
    have hf : flipAt i theta j = theta j := by simp [flipAt, hji]
    simp only [hf, sub_self, mul_zero, Finset.sum_const_zero]
  · simp

theorem neighbor_kl_bound (m : ℕ) (hm : 0 < m) (a : ℝ)
    (ha : 0 < a) (ha2 : a ≤ 1/2) (theta : Cube m) (i : Fin m) :
    kl (pairedLaw m hm a ha (by linarith) theta)
      (pairedLaw m hm a ha (by linarith) (flipAt i theta)) ≤ 4*a^2/(m : ℝ) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have ha1 : a < 1 := by linarith
  have hl := Real.log_le_sub_one_of_pos
    (div_pos (by linarith : 0 < 1+a) (sub_pos.mpr ha1))
  rw [Real.log_div (by positivity) (ne_of_gt (sub_pos.mpr ha1))] at hl
  have hr : (1+a)/(1-a) ≤ 1+4*a := by
    apply (div_le_iff₀ (sub_pos.mpr ha1)).mpr
    nlinarith
  have hg : Real.log (1+a)-Real.log (1-a) ≤ 4*a := by linarith
  rw [neighbor_kl]
  calc
    _ ≤ a/(m : ℝ)*(4*a) := mul_le_mul_of_nonneg_left hg (by positivity)
    _ = 4*a^2/(m : ℝ) := by ring

end
end Qatlib.Concepts.MonteCarloMean.FinDistBounds.PairedCategoricalLowerBound
