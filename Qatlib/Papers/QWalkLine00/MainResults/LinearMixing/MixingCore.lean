/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Finite-set overlap estimates for mixing

This module proves finite-set inequalities that turn lower bounds on mass at many sites into
bounds on total variation from uniform. A cardinality estimate for a distinguished subset
supplies the height-and-mass criterion used in the line-walk mixing analysis of
[NayakVishwanath2000].

## Main statements

* `mixing_core`: bounds variation by `1 - β * c` from a subset of relative size at least `β`.
* `good_card_lower`: bounds the distinguished subset cardinality from a mass and height
  estimate.
* `mixing_of_height_mass`: combines these estimates into a conditional mixing bound.

## References

* [Nayak and Vishwanath, 2000][NayakVishwanath2000]
-/

namespace Qatlib.Papers.QWalkLine00.MainResults

set_option autoImplicit false

open Finset
open scoped BigOperators

/-- For a probability function on a nonempty finite set, a subset of relative size at least `β`
whose masses are at least `c / card s` bounds total variation from uniform by `1 - β * c`,
with `β ≥ 0` and `0 ≤ c ≤ 1`. See [NayakVishwanath2000]. -/
theorem mixing_core {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) (hcard : 0 < s.card)
    (hp_nonneg : ∀ i ∈ s, 0 ≤ p i) (hp_sum : ∑ i ∈ s, p i = 1)
    {β c : ℝ} (hβ : 0 ≤ β) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (G : Finset ι) (hGsub : ∀ i ∈ G, i ∈ s)
    (hGcard : β * (s.card : ℝ) ≤ (G.card : ℝ))
    (hmass : ∀ i ∈ G, c / (s.card : ℝ) ≤ p i) :
    (1 / 2) * ∑ i ∈ s, |p i - 1 / (s.card : ℝ)| ≤ 1 - β * c := by
  have hpos : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hcard
  have hne : (s.card : ℝ) ≠ 0 := ne_of_gt hpos

  have hpoint : ∀ i ∈ s, |p i - 1 / (s.card : ℝ)|
      = p i + 1 / (s.card : ℝ) - 2 * min (p i) (1 / (s.card : ℝ)) := by
    intro i _
    rcases le_total (p i) (1 / (s.card : ℝ)) with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  have hsumu : (∑ i ∈ s, (1 / (s.card : ℝ) : ℝ)) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp

  have hsumabs : (∑ i ∈ s, |p i - 1 / (s.card : ℝ)|)
      = 2 - 2 * ∑ i ∈ s, min (p i) (1 / (s.card : ℝ)) := by
    rw [Finset.sum_congr rfl hpoint]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [show (∑ i ∈ s, 2 * min (p i) (1 / (s.card : ℝ)))
          = 2 * ∑ i ∈ s, min (p i) (1 / (s.card : ℝ)) from
        (Finset.mul_sum s (fun i => min (p i) (1 / (s.card : ℝ))) 2).symm]
    rw [hp_sum, hsumu]
    ring

  have hGsum : (∑ i ∈ G, (c / (s.card : ℝ))) = (G.card : ℝ) * (c / (s.card : ℝ)) := by
    rw [Finset.sum_const, nsmul_eq_mul]

  have hGmin : (∑ i ∈ G, (c / (s.card : ℝ)))
      ≤ ∑ i ∈ G, min (p i) (1 / (s.card : ℝ)) := by
    apply Finset.sum_le_sum
    intro i hi
    apply le_min
    · exact hmass i hi
    · exact (div_le_div_iff_of_pos_right hpos).2 hc1

  have hmono : (∑ i ∈ G, min (p i) (1 / (s.card : ℝ)))
      ≤ ∑ i ∈ s, min (p i) (1 / (s.card : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi; exact hGsub i hi
    · intro i hi_s _hiG
      exact le_min (hp_nonneg i hi_s) (by positivity)

  have hbeta : β * c ≤ (G.card : ℝ) * (c / (s.card : ℝ)) := by
    have hcN : β * c = ((β * (s.card : ℝ)) * c) / (s.card : ℝ) := by
      field_simp
    rw [hcN]
    have hrr : (G.card : ℝ) * (c / (s.card : ℝ)) = (G.card : ℝ) * c / (s.card : ℝ) := by ring
    rw [hrr]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hGcard hc) (le_of_lt hpos)
  have hGbound : β * c ≤ ∑ i ∈ s, min (p i) (1 / (s.card : ℝ)) := by
    rw [← hGsum] at hbeta
    exact le_trans hbeta (le_trans hGmin hmono)
  rw [hsumabs]
  have : (1 / 2 : ℝ) * (2 - 2 * ∑ i ∈ s, min (p i) (1 / (s.card : ℝ)))
      = 1 - ∑ i ∈ s, min (p i) (1 / (s.card : ℝ)) := by ring
  rw [this]
  linarith

/-- If the total mass is at least `M`, all values are at most `U`, and values outside `G` are at
most `c / card s`, then `card G ≥ (M - c) / (U - c / card s)` when the denominator is
positive. See [NayakVishwanath2000]. -/
theorem good_card_lower {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) (hcard : 0 < s.card)
    {U c M : ℝ} (hU : ∀ i ∈ s, p i ≤ U)
    (G : Finset ι) (hGsub : ∀ i ∈ G, i ∈ s)
    (hGlo : ∀ i ∈ s, i ∉ G → p i ≤ c / (s.card : ℝ))
    (hmass : M ≤ ∑ i ∈ s, p i)
    (hden : 0 < U - c / (s.card : ℝ)) :
    (M - c) / (U - c / (s.card : ℝ)) ≤ (G.card : ℝ) := by
  set N : ℝ := (s.card : ℝ) with hNdef
  have hNpos : 0 < N := by rw [hNdef]; exact_mod_cast hcard
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hNc : N * (c / N) = c := by field_simp

  have hsplit := Finset.sum_sdiff (f := p) (s₁ := G) (s₂ := s) hGsub
  have hGle : (∑ i ∈ G, p i) ≤ (G.card : ℝ) * U := by
    have h := Finset.sum_le_card_nsmul G p U (fun i hi => hU i (hGsub i hi))
    simpa [nsmul_eq_mul, mul_comm] using h
  have hCle : (∑ i ∈ s \ G, p i) ≤ ((s \ G).card : ℝ) * (c / N) := by
    have h := Finset.sum_le_card_nsmul (s \ G) p (c / N) (fun i hi => by
      exact hGlo i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hi).2)
    simpa [nsmul_eq_mul, mul_comm] using h
  have hCcard : ((s \ G).card : ℝ) = N - (G.card : ℝ) := by
    have h1 : (s \ G).card = s.card - G.card := by
      rw [Finset.card_sdiff]
      rw [Finset.inter_eq_left.mpr hGsub]
    rw [h1, hNdef]
    exact_mod_cast (Nat.cast_sub (Finset.card_le_card hGsub))
  have htot : (∑ i ∈ s, p i) ≤ (G.card : ℝ) * U + (N - (G.card : ℝ)) * (c / N) := by
    calc (∑ i ∈ s, p i) = (∑ i ∈ s \ G, p i) + ∑ i ∈ G, p i := by linarith [hsplit]
      _ ≤ ((s \ G).card : ℝ) * (c / N) + (G.card : ℝ) * U := by linarith [hCle, hGle]
      _ = (G.card : ℝ) * U + (N - (G.card : ℝ)) * (c / N) := by rw [hCcard]; ring
  have hkey : M - c ≤ (G.card : ℝ) * (U - c / N) := by
    have := le_trans hmass htot
    nlinarith [this, hNc]
  rw [hNdef] at hden ⊢
  rw [div_le_iff₀ hden]
  linarith [hkey]

/-- Under the stated probability, height, and subset mass hypotheses, total variation from
uniform is at most `1 - ((M - c) / (1 - c)) * c`. See [NayakVishwanath2000]. -/
theorem mixing_of_height_mass {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) (hcard : 0 < s.card)
    (hp_nonneg : ∀ i ∈ s, 0 ≤ p i) (hp_sum : ∑ i ∈ s, p i = 1)
    {c M : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) (hMc : c ≤ M)
    (hheight : ∀ i ∈ s, p i ≤ 1 / (s.card : ℝ))
    (G : Finset ι) (hGsub : ∀ i ∈ G, i ∈ s)
    (hGmass : ∀ i ∈ G, c / (s.card : ℝ) ≤ p i)
    (hGlo : ∀ i ∈ s, i ∉ G → p i ≤ c / (s.card : ℝ))
    (hmassG : M ≤ ∑ i ∈ G, p i) :
    (1 / 2) * ∑ i ∈ s, |p i - 1 / (s.card : ℝ)|
      ≤ 1 - ((M - c) / (1 - c)) * c := by
  have hNpos : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hcard
  have hNne : (s.card : ℝ) ≠ 0 := ne_of_gt hNpos
  have hMsum : M ≤ ∑ i ∈ s, p i :=
    le_trans hmassG (Finset.sum_le_sum_of_subset_of_nonneg hGsub
      (fun i hi _ => hp_nonneg i hi))
  have hUc : (1 / (s.card : ℝ) - c / (s.card : ℝ)) = (1 - c) / (s.card : ℝ) := by ring
  have hdenpos : (0 : ℝ) < (1 - c) / (s.card : ℝ) := div_pos (by linarith) hNpos
  have hcount := good_card_lower s p hcard (fun i hi => hheight i hi) G hGsub hGlo hMsum
    (by rw [hUc]; exact hdenpos)
  rw [hUc] at hcount

  have hbetaN : ((M - c) / (1 - c)) * (s.card : ℝ) ≤ (G.card : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0:ℝ) < 1 - c)]
    rw [div_le_iff₀ hdenpos] at hcount
    have hmul := mul_le_mul_of_nonneg_right hcount hNpos.le
    have h3 : ((G.card : ℝ) * ((1 - c) / (s.card : ℝ))) * (s.card : ℝ)
        = (G.card : ℝ) * (1 - c) := by
      field_simp
    nlinarith [hmul, h3]
  have hβ0 : (0 : ℝ) ≤ (M - c) / (1 - c) := div_nonneg (by linarith) (by linarith)
  exact mixing_core s p hcard hp_nonneg hp_sum hβ0 hc (le_of_lt hc1) G hGsub hbetaN hGmass

end Qatlib.Papers.QWalkLine00.MainResults
