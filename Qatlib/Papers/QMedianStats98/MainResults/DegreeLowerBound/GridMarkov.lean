/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact

/-!
# Markov bounds on the rescaled weight grid

This module develops the evenly spaced grid `sourceGrid n k = 2*k/n - 1` used in the proof of
Lemma 2.1 of [NayakWu1998]. It records interval membership, proximity to arbitrary points, and
the exact distance between two weight nodes.

A sharp Markov derivative bound gives a Lipschitz estimate on `[-1, 1]`. Combining it with grid
boundedness and a value gap yields the squared first-term lower bound on degree.

## Main statements

- `sourceGrid_near`: finds a grid point within `2/n` of every point of `[-1, 1]`.
- `source_markov_lipschitz`: bounds polynomial variation by `d² * C` times distance.
- `source_grid_first_term_sq`: converts grid separation into a lower bound on `d²`.

## References

[Nayak and Wu, 1998][NayakWu1998]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound
open Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- The affine image `2*k/n - 1` of the integer weight `k` on the normalized weight grid. -/
def sourceGrid (n k : ℕ) : ℝ := 2 * (k : ℝ) / (n : ℝ) - 1

/-- For `n > 0` and `k ≤ n`, the normalized weight node `sourceGrid n k` lies in `[-1, 1]`. -/
theorem sourceGrid_mem {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    sourceGrid n k ∈ Set.Icc (-1 : ℝ) 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hb : 0 ≤ 2 * (k : ℝ) / n := by positivity
  have ht : 2 * (k : ℝ) / n ≤ 2 := (div_le_iff₀ hnR).mpr (by linarith)
  constructor <;> dsimp [sourceGrid] <;> linarith

/-- For `n > 0`, every point of `[-1, 1]` is within `2/n` of a node `sourceGrid n k` with `k ≤
n`. -/
theorem sourceGrid_near {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ k : ℕ, k ≤ n ∧ |x - sourceGrid n k| ≤ 2 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let t : ℝ := (x+1) * n / 2
  have hx0 : 0 ≤ x+1 := by linarith [hx.1]
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htn : t ≤ n := by dsimp [t]; nlinarith [hx.2]
  let k := ⌊t⌋₊
  have hk : k ≤ n := Nat.floor_le_of_le htn
  have hkl : (k : ℝ) ≤ t := Nat.floor_le ht0
  have hkr : t < (k : ℝ) + 1 := Nat.lt_floor_add_one t
  refine ⟨k,hk,?_⟩
  have hl : sourceGrid n k ≤ x := by
    dsimp [sourceGrid]
    rw [sub_le_iff_le_add, div_le_iff₀ hnR]
    dsimp [t] at hkl
    nlinarith
  have he : x-sourceGrid n k = 2*(t-(k : ℝ))/n := by
    dsimp [sourceGrid,t]
    field_simp
    ring
  rw [abs_of_nonneg (sub_nonneg.mpr hl),he]
  exact (div_le_div_iff_of_pos_right hnR).mpr (by linarith)

/-- A polynomial of degree at most `d` bounded in absolute value by `C ≥ 0` on `[-1, 1]`
satisfies `|q(x) - q(y)| ≤ d² * C * |x - y|` for any two points of the interval. -/
theorem source_markov_lipschitz (d : ℕ) (q : Polynomial ℝ) (C : ℝ)
    (hd : q.natDegree ≤ d) (hC : 0 ≤ C)
    (hb : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |q.eval z| ≤ C)
    (x y : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    |q.eval x-q.eval y| ≤ (d : ℝ)^2*C*|x-y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun z : ℝ => q.eval z)
    (fun z _ => q.differentiableAt)
    (fun z hz => by
      rw [(q.hasDerivAt z).deriv,Real.norm_eq_abs]
      exact sharp_markov_derivative d q C hd hC hb z hz)
    (convex_Icc (-1 : ℝ) 1) hy hx
  simpa only [Real.norm_eq_abs] using h

/-- Casting the natural-number distance between `lo` and `hi` to the reals gives `|(lo : ℝ) -
(hi : ℝ)|`. -/
theorem source_weight_gap_cast (lo hi : ℕ) :
    (Nat.dist lo hi : ℝ) = |(lo : ℝ)-(hi : ℝ)| := by
  rcases le_total lo hi with h | h
  · have hr : (lo : ℝ) ≤ hi := by exact_mod_cast h
    rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr hr)]
    ring
  · have hr : (hi : ℝ) ≤ lo := by exact_mod_cast h
    rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr hr)]

/-- For `n > 0`, the distance between normalized weight nodes `lo` and `hi` is `2 * dist(lo, hi)
/ n`. -/
theorem sourceGrid_distance {n : ℕ} (hn : 0 < n) (lo hi : ℕ) :
    |sourceGrid n lo-sourceGrid n hi| = 2*(Nat.dist lo hi : ℝ)/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : sourceGrid n lo-sourceGrid n hi = (2/(n : ℝ))*((lo : ℝ)-(hi : ℝ)) := by
    dsimp [sourceGrid]
    ring
  rw [he,abs_mul,abs_of_pos (div_pos (by norm_num) hnR),← source_weight_gap_cast]
  ring

/-- If a polynomial of degree at most `d` is bounded by `3/2` on the normalized weight grid and
has value separation at least `gap ≤ 1` at distinct valid weights, then `gap * n / (8 *
dist(lo, hi)) ≤ d²`. This is the grid estimate for the first degree term in [NayakWu1998]. -/
theorem source_grid_first_term_sq {n lo hi : ℕ} (hn : 0 < n)
    (hl : lo ≤ n) (hh : hi ≤ n) (hne : lo ≠ hi)
    (d : ℕ) (q : Polynomial ℝ) (hd : q.natDegree ≤ d)
    (hgrid : ∀ k : ℕ, k ≤ n → |q.eval (sourceGrid n k)| ≤ 3/2)
    (gap : ℝ) (hgap : gap ≤ 1)
    (hsep : gap ≤ |q.eval (sourceGrid n lo)-q.eval (sourceGrid n hi)|) :
    gap*(n : ℝ)/(8*(Nat.dist lo hi : ℝ)) ≤ (d : ℝ)^2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdelta : (0 : ℝ) < (Nat.dist lo hi : ℝ) := by
    exact_mod_cast Nat.dist_pos_of_ne hne
  have hdelta1 : (1 : ℝ) ≤ (Nat.dist lo hi : ℝ) := by
    exact_mod_cast Nat.dist_pos_of_ne hne
  obtain ⟨z,hz,hmax⟩ := (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).exists_isMaxOn
    ⟨0,by norm_num⟩ q.continuous.abs.continuousOn
  let C := |q.eval z|
  have hC0 : 0 ≤ C := abs_nonneg _
  have hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |q.eval x| ≤ C := fun x hx => hmax hx
  apply (div_le_iff₀ (by positivity : 0 < 8*(Nat.dist lo hi : ℝ))).mpr
  by_cases hlow : C < 2
  · have hle := source_markov_lipschitz d q C hd hC0 hb
      (sourceGrid n lo) (sourceGrid n hi) (sourceGrid_mem hn hl) (sourceGrid_mem hn hh)
    rw [sourceGrid_distance hn lo hi] at hle
    have hs : gap ≤ (2*(d : ℝ)^2*C*(Nat.dist lo hi : ℝ))/(n : ℝ) := by
      calc gap ≤ _ := hsep.trans hle
        _ = _ := by ring
    have hp := (le_div_iff₀ hnR).mp hs
    have hscale : 2*(d : ℝ)^2*C*(Nat.dist lo hi : ℝ) ≤ 4*(d : ℝ)^2*(Nat.dist lo hi : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hlow.le (sq_nonneg (d : ℝ))
      calc _ = (2*(Nat.dist lo hi : ℝ))*((d : ℝ)^2*C) := by ring
        _ ≤ (2*(Nat.dist lo hi : ℝ))*((d : ℝ)^2*2) :=
          mul_le_mul_of_nonneg_left h (by positivity)
        _ = _ := by ring
    have hnonneg := mul_nonneg (sq_nonneg (d : ℝ)) hdelta.le
    nlinarith [hp.trans hscale]
  · have hhigh : 2 ≤ C := le_of_not_gt hlow
    have hCpos : 0 < C := by linarith
    obtain ⟨k,hk,hnear⟩ := sourceGrid_near hn hz
    have hle := source_markov_lipschitz d q C hd hC0 hb z (sourceGrid n k) hz (sourceGrid_mem hn hk)
    have hle' : |q.eval z-q.eval (sourceGrid n k)| ≤ (d : ℝ)^2*C*(2/(n : ℝ)) :=
      hle.trans (mul_le_mul_of_nonneg_left hnear (by positivity))
    have htri : C ≤ |q.eval (sourceGrid n k)|+|q.eval z-q.eval (sourceGrid n k)| := by
      calc C = |q.eval (sourceGrid n k)+(q.eval z-q.eval (sourceGrid n k))| := by
              dsimp [C]; congr 1; ring
        _ ≤ _ := abs_add_le _ _
    have hs : C-3/2 ≤ (2*(d : ℝ)^2*C)/(n : ℝ) := by
      have hg := hgrid k hk
      have he : (d : ℝ)^2*C*(2/(n : ℝ)) = (2*(d : ℝ)^2*C)/(n : ℝ) := by ring
      rw [he] at hle'
      linarith
    have hp := (le_div_iff₀ hnR).mp hs
    have hcquarter : C/4 ≤ C-3/2 := by linarith
    have hquarter := mul_le_mul_of_nonneg_right hcquarter hnR.le
    have hprod : (n : ℝ)*C ≤ (8*(d : ℝ)^2)*C := by nlinarith
    have hn8 : (n : ℝ) ≤ 8*(d : ℝ)^2 := (mul_le_mul_iff_left₀ hCpos).mp hprod
    have hgn : gap*(n : ℝ) ≤ n := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hgap hnR.le
    have hlast : 8*(d : ℝ)^2 ≤ 8*(d : ℝ)^2*(Nat.dist lo hi : ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdelta1
        (by positivity : 0 ≤ 8*(d : ℝ)^2)
    nlinarith [hgn.trans (hn8.trans hlast)]

end Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound
