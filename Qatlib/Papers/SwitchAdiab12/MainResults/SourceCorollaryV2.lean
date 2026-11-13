/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Qatlib.Papers.SwitchAdiab12.MainResults.SourceLemmaV1

set_option backward.isDefEq.respectTransparency false

/-!
# Gevrey Factorial-Power Convolution Bound (Corollary V.2)

This module formalizes Corollary V.2: for `α ≥ 1`, `n ≥ 1`, and `1 ≤ i ≤ n`, the
binomial-weighted Gevrey product `(k! / (k₁! k₂!)) (k₁ + n + 1 - i)^{α(k₁ + n + 1 - i)}
(k₂ + i)^{α(k₂ + i)}` is bounded by `4^{-(α - 1) min(k₁ + 1, k₂ + 1)} (k + n + 1)^{α(k + n + 1)}`.

## Main statements

* `source_corollary_V2`: Gevrey binomial-product estimate uniformly over
  intermediate indices `1 ≤ i ≤ n`.

## References

* [Elgart and Hagedorn, 2012][ElgartHagedorn2012SwitchAdiab], Appendix V,
  Corollary V.2, Eq. (V.6), p. 16.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SwitchAdiab12.MainResults.SourceCorollaryV2

/-- Moving mass from the smaller positive argument to the larger increases the product. -/
private lemma product_monotone (α a b : ℝ) (hα : 1 ≤ α) (hb : 1 ≤ b) (hba : b ≤ a) :
    MonotoneOn (fun t : ℝ ↦ (a + t) ^ (α * (a + t)) *
      (b - t) ^ (α * (b - t))) (Set.Icc 0 (b - 1)) := by
  let h := fun t : ℝ ↦ (a + t) * Real.log (a + t) + (b - t) * Real.log (b - t)
  have hpos (t : ℝ) (ht : t ∈ Set.Icc 0 (b - 1)) : 0 < a + t ∧ 0 < b - t := by
    constructor <;> linarith [ht.1, ht.2]
  have hd (t : ℝ) (ht : t ∈ Set.Icc 0 (b - 1)) :
      HasDerivAt h (Real.log (a + t) - Real.log (b - t)) t := by
    have ha := (hasDerivAt_const t a).add (hasDerivAt_id t)
    have hb' := (hasDerivAt_const t b).sub (hasDerivAt_id t)
    convert (ha.mul (ha.log (hpos t ht).1.ne')).add
      (hb'.mul (hb'.log (hpos t ht).2.ne')) using 1
    · rfl
    · dsimp
      field_simp [(hpos t ht).1.ne', (hpos t ht).2.ne']
      ring
  have hm : MonotoneOn h (Set.Icc 0 (b - 1)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := interior_subset ht
      rw [(hd t ht').deriv]
      exact sub_nonneg.mpr (Real.log_le_log (hpos t ht').2 (by linarith [ht'.1]))
  have he (t : ℝ) (ht : t ∈ Set.Icc 0 (b - 1)) :
      (a + t) ^ (α * (a + t)) * (b - t) ^ (α * (b - t)) = Real.exp (α * h t) := by
    rw [Real.rpow_def_of_pos (hpos t ht).1, Real.rpow_def_of_pos (hpos t ht).2,
      ← Real.exp_add]
    congr 1
    dsimp [h]
    ring
  intro x hx y hy hxy
  dsimp only
  rw [he x hx, he y hy]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hm hx hy hxy) (by linarith))

/-- The endpoint estimate when the second argument is the smaller one. -/
private lemma ordered_bound (α : ℝ) (hα : 1 ≤ α) (k₁ k₂ n : ℕ) (hn : 1 ≤ n)
    (i : ℕ) (hi : 1 ≤ i) (horder : k₂ + i ≤ k₁ + n + 1 - i) :
    (Nat.factorial (k₁ + k₂) : ℝ) /
        ((Nat.factorial k₁ : ℝ) * (Nat.factorial k₂ : ℝ)) *
      ((k₁ + n + 1 - i : ℕ) : ℝ) ^ (α * ((k₁ + n + 1 - i : ℕ) : ℝ)) *
      ((k₂ + i : ℕ) : ℝ) ^ (α * ((k₂ + i : ℕ) : ℝ))
    ≤ (4 : ℝ) ^ (-(α - 1) * ((min (k₁ + 1) (k₂ + 1) : ℕ) : ℝ)) *
      ((k₁ + k₂ + n + 1 : ℕ) : ℝ) ^ (α * ((k₁ + k₂ + n + 1 : ℕ) : ℝ)) := by
  have hsum : k₁ + n + 1 - i + (i - 1) = k₁ + n := by omega
  have hsub : k₂ + i - (i - 1) = k₂ + 1 := by omega
  have hprod := product_monotone α ((k₁ + n + 1 - i : ℕ) : ℝ) ((k₂ + i : ℕ) : ℝ) hα
    (by exact_mod_cast (show 1 ≤ k₂ + i by omega)) (by exact_mod_cast horder)
    (show (0 : ℝ) ∈ Set.Icc 0 (((k₂ + i : ℕ) : ℝ) - 1) by
      constructor
      · rfl
      · have : (1 : ℝ) ≤ ((k₂ + i : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k₂ + i by omega)
        linarith)
    (show ((i - 1 : ℕ) : ℝ) ∈ Set.Icc 0 (((k₂ + i : ℕ) : ℝ) - 1) by
      constructor
      · positivity
      · have : (i - 1 : ℕ) + 1 ≤ k₂ + i := by omega
        have hh : ((i - 1 : ℕ) : ℝ) + 1 ≤ ((k₂ + i : ℕ) : ℝ) := by exact_mod_cast this
        linarith)
    (by positivity : (0 : ℝ) ≤ ((i - 1 : ℕ) : ℝ))
  have headd : ((k₁ + n + 1 - i : ℕ) : ℝ) + ((i - 1 : ℕ) : ℝ) = (k₁ + n : ℕ) := by
    exact_mod_cast hsum
  have hesub : ((k₂ + i : ℕ) : ℝ) - ((i - 1 : ℕ) : ℝ) = (k₂ + 1 : ℕ) := by
    rw [← Nat.cast_sub (by omega), hsub]
  simp only [add_zero, sub_zero, headd, hesub] at hprod
  have hc : (Nat.factorial (k₁ + k₂) : ℝ) /
      ((Nat.factorial k₁ : ℝ) * (Nat.factorial k₂ : ℝ)) ≤
      (Nat.factorial (k₁ + (k₂ + 1)) : ℝ) /
      ((Nat.factorial k₁ : ℝ) * (Nat.factorial (k₂ + 1) : ℝ)) := by
    rw [← Nat.cast_add_choose, ← Nat.cast_add_choose]
    exact_mod_cast Nat.choose_le_succ (k₁ + k₂) k₁
  have hm : min (k₁ + 1) (k₂ + 1) ≤ min (k₁ + n) (k₂ + 1) :=
    min_le_min (by omega) le_rfl
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
    (mul_le_mul_of_nonpos_left (show ((min (k₁ + 1) (k₂ + 1) : ℕ) : ℝ) ≤
      ((min (k₁ + n) (k₂ + 1) : ℕ) : ℝ) by exact_mod_cast hm) (by linarith : -(α - 1) ≤ 0))
  calc
    _ = ((Nat.factorial (k₁ + k₂) : ℝ) /
        ((Nat.factorial k₁ : ℝ) * (Nat.factorial k₂ : ℝ))) *
        (((k₁ + n + 1 - i : ℕ) : ℝ) ^ (α * ((k₁ + n + 1 - i : ℕ) : ℝ)) *
        ((k₂ + i : ℕ) : ℝ) ^ (α * ((k₂ + i : ℕ) : ℝ))) := by ring
    _ ≤ ((Nat.factorial (k₁ + (k₂ + 1)) : ℝ) /
        ((Nat.factorial k₁ : ℝ) * (Nat.factorial (k₂ + 1) : ℝ))) *
        (((k₁ + n : ℕ) : ℝ) ^ (α * ((k₁ + n : ℕ) : ℝ)) *
        ((k₂ + 1 : ℕ) : ℝ) ^ (α * ((k₂ + 1 : ℕ) : ℝ))) :=
      mul_le_mul hc hprod (by positivity) (by positivity)
    _ ≤ (4 : ℝ) ^ (-(α - 1) * ((min (k₁ + n) (k₂ + 1) : ℕ) : ℝ)) *
        ((k₁ + k₂ + n + 1 : ℕ) : ℝ) ^ (α * ((k₁ + k₂ + n + 1 : ℕ) : ℝ)) := by
      simpa only [mul_assoc, show k₁ + (k₂ + 1) + n = k₁ + k₂ + n + 1 by omega]
        using SourceLemmaV1.lemma_V1 α hα k₁ (k₂ + 1) n hn
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (by positivity)

/-- **Corollary V.2**: uniform Gevrey factorial-power bound across `1 ≤ i ≤ n`,
deduced from Lemma V.1 via convexity/monotonicity of `x ↦ x^{α x}`. -/
theorem source_corollary_V2 (α : ℝ) (hα : 1 ≤ α) (k₁ k₂ n : ℕ) (hn : 1 ≤ n)
    (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    (Nat.factorial (k₁ + k₂) : ℝ) /
        ((Nat.factorial k₁ : ℝ) * (Nat.factorial k₂ : ℝ)) *
      ((k₁ + n + 1 - i : ℕ) : ℝ) ^ (α * ((k₁ + n + 1 - i : ℕ) : ℝ)) *
      ((k₂ + i : ℕ) : ℝ) ^ (α * ((k₂ + i : ℕ) : ℝ))
    ≤ (4 : ℝ) ^ (-(α - 1) * ((min (k₁ + 1) (k₂ + 1) : ℕ) : ℝ)) *
      ((k₁ + k₂ + n + 1 : ℕ) : ℝ) ^
        (α * ((k₁ + k₂ + n + 1 : ℕ) : ℝ)) := by
  rcases le_total (k₂ + i) (k₁ + n + 1 - i) with h | h
  · exact ordered_bound α hα k₁ k₂ n hn i hi h
  · have hi' : 1 ≤ n + 1 - i := by omega
    have he : k₂ + n + 1 - (n + 1 - i) = k₂ + i := by omega
    have he' : k₁ + (n + 1 - i) = k₁ + n + 1 - i := by omega
    have hh := ordered_bound α hα k₂ k₁ n hn (n + 1 - i) hi'
      (by omega)
    simpa only [he, he', Nat.add_comm k₂ k₁, min_comm (k₂ + 1), mul_comm,
      mul_left_comm, mul_assoc] using hh

end Qatlib.Papers.SwitchAdiab12.MainResults.SourceCorollaryV2

#lint only unusedArguments
