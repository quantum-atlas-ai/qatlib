/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Papers.ExpCongruence08.MainResults.SolutionCount
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Second moment of exponential congruence counts

The deviations from the mean over the additive group of the field form a real Euclidean
vector. This is the variance used in [VanDamShparlinski2008], Lemma 2.

* [van Dam and Shparlinski, 2008](https://arxiv.org/abs/0804.1109v1)
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical ComplexConjugate
open Qatlib.Papers.ExpCongruence08.MainResults

namespace Qatlib.Papers.ExpCongruence08.MainResults

variable {F : Type*} [Field F] [Fintype F]

/-- The centered count at every target, including zero, in the real Euclidean space indexed by
the field. Its center is the exact mean over all field targets. -/
def countDeviation (a b f g : Fˣ) (r : ℕ) : EuclideanSpace ℝ F :=
  WithLp.toLp 2 fun c => (numSolutionsAt a b c f g (orderOf f) r : ℝ) -
    (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ)

/-- The squared Euclidean norm is the unnormalized variance of the source count over the field. -/
theorem countDeviation_norm_sq (a b f g : Fˣ) (r : ℕ) :
    ‖countDeviation a b f g r‖ ^ 2 =
      ∑ c : F, ((numSolutionsAt a b c f g (orderOf f) r : ℝ) -
        (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-- Centering the count at `r * orderOf f / |F|` makes the sum of all coordinates zero. -/
theorem sum_countDeviation (a b f g : Fˣ) (r : ℕ) :
    (∑ c : F, countDeviation a b f g r c) = 0 := by
  change (∑ c : F, ((numSolutionsAt a b c f g (orderOf f) r : ℝ) -
    (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ))) = 0
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, sum_numSolutionsAt, Nat.cast_mul]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- An unnormalized additive Fourier coefficient, with the positive character convention. -/
private def additiveCoefficient (d : F → ℂ) (ψ : AddChar F ℂ) : ℂ :=
  ∑ c : F, d c * ψ c

/-- Parseval for the unnormalized transform over all complex additive characters of the field. -/
private theorem sum_sq_additiveCoefficient (d : F → ℂ) :
    ∑ ψ : AddChar F ℂ, ‖additiveCoefficient d ψ‖ ^ 2 =
      (Fintype.card F : ℝ) * ∑ c : F, ‖d c‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_conj_mul_self, additiveCoefficient, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  calc
    ∑ ψ : AddChar F ℂ, ∑ y : F, ∑ x : F, (conj (d x) * conj (ψ x)) * (d y * ψ y) =
        ∑ y : F, ∑ x : F, ∑ ψ : AddChar F ℂ,
          (conj (d x) * d y) * ψ (y - x) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun ψ _ => ?_
      rw [sub_eq_add_neg, ψ.map_add_eq_mul, ψ.map_neg_eq_inv, ψ.inv_apply_eq_conj]
      ring
    _ = _ := by
      simp only [← Finset.mul_sum, AddChar.sum_apply_eq_ite, sub_eq_zero]
      simp [eq_comm, mul_comm]
      rw [Finset.mul_sum]

/-- The additive character sum of an exponent segment with a nonzero coefficient. -/
private def segmentSum (a f : Fˣ) (r : ℕ) (ψ : AddChar F ℂ) : ℂ :=
  ∑ x ∈ Finset.range r, ψ ((a : F) * (f : F) ^ x)

omit [Fintype F] in
/-- The segment values are distinct when the length is at most the order of the base. -/
private theorem segment_injective (a f : Fˣ) (r : ℕ) (hr : r ≤ orderOf f) :
    Set.InjOn (fun x : ℕ => (a : F) * (f : F) ^ x) (Finset.range r : Set ℕ) := by
  intro i hi j hj hij
  apply pow_injOn_Iio_orderOf (x := f)
    (lt_of_lt_of_le (Finset.mem_range.mp hi) hr) (lt_of_lt_of_le (Finset.mem_range.mp hj) hr)
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val] using mul_left_cancel₀ a.ne_zero hij

/-- Parseval applied to the indicator of the exponent segment. -/
private theorem sum_sq_segmentSum (a f : Fˣ) (r : ℕ) (hr : r ≤ orderOf f) :
    ∑ ψ : AddChar F ℂ, ‖segmentSum a f r ψ‖ ^ 2 = (Fintype.card F : ℝ) * r := by
  classical
  let v : ℕ → F := fun x => (a : F) * (f : F) ^ x
  let S := (Finset.range r).image v
  have hS : S.card = r := by
    rw [Finset.card_image_of_injOn (segment_injective a f r hr), Finset.card_range]
  let d : F → ℂ := fun c => if c ∈ S then 1 else 0
  have hcoeff (ψ : AddChar F ℂ) : additiveCoefficient d ψ = segmentSum a f r ψ := by
    simp only [additiveCoefficient, d, ite_mul, one_mul, zero_mul, ← Finset.sum_filter,
      Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact Finset.sum_image (segment_injective a f r hr)
  have hd : (∑ c : F, ‖d c‖ ^ 2) = (r : ℝ) := by
    simp only [d, apply_ite norm, norm_one, norm_zero, ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0),
      ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, mul_one, hS]
  simpa only [hcoeff, hd] using sum_sq_additiveCoefficient d

/-- Multiplication by any power of `f` permutes one full exponent period. -/
private theorem segmentSum_mulShift (a f : Fˣ) (ψ : AddChar F ℂ) (k : ℕ) :
    segmentSum a f (orderOf f) (ψ.mulShift ((f : F) ^ k)) =
      segmentSum a f (orderOf f) ψ := by
  classical
  let h : Subgroup.zpowers f := ⟨f ^ k, ⟨(k : ℤ), by simp⟩⟩
  let e := finEquivZPowers (isOfFinOrder_of_finite f)
  let weight : Subgroup.zpowers f → ℂ := fun x => ψ ((a : F) * ((x : Fˣ) : F))
  rw [segmentSum, segmentSum, ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ x : Fin (orderOf f), weight (h * e x) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [weight, h, e, finEquivZPowers_apply, AddChar.mulShift_apply,
        Subgroup.coe_mul, Units.val_mul, Units.val_pow_eq_pow_val]
      rw [mul_left_comm]
    _ = ∑ x : Subgroup.zpowers f, weight (h * x) := e.sum_comp (fun x => weight (h * x))
    _ = ∑ x : Subgroup.zpowers f, weight x := Equiv.sum_comp (Equiv.mulLeft h) weight
    _ = _ := by
      rw [← e.sum_comp weight]
      simp [weight, e, finEquivZPowers_apply]

omit [Fintype F] in
/-- Multiplication by a distinct field scalar gives a distinct shift of a nontrivial character. -/
private theorem mulShift_injective (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    Function.Injective ψ.mulShift := by
  intro u v h
  by_contra huv
  have hzero : ψ.mulShift (u - v) = 1 := by
    have he := ψ.mulShift_mul (u - v) v
    rw [sub_add_cancel, h] at he
    exact mul_right_cancel (he.trans (one_mul _).symm)
  exact hψ ((ψ.mulShift_unit_eq_one_iff (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr huv))).mp hzero)

/-- The full multiplicative orbit has Fourier power at most `q - s` at each nontrivial
additive frequency. The orbit of that frequency contains `s` equal contributions to Parseval,
all distinct from the trivial frequency, whose power is `s²`. -/
private theorem segmentSum_period_sq_le (a f : Fˣ) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    ‖segmentSum a f (orderOf f) ψ‖ ^ 2 ≤ (Fintype.card F : ℝ) - (orderOf f : ℝ) := by
  classical
  let s := orderOf f
  let v : ℕ → AddChar F ℂ := fun k => ψ.mulShift ((f : F) ^ k)
  let S := (Finset.range s).image v
  let energy : AddChar F ℂ → ℝ := fun χ => ‖segmentSum a f s χ‖ ^ 2
  have hv : Set.InjOn v (Finset.range s : Set ℕ) := by
    intro i hi j hj he
    apply segment_injective (1 : Fˣ) f s le_rfl hi hj
    simpa using mulShift_injective ψ hψ he
  have hS : (1 : AddChar F ℂ) ∉ S := by
    rintro hm
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hm
    exact hψ ((ψ.mulShift_unit_eq_one_iff (isUnit_iff_ne_zero.mpr (pow_ne_zero _ f.ne_zero))).mp hk)
  have hsum : ∑ χ ∈ S, energy χ = (s : ℝ) * energy ψ := by
    rw [Finset.sum_image hv]
    simp [energy, v, s, segmentSum_mulShift, nsmul_eq_mul]
  have hone : energy 1 = (s : ℝ) ^ 2 := by
    simp [energy, segmentSum, nsmul_eq_mul]
  have hle : ∑ χ ∈ insert 1 S, energy χ ≤ ∑ χ : AddChar F ℂ, energy χ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  rw [Finset.sum_insert hS, hsum, hone, sum_sq_segmentSum a f s le_rfl] at hle
  have hs : (0 : ℝ) < (s : ℝ) := by exact_mod_cast orderOf_pos f
  apply le_of_mul_le_mul_left _ hs
  change (s : ℝ) * energy ψ ≤ _
  linarith only [hle, show (s : ℝ) * ((Fintype.card F : ℝ) - (s : ℝ)) =
    (Fintype.card F : ℝ) * (s : ℝ) - (s : ℝ) ^ 2 by ring]

/-- The Fourier coefficient of the box count is the product of the two segment sums. -/
private theorem additiveCoefficient_count (a b f g : Fˣ) (r : ℕ) (ψ : AddChar F ℂ) :
    additiveCoefficient (fun c => (numSolutionsAt a b c f g (orderOf f) r : ℂ)) ψ =
      segmentSum a f (orderOf f) ψ * segmentSum b g r ψ := by
  classical
  let S := (Finset.range (orderOf f)).product (Finset.range r)
  let v := solValue a b f g
  calc
    _ = ∑ p ∈ S, ψ (v p) := by
      rw [additiveCoefficient, ← Finset.sum_fiberwise_of_maps_to (g := v) (t := Finset.univ)
        (s := S) (fun _ _ => Finset.mem_univ _) (fun p => ψ (v p))]
      apply Finset.sum_congr rfl
      intro c _
      change ((S.filter fun p => v p = c).card : ℂ) * ψ c =
        ∑ p ∈ S.filter (fun p => v p = c), ψ (v p)
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Finset.mem_filter.mp hp).2]
    _ = ∑ y ∈ Finset.range r, ∑ x ∈ Finset.range (orderOf f), ψ (v (x, y)) :=
      Finset.sum_product_right (Finset.range (orderOf f)) (Finset.range r) (fun p => ψ (v p))
    _ = _ := by
      simp only [v, solValue, ψ.map_add_eq_mul, segmentSum,
        Finset.sum_mul, Finset.mul_sum]

/-- Centering removes the trivial frequency and preserves the other count coefficients. -/
private theorem additiveCoefficient_deviation (a b f g : Fˣ) (r : ℕ) (ψ : AddChar F ℂ) :
    additiveCoefficient (fun c => (countDeviation a b f g r c : ℂ)) ψ =
      if ψ = 1 then 0 else segmentSum a f (orderOf f) ψ * segmentSum b g r ψ := by
  classical
  by_cases h : ψ = 1
  · subst ψ
    simp only [ite_true, additiveCoefficient, AddChar.one_apply, mul_one, ← Complex.ofReal_sum]
    rw [sum_countDeviation, Complex.ofReal_zero]
  · rw [ite_eq_right h, ← additiveCoefficient_count]
    have hsum : ∑ c : F, ψ c = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr h
    change (∑ c : F, (((numSolutionsAt a b c f g (orderOf f) r : ℝ) -
      (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ) : ℝ) : ℂ) * ψ c) = _
    simp only [Complex.ofReal_sub, Complex.ofReal_natCast, sub_mul, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, hsum, mul_zero, sub_zero]
    rfl

/-- For every scan length `r ≤ orderOf g`, the full centered count has squared Euclidean
norm at most `(|F| - orderOf f) * r`. This strengthens the second-moment estimate used in
[VanDamShparlinski2008], Lemma 2. It uses additive character orthogonality and the multiplicative
symmetry of a complete first period. For an empty scan the count vector and the bound both
vanish. -/
theorem countDeviation_norm_sq_le (a b f g : Fˣ) (r : ℕ) (hr : r ≤ orderOf g) :
    ‖countDeviation a b f g r‖ ^ 2 ≤
      ((Fintype.card F : ℝ) - (orderOf f : ℝ)) * r := by
  classical
  let d := countDeviation a b f g r
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by positivity
  have hs : (orderOf f : ℝ) ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast (orderOf_le_card_sub_one f).trans (Nat.sub_le ..)
  have hparseval : ∑ ψ : AddChar F ℂ, ‖additiveCoefficient (fun c => (d c : ℂ)) ψ‖ ^ 2 =
      (Fintype.card F : ℝ) * ‖d‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      sum_sq_additiveCoefficient (fun c => (d c : ℂ))
  have henergy : ∑ ψ : AddChar F ℂ, ‖additiveCoefficient (fun c => (d c : ℂ)) ψ‖ ^ 2 ≤
      ((Fintype.card F : ℝ) - (orderOf f : ℝ)) * ((Fintype.card F : ℝ) * r) := by
    rw [← sum_sq_segmentSum b g r hr, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ψ _
    change ‖additiveCoefficient (fun c => (countDeviation a b f g r c : ℂ)) ψ‖ ^ 2 ≤ _
    rw [additiveCoefficient_deviation]
    split_ifs with h
    · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg _)
    · rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right (segmentSum_period_sq_le a f ψ h) (sq_nonneg _)
  rw [hparseval] at henergy
  apply le_of_mul_le_mul_left _ hq
  convert henergy using 1
  ring

/-- The sum over nonzero targets satisfies the second-moment premise of the public counting and
solvability lemmas. The bound follows by dropping the nonnegative term at zero. -/
theorem second_moment_units_le (a b f g : Fˣ) (r : ℕ) (hr : r ≤ orderOf g) :
    ∑ c : Fˣ, ((numSolutions a b c f g (orderOf f) r : ℝ) -
      (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ)) ^ 2 ≤
        (Fintype.card F : ℝ) * r := by
  classical
  let e : Fˣ ↪ F := ⟨Units.val, fun _ _ h => Units.ext h⟩
  let energy : F → ℝ := fun c => ((numSolutionsAt a b c f g (orderOf f) r : ℝ) -
    (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ)) ^ 2
  calc
    _ = ∑ c ∈ Finset.univ.map e, energy c := by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun c _ => ?_
      exact congrArg (fun n : ℕ => ((n : ℝ) -
        (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ)) ^ 2)
        (numSolutions_eq_numSolutionsAt a b c f g (orderOf f) r)
    _ ≤ ∑ c : F, energy c :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ = ‖countDeviation a b f g r‖ ^ 2 := (countDeviation_norm_sq a b f g r).symm
    _ ≤ ((Fintype.card F : ℝ) - (orderOf f : ℝ)) * r :=
      countDeviation_norm_sq_le a b f g r hr
    _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_self _ (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

/-- All nonzero targets outside a set of size at most `|F| / δ²` have count deviation less
than `δ * √r`. This is [VanDamShparlinski2008], Lemma 2, without a second-moment premise. -/
theorem typical_count (a b f g : Fˣ) (r : ℕ) (δ : ℝ)
    (hr : 1 ≤ r) (hrt : r ≤ orderOf g) (hδ : 0 < δ) :
    ∃ bad : Finset Fˣ,
      (bad.card : ℝ) ≤ (Fintype.card F : ℝ) / δ ^ 2 ∧
      ∀ c : Fˣ, c ∉ bad →
        |(numSolutions a b c f g (orderOf f) r : ℝ) -
          (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ)| < δ * Real.sqrt (r : ℝ) := by
  apply lemma2_typical_count_of_second_moment a b f g r δ hr hδ
  exact second_moment_units_le a b f g r hrt

/-- At the scan threshold in [VanDamShparlinski2008], Corollary 2, every nonzero target has a
solution in the scan box except for at most `|F| / log |F|` targets. -/
theorem typical_solvable (a b f g : Fˣ) (r : ℕ)
    (hlow : (Fintype.card F : ℝ) ^ 2 / (orderOf f : ℝ) ^ 2 *
      Real.log (Fintype.card F : ℝ) ≤ (r : ℝ)) (hrt : r ≤ orderOf g) :
    ∃ bad : Finset Fˣ,
      (bad.card : ℝ) ≤ (Fintype.card F : ℝ) / Real.log (Fintype.card F : ℝ) ∧
      ∀ c : Fˣ, c ∉ bad →
        ∃ x y : ℕ, x < orderOf f ∧ y < r ∧
          (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y = (c : F) := by
  have hq : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast (Fintype.one_lt_card (α := F))
  have hlog := Real.log_pos hq
  obtain ⟨bad, hbad, hsol⟩ := corollary2_typical_solvable_of_second_moment a b f g
    (fun n _ hn => second_moment_units_le a b f g n hn)
    (Real.log (Fintype.card F : ℝ))⁻¹ (inv_pos.mpr hlog)
    (by rw [one_div, inv_inv, Real.exp_log (by positivity)]) r hlow (by exact_mod_cast hrt)
  exact ⟨bad, by simpa [div_eq_mul_inv, mul_comm] using hbad, hsol⟩

end Qatlib.Papers.ExpCongruence08.MainResults
