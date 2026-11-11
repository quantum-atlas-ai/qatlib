/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.IntervalArith.IntervalOps.RationalIntervalArithmeticDefs

/-!
# Correctness of rational interval arithmetic

`g1` certifies dyadic floor rounding, including containment, exact width, lattice membership,
and monotonicity. `g2` proves containment and width bounds for addition and multiplication of
valid rational intervals.

`g3` verifies division by an interval bounded below by a positive gap, including an enclosure
and a width bound, and characterizes rejected inputs. Quantum numerical estimation supplies a
motivating setting for certified enclosures; see [Montanaro2015].

## Main statements

* `g1`: Correctness of dyadic rounding.
* `g2`: Enclosures and width propagation for addition and multiplication.
* `g3`: Certified division with a positive denominator gap.

## References

* [Montanaro, 2015][Montanaro2015]
-/

namespace Qatlib.Foundations.IntervalArith.IntervalOps
set_option autoImplicit false

/-- Dyadic rounding produces a valid interval containing the input, with width `2⁻ᵏ` and a lower
endpoint on the dyadic lattice. The rounded-down endpoint is monotone in the input. -/
theorem g1 :
    (∀ (q : ℚ) (k : ℕ), Valid (rounded q k) ∧ Contains (rounded q k) (q:ℝ) ∧
      width (rounded q k)=unit k ∧ ∃ z : ℤ, roundDown q k=(z:ℚ)/(2:ℚ)^k) ∧
    (∀ (a b : ℚ) (k : ℕ), a≤b → roundDown a k≤roundDown b k) := by
  constructor
  · intro q k
    have hd : (0:ℚ) < 2^k := by positivity
    have hlo : roundDown q k ≤ q := by
      exact (div_le_iff₀ hd).mpr (Int.floor_le (q*(2:ℚ)^k))
    have hhi : q ≤ roundDown q k+unit k := by
      change q ≤ (⌊q*(2:ℚ)^k⌋:ℚ)/(2:ℚ)^k + 1/(2:ℚ)^k
      rw [← add_div]
      exact (le_div_iff₀ hd).mpr (Int.lt_floor_add_one (q*(2:ℚ)^k)).le
    refine ⟨?_,?_,?_,⌊q*(2:ℚ)^k⌋,rfl⟩
    · change roundDown q k ≤ roundDown q k + unit k
      have hu : 0 ≤ unit k := by unfold unit; positivity
      linarith
    · change ((roundDown q k:ℚ):ℝ) ≤ q ∧ (q:ℝ) ≤ ((roundDown q k+unit k:ℚ):ℝ)
      exact ⟨by exact_mod_cast hlo,by exact_mod_cast hhi⟩
    · simp [width,rounded]
  · intro a b k hab
    apply div_le_div_of_nonneg_right
    · exact_mod_cast Int.floor_mono (mul_le_mul_of_nonneg_right hab (by positivity : (0:ℚ) ≤ 2^k))
    · positivity

/-- The maximum absolute endpoint of a rational interval is nonnegative. -/
private theorem radius_nonneg (a : Interval) : 0 ≤ radius a :=
  (abs_nonneg a.lo).trans (le_max_left _ _)

/-- Every rational point between the interval endpoints has absolute value at most `radius a`. -/
private theorem point_abs (a : Interval) (x : ℚ) (hx : a.lo ≤ x ∧ x ≤ a.hi) :
    |x| ≤ radius a := by
  have hl := abs_le.mp (le_max_left |a.lo| |a.hi|)
  have hu := abs_le.mp (le_max_right |a.lo| |a.hi|)
  exact abs_le.mpr ⟨hl.1.trans hx.1,hx.2.trans hu.2⟩

/-- The distance between two rational points in an interval is at most its width. -/
private theorem point_distance (a : Interval) (x u : ℚ)
    (hx : a.lo ≤ x ∧ x ≤ a.hi) (hu : a.lo ≤ u ∧ u ≤ a.hi) : |x-u| ≤ width a := by
  dsimp only [width]
  exact abs_le.mpr ⟨by linarith [hx.1,hx.2,hu.1,hu.2],by linarith [hx.1,hx.2,hu.1,hu.2]⟩

/-- Products of points from two intervals differ by at most the sum of each interval's radius
times the other's width. -/
private theorem product_variation (a b : Interval) {x y u v : ℚ}
    (hx : a.lo ≤ x ∧ x ≤ a.hi) (hy : b.lo ≤ y ∧ y ≤ b.hi)
    (hu : a.lo ≤ u ∧ u ≤ a.hi) (hv : b.lo ≤ v ∧ v ≤ b.hi) :
    |x*y-u*v| ≤ radius a*width b+radius b*width a := by
  calc
    _ = |x*(y-v)+v*(x-u)| := by congr 1; ring
    _ ≤ |x*(y-v)|+|v*(x-u)| := abs_add_le _ _
    _ = |x| * |y-v| + |v| * |x-u| := by rw [abs_mul,abs_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul (point_abs a x hx) (point_distance b y v hy hv) (abs_nonneg _) (radius_nonneg a))
      (mul_le_mul (point_abs b v hv) (point_distance a x u hx hu) (abs_nonneg _) (radius_nonneg b))

/-- The nested minimum of four rational numbers is one of those four numbers. -/
private theorem min4_mem (w x y z : ℚ) : min (min w x) (min y z) ∈ [w,x,y,z] := by
  rcases min_choice (min w x) (min y z) with h | h
  · rw [h]
    rcases min_choice w x with h | h <;> simp [h]
  · rw [h]
    rcases min_choice y z with h | h <;> simp [h]

/-- The nested maximum of four rational numbers is one of those four numbers. -/
private theorem max4_mem (w x y z : ℚ) : max (max w x) (max y z) ∈ [w,x,y,z] := by
  rcases max_choice (max w x) (max y z) with h | h
  · rw [h]
    rcases max_choice w x with h | h <;> simp [h]
  · rw [h]
    rcases max_choice y z with h | h <;> simp [h]

/-- The width of the product of valid intervals is bounded by `radius a * width b + radius b *
width a`. -/
private theorem mul_width (a b : Interval) (ha : Valid a) (hb : Valid b) :
    width (mul a b) ≤ radius a*width b+radius b*width a := by
  have hmin := min4_mem (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi)
  have hmax := max4_mem (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hmin hmax
  change max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi)) -
    min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)) ≤ _
  rcases hmax with hmax | hmax | hmax | hmax <;>
    rcases hmin with hmin | hmin | hmin | hmin <;>
    rw [hmax,hmin] <;>
    apply le_trans (le_abs_self _) <;>
    apply product_variation a b <;>
    first | exact ⟨le_rfl,ha⟩ | exact ⟨ha,le_rfl⟩ | exact ⟨le_rfl,hb⟩ | exact ⟨hb,le_rfl⟩

/-- Multiplication by a fixed real scalar places a point between the minimum and maximum of the
two endpoint products. -/
private theorem linear_product_bounds (l u x t : ℝ) (hl : l ≤ x) (hu : x ≤ u) :
    min (l*t) (u*t) ≤ x*t ∧ x*t ≤ max (l*t) (u*t) := by
  rcases le_total 0 t with ht | ht
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hl ht),
      (mul_le_mul_of_nonneg_right hu ht).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hu ht),
      (mul_le_mul_of_nonpos_right hl ht).trans (le_max_left _ _)⟩

/-- The product of two enclosed real points lies between the minimum and maximum of the four
endpoint products. -/
private theorem bilinear_bounds (l u r s x y : ℝ)
    (hx : l ≤ x ∧ x ≤ u) (hy : r ≤ y ∧ y ≤ s) :
    min (min (l*r) (l*s)) (min (u*r) (u*s)) ≤ x*y ∧
      x*y ≤ max (max (l*r) (l*s)) (max (u*r) (u*s)) := by
  have hxy := linear_product_bounds l u x y hx.1 hx.2
  have hly : min (l*r) (l*s) ≤ l*y ∧ l*y ≤ max (l*r) (l*s) := by
    simpa only [mul_comm] using linear_product_bounds r s y l hy.1 hy.2
  have huy : min (u*r) (u*s) ≤ u*y ∧ u*y ≤ max (u*r) (u*s) := by
    simpa only [mul_comm] using linear_product_bounds r s y u hy.1 hy.2
  constructor
  · exact (le_min ((min_le_left _ _).trans hly.1) ((min_le_right _ _).trans huy.1)).trans hxy.1
  · exact hxy.2.trans (max_le (hly.2.trans (le_max_left _ _)) (huy.2.trans (le_max_right _ _)))

/-- Addition and multiplication preserve validity and enclose sums and products of contained
real points. Their widths satisfy the stated exact addition formula and radius-weighted
multiplication bound. -/
theorem g2 :
    ∀ (a b : Interval), Valid a → Valid b →
      Valid (add a b) ∧ Valid (mul a b) ∧ width (add a b)=width a+width b ∧
      width (mul a b) ≤ radius a*width b+radius b*width a ∧
      ∀ (x y : ℝ), Contains a x → Contains b y →
        Contains (add a b) (x+y) ∧ Contains (mul a b) (x*y) := by
  intro a b ha hb
  refine ⟨?_,?_,?_,mul_width a b ha hb,?_⟩
  · exact add_le_add ha hb
  · change min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)) ≤
      max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))
    exact ((min_le_left _ _).trans (min_le_left _ _)).trans
      ((le_max_left _ _).trans (le_max_left _ _))
  · dsimp only [width,add]
    ring
  · intro x y hx hy
    constructor
    · exact ⟨by simpa only [add,Rat.cast_add] using add_le_add hx.1 hy.1,
        by simpa only [add,Rat.cast_add] using add_le_add hx.2 hy.2⟩
    · simpa only [Contains,mul,Rat.cast_min,Rat.cast_max,Rat.cast_mul] using
        bilinear_bounds a.lo a.hi b.lo b.hi x y hx hy

/-- Valid intervals with a denominator lower endpoint above a positive gap produce a valid
quotient enclosure with the stated width bound and nonzero denominators. Invalid intervals
or failed gap checks produce `none`. -/
theorem g3 :
    (∀ (a b : Interval) (gap : ℚ), 0<gap → gap≤b.lo → Valid a → Valid b →
      ∃ c, divPositive a b gap=some c ∧ Valid c ∧
        width c ≤ width a/gap+radius a*width b/gap^2 ∧
        ∀ (x y : ℝ), Contains a x → Contains b y →
          y≠0 ∧ Contains c (x/y)) ∧
    (∀ (a b : Interval) (gap : ℚ), (gap≤0 ∨ b.lo<gap ∨ ¬Valid a ∨ ¬Valid b) →
      divPositive a b gap=none) := by
  constructor
  · intro a b gap hg hgb ha hb
    have hlo : 0 < b.lo := hg.trans_le hgb
    have hhi : 0 < b.hi := hlo.trans_le hb
    let r : Interval := ⟨1/b.hi,1/b.lo⟩
    have hr : Valid r := one_div_le_one_div_of_le hlo hb
    have hrad : radius r = 1/b.lo := by
      dsimp only [radius,r]
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity),max_eq_right hr]
    have hradbound : radius r ≤ 1/gap := by
      rw [hrad]
      exact one_div_le_one_div_of_le hg hgb
    have hw : width r = width b/(b.lo*b.hi) := by
      dsimp only [width,r]
      field_simp [ne_of_gt hlo,ne_of_gt hhi]
    have hw0 : 0 ≤ width b := sub_nonneg.mpr hb
    have hprod : gap^2 ≤ b.lo*b.hi := by
      have hgb' : gap ≤ b.hi := hgb.trans hb
      nlinarith [mul_le_mul hgb hgb' hg.le hlo.le]
    have hwidthbound : width r ≤ width b/gap^2 := by
      rw [hw]
      exact div_le_div_of_nonneg_left hw0 (sq_pos_of_pos hg) hprod
    have hmul := g2 a r ha hr
    have hcond : 0<gap ∧ gap≤b.lo ∧ Valid a ∧ Valid b := ⟨hg,hgb,ha,hb⟩
    refine ⟨mul a r,by simp only [divPositive,if_pos hcond]; rfl,hmul.2.1,?_,?_⟩
    · calc
        _ ≤ radius a*width r+radius r*width a := hmul.2.2.2.1
        _ ≤ radius a*(width b/gap^2)+(1/gap)*width a :=
          add_le_add (mul_le_mul_of_nonneg_left hwidthbound (radius_nonneg a))
            (mul_le_mul_of_nonneg_right hradbound (sub_nonneg.mpr ha))
        _ = _ := by ring
    · intro x y hx hy
      have hloR : (0:ℝ) < b.lo := by exact_mod_cast hlo
      have hypos : 0 < y := hloR.trans_le hy.1
      have hrecip : Contains r (1/y) := by
        change ((1/b.hi:ℚ):ℝ) ≤ 1/y ∧ 1/y ≤ ((1/b.lo:ℚ):ℝ)
        push_cast
        exact ⟨one_div_le_one_div_of_le hypos hy.2,one_div_le_one_div_of_le hloR hy.1⟩
      exact ⟨ne_of_gt hypos,by
        simpa only [one_div,div_eq_mul_inv,one_mul] using (hmul.2.2.2.2 x (1/y) hx hrecip).2⟩
  · intro a b gap hbad
    have hn : ¬(0<gap ∧ gap≤b.lo ∧ Valid a ∧ Valid b) := by
      intro ⟨hg,hgb,ha,hb⟩
      rcases hbad with hbad | hbad | hbad | hbad
      · exact not_lt_of_ge hbad hg
      · exact not_lt_of_ge hgb hbad
      · exact hbad ha
      · exact hbad hb
    exact if_neg hn

end Qatlib.Foundations.IntervalArith.IntervalOps
