/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Papers.ExpCongruence08.MainResults.SecondMoment

/-!
# Density bounds for exponential congruence search

The half-mean bounds give a positive supply of marked second exponents in a scan box.
For [VanDamShparlinski2008], Theorem 4, the worst-case premise accounts for the full logarithm
in the deviation estimate of Lemma 1. For Theorem 6, the exceptional set comes from the proved
second moment. These statements concern counts and the scalar search factor `√(r / m)`.

* [van Dam and Shparlinski, 2008](https://arxiv.org/abs/0804.1109v1)
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Qatlib.Papers.ExpCongruence08.MainResults

namespace Qatlib.Papers.ExpCongruence08.MainResults

universe u

variable {F : Type*} [Field F] [Fintype F]

/-- Both the target count and the worst-case center `rs/(q-1)` lie between zero and
`min r s`. This bounds the deviation of [VanDamShparlinski2008], Lemma 1, by the shorter
side, giving the claimed error scale whenever the shorter side is at most `√q log q`. -/
theorem abs_count_sub_mean_le_min (a b c f g : Fˣ) (r : ℕ) (hrt : r ≤ orderOf g) :
    |(numSolutions a b c f g (orderOf f) r : ℝ) -
      (r : ℝ) * (orderOf f : ℝ) / ((Fintype.card F : ℝ) - 1)| ≤
        (min r (orderOf f) : ℕ) := by
  let q := Fintype.card F
  let s := orderOf f
  have hq : 1 < q := Fintype.one_lt_card
  have hqpos : (0 : ℝ) < (q : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hq)
  have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by simp [Nat.cast_sub hq.le]
  have hs : (s : ℝ) ≤ (q : ℝ) - 1 := by
    rw [← hcast]
    exact_mod_cast orderOf_le_card_sub_one f
  have hr : (r : ℝ) ≤ (q : ℝ) - 1 := by
    rw [← hcast]
    exact_mod_cast hrt.trans (orderOf_le_card_sub_one g)
  let μ := (r : ℝ) * (s : ℝ) / ((q : ℝ) - 1)
  have hμ0 : 0 ≤ μ := div_nonneg (by positivity) hqpos.le
  have hμ : μ ≤ (min r s : ℕ) := by
    rw [Nat.cast_min]
    apply le_min
    · exact (div_le_iff₀ hqpos).mpr (mul_le_mul_of_nonneg_left hs (by positivity))
    · apply (div_le_iff₀ hqpos).mpr
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
  have hN : (numSolutions a b c f g s r : ℝ) ≤ (min r s : ℕ) := by
    exact_mod_cast le_min (numSolutions_le_r a b c f g s r le_rfl hrt)
      (numSolutions_le_s a b c f g s r le_rfl hrt)
  apply abs_le.mpr
  have hN0 : (0 : ℝ) ≤ (numSolutions a b c f g s r : ℝ) := by positivity
  change -((min r s : ℕ) : ℝ) ≤ (numSolutions a b c f g s r : ℝ) - μ ∧
    (numSolutions a b c f g s r : ℝ) - μ ≤ (min r s : ℕ)
  exact ⟨by linarith only [hμ, hN0], by linarith only [hN, hμ0]⟩

/-- The marked search positions are the second exponents admitting a first exponent within
one full period. -/
def markedExponents (a b c f g : Fˣ) (r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range r).filter fun y => ∃ x : ℕ, x < orderOf f ∧
    (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y = (c : F)

omit [Fintype F] in
/-- Each marked second exponent corresponds to exactly one pair of exponents in the scan box.
Thus the source solution count is the number of marked items in Theorems 4 and 6 of
[VanDamShparlinski2008]. -/
theorem markedExponents_card (a b c f g : Fˣ) (r : ℕ) :
    (markedExponents a b c f g r).card = numSolutions a b c f g (orderOf f) r := by
  classical
  unfold markedExponents numSolutions solValue
  symm
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    obtain ⟨hbox, hval⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hbox
    exact Finset.mem_filter.mpr ⟨hy, x, Finset.mem_range.mp hx, hval⟩
  · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' hy
    change y = y' at hy
    subst y'
    obtain ⟨hbox, hval⟩ := Finset.mem_filter.mp hp
    obtain ⟨hbox', hval'⟩ := Finset.mem_filter.mp hp'
    have hpowers : (f : F) ^ x = (f : F) ^ x' :=
      mul_left_cancel₀ a.ne_zero (add_right_cancel (hval.trans hval'.symm))
    have hx : x = x' := pow_injOn_Iio_orderOf (x := f)
      (Finset.mem_range.mp (Finset.mem_product.mp hbox).1)
      (Finset.mem_range.mp (Finset.mem_product.mp hbox').1)
      (Units.ext (by simpa only [Units.val_pow_eq_pow_val] using hpowers))
    subst x'
    rfl
  · intro y hy
    obtain ⟨hy, x, hx, hval⟩ := Finset.mem_filter.mp hy
    exact ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mk_mem_product (Finset.mem_range.mpr hx) hy,
      hval⟩, rfl⟩

/-- A worst-case deviation estimate of `E` around `rs/(q-1)` guarantees at least `rs/(2q)`
solutions when `2qE ≤ rs`. With the error term of [VanDamShparlinski2008], Lemma 1, the
threshold contains `log q` and suffices for the density step of Theorem 4. -/
theorem count_ge_half_mean_of_worst_case_error (a b c f g : Fˣ) (r : ℕ) (E : ℝ)
    (herror : |(numSolutions a b c f g (orderOf f) r : ℝ) -
      (r : ℝ) * (orderOf f : ℝ) / ((Fintype.card F : ℝ) - 1)| ≤ E)
    (hdense : 2 * (Fintype.card F : ℝ) * E ≤ (r : ℝ) * (orderOf f : ℝ)) :
    (r : ℝ) * (orderOf f : ℝ) / (2 * (Fintype.card F : ℝ)) ≤
      (numSolutions a b c f g (orderOf f) r : ℝ) := by
  have hq : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast (Fintype.one_lt_card (α := F))
  have hcenter := div_le_div_of_nonneg_left
    (show (0 : ℝ) ≤ (r : ℝ) * (orderOf f : ℝ) by positivity)
    (show (0 : ℝ) < (Fintype.card F : ℝ) - 1 by linarith)
    (show (Fintype.card F : ℝ) - 1 ≤ (Fintype.card F : ℝ) by linarith)
  have hE : E ≤ (r : ℝ) * (orderOf f : ℝ) / (2 * (Fintype.card F : ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm E] using hdense
  rw [show (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ) =
    2 * ((r : ℝ) * (orderOf f : ℝ) / (2 * (Fintype.card F : ℝ))) by ring] at hcenter
  linarith only [hcenter, hE, (abs_le.mp herror).1]

/-- At the typical scan threshold there are more than `rs/(2q)` solutions outside at most
`4q/log q` nonzero targets. This takes `δ = √(log q)/2` in [VanDamShparlinski2008], Lemma 2. -/
theorem typical_count_gt_half_mean (a b f g : Fˣ) (r : ℕ)
    (hr : 1 ≤ r) (hrt : r ≤ orderOf g)
    (hdense : (Fintype.card F : ℝ) ^ 2 * Real.log (Fintype.card F : ℝ) ≤
      (r : ℝ) * (orderOf f : ℝ) ^ 2) :
    ∃ bad : Finset Fˣ,
      (bad.card : ℝ) ≤ 4 * (Fintype.card F : ℝ) / Real.log (Fintype.card F : ℝ) ∧
      ∀ c : Fˣ, c ∉ bad →
        (r : ℝ) * (orderOf f : ℝ) / (2 * (Fintype.card F : ℝ)) <
          (numSolutions a b c f g (orderOf f) r : ℝ) := by
  have hq : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast (Fintype.one_lt_card (α := F))
  have hlog := Real.log_pos hq
  have hs : (0 : ℝ) < (orderOf f : ℝ) := by exact_mod_cast (orderOf_pos f)
  obtain ⟨bad, hcard, hdev⟩ := typical_count a b f g r
    (Real.sqrt (Real.log (Fintype.card F : ℝ)) / 2) hr hrt (by positivity)
  have hsq : Real.sqrt (Real.log (Fintype.card F : ℝ)) ^ 2 =
      Real.log (Fintype.card F : ℝ) := Real.sq_sqrt hlog.le
  have hδsq : (Real.sqrt (Real.log (Fintype.card F : ℝ)) / 2) ^ 2 =
      Real.log (Fintype.card F : ℝ) / 4 := by rw [div_pow, hsq]; norm_num
  refine ⟨bad, ?_, fun c hc => ?_⟩
  · rw [hδsq] at hcard
    convert hcard using 1
    ring
  have hprod : Real.sqrt (Real.log (Fintype.card F : ℝ)) * Real.sqrt (r : ℝ) ≤
      (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ) := by
    rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow, hsq,
      Real.sq_sqrt (by positivity), div_pow, mul_pow, le_div_iff₀ (by positivity)]
    calc
      _ = (r : ℝ) * ((Fintype.card F : ℝ) ^ 2 * Real.log (Fintype.card F : ℝ)) := by ring
      _ ≤ (r : ℝ) * ((r : ℝ) * (orderOf f : ℝ) ^ 2) := by gcongr
      _ = _ := by ring
  have hdeviation := (abs_lt.mp (hdev c hc)).1
  have hfactor : (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ) =
      2 * ((r : ℝ) * (orderOf f : ℝ) / (2 * (Fintype.card F : ℝ))) := by ring
  rw [hfactor] at hdeviation hprod
  linarith only [hdeviation, hprod]

/-- A half-mean lower bound implies the large-order scalar search factor
`√(2q / √(st))` when the larger order is scanned for discrete logarithms. The count is
positive for a nonempty scan, and the bound uses its actual value as the number of matches. -/
theorem sqrt_scan_div_count_le_of_half_mean (a b c f g : Fˣ) (r : ℕ)
    (hr : 1 ≤ r) (hst : orderOf g ≤ orderOf f)
    (hcount : (r : ℝ) * (orderOf f : ℝ) / (2 * (Fintype.card F : ℝ)) ≤
      (numSolutions a b c f g (orderOf f) r : ℝ)) :
    0 < numSolutions a b c f g (orderOf f) r ∧
      Real.sqrt ((r : ℝ) / (numSolutions a b c f g (orderOf f) r : ℝ)) ≤
        Real.sqrt (2 * (Fintype.card F : ℝ) /
          Real.sqrt ((orderOf f : ℝ) * (orderOf g : ℝ))) := by
  have hrs : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hs : (0 : ℝ) < (orderOf f : ℝ) := by exact_mod_cast (orderOf_pos f)
  have ht : (0 : ℝ) < (orderOf g : ℝ) := by exact_mod_cast (orderOf_pos g)
  have hpos : (0 : ℝ) < (numSolutions a b c f g (orderOf f) r : ℝ) :=
    lt_of_lt_of_le (by positivity) hcount
  refine ⟨by exact_mod_cast hpos, Real.sqrt_le_sqrt ?_⟩
  have hgeom : Real.sqrt ((orderOf f : ℝ) * (orderOf g : ℝ)) ≤ (orderOf f : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨hs.le, ?_⟩
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hst) hs.le
  calc
    _ ≤ 2 * (Fintype.card F : ℝ) / (orderOf f : ℝ) := by
      apply (div_le_div_iff₀ hpos hs).mpr
      simpa only [mul_comm] using (div_le_iff₀ (by positivity)).mp hcount
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hgeom

/-- A uniform constant `K` in [VanDamShparlinski2008], Lemma 1, gives the fixed threshold
constant `2K` for the density step of Theorem 4. The resulting scalar search factor uses
the marked-item count and requires a nonempty scan within one period of the second base. -/
theorem exists_worst_case_search_constant_of_count_bound (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, C = 2 * K ∧ 0 < C ∧
      ∀ {L : Type u} [Field L] [Fintype L] (a b c f g : Lˣ) (r : ℕ),
        1 ≤ r → r ≤ orderOf g → orderOf g ≤ orderOf f →
        (∀ n : ℕ, 1 ≤ n → n ≤ orderOf g →
          |(numSolutions a b c f g (orderOf f) n : ℝ) -
            (n : ℝ) * (orderOf f : ℝ) / ((Fintype.card L : ℝ) - 1)| ≤
              K * Real.sqrt (Fintype.card L : ℝ) * Real.log (Fintype.card L : ℝ)) →
        C * (Fintype.card L : ℝ) * Real.sqrt (Fintype.card L : ℝ) *
          Real.log (Fintype.card L : ℝ) ≤ (r : ℝ) * (orderOf f : ℝ) →
        0 < (markedExponents a b c f g r).card ∧
        Real.sqrt ((r : ℝ) / (markedExponents a b c f g r).card) ≤
          Real.sqrt (2 * (Fintype.card L : ℝ) /
            Real.sqrt ((orderOf f : ℝ) * (orderOf g : ℝ))) := by
  refine ⟨2 * K, rfl, by positivity, ?_⟩
  intro L _ _ a b c f g r hr hrt hst hbound hthreshold
  rw [markedExponents_card]
  apply sqrt_scan_div_count_le_of_half_mean a b c f g r hr hst
  apply count_ge_half_mean_of_worst_case_error a b c f g r _ (hbound r hr hrt)
  convert hthreshold using 1
  ring

/-- The exceptional proportion in Corollary 2 of [VanDamShparlinski2008] is uniformly `o(1)`.
For every positive `ε`, the field-size threshold is fixed before choosing the field and the
parameters of the congruence. -/
theorem exists_field_size_for_typical_solvability (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℝ, ∀ {L : Type u} [Field L] [Fintype L] (a b f g : Lˣ) (r : ℕ),
      Q ≤ (Fintype.card L : ℝ) →
      (Fintype.card L : ℝ) ^ 2 / (orderOf f : ℝ) ^ 2 * Real.log (Fintype.card L : ℝ) ≤ (r : ℝ) →
      r ≤ orderOf g →
      ∃ bad : Finset Lˣ,
        (bad.card : ℝ) ≤ ε * (Fintype.card L : ℝ) ∧
        ∀ c : Lˣ, c ∉ bad →
          ∃ x y : ℕ, x < orderOf f ∧ y < r ∧
            (a : L) * (f : L) ^ x + (b : L) * (g : L) ^ y = (c : L) := by
  refine ⟨Real.exp (1 / ε), ?_⟩
  intro L _ _ a b f g r hQ hlow hrt
  exact corollary2_typical_solvable_of_second_moment a b f g
    (fun n _ hn => second_moment_units_le a b f g n hn) ε hε hQ r hlow (by exact_mod_cast hrt)

/-- The scan in [VanDamShparlinski2008], Theorems 2 and 5, is complete outside at most
`q/log q` targets. With a short scan this follows from the typical solvability bound, and
with a full-period scan every solution reduces to the box. -/
theorem typical_scan_complete (a b f g : Fˣ) :
    let r := ⌈(Fintype.card F : ℝ) ^ 2 / (orderOf f : ℝ) ^ 2 *
      Real.log (Fintype.card F : ℝ)⌉₊
    ∃ bad : Finset Fˣ,
      (bad.card : ℝ) ≤ (Fintype.card F : ℝ) / Real.log (Fintype.card F : ℝ) ∧
      ∀ c : Fˣ, c ∉ bad →
        ((∃ x y : ℕ, x < orderOf f ∧ y < min r (orderOf g) ∧
          (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y = (c : F)) ↔
        (∃ x y : ℕ, (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y = (c : F))) := by
  intro r
  by_cases h : r ≤ orderOf g
  · obtain ⟨bad, hcard, hgood⟩ := typical_solvable a b f g r (Nat.le_ceil _) h
    refine ⟨bad, hcard, fun c hc => ?_⟩
    rw [min_eq_left h]
    constructor
    · rintro ⟨x, y, _, _, heq⟩
      exact ⟨x, y, heq⟩
    · intro _
      exact hgood c hc
  · have hq : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast (Fintype.one_lt_card (α := F))
    have hlog := Real.log_pos hq
    refine ⟨∅, by simp only [Finset.card_empty, Nat.cast_zero]; positivity, fun c _ => ?_⟩
    rw [min_eq_right (le_of_not_ge h)]
    constructor
    · rintro ⟨x, y, _, _, heq⟩
      exact ⟨x, y, heq⟩
    · intro hsol
      exact exists_of_numSolutions_pos a b c f g (orderOf f) (orderOf g)
        ((numSolutions_pos_iff_exists a b c f g (orderOf g) le_rfl).mpr hsol)

/-- Under the order-product threshold of [VanDamShparlinski2008], Theorem 6, the full scan has
a positive number of marked second exponents outside at most `4q/log q` targets. Its scalar
search factor is at most `√(2q / √(st))`. The threshold is written without fractional powers,
as `q⁴ (log q)² < (st)³`, and the larger order is used for the first exponent. -/
theorem typical_full_scan_marked_search (a b f g : Fˣ) (hst : orderOf g ≤ orderOf f)
    (hlarge : (Fintype.card F : ℝ) ^ 4 * (Real.log (Fintype.card F : ℝ)) ^ 2 <
      ((orderOf f : ℝ) * (orderOf g : ℝ)) ^ 3) :
    ∃ bad : Finset Fˣ,
      (bad.card : ℝ) ≤ 4 * (Fintype.card F : ℝ) / Real.log (Fintype.card F : ℝ) ∧
      ∀ c : Fˣ, c ∉ bad →
        0 < (markedExponents a b c f g (orderOf g)).card ∧
        Real.sqrt ((orderOf g : ℝ) / (markedExponents a b c f g (orderOf g)).card) ≤
          Real.sqrt (2 * (Fintype.card F : ℝ) /
            Real.sqrt ((orderOf f : ℝ) * (orderOf g : ℝ))) := by
  have hq : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast (Fintype.one_lt_card (α := F))
  have hlog := Real.log_pos hq
  have ht : 1 ≤ orderOf g := orderOf_pos g
  have hdense : (Fintype.card F : ℝ) ^ 2 * Real.log (Fintype.card F : ℝ) ≤
      (orderOf g : ℝ) * (orderOf f : ℝ) ^ 2 := by
    rw [← sq_le_sq₀ (by positivity) (by positivity)]
    calc
      _ = (Fintype.card F : ℝ) ^ 4 * (Real.log (Fintype.card F : ℝ)) ^ 2 := by ring
      _ ≤ ((orderOf f : ℝ) * (orderOf g : ℝ)) ^ 3 := hlarge.le
      _ = ((orderOf f : ℝ) ^ 3 * (orderOf g : ℝ) ^ 2) * (orderOf g : ℝ) := by ring
      _ ≤ ((orderOf f : ℝ) ^ 3 * (orderOf g : ℝ) ^ 2) * (orderOf f : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hst) (by positivity)
      _ = _ := by ring
  obtain ⟨bad, hbad, hgood⟩ := typical_count_gt_half_mean a b f g (orderOf g) ht le_rfl hdense
  refine ⟨bad, hbad, fun c hc => ?_⟩
  rw [markedExponents_card]
  exact sqrt_scan_div_count_le_of_half_mean a b c f g (orderOf g) ht hst (hgood c hc).le

end Qatlib.Papers.ExpCongruence08.MainResults
