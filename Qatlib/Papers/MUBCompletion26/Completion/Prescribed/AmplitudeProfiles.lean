/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Obstruction for Three Prescribed Amplitude Profiles

This module formalizes Theorem 7.3 of Sun showing that there are no real triples
`α, β : Fin 3 → ℝ` for which all three profiles `α`, `β`, and `β - α` satisfy
`∑ j, cos²(θ_j) = 3 / 2` together with cyclic weak triangle inequalities on both
`(|cos θ_j cos θ_{j+1}|)_j` and `(|sin θ_j sin θ_{j+1}|)_j`.

## Main statements

* `WeakTriangle3`: cyclic weak triangle inequalities on `Fin 3 → ℝ`.
* `ProfileOK`: amplitude-profile feasibility conditions of Eq. (7.12).
* `theorem_7_3`: nonexistence of `α, β` making `α`, `β`, and `β - α` feasible.

## References

* [Sun, 2026][Sun2026], Section 7.3, Theorem 7.3, Eq. (7.12).
-/

open scoped BigOperators

set_option autoImplicit false

namespace Qatlib.Papers.MUBCompletion26.Completion.Prescribed

/-- A length triple satisfies all three weak triangle inequalities cyclically,
including zeros and equality cases. -/
def WeakTriangle3 (f : Fin 3 → ℝ) : Prop :=
  ∀ i : Fin 3, f i ≤ f (i + 1) + f (i + 2)

/-- The amplitude profile condition: `cos²` sum equal to `3 / 2` and weak
triangle inequalities for both cosine and sine product triples. -/
def ProfileOK (θ : Fin 3 → ℝ) : Prop :=
  (∑ j : Fin 3, Real.cos (θ j) ^ 2 = 3 / 2) ∧
  WeakTriangle3 (fun j => |Real.cos (θ j) * Real.cos (θ (j + 1))|) ∧
  WeakTriangle3 (fun j => |Real.sin (θ j) * Real.sin (θ (j + 1))|)

private lemma heron_nonneg (f : Fin 3 → ℝ) (ht : WeakTriangle3 f) :
    0 ≤ 2 * (f 0 ^ 2 * f 1 ^ 2 + f 1 ^ 2 * f 2 ^ 2 + f 2 ^ 2 * f 0 ^ 2) -
      ((f 0 ^ 2) ^ 2 + (f 1 ^ 2) ^ 2 + (f 2 ^ 2) ^ 2) := by
  have ht0 := ht 0
  have ht1 := ht 1
  have ht2 := ht 2
  norm_num only [Fin.reduceAdd] at ht0 ht1 ht2
  have hp := mul_nonneg
    (mul_nonneg
      (mul_nonneg (by linarith only [ht0, ht1, ht2] : 0 ≤ f 0 + f 1 + f 2)
        (by linarith : 0 ≤ -f 0 + f 1 + f 2))
      (by linarith : 0 ≤ f 0 - f 1 + f 2))
    (by linarith : 0 ≤ f 0 + f 1 - f 2)
  nlinarith only [hp]

-- Heron's expression in the double-angle coordinates, after eliminating the third coordinate.
private lemma heron_polynomial (x y z : ℝ) (hsum : x + y + z = 0)
    (h : 0 ≤ 2 *
      (((1 + x) / 2 * ((1 + y) / 2)) * ((1 + y) / 2 * ((1 + z) / 2)) +
       ((1 + y) / 2 * ((1 + z) / 2)) * ((1 + z) / 2 * ((1 + x) / 2)) +
       ((1 + z) / 2 * ((1 + x) / 2)) * ((1 + x) / 2 * ((1 + y) / 2))) -
      (((1 + x) / 2 * ((1 + y) / 2)) ^ 2 +
       ((1 + y) / 2 * ((1 + z) / 2)) ^ 2 +
       ((1 + z) / 2 * ((1 + x) / 2)) ^ 2)) :
    (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 + 12 * (x ^ 2 + y ^ 2 + z ^ 2) -
      48 * (x * y * z) ≤ 12 := by
  have hz : z = -(x + y) := by linarith
  rw [hz] at h ⊢
  nlinarith only [h]

-- Both signs of the cubic term force each coordinate below the rational cutoff.
private lemma coordinate_upper_bound (x y z : ℝ) (hx : x ≤ 1)
    (hsum : x + y + z = 0)
    (hp : (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 + 12 * (x ^ 2 + y ^ 2 + z ^ 2) +
      48 * (x * y * z) ≤ 12)
    (hm : (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 + 12 * (x ^ 2 + y ^ 2 + z ^ 2) -
      48 * (x * y * z) ≤ 12) : x < 15 / 22 := by
  by_contra h
  have hlow : 15 / 22 ≤ x := le_of_not_gt h
  let R := x ^ 2 + y ^ 2 + z ^ 2
  let s := (y + x / 2) ^ 2
  have hz : z = -(x + y) := by linarith
  have hR : R = 3 / 2 * x ^ 2 + 2 * s := by
    dsimp [R, s]
    rw [hz]
    ring
  have hP : x * y * z = x ^ 3 / 4 - x * s := by
    dsimp [s]
    rw [hz]
    ring
  have hx0 : 0 ≤ x := by linarith
  have hx2 : x ^ 2 ≤ 1 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hx) (by linarith : 0 ≤ 1 + x)]
  have hx2low : (225 : ℝ) / 484 ≤ x ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hlow)
      (by linarith : 0 ≤ x + 15 / 22)]
  have hbase : 12 < 4 * x ^ 4 + 24 * x ^ 2 := by
    nlinarith only [hx2low, sq_nonneg (x ^ 2 - 225 / 484)]
  have havg : R ^ 2 + 12 * R ≤ 12 := by
    dsimp [R]
    linarith only [hp, hm]
  by_cases hs : x ^ 2 / 4 ≤ s
  · have hRlow : 2 * x ^ 2 ≤ R := by linarith only [hR, hs]
    have hRsq := mul_self_le_mul_self (by positivity : 0 ≤ 2 * x ^ 2) hRlow
    nlinarith only [havg, hRlow, hRsq, hbase]
  · have hfactor : 0 ≤ 48 * x - 24 - 7 * x ^ 2 - 4 * s := by
      linarith only [hlow, hx2, hs]
    have hid : R ^ 2 + 12 * R + 48 * (x * y * z) -
        (4 * x ^ 4 + 24 * x ^ 2) =
        (x ^ 2 / 4 - s) * (48 * x - 24 - 7 * x ^ 2 - 4 * s) := by
      rw [hR, hP]
      ring
    have hprod := mul_nonneg (by linarith only [hs] : 0 ≤ x ^ 2 / 4 - s) hfactor
    change R ^ 2 + 12 * R + 48 * (x * y * z) ≤ 12 at hp
    linarith only [hp, hid, hprod, hbase]

private lemma coordinate_abs_bound (x y z : ℝ) (hx : |x| ≤ 1)
    (hsum : x + y + z = 0)
    (hp : (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 + 12 * (x ^ 2 + y ^ 2 + z ^ 2) +
      48 * (x * y * z) ≤ 12)
    (hm : (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 + 12 * (x ^ 2 + y ^ 2 + z ^ 2) -
      48 * (x * y * z) ≤ 12) : |x| ≤ 15 / 22 := by
  have hu := coordinate_upper_bound x y z (abs_le.mp hx).2 hsum hp hm
  have hl := coordinate_upper_bound (-x) (-y) (-z)
    (by linarith [(abs_le.mp hx).1]) (by linarith only [hsum])
    (by nlinarith only [hm]) (by nlinarith only [hp])
  exact abs_le.mpr ⟨by linarith only [hl], le_of_lt hu⟩

private lemma profile_bounds (θ : Fin 3 → ℝ) (hθ : ProfileOK θ) :
    (∑ j : Fin 3, Real.cos (2 * θ j) = 0) ∧
      (∀ j : Fin 3, |Real.cos (2 * θ j)| ≤ 15 / 22) := by
  obtain ⟨hsum, hc, hs⟩ := hθ
  let r := fun j : Fin 3 => Real.cos (2 * θ j)
  have hcos (j : Fin 3) : Real.cos (θ j) ^ 2 = (1 + r j) / 2 := by
    dsimp [r]
    nlinarith only [Real.cos_two_mul (θ j)]
  have hsin (j : Fin 3) : Real.sin (θ j) ^ 2 = (1 + -r j) / 2 := by
    nlinarith only [hcos j, Real.cos_sq_add_sin_sq (θ j)]
  rw [Fin.sum_univ_three] at hsum
  have hr : r 0 + r 1 + r 2 = 0 := by
    linarith only [hsum, hcos 0, hcos 1, hcos 2]
  have HC := heron_nonneg _ hc
  have HS := heron_nonneg _ hs
  norm_num only [Fin.reduceAdd] at HC HS
  simp only [sq_abs, mul_pow, hcos] at HC
  simp only [sq_abs, mul_pow, hsin] at HS
  have hm := heron_polynomial (r 0) (r 1) (r 2) hr (by simpa only [mul_pow] using HC)
  have hpneg := heron_polynomial (-r 0) (-r 1) (-r 2) (by linarith only [hr])
    (by simpa only [mul_pow] using HS)
  have hp : (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2) ^ 2 +
      12 * (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2) + 48 * (r 0 * r 1 * r 2) ≤ 12 := by
    nlinarith only [hpneg]
  refine ⟨?_, ?_⟩
  · change ∑ j : Fin 3, r j = 0
    simpa only [Fin.sum_univ_three] using hr
  · intro j
    change |r j| ≤ 15 / 22
    have hunit (k : Fin 3) : |r k| ≤ 1 := Real.abs_cos_le_one _
    fin_cases j
    · exact coordinate_abs_bound (r 0) (r 1) (r 2) (hunit 0) hr hp hm
    · exact coordinate_abs_bound (r 1) (r 2) (r 0) (hunit 1)
        (by linarith only [hr]) (by nlinarith only [hp]) (by nlinarith only [hm])
    · exact coordinate_abs_bound (r 2) (r 0) (r 1) (hunit 2)
        (by linarith only [hr]) (by nlinarith only [hp]) (by nlinarith only [hm])

private lemma row_bound (r : Fin 3 → ℝ) (hsum : ∑ j, r j = 0)
    (hb : ∀ j, |r j| ≤ 15 / 22) : |r 0| + |r 1| + |r 2| ≤ 2 * (15 / 22) := by
  rw [Fin.sum_univ_three] at hsum
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  rcases le_total 0 (r 0) with h | h <;>
    rcases le_total 0 (r 1) with h' | h' <;>
      rcases le_total 0 (r 2) with h'' | h'' <;>
        simp only [abs_of_nonneg, abs_of_nonpos, h, h', h''] at * <;> linarith

private lemma cosine_relation (a b : ℝ) :
    Real.cos a ^ 2 + Real.cos b ^ 2 + Real.cos (b - a) ^ 2 -
      2 * Real.cos a * Real.cos b * Real.cos (b - a) = 1 := by
  rw [Real.cos_sub]
  nlinarith only [Real.cos_sq_add_sin_sq a, Real.cos_sq_add_sin_sq b,
    mul_nonneg (sq_nonneg (Real.sin a)) (sq_nonneg (Real.sin b))]

private lemma column_bound (x y z : ℝ)
    (hx : |x| ≤ 15 / 22) (hy : |y| ≤ 15 / 22) (hz : |z| ≤ 15 / 22)
    (heq : x ^ 2 + y ^ 2 + z ^ 2 - 2 * x * y * z = 1) :
    7 / 5 ≤ |x| + |y| + |z| := by
  let a := |x|
  let b := |y|
  let c := |z|
  let M : ℝ := 15 / 22
  let s := a + b + c
  have ha : 0 ≤ a := abs_nonneg x
  have hb : 0 ≤ b := abs_nonneg y
  have hc : 0 ≤ c := abs_nonneg z
  have haM : a ≤ M := hx
  have hbM : b ≤ M := hy
  have hcM : c ≤ M := hz
  have hF : 1 ≤ a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c := by
    have hprod : -(x * y * z) ≤ a * b * c := by
      simpa only [abs_mul] using neg_le_abs (x * y * z)
    dsimp [a, b, c] at *
    nlinarith only [heq, hprod, sq_abs x, sq_abs y, sq_abs z]
  have hs1 : 1 ≤ s := by
    have hab := mul_nonneg ha hb
    have hac := mul_nonneg ha hc
    have hbc := mul_nonneg hb hc
    have habc := mul_nonneg hab (by dsimp [M] at hcM; linarith : 0 ≤ 1 - c)
    have hFs : a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c ≤ s ^ 2 := by
      dsimp [s]
      nlinarith only [habc, hac, hbc]
    have hs0 : 0 ≤ s := by dsimp [s]; linarith only [ha, hb, hc]
    nlinarith only [hF, hFs, hs0]
  have hG : 1 ≤ 2 * M ^ 2 + (s - 2 * M) ^ 2 + 2 * M ^ 2 * (s - 2 * M) := by
    have hprod1 := mul_nonneg
      (mul_nonneg (by dsimp [M] at hcM; linarith : 0 ≤ 1 - c)
        (sub_nonneg.mpr haM)) (sub_nonneg.mpr hbM)
    have hprod2 := mul_nonneg
      (mul_nonneg (by norm_num [M] : 0 ≤ 1 - M)
        (by linarith only [haM, hbM] : 0 ≤ 2 * M - a - b))
      (sub_nonneg.mpr hcM)
    have hid : 2 * M ^ 2 + (s - 2 * M) ^ 2 + 2 * M ^ 2 * (s - 2 * M) -
        (a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c) =
        2 * (1 - c) * (M - a) * (M - b) +
          2 * (1 - M) * (2 * M - a - b) * (M - c) := by
      dsimp [s]
      ring
    linarith only [hF, hid, hprod1, hprod2]
  -- The quadratic is below one throughout [1, 7/5], by its endpoint bounds.
  by_contra h
  have hslt : s < 7 / 5 := lt_of_not_ge h
  have hinterval := mul_nonneg (sub_nonneg.mpr hs1)
    (by linarith only [hslt] : 0 ≤ 7 / 5 - s)
  dsimp [M] at hG
  nlinarith only [hG, hinterval, hs1, hslt]

/-- Theorem 7.3: there is no pair of real amplitude profiles `α, β` such that
`α`, `β`, and `β - α` all satisfy `ProfileOK`. -/
theorem theorem_7_3 :
    ¬ ∃ α β : Fin 3 → ℝ, ProfileOK α ∧ ProfileOK β ∧ ProfileOK (fun j => β j - α j) := by
  rintro ⟨α, β, hα, hβ, hδ⟩
  obtain ⟨hsα, hbα⟩ := profile_bounds α hα
  obtain ⟨hsβ, hbβ⟩ := profile_bounds β hβ
  obtain ⟨hsδ, hbδ⟩ := profile_bounds (fun j => β j - α j) hδ
  have hrα := row_bound _ hsα hbα
  have hrβ := row_bound _ hsβ hbβ
  have hrδ := row_bound _ hsδ hbδ
  have hcol (j : Fin 3) := column_bound _ _ _ (hbα j) (hbβ j) (hbδ j)
    (by simpa only [mul_sub] using cosine_relation (2 * α j) (2 * β j))
  have hc0 := hcol 0
  have hc1 := hcol 1
  have hc2 := hcol 2
  linarith only [hrα, hrβ, hrδ, hc0, hc1, hc2]

end Qatlib.Papers.MUBCompletion26.Completion.Prescribed
