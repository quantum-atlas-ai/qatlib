/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma4RestrictedQuan
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem2QuadraticSpeedupRestrictedStat

/-!
# Amplification with known success probability

This module derives the trigonometric rotation formula and good-component squared mass after
repeated rank-one sign-phase iterations. `zoo_counting_rankone_known_success_amplification`
proves the success lower bound for the iteration count obtained from the known angle. For
background, see [BrassardHoyerTapp1998Counting].

## Main statements

* `zoo_counting_rankone_known_success_amplification_rotation`: For a unitary preparation with
  initial good mass strictly between zero and one and `sin² θ` equal to that mass for `0 ≤ θ ≤
  π/2`, the state after `j` sign-phase iterations has the stated sine and cosine coefficients at
  angle `(2 * j + 1) * θ`. See [Brassard et al., Theorem 1][BrassardHoyerTapp1998Counting].
* `zoo_counting_rankone_known_success_amplification`: For a unitary preparation with positive
  initial good mass `a = sin² θ` and `0 ≤ θ ≤ π/2`, taking `Nat.floor (π / (4 * θ))` sign-phase
  iterations gives good squared mass at least `max (1 - a) a`. See [Brassard et al., Theorem
  2][BrassardHoyerTapp1998Counting].

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

/-- The prepared state is the sum of its good and bad components. -/
lemma zoo_counting_rankone_known_success_amplification_state_split
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool) :
    (fun i => A i 0) =
      RankOneReflection.goodPart g (fun i => A i 0) +
        RankOneReflection.badPart g (fun i => A i 0) := by
  funext i
  by_cases h : g i <;> simp [RankOneReflection.goodPart, RankOneReflection.badPart, h]

/-- Taking the good part of a linear combination of good and bad components retains exactly the
good summand. -/
lemma zoo_counting_rankone_known_success_amplification_goodPart_combination
    {n : ℕ} (g : Fin (n + 1) → Bool) (v : Fin (n + 1) → ℂ) (c₁ c₂ : ℂ) :
    RankOneReflection.goodPart g
        (c₁ • RankOneReflection.goodPart g v + c₂ • RankOneReflection.badPart g v) =
      c₁ • RankOneReflection.goodPart g v := by
  funext i
  by_cases h : g i <;>
    simp [RankOneReflection.goodPart, RankOneReflection.badPart, h,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- The sum of squared coordinate norms of `c • v` equals `Complex.normSq c` times that of `v`. -/
lemma zoo_counting_rankone_known_success_amplification_normSq_sum_smul
    {n : ℕ} (c : ℂ) (v : Fin (n + 1) → ℂ) :
    (∑ i, Complex.normSq ((c • v) i)) =
      Complex.normSq c * ∑ i, Complex.normSq (v i) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]

/-- With `s = sin θ`, `c = cos θ`, `c² = b = 1 - a`, and nonzero `s` and `c`, the coefficient
`sin (α + 2θ) / s` equals `(1 - 2a) * (sin α / s) + 2b * (cos α / c)`. -/
lemma zoo_counting_rankone_known_success_amplification_sin_rec
    {θ a b s c α : ℝ} (hs : Real.sin θ = s) (hc : Real.cos θ = c)
    (hcq : c ^ 2 = 1 - a) (hb : b = 1 - a) (hs0 : s ≠ 0) (hc0 : c ≠ 0) :
    Real.sin (α + 2 * θ) / s =
      (1 - 2 * a) * (Real.sin α / s) + 2 * b * (Real.cos α / c) := by
  have hbc : b = c ^ 2 := by rw [hb, hcq]
  have hcos2 : Real.cos (2 * θ) = 1 - 2 * a := by
    rw [Real.cos_two_mul, hc, hcq]; ring
  have hsin2 : Real.sin (2 * θ) = 2 * s * c := by
    rw [Real.sin_two_mul, hs, hc]
  have e1 : (1 - 2 * a) * (Real.sin α / s) = Real.sin α * (1 - 2 * a) / s := by
    ring
  have e2 : 2 * b * (Real.cos α / c) = Real.cos α * (2 * s * c) / s := by
    rw [mul_div_assoc', div_eq_div_iff hc0 hs0]
    linear_combination 2 * Real.cos α * s * hbc
  rw [Real.sin_add, hcos2, hsin2, e1, e2, ← add_div]

/-- With `s = sin θ`, `c = cos θ`, `s² = a`, `c² = 1 - a`, and nonzero `s` and `c`, the
coefficient `cos (α + 2θ) / c` equals `(1 - 2a) * (cos α / c) - 2a * (sin α / s)`. -/
lemma zoo_counting_rankone_known_success_amplification_cos_rec
    {θ a s c α : ℝ} (hs : Real.sin θ = s) (hc : Real.cos θ = c)
    (hsq : s ^ 2 = a) (hcq : c ^ 2 = 1 - a) (hs0 : s ≠ 0) (hc0 : c ≠ 0) :
    Real.cos (α + 2 * θ) / c =
      (1 - 2 * a) * (Real.cos α / c) - 2 * a * (Real.sin α / s) := by
  have hcos2 : Real.cos (2 * θ) = 1 - 2 * a := by
    rw [Real.cos_two_mul, hc, hcq]; ring
  have hsin2 : Real.sin (2 * θ) = 2 * s * c := by
    rw [Real.sin_two_mul, hs, hc]
  have e1 : (1 - 2 * a) * (Real.cos α / c) = Real.cos α * (1 - 2 * a) / c := by
    ring
  have e2 : 2 * a * (Real.sin α / s) = Real.sin α * (2 * s * c) / c := by
    rw [mul_div_assoc', div_eq_div_iff hs0 hc0]
    linear_combination -2 * Real.sin α * c * hsq
  rw [Real.cos_add, hcos2, hsin2, e1, e2, ← sub_div]

/-- For a unitary preparation with initial good mass strictly between zero and one and `sin² θ`
equal to that mass for `0 ≤ θ ≤ π/2`, the state after `j` sign-phase iterations has the
stated sine and cosine coefficients at angle `(2 * j + 1) * θ`. See [Brassard et al.,
Theorem 1][BrassardHoyerTapp1998Counting]. -/
lemma zoo_counting_rankone_known_success_amplification_rotation
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (hA : A * A.conjTranspose = 1) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi / 2)
    (hsin2a : Real.sin θ ^ 2 =
      ∑ i, Complex.normSq (RankOneReflection.goodPart g (fun i => A i 0) i))
    (ha0 : 0 < ∑ i, Complex.normSq (RankOneReflection.goodPart g (fun i => A i 0) i))
    (ha1 : ∑ i, Complex.normSq (RankOneReflection.goodPart g (fun i => A i 0) i) < 1)
    (j : ℕ) :
    ((RankOneReflection.iterate A g (-1) (-1)) ^ j).mulVec (fun i => A i 0) =
      (↑(Real.sin ((2 * (j : ℝ) + 1) * θ) /
          Real.sqrt (∑ i, Complex.normSq
            (RankOneReflection.goodPart g (fun i => A i 0) i))) : ℂ) •
        RankOneReflection.goodPart g (fun i => A i 0) +
      (↑(Real.cos ((2 * (j : ℝ) + 1) * θ) /
          Real.sqrt (1 - ∑ i, Complex.normSq
            (RankOneReflection.goodPart g (fun i => A i 0) i))) : ℂ) •
        RankOneReflection.badPart g (fun i => A i 0) := by
  obtain ⟨hQa, hQb, hb⟩ := zoo_counting_two_dimensional_sign_action n A g hA
  set a : ℝ := ∑ i, Complex.normSq (RankOneReflection.goodPart g (fun i => A i 0) i)
    with ha_def
  set s : ℝ := Real.sqrt a with hs_def
  set c : ℝ := Real.sqrt (1 - a) with hc_def
  have hθpi : θ ≤ Real.pi := by linarith [Real.pi_pos]
  have hs_sin : s = Real.sin θ := by
    rw [hs_def, ← hsin2a,
      Real.sqrt_sq (Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθpi)]
  have hs_sq : s ^ 2 = a := by rw [hs_def]; exact Real.sq_sqrt (le_of_lt ha0)
  have hs_ne : s ≠ 0 := by
    rw [hs_sin]
    intro h
    have hz : a = 0 := by rw [← hsin2a, h]; norm_num
    linarith
  have hcos_sq : Real.cos θ ^ 2 = 1 - a := by
    have h := Real.sin_sq_add_cos_sq θ
    linarith
  have hc_cos : c = Real.cos θ := by
    rw [hc_def, ← hcos_sq,
      Real.sqrt_sq (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith [Real.pi_pos]) hθπ)]
  have hc_sq : c ^ 2 = 1 - a := by rw [hc_cos]; exact hcos_sq
  have hc_ne : c ≠ 0 := by
    intro h
    have hz : c ^ 2 = 0 := by rw [h]; norm_num
    rw [hc_sq] at hz
    linarith
  induction j with
  | zero =>
      have h0 : (2 * ((0 : ℕ) : ℝ) + 1) * θ = θ := by push_cast; ring
      rw [pow_zero, Matrix.one_mulVec, h0, ← hs_sin, ← hc_cos,
        div_self hs_ne, div_self hc_ne, Complex.ofReal_one, one_smul, one_smul]
      exact zoo_counting_rankone_known_success_amplification_state_split A g
  | succ j ih =>
      have hα : (2 * ((j + 1 : ℕ) : ℝ) + 1) * θ = (2 * (j : ℝ) + 1) * θ + 2 * θ := by
        push_cast; ring
      have coeffA :
          (↑(Real.sin ((2 * ((j + 1 : ℕ) : ℝ) + 1) * θ) / s) : ℂ) =
            (1 - 2 * (a : ℂ)) * (↑(Real.sin ((2 * (j : ℝ) + 1) * θ) / s) : ℂ) +
              (2 * ↑(∑ i, Complex.normSq
                (RankOneReflection.badPart g (fun i => A i 0) i))) *
                (↑(Real.cos ((2 * (j : ℝ) + 1) * θ) / c) : ℂ) := by
        rw [hα,
          zoo_counting_rankone_known_success_amplification_sin_rec
            hs_sin.symm hc_cos.symm hc_sq hb hs_ne hc_ne]
        push_cast
        ring
      have coeffB :
          (↑(Real.cos ((2 * ((j + 1 : ℕ) : ℝ) + 1) * θ) / c) : ℂ) =
            (1 - 2 * (a : ℂ)) * (↑(Real.cos ((2 * (j : ℝ) + 1) * θ) / c) : ℂ) -
              (2 * (a : ℂ)) * (↑(Real.sin ((2 * (j : ℝ) + 1) * θ) / s) : ℂ) := by
        rw [hα,
          zoo_counting_rankone_known_success_amplification_cos_rec
            hs_sin.symm hc_cos.symm hs_sq hc_sq hs_ne hc_ne]
        push_cast
        ring
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, hQa, hQb, coeffA, coeffB]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring

/-- For a unitary preparation with initial good mass `sin² θ` strictly between zero and one and
`0 ≤ θ ≤ π/2`, the good-component squared mass after `j` iterations is `sin²((2j + 1)θ)`.
See [BrassardHoyerTapp1998Counting]. -/
lemma zoo_counting_rankone_known_success_amplification_success_sq
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (hA : A * A.conjTranspose = 1) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi / 2)
    (hsin2a : Real.sin θ ^ 2 =
      ∑ i, Complex.normSq (RankOneReflection.goodPart g (fun i => A i 0) i))
    (ha0 : 0 < ∑ i, Complex.normSq (RankOneReflection.goodPart g (fun i => A i 0) i))
    (ha1 : ∑ i, Complex.normSq (RankOneReflection.goodPart g (fun i => A i 0) i) < 1)
    (j : ℕ) :
    ∑ i, Complex.normSq (RankOneReflection.goodPart g
        (((RankOneReflection.iterate A g (-1) (-1)) ^ j).mulVec (fun i => A i 0)) i) =
      Real.sin ((2 * (j : ℝ) + 1) * θ) ^ 2 := by
  rw [zoo_counting_rankone_known_success_amplification_rotation
    A g hA θ hθ0 hθπ hsin2a ha0 ha1 j,
    zoo_counting_rankone_known_success_amplification_goodPart_combination,
    zoo_counting_rankone_known_success_amplification_normSq_sum_smul,
    Complex.normSq_ofReal]
  set s : ℝ :=
    Real.sqrt (∑ i, Complex.normSq (RankOneReflection.goodPart g (fun i => A i 0) i))
    with hs_def
  have hs_ne : s ≠ 0 := by
    rw [hs_def]
    exact ne_of_gt (Real.sqrt_pos_of_pos ha0)
  have hsq : s ^ 2 =
      ∑ i, Complex.normSq (RankOneReflection.goodPart g (fun i => A i 0) i) := by
    rw [hs_def]
    exact Real.sq_sqrt (le_of_lt ha0)
  rw [← hsq]
  field_simp [hs_ne]

/-- If `0 < θ ≤ π/4` and `sin² θ = a`, the squared sine at the angle selected by `Nat.floor (π /
(4 * θ))` is at least `1 - a`. -/
lemma zoo_counting_rankone_known_success_amplification_floor_estimate
    {θ a : ℝ} (hθ0 : 0 < θ) (hθπ4 : θ ≤ Real.pi / 4)
    (hsin2a : Real.sin θ ^ 2 = a) :
    1 - a ≤ Real.sin ((2 * (Nat.floor (Real.pi / (4 * θ)) : ℝ) + 1) * θ) ^ 2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have h4θ : (0 : ℝ) < 4 * θ := by linarith
  have hx_pos : 0 < Real.pi / (4 * θ) := div_pos hπ h4θ
  set m := Nat.floor (Real.pi / (4 * θ)) with hm
  have hm_le : (m : ℝ) ≤ Real.pi / (4 * θ) := Nat.floor_le (le_of_lt hx_pos)
  have hlt : Real.pi / (4 * θ) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2θ : (2 : ℝ) * θ * (Real.pi / (4 * θ)) = Real.pi / 2 := by
    field_simp [h4θ.ne']
    ring
  have hδ_upper : (2 * (m : ℝ) + 1) * θ ≤ Real.pi / 2 + θ := by
    have h1 := mul_le_mul_of_nonneg_left hm_le (le_of_lt (by linarith : (0 : ℝ) < 2 * θ))
    rw [h2θ] at h1
    linarith
  have hδ_lower : Real.pi / 2 - θ < (2 * (m : ℝ) + 1) * θ := by
    have h1 := mul_lt_mul_of_pos_left hlt (by linarith : (0 : ℝ) < 2 * θ)
    rw [h2θ] at h1
    linarith
  set δ := (2 * (m : ℝ) + 1) * θ - Real.pi / 2 with hδ
  have hδabs : |δ| ≤ θ := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hnn : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
  have hcos : Real.cos θ ≤ Real.cos |δ| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg δ) (by linarith) hδabs
  have hcosδ : Real.cos δ = Real.cos |δ| := by
    rcases lt_or_ge δ 0 with h | h
    · rw [abs_of_neg h, Real.cos_neg]
    · rw [abs_of_nonneg h]
  have hsq : Real.cos θ ^ 2 ≤ Real.cos δ ^ 2 := by
    rw [pow_two, pow_two, hcosδ]
    exact mul_le_mul hcos hcos hnn (le_trans hnn hcos)
  have hsin : Real.sin ((2 * (m : ℝ) + 1) * θ) = Real.cos δ := by
    rw [show (2 * (m : ℝ) + 1) * θ = δ + Real.pi / 2 from by rw [hδ]; ring,
      Real.sin_add_pi_div_two]
  rw [hsin]
  have hcos2θ : Real.cos θ ^ 2 = 1 - a := by
    have h := Real.sin_sq_add_cos_sq θ
    linarith
  rw [← hcos2θ]
  exact hsq

/-- For a unitary preparation with positive initial good mass `a = sin² θ` and `0 ≤ θ ≤ π/2`,
taking `Nat.floor (π / (4 * θ))` sign-phase iterations gives good squared mass at least `max
(1 - a) a`. See [Brassard et al., Theorem 2][BrassardHoyerTapp1998Counting]. -/
theorem zoo_counting_rankone_known_success_amplification :
    ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (g : Fin (n + 1) → Bool),
    A * A.conjTranspose = 1 →
    let ψ : Fin (n + 1) → ℂ := fun i => A i 0;
    let a : ℝ := ∑ i, Complex.normSq (RankOneReflection.goodPart g ψ i);
    ∀ (θ : ℝ),
      0 ≤ θ → θ ≤ Real.pi / 2 →
      Real.sin θ ^ 2 = a →
      0 < a →
      let m : ℕ := Nat.floor (Real.pi / (4 * θ));
      let v : Fin (n + 1) → ℂ :=
        ((RankOneReflection.iterate A g (-1) (-1)) ^ m).mulVec ψ;
      max (1 - a) a ≤
        ∑ i, Complex.normSq (RankOneReflection.goodPart g v i) := by
  intro n A g hA ψ a θ hθ0 hθπ hsin2a ha0 m v
  have hψ : ψ = fun i => A i 0 := rfl
  have ha : a = ∑ i, Complex.normSq (RankOneReflection.goodPart g ψ i) := rfl
  rw [hψ] at ha
  have hm : m = Nat.floor (Real.pi / (4 * θ)) := rfl
  have hv : v = ((RankOneReflection.iterate A g (-1) (-1)) ^ m).mulVec ψ := rfl
  rw [hv, hψ, hm]
  have hθpos : 0 < θ := by
    rcases eq_or_lt_of_le hθ0 with h | h
    · exfalso
      rw [← h] at hsin2a
      simp at hsin2a
      linarith
    · exact h
  rcases lt_or_ge (Real.pi / 4) θ with hθπ4 | hθπ4
  · have hx_lt1 : Real.pi / (4 * θ) < 1 := by
      rw [div_lt_one (by linarith : (0 : ℝ) < 4 * θ)]
      linarith [Real.pi_pos]
    have hm0 : Nat.floor (Real.pi / (4 * θ)) = 0 := Nat.floor_eq_zero.mpr hx_lt1
    rw [hm0, pow_zero, Matrix.one_mulVec]
    have ha_gt : 1 / 2 < a := by
      rw [← hsin2a]
      have h1 : Real.sin (Real.pi / 4) < Real.sin θ :=
        Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) hθπ hθπ4
      rw [Real.sin_pi_div_four] at h1
      have h2 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      have h3 : (Real.sqrt 2 / 2 : ℝ) ^ 2 < Real.sin θ ^ 2 :=
        pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
      rw [h2] at h3
      exact h3
    rw [← ha]
    rw [max_eq_right (by linarith : 1 - a ≤ a)]
  · have ha_le : a ≤ 1 / 2 := by
      rw [← hsin2a]
      have hsnn : 0 ≤ Real.sin θ :=
        Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])
      have h1 : Real.sin θ ≤ Real.sin (Real.pi / 4) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
          (by linarith [Real.pi_pos]) hθπ4
      rw [Real.sin_pi_div_four] at h1
      have h2 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      have h3 : Real.sin θ ^ 2 ≤ (Real.sqrt 2 / 2 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hsnn h1 2
      rw [h2] at h3
      exact h3
    have hkey := zoo_counting_rankone_known_success_amplification_success_sq
      A g hA θ hθ0 hθπ
      (by rw [← ha]; exact hsin2a) (by rw [← ha]; exact ha0)
      (by rw [← ha]; linarith) (Nat.floor (Real.pi / (4 * θ)))
    rw [hkey]
    rw [max_eq_left (by linarith : a ≤ 1 - a)]
    exact zoo_counting_rankone_known_success_amplification_floor_estimate
      hθpos hθπ4 hsin2a

/-- The known-success amplification theorem satisfies `Theorem2RestrictedSpec.expected`. -/
theorem zoo_counting_rankone_known_success_amplification_contract :
    Theorem2RestrictedSpec.expected :=
  zoo_counting_rankone_known_success_amplification

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
