/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.GroverInterp.GroverInterpClaims
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Data.Complex.BigOperators

/-!
# Overlap bounds for Grover interpolation

This module develops the conjugate dot product `cdot` on finite complex vectors and the
trigonometric estimates needed for the final overlap bound. `claim6` proves `Claim6Statement`,
the spectral-expansion overlap statement associated with Claim 6 in the quantum-walk analysis.

For background, see [Ambainis2007ElementDistinctness].

## Main statements

* `cdot_self_eq`: the self-product is the sum of squared coordinate norms.
* `cot_sq_le`: a phase gap bounds the squared half-angle cotangent.
* `claim6`: the normalized endpoint overlap lower bound.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.WalkFind.GroverInterp

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

/-- The conjugate dot product on finite complex vectors, conjugate-linear in the first argument
and linear in the second. -/
def cdot {m : ℕ} (u v : Fin m → ℂ) : ℂ := ∑ i, star (u i) * v i

/-- The star operation on complex numbers agrees with complex conjugation. -/
lemma star_eq_conj (z : ℂ) : star z = starRingEnd ℂ z := rfl

/-- The conjugate dot product with zero in the first argument is zero. -/
@[simp] lemma cdot_zero_left {m : ℕ} (v : Fin m → ℂ) :
    cdot (0 : Fin m → ℂ) v = 0 := by
  simp [cdot]

/-- The conjugate dot product with zero in the second argument is zero. -/
@[simp] lemma cdot_zero_right {m : ℕ} (u : Fin m → ℂ) :
    cdot u (0 : Fin m → ℂ) = 0 := by
  simp [cdot]

/-- The conjugate dot product distributes over addition in its first argument. -/
lemma cdot_add_left {m : ℕ} (u₁ u₂ v : Fin m → ℂ) :
    cdot (u₁ + u₂) v = cdot u₁ v + cdot u₂ v := by
  simp only [cdot, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

/-- The conjugate dot product distributes over addition in its second argument. -/
lemma cdot_add_right {m : ℕ} (u v₁ v₂ : Fin m → ℂ) :
    cdot u (v₁ + v₂) = cdot u v₁ + cdot u v₂ := by
  simp only [cdot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- A scalar in the first argument of `cdot` factors out as its complex conjugate. -/
lemma cdot_smul_left {m : ℕ} (c : ℂ) (u v : Fin m → ℂ) :
    cdot (c • u) v = star c * cdot u v := by
  rw [cdot, cdot, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, star_mul]
  ring

/-- A scalar in the second argument of `cdot` factors out unchanged. -/
lemma cdot_smul_right {m : ℕ} (c : ℂ) (u v : Fin m → ℂ) :
    cdot u (c • v) = c * cdot u v := by
  rw [cdot, cdot, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Scaling both arguments of `cdot` multiplies the product by the conjugate of the first scalar
and the second scalar. -/
lemma cdot_smul_smul {m : ℕ} (c d : ℂ) (u v : Fin m → ℂ) :
    cdot (c • u) (d • v) = star c * (d * cdot u v) := by
  rw [cdot_smul_left, cdot_smul_right]

/-- The conjugate dot product distributes over a finite sum in its first argument. -/
lemma cdot_sum_left {m : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → Fin m → ℂ) (v : Fin m → ℂ) :
    cdot (∑ j, F j) v = ∑ j, cdot (F j) v := by
  have h : (∑ j, F j) = fun i => ∑ j, F j i := by
    funext i; simp
  rw [h]
  simp only [cdot, star_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- The conjugate dot product distributes over a finite sum in its second argument. -/
lemma cdot_sum_right {m : ℕ} {ι : Type*} [Fintype ι]
    (u : Fin m → ℂ) (F : ι → Fin m → ℂ) :
    cdot u (∑ j, F j) = ∑ j, cdot u (F j) := by
  have h : (∑ j, F j) = fun i => ∑ j, F j i := by
    funext i; simp
  rw [h]
  simp only [cdot, Finset.mul_sum]
  exact Finset.sum_comm

/-- Swapping the arguments of `cdot` conjugates its value. -/
lemma cdot_conj_symm {m : ℕ} (u v : Fin m → ℂ) :
    cdot u v = star (cdot v u) := by
  rw [cdot, cdot, star_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [star_mul, star_star]

/-- The conjugate dot product of a vector with itself equals the complex coercion of the sum of
its squared coordinate norms. -/
lemma cdot_self_eq {m : ℕ} (u : Fin m → ℂ) :
    cdot u u = ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) := by
  rw [cdot]
  have h : ∀ i, star (u i) * u i = ((‖u i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    apply Complex.ext <;>
      simp [star_eq_conj, Complex.conj_re, Complex.conj_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sq_norm, Complex.normSq_apply] <;>
      ring
  simp only [h]
  rw [← Complex.ofReal_sum (s := Finset.univ) (f := fun i => ‖u i‖ ^ 2)]

/-- When the sine is nonzero, one plus the squared cotangent equals the reciprocal squared sine. -/
lemma cot_sq_add_one {x : ℝ} (hx : Real.sin x ≠ 0) :
    1 + Real.cot x ^ 2 = 1 / Real.sin x ^ 2 := by
  rw [Real.cot_eq_cos_div_sin]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq x]

/-- For a phase between `ε` and `2 * pi - ε` with positive `ε`, its half-angle sine is at least
`sin (ε / 2)`. -/
lemma sin_half_mono {ε θ : ℝ} (hε : 0 < ε) (hεθ : ε ≤ θ)
    (hθ : θ ≤ 2 * Real.pi - ε) :
    Real.sin (ε / 2) ≤ Real.sin (θ / 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  by_cases hle : θ / 2 ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hle (by linarith)
  · push Not at hle
    have hsub_ge : ε / 2 ≤ Real.pi - θ / 2 := by linarith
    have hsub_le : Real.pi - θ / 2 ≤ Real.pi / 2 := by linarith
    have hmono : Real.sin (ε / 2) ≤ Real.sin (Real.pi - θ / 2) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hsub_le hsub_ge
    rwa [Real.sin_pi_sub] at hmono

/-- For a phase between `ε` and `2 * pi - ε` with positive `ε`, its squared half-angle cotangent
is at most `cot (ε / 2)^2`. This is a phase-gap estimate used for Claim 6 of
[Ambainis2007ElementDistinctness]. -/
lemma cot_sq_le {ε θ : ℝ} (hε : 0 < ε) (hεθ : ε ≤ θ)
    (hθ : θ ≤ 2 * Real.pi - ε) :
    Real.cot (θ / 2) ^ 2 ≤ Real.cot (ε / 2) ^ 2 := by
  have hsinε : 0 < Real.sin (ε / 2) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith) ?_
    linarith [Real.pi_pos]
  have hsinθ : 0 < Real.sin (θ / 2) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith) ?_
    linarith [Real.pi_pos]
  have hle : Real.sin (ε / 2) ≤ Real.sin (θ / 2) := sin_half_mono hε hεθ hθ
  have hsq : Real.sin (ε / 2) ^ 2 ≤ Real.sin (θ / 2) ^ 2 := by
    nlinarith [hle, hsinε, hsinθ]
  have hinv : 1 / Real.sin (θ / 2) ^ 2 ≤ 1 / Real.sin (ε / 2) ^ 2 :=
    one_div_le_one_div_of_le (pow_pos hsinε 2) hsq
  have hεcot := cot_sq_add_one (ne_of_gt hsinε)
  have hθcot := cot_sq_add_one (ne_of_gt hsinθ)
  linarith [hεcot, hθcot]

/-- If `0 ≤ t ≤ 1`, `t ≤ S ≤ (1 + cot (ε / 2)^2) * t`, and `0 < ε ≤ pi`, then `min (t / 2) (t *
ε / 4) ≤ t / sqrt S`. This is the scalar overlap estimate used for Claim 6 of
[Ambainis2007ElementDistinctness]. -/
lemma claim6_final {t S ε : ℝ} (hε : 0 < ε) (hεpi : ε ≤ Real.pi)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hS0 : 0 ≤ S) (htS : t ≤ S)
    (hS : S ≤ (1 + Real.cot (ε / 2) ^ 2) * t) :
    min (t / 2) (t / 4 * ε) ≤ t / Real.sqrt S := by
  rcases eq_or_lt_of_le ht0 with htz | ht
  · rw [← htz]
    simp
  have hSpos : 0 < S := lt_of_lt_of_le ht htS
  rw [le_div_iff₀ (Real.sqrt_pos_of_pos hSpos)]
  have hsinε : 0 < Real.sin (ε / 2) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith) ?_
    linarith
  have hsinpos : 0 < 1 / Real.sin (ε / 2) := one_div_pos.mpr hsinε
  have hcot : Real.sqrt (1 + Real.cot (ε / 2) ^ 2) = 1 / Real.sin (ε / 2) := by
    rw [cot_sq_add_one (ne_of_gt hsinε)]
    rw [show (1 : ℝ) / Real.sin (ε / 2) ^ 2 = (1 / Real.sin (ε / 2)) ^ 2 by ring]
    rw [Real.sqrt_sq (le_of_lt hsinpos)]
  have hsqrtS : Real.sqrt S ≤ (1 / Real.sin (ε / 2)) * Real.sqrt t := by
    calc Real.sqrt S ≤ Real.sqrt ((1 + Real.cot (ε / 2) ^ 2) * t) := Real.sqrt_le_sqrt hS
      _ = Real.sqrt (1 + Real.cot (ε / 2) ^ 2) * Real.sqrt t :=
            Real.sqrt_mul (by positivity) t
      _ = (1 / Real.sin (ε / 2)) * Real.sqrt t := by rw [hcot]
  have hcoef : 0 ≤ t / 4 * ε :=
    mul_nonneg (div_nonneg ht0 (by norm_num)) (le_of_lt hε)
  have hstep : min (t / 2) (t / 4 * ε) * Real.sqrt S
      ≤ (t / 4 * ε) * ((1 / Real.sin (ε / 2)) * Real.sqrt t) := by
    refine le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)) ?_
    exact mul_le_mul_of_nonneg_left hsqrtS hcoef
  refine le_trans hstep ?_
  have hsin : ε / 4 ≤ Real.sin (ε / 2) := by
    have hε2 : 0 < ε / 2 := by linarith
    have hπε : ε / 2 ≤ Real.pi / 2 := by linarith
    rcases lt_or_eq_of_le hπε with hlt | heq
    · have hmul := Real.mul_lt_sin hε2 hlt
      have h4 : ε / Real.pi < Real.sin (ε / 2) := by
        have := hmul
        rwa [show 2 / Real.pi * (ε / 2) = ε / Real.pi by
          field_simp [Real.pi_ne_zero]] at this
      have h3 : ε / 4 ≤ ε / Real.pi := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) (by positivity : (0 : ℝ) < Real.pi)]
        exact mul_le_mul_of_nonneg_left Real.pi_le_four (le_of_lt hε)
      linarith
    · rw [heq, Real.sin_pi_div_two]
      have : ε / 4 ≤ 1 := by nlinarith [heq, Real.pi_le_four]
      linarith
  have hsq : Real.sqrt t ≤ 1 := by
    have h := Real.sqrt_le_sqrt ht1
    simpa using! h
  have hb : ε * Real.sqrt t ≤ 4 * Real.sin (ε / 2) := by
    have h1 : ε * Real.sqrt t ≤ ε * 1 :=
      mul_le_mul_of_nonneg_left hsq (le_of_lt hε)
    have h2 : ε ≤ 4 * Real.sin (ε / 2) := by linarith
    linarith
  have hden : 0 < 4 * Real.sin (ε / 2) := mul_pos (by norm_num) hsinε
  have hx : ε * Real.sqrt t / (4 * Real.sin (ε / 2)) ≤ 1 := by
    rw [div_le_one hden]
    exact hb
  have heq2 : (t / 4 * ε) * ((1 / Real.sin (ε / 2)) * Real.sqrt t)
      = t * (ε * Real.sqrt t / (4 * Real.sin (ε / 2))) := by
    field_simp [ne_of_gt hsinε]
  rw [heq2]
  exact mul_le_of_le_one_right ht0 hx

/-- Establishes the normalized endpoint overlap bound in `Claim6Statement` from its orthonormal
spectral expansion and phase-gap assumptions, corresponding to Claim 6 of
[Ambainis2007ElementDistinctness]. -/
theorem claim6 : Claim6Statement := by
  intro m l α ε start good a θ w hstart hgood hw horth hstartorth hstartre hare
    hstr hgoodexp hε hθ
  let vend : Fin m → ℂ := fun i => ∑ j, a j *
      ((1 + Complex.I * (Real.cot (θ j / 2) : ℂ)) * w j true i +
        (1 - Complex.I * (Real.cot (θ j / 2) : ℂ)) * w j false i)
  have hvend : vend = fun i => ∑ j, a j *
      ((1 + Complex.I * (Real.cot (θ j / 2) : ℂ)) * w j true i +
        (1 - Complex.I * (Real.cot (θ j / 2) : ℂ)) * w j false i) := rfl
  change min ((1 - α ^ 2) / 2) ((1 - α ^ 2) / 4 * ε) ≤
    ‖∑ i, star (good i) * vend i‖ / Real.sqrt (∑ i, ‖vend i‖ ^ 2)
  set S : ℝ := ∑ i, ‖vend i‖ ^ 2 with hSdef
  set t : ℝ := 1 - α ^ 2 with htdef
  set S0 : Fin m → ℂ := fun i => (α : ℂ) * start i with hS0
  set A : Fin l → Fin m → ℂ := fun j i => a j * (w j true i + w j false i) with hA
  set u : Fin l → Fin m → ℂ := fun j =>
      (1 + Complex.I * (Real.cot (θ j / 2) : ℂ)) • w j true +
        (1 - Complex.I * (Real.cot (θ j / 2) : ℂ)) • w j false with hu
  set B : Fin l → Fin m → ℂ := fun j i => a j * u j i with hB
  set ar : Fin l → ℝ := fun j => (a j).re with har
  set q : ℝ := ∑ j, (ar j) ^ 2 with hqdef

  have hgood_eq : good = S0 + ∑ j, A j := by
    funext i
    rw [hS0, hA]
    simpa [Pi.add_apply, Pi.smul_apply, Finset.sum_apply] using! hgoodexp i
  have hvend_eq : vend = ∑ j, B j := by
    funext i
    rw [hvend, hB, hu]
    simp [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hA_eq : ∀ j, A j = a j • (w j true + w j false) := by
    intro j
    funext i
    simp [hA, Pi.smul_apply, mul_add, smul_eq_mul]
  have hB_eq : ∀ j, B j = a j • u j := by
    intro j
    funext i
    simp [hB, Pi.smul_apply, smul_eq_mul]
  have hS0_eq : S0 = (α : ℂ) • start := by
    funext i
    simp [hS0, Pi.smul_apply, smul_eq_mul]

  have hwn : ∀ (j : Fin l) (s : Bool), cdot (w j s) (w j s) = 1 := by
    intro j s
    rw [cdot_self_eq, hw j s]
    norm_num
  have hstart_w : ∀ (j : Fin l) (s : Bool), cdot start (w j s) = 0 := by
    intro j s
    rw [cdot_conj_symm,
      show cdot (w j s) start = 0 from hstartorth j s]
    simp
  have hstart_u : ∀ j : Fin l, cdot start (u j) = 0 := by
    intro j
    rw [hu]
    simp only [cdot_add_right, cdot_smul_right]
    rw [hstart_w j true, hstart_w j false]
    ring
  have hpair : ∀ {j j' : Fin l} (s s' : Bool), j ≠ j' → (j, s) ≠ (j', s') := by
    intro j j' s s' hne h
    exact hne (congrArg Prod.fst h)
  have horthc : ∀ (j j' : Fin l) (s s' : Bool), (j, s) ≠ (j', s') →
      cdot (w j s) (w j' s') = 0 := by
    intro j j' s s' h
    exact horth j j' s s' h

  have hww_diag : ∀ j : Fin l,
      cdot (w j true + w j false) (w j true + w j false) = 2 := by
    intro j
    simp only [cdot_add_left, cdot_add_right, hwn j true, hwn j false,
      horthc j j true false (by simp), horthc j j false true (by simp)]
    ring
  have hAA_diag : ∀ j : Fin l, cdot (A j) (A j) = 2 * (star (a j) * a j) := by
    intro j
    rw [hA_eq j, cdot_smul_smul, hww_diag j]
    ring
  have hAA_orth : ∀ (j j' : Fin l), j ≠ j' → cdot (A j) (A j') = 0 := by
    intro j j' hne
    simp only [hA_eq j, hA_eq j', cdot_smul_smul, cdot_add_left, cdot_add_right,
      horthc j j' true true (hpair true true hne),
      horthc j j' true false (hpair true false hne),
      horthc j j' false true (hpair false true hne),
      horthc j j' false false (hpair false false hne)]
    ring_nf
  have hS0A : ∀ j : Fin l, cdot S0 (A j) = 0 := by
    intro j
    simp only [hS0_eq, hA_eq j, cdot_smul_smul, cdot_add_right,
      hstart_w j true, hstart_w j false]
    ring
  have hAS0 : ∀ j : Fin l, cdot (A j) S0 = 0 := by
    intro j
    rw [cdot_conj_symm, hS0A j, star_zero]

  have hconj : ∀ c : ℝ,
      star (1 + Complex.I * (c : ℂ)) * (1 + Complex.I * (c : ℂ)) = ((1 + c ^ 2 : ℝ) : ℂ) := by
    intro c
    apply Complex.ext <;>
      simp [star_eq_conj, Complex.mul_re,
        Complex.mul_im, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        - Complex.ofReal_pow] <;>
      ring
  have hconj' : ∀ c : ℝ,
      star (1 - Complex.I * (c : ℂ)) * (1 - Complex.I * (c : ℂ)) = ((1 + c ^ 2 : ℝ) : ℂ) := by
    intro c
    apply Complex.ext <;>
      simp [star_eq_conj, Complex.mul_re,
        Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        - Complex.ofReal_pow] <;>
      ring
  have huu_diag : ∀ j : Fin l,
      cdot (u j) (u j) = ((2 * (1 + Real.cot (θ j / 2) ^ 2) : ℝ) : ℂ) := by
    intro j
    simp only [hu, cdot_add_left, cdot_add_right, cdot_smul_smul,
      hwn j true, hwn j false, horthc j j true false (by simp),
      horthc j j false true (by simp), mul_one, mul_zero, add_zero, zero_add,
      hconj (Real.cot (θ j / 2)), hconj' (Real.cot (θ j / 2))]
    push_cast
    ring
  have huu_orth : ∀ (j j' : Fin l), j ≠ j' → cdot (u j) (u j') = 0 := by
    intro j j' hne
    simp only [hu, cdot_add_left, cdot_add_right, cdot_smul_smul,
      horthc j j' true true (hpair true true hne),
      horthc j j' true false (hpair true false hne),
      horthc j j' false true (hpair false true hne),
      horthc j j' false false (hpair false false hne)]
    ring_nf
  have hu_diag : ∀ j : Fin l, cdot (w j true + w j false) (u j) = 2 := by
    intro j
    simp only [hu, cdot_add_left, cdot_add_right, cdot_smul_right,
      hwn j true, hwn j false, horthc j j true false (by simp),
      horthc j j false true (by simp)]
    ring
  have hBB_diag : ∀ j : Fin l,
      cdot (B j) (B j) = (star (a j) * a j) * ((2 * (1 + Real.cot (θ j / 2) ^ 2) : ℝ) : ℂ) := by
    intro j
    rw [hB_eq j, cdot_smul_smul, huu_diag j]
    ring
  have hBB_orth : ∀ (j j' : Fin l), j ≠ j' → cdot (B j) (B j') = 0 := by
    intro j j' hne
    rw [hB_eq j, hB_eq j', cdot_smul_smul, huu_orth j j' hne]
    ring
  have hAB_diag : ∀ j : Fin l, cdot (A j) (B j) = 2 * (star (a j) * a j) := by
    intro j
    rw [hA_eq j, hB_eq j, cdot_smul_smul, hu_diag j]
    ring
  have hAB_orth : ∀ (j j' : Fin l), j ≠ j' → cdot (A j) (B j') = 0 := by
    intro j j' hne
    simp only [hA_eq j, hB_eq j', hu, cdot_smul_left, cdot_smul_right,
      cdot_add_left, cdot_add_right,
      horthc j j' true true (hpair true true hne),
      horthc j j' true false (hpair true false hne),
      horthc j j' false true (hpair false true hne),
      horthc j j' false false (hpair false false hne)]
    ring_nf
  have hS0B : ∀ j : Fin l, cdot S0 (B j) = 0 := by
    intro j
    rw [hS0_eq, hB_eq j, cdot_smul_smul, hstart_u j]
    ring

  have ha_real : ∀ j : Fin l, a j = ((ar j : ℝ) : ℂ) := by
    intro j
    apply Complex.ext
    · simp [har]
    · simp [har, hare j]
  have hterm2 : ∀ j : Fin l,
      2 * (star (a j) * a j) = ((2 * (ar j) ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [ha_real j]
    simp only [star_eq_conj, Complex.conj_ofReal]
    push_cast
    ring
  have htermB : ∀ j : Fin l,
      (star (a j) * a j) * ((2 * (1 + Real.cot (θ j / 2) ^ 2) : ℝ) : ℂ)
        = ((2 * (ar j) ^ 2 * (1 + Real.cot (θ j / 2) ^ 2) : ℝ) : ℂ) := by
    intro j
    rw [ha_real j]
    simp only [star_eq_conj, Complex.conj_ofReal]
    push_cast
    ring
  have hsum2a : ∑ j, 2 * (star (a j) * a j) = ((2 * q : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun j _ => hterm2 j)]
    rw [← Complex.ofReal_sum (s := Finset.univ) (f := fun j => 2 * (ar j) ^ 2)]
    congr 1
    rw [hqdef, Finset.mul_sum]
  have hsumB : ∑ j, (star (a j) * a j) * ((2 * (1 + Real.cot (θ j / 2) ^ 2) : ℝ) : ℂ)
      = ((∑ j, 2 * (ar j) ^ 2 * (1 + Real.cot (θ j / 2) ^ 2) : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun j _ => htermB j)]
    rw [← Complex.ofReal_sum (s := Finset.univ)
      (f := fun j => 2 * (ar j) ^ 2 * (1 + Real.cot (θ j / 2) ^ 2))]

  have hgg : cdot good good = 1 := by
    rw [cdot_self_eq, hgood]
    norm_num
  have hpairA : ∀ j : Fin l, cdot (A j) (∑ j', A j') = cdot (A j) (A j) := by
    intro j
    rw [cdot_sum_right]
    exact Finset.sum_eq_single j (fun b _ hb => hAA_orth j b (Ne.symm hb))
      (fun hmem => absurd (Finset.mem_univ j) hmem)
  have hAA_sum : cdot (∑ j, A j) (∑ j', A j') = ∑ j, 2 * (star (a j) * a j) := by
    rw [cdot_sum_left]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hpairA j, hAA_diag j]
  have hS0A_sum : cdot S0 (∑ j, A j) = 0 := by
    rw [cdot_sum_right]
    exact Finset.sum_eq_zero (fun j _ => hS0A j)
  have hAS0_sum : cdot (∑ j, A j) S0 = 0 := by
    rw [cdot_sum_left]
    exact Finset.sum_eq_zero (fun j _ => hAS0 j)
  have hS0S0 : cdot S0 S0 = ((α ^ 2 : ℝ) : ℂ) := by
    rw [hS0_eq, cdot_smul_smul, cdot_self_eq, hstart]
    simp only [star_eq_conj, Complex.conj_ofReal]
    push_cast
    ring
  have hgg_expand : cdot good good
      = ((α ^ 2 : ℝ) : ℂ) + ∑ j, 2 * (star (a j) * a j) := by
    simp only [hgood_eq, cdot_add_left, cdot_add_right,
      hS0S0, hS0A_sum, hAS0_sum, hAA_sum]
    ring

  have hreal : α ^ 2 + 2 * q = 1 := by
    have h1 := hgg_expand
    rw [hgg, hsum2a] at h1
    have h2 : ((α ^ 2 + 2 * q : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_add]
      exact h1.symm
    exact Complex.ofReal_injective (by rw [Complex.ofReal_one]; exact h2)
  have ht_eq : t = 2 * q := by
    rw [htdef]
    linarith

  have hpairAB : ∀ j : Fin l, cdot (A j) (∑ j', B j') = cdot (A j) (B j) := by
    intro j
    rw [cdot_sum_right]
    exact Finset.sum_eq_single j (fun b _ hb => hAB_orth j b (Ne.symm hb))
      (fun hmem => absurd (Finset.mem_univ j) hmem)
  have hS0B_sum : cdot S0 (∑ j, B j) = 0 := by
    rw [cdot_sum_right]
    exact Finset.sum_eq_zero (fun j _ => hS0B j)
  have hgood_vend : cdot good vend = ((t : ℝ) : ℂ) := by
    have h1 : cdot good vend = ((2 * q : ℝ) : ℂ) := by
      rw [hgood_eq, hvend_eq, cdot_add_left, hS0B_sum, zero_add, cdot_sum_left]
      refine Eq.trans (Finset.sum_congr rfl (fun j _ => ?_)) hsum2a
      rw [hpairAB j, hAB_diag j]
    rw [h1, ht_eq]

  have hpairB : ∀ j : Fin l, cdot (B j) (∑ j', B j') = cdot (B j) (B j) := by
    intro j
    rw [cdot_sum_right]
    exact Finset.sum_eq_single j (fun b _ hb => hBB_orth j b (Ne.symm hb))
      (fun hmem => absurd (Finset.mem_univ j) hmem)
  have hBB_sum : cdot (∑ j, B j) (∑ j', B j')
      = ∑ j, (star (a j) * a j) * ((2 * (1 + Real.cot (θ j / 2) ^ 2) : ℝ) : ℂ) := by
    rw [cdot_sum_left]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hpairB j, hBB_diag j]
  have hS_eq : S = ∑ j, 2 * (ar j) ^ 2 * (1 + Real.cot (θ j / 2) ^ 2) := by
    have h1 : cdot vend vend = ((S : ℝ) : ℂ) := by
      rw [hSdef, cdot_self_eq]
    have h2 : cdot vend vend
        = ((∑ j, 2 * (ar j) ^ 2 * (1 + Real.cot (θ j / 2) ^ 2) : ℝ) : ℂ) := by
      rw [hvend_eq, hBB_sum, hsumB]
    rw [h1] at h2
    exact Complex.ofReal_injective h2
  have h2q : (∑ j, 2 * (ar j) ^ 2) = 2 * q := by
    rw [hqdef, Finset.mul_sum]

  have hS_bound : S ≤ (1 + Real.cot (ε / 2) ^ 2) * t := by
    rw [hS_eq, ht_eq, ← h2q, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hc : (1 + Real.cot (θ j / 2) ^ 2) ≤ (1 + Real.cot (ε / 2) ^ 2) := by
      linarith [cot_sq_le hε (hθ j).1 (hθ j).2]
    have h0 : 0 ≤ 2 * (ar j) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hc h0]
  have hS0' : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun i _ => by positivity)
  have hq0 : 0 ≤ q := by
    rw [hqdef]
    exact Finset.sum_nonneg (fun j _ => sq_nonneg (ar j))
  have ht0 : 0 ≤ t := by
    rw [ht_eq]
    exact mul_nonneg (by norm_num) hq0
  have ht1 : t ≤ 1 := by
    rw [ht_eq]
    nlinarith [sq_nonneg α, hreal]
  have htS : t ≤ S := by
    rw [hS_eq, ht_eq, ← h2q]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have h1 : 0 ≤ (ar j) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ Real.cot (θ j / 2) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg h1 h2]
  have hnorm : ‖∑ i, star (good i) * vend i‖ = t := by
    change ‖cdot good vend‖ = t
    rw [hgood_vend, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  rcases eq_or_lt_of_le ht0 with htz | ht
  · rw [hnorm, ← htz]
    simp
  · have hl : 0 < l := by
      rcases Nat.eq_zero_or_pos l with hl0 | hl
      · exfalso
        subst hl0
        rw [hqdef] at ht_eq
        simp at ht_eq
        rw [ht_eq] at ht
        exact absurd ht (lt_irrefl 0)
      · exact hl
    have hεpi : ε ≤ Real.pi := by
      have h0 := hθ ⟨0, hl⟩
      linarith [h0.2, Real.pi_pos]
    rw [hnorm]
    exact claim6_final hε hεpi ht0 ht1 hS0' htS hS_bound

end

end Qatlib.Concepts.WalkFind.GroverInterp
