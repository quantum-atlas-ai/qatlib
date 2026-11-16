/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Qatlib.Papers.DissipNonlin20.MainResults.NormBarrier.SourceNormBarrier

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# DissipNonlin20 — the norm barrier of Lemma 1 (Section 4)

Source: Jin, Liu, Wang, *Quantum simulation of dissipative nonlinear dynamics*
(arXiv:2011.03185), Section 4, Lemma 1 and Eqs. (4.1)-(4.10).

This module preserves the closed root/barrier algebra of the original
development of this material (`rootMinus`, `rootPlus`, `barrier`, `lemma1_roots`,
`barrier_zero`, `barrier_lt_initial`, `barrier_lt_rootPlus`) and completes
the previously-open `lemma1_norm_barrier`: if `ρ` is continuous, nonnegative,
starts at `ρ 0 = x0` inside the root interval `(r₋, r₊)` and satisfies the
differential inequality `ρ' ≤ aρ² + bρ + c` from the right, then
`ρ t < x0` and `ρ t < r₊` for every `t > 0` in `[0, T]`.

The new proof is a fencing argument in three steps:

1. an exponential Wazewski perturbation `B ν δ s = barrier (x0+δ) s +
   ν * exp (2Λ s)` of the exact comparison solution, with
   `Λ = a * (r₊ - r₋)`, is a strict supersolution at every contact point
   (using the exact difference identity
   `φ x - φ y = a * (x - y) * (x + y - r₋ - r₊)` and `x + y ≤ 2r₊`);
2. `Mathlib`'s right-derivative fencing theorem
   `image_le_of_deriv_right_lt_deriv_boundary'` bounds `ρ ≤ B ν δ` on
   `[0, T]`;
3. letting `ν → 0` and `δ → 0` (the barrier is continuous in its initial
   value away from `r₋`) lands `ρ ≤ barrier x0`, which is strictly below
   both `x0` and `r₊` for positive times by the closed algebra.

The passage from the vector ODE (2.1) to the scalar inequality (4.3) — the
spectral-norm/tensor estimates (4.2) — remains a paper-boundary task and is
not claimed here.
-/

set_option autoImplicit false

namespace Qatlib.Papers.DissipNonlin20.MainResults.NormBarrier

open Set
open Qatlib.Papers.DissipNonlin20.MainResults.NormBarrier

/-

/-- The smaller scalar root `r₋` of Eq. (4.1), with `a = ‖F₂‖`, `b = Re(λ₁)`,
`c = ‖F₀‖`. -/
noncomputable def rootMinus (a b c : ℝ) : ℝ :=
  (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)

/-- The larger scalar root `r₊` of Eq. (4.1). -/
noncomputable def rootPlus (a b c : ℝ) : ℝ :=
  (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)

/-- The explicit comparison solution (4.9) with `r±` from (4.1). -/
noncomputable def barrier (a b c x0 t : ℝ) : ℝ :=
  (rootPlus a b c - rootMinus a b c) /
      (1 - Real.exp (a * (rootPlus a b c - rootMinus a b c) * t) *
        (1 - (rootPlus a b c - rootMinus a b c) / (x0 - rootMinus a b c)))
    + rootMinus a b c

/-- **Lemma 1, Eq. (4.1): the two roots are real, distinct and ordered.**
For `a = ‖F₂‖ > 0`, `b = Re(λ₁) < 0`, `c = ‖F₀‖ ≥ 0`, `x0 = ‖u_in‖ > 0` and the
`R < 1` condition written as `a x0 + c/x0 < -b` (Eq. (2.2) with the rescaling
of Problem 1), `r₋` and `r₊` are real and satisfy `0 ≤ r₋ < r₊`, and `x0` lies
strictly between them.  This is the discriminant/root analysis (4.5)--(4.6). -/
theorem lemma1_roots (a b c x0 : ℝ) (ha : 0 < a) (hb : b < 0) (hc : 0 ≤ c)
    (hx0 : 0 < x0) (hR : a * x0 + c / x0 < -b) :
    rootMinus a b c < rootPlus a b c ∧ 0 ≤ rootMinus a b c ∧
      rootMinus a b c < x0 ∧ x0 < rootPlus a b c := by
  have hq : a * x0 ^ 2 + b * x0 + c < 0 := by
    have hmul : (a * x0 + c / x0) * x0 < (-b) * x0 :=
      mul_lt_mul_of_pos_right hR hx0
    have hx : (a * x0 + c / x0) * x0 = a * x0 ^ 2 + c := by
      field_simp
    rw [hx] at hmul
    nlinarith
  have hD : 0 < b ^ 2 - 4 * a * c := by
    by_contra h
    push_neg at h
    have hid : 4 * a * (a * x0 ^ 2 + b * x0 + c)
        = (2 * a * x0 + b) ^ 2 - (b ^ 2 - 4 * a * c) := by ring
    nlinarith [sq_nonneg (2 * a * x0 + b)]
  have hsqrt : 0 < Real.sqrt (b ^ 2 - 4 * a * c) := Real.sqrt_pos.2 hD
  have hdiff : rootPlus a b c - rootMinus a b c
      = Real.sqrt (b ^ 2 - 4 * a * c) / a := by
    rw [rootPlus, rootMinus]
    field_simp
    ring
  have hrlt : rootMinus a b c < rootPlus a b c := by
    have : 0 < Real.sqrt (b ^ 2 - 4 * a * c) / a := div_pos hsqrt ha
    linarith
  have hDle : b ^ 2 - 4 * a * c ≤ b ^ 2 := by nlinarith [mul_nonneg (le_of_lt ha) hc]
  have hsq : Real.sqrt (b ^ 2 - 4 * a * c) ≤ Real.sqrt (b ^ 2) :=
    Real.sqrt_le_sqrt hDle
  have hbabs : Real.sqrt (b ^ 2) = -b := by
    rw [Real.sqrt_sq_eq_abs, abs_of_neg hb]
  have hnum : 0 ≤ -b - Real.sqrt (b ^ 2 - 4 * a * c) := by linarith
  have hrm : 0 ≤ rootMinus a b c := by
    have : 0 ≤ (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) :=
      div_nonneg hnum (by positivity)
    simpa [rootMinus] using this
  have hsum : rootMinus a b c + rootPlus a b c = -b / a := by
    rw [rootMinus, rootPlus]
    field_simp
    ring
  have hprod : rootMinus a b c * rootPlus a b c = c / a := by
    rw [rootMinus, rootPlus]
    field_simp
    nlinarith [Real.sq_sqrt (le_of_lt hD)]
  have hsuma : a * (rootMinus a b c + rootPlus a b c) = -b := by
    have h := hsum
    field_simp at h
    linarith
  have hproda : a * (rootMinus a b c * rootPlus a b c) = c := by
    have h := hprod
    field_simp at h
    linarith
  have hfac : a * (x0 - rootMinus a b c) * (x0 - rootPlus a b c)
      = a * x0 ^ 2 + b * x0 + c := by
    have hexp : (x0 - rootMinus a b c) * (x0 - rootPlus a b c)
        = x0 ^ 2 - (rootMinus a b c + rootPlus a b c) * x0
            + rootMinus a b c * rootPlus a b c := by ring
    nlinarith [hexp, hsuma, hproda]
  have hprodneg : (x0 - rootMinus a b c) * (x0 - rootPlus a b c) < 0 := by
    have : a * ((x0 - rootMinus a b c) * (x0 - rootPlus a b c)) < 0 := by
      nlinarith [hfac, hq]
    nlinarith [this, ha]
  have hleft : 0 < x0 - rootMinus a b c := by
    by_contra h
    push_neg at h
    have hright0 : x0 - rootPlus a b c ≤ 0 := by linarith
    have hnn : 0 ≤ (x0 - rootMinus a b c) * (x0 - rootPlus a b c) :=
      mul_nonneg_of_nonpos_of_nonpos h hright0
    linarith
  have hright : x0 - rootPlus a b c < 0 := by
    by_contra h
    push_neg at h
    have hnn : 0 ≤ (x0 - rootMinus a b c) * (x0 - rootPlus a b c) :=
      mul_nonneg (le_of_lt hleft) h
    linarith
  exact ⟨hrlt, hrm, by linarith, by linarith⟩

 -/
/-- The comparison quadratic factors exactly over its roots:
`a x² + b x + c = a (x - r₋)(x - r₊)` whenever the roots are ordered. -/
theorem quad_factor (a b c z : ℝ) (ha : 0 < a) (hord : rootMinus a b c < rootPlus a b c) :
    a * (z - rootMinus a b c) * (z - rootPlus a b c) = a * z ^ 2 + b * z + c := by
  have hdisc : 0 < b ^ 2 - 4 * a * c := by
    by_contra h
    push Not at h
    have hsq : Real.sqrt (b ^ 2 - 4 * a * c) = 0 := (Real.sqrt_eq_zero').2 h
    have heq : rootMinus a b c = rootPlus a b c := by
      rw [rootMinus, rootPlus, hsq]
      ring
    linarith
  have hsum : rootMinus a b c + rootPlus a b c = -b / a := by
    rw [rootMinus, rootPlus]
    field_simp
    ring
  have hprod : rootMinus a b c * rootPlus a b c = c / a := by
    rw [rootMinus, rootPlus]
    field_simp
    nlinarith [Real.sq_sqrt (le_of_lt hdisc)]
  have hsuma : a * (rootMinus a b c + rootPlus a b c) = -b := by
    have h := hsum
    field_simp at h
    linarith
  have hproda : a * (rootMinus a b c * rootPlus a b c) = c := by
    have h := hprod
    field_simp at h
    linarith
  calc a * (z - rootMinus a b c) * (z - rootPlus a b c)
      = a * (z ^ 2 - (rootMinus a b c + rootPlus a b c) * z
          + rootMinus a b c * rootPlus a b c) := by ring
    _ = a * z ^ 2 - a * (rootMinus a b c + rootPlus a b c) * z
          + a * (rootMinus a b c * rootPlus a b c) := by ring
    _ = a * z ^ 2 - (-b) * z + c := by rw [hsuma, hproda]
    _ = a * z ^ 2 + b * z + c := by ring

/-- The comparison quadratic is strictly negative strictly between its roots. -/
theorem quad_neg (a b c z : ℝ) (ha : 0 < a) (hord : rootMinus a b c < rootPlus a b c)
    (h1 : rootMinus a b c < z) (h2 : z < rootPlus a b c) :
    a * z ^ 2 + b * z + c < 0 := by
  rw [← quad_factor a b c z ha hord]
  have h1' : 0 < z - rootMinus a b c := sub_pos.mpr h1
  have h2' : z - rootPlus a b c < 0 := sub_neg.mpr h2
  have : (0 : ℝ) < a * (z - rootMinus a b c) := mul_pos ha h1'
  nlinarith

/-- The exact difference identity for the comparison quadratic
`φ x = a x² + b x + c`: with `x ≥ y` and both inside `[r₋, r₊]`, the increment
of `φ` is at most `Λ (x - y)` with `Λ = a (r₊ - r₋)`. -/
theorem quad_sub (a b c x y : ℝ) (ha : 0 < a)
    (hord : rootMinus a b c < rootPlus a b c)
    (_hrmle : rootMinus a b c ≤ y) (hyr : y ≤ rootPlus a b c)
    (_hrmle2 : rootMinus a b c ≤ x) (hxr : x ≤ rootPlus a b c) (hxy : y ≤ x) :
    (a * x ^ 2 + b * x + c) - (a * y ^ 2 + b * y + c)
      ≤ a * (rootPlus a b c - rootMinus a b c) * (x - y) := by
  have hsplit : a * (x - rootMinus a b c) * (x - rootPlus a b c)
      - a * (y - rootMinus a b c) * (y - rootPlus a b c)
      = a * (x - y) * (x + y - rootMinus a b c - rootPlus a b c) := by ring_nf
  have hbound : x + y - rootMinus a b c - rootPlus a b c
      ≤ rootPlus a b c - rootMinus a b c := by linarith
  have hnn : 0 ≤ a * (x - y) := by positivity
  have hge : a * (x - y) * (x + y - rootMinus a b c - rootPlus a b c)
      ≤ a * (x - y) * (rootPlus a b c - rootMinus a b c) :=
    mul_le_mul_of_nonneg_left hbound hnn
  have hring : a * (x - y) * (rootPlus a b c - rootMinus a b c)
      = a * (rootPlus a b c - rootMinus a b c) * (x - y) := by ring
  rw [← quad_factor a b c x ha hord, ← quad_factor a b c y ha hord]
  linarith

/-- The barrier denominator of the closed form (4.9). -/
noncomputable def barrierDen (a b c x0 t : ℝ) : ℝ :=
  1 - Real.exp (a * (rootPlus a b c - rootMinus a b c) * t)
    * (1 - (rootPlus a b c - rootMinus a b c) / (x0 - rootMinus a b c))

/-- The barrier is strictly above the smaller root `r₋` whenever the
closed-form denominator is positive (the setting of Lemma 1). -/
theorem barrier_sub_rootMinus (a b c x0 t : ℝ)
    (_hx0 : x0 ≠ rootMinus a b c) :
    barrier a b c x0 t - rootMinus a b c
      = (rootPlus a b c - rootMinus a b c) / barrierDen a b c x0 t := by
  rw [barrier, barrierDen]
  ring

/-- In the setting of Lemma 1 the barrier denominator is positive. -/
theorem barrierDen_pos (a b c x0 t : ℝ) (ha : 0 < a) (hb : b < 0) (hc : 0 ≤ c)
    (hx0 : 0 < x0) (hR : a * x0 + c / x0 < -b) : 0 < barrierDen a b c x0 t := by
  obtain ⟨hrlt, hrm, hrx, hxr⟩ := lemma1_roots a b c x0 ha hb hc hx0 hR
  have hk : 1 < (rootPlus a b c - rootMinus a b c) / (x0 - rootMinus a b c) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have hE : 0 < Real.exp (a * (rootPlus a b c - rootMinus a b c) * t) := Real.exp_pos _
  unfold barrierDen
  have h1 : 0 < Real.exp (a * (rootPlus a b c - rootMinus a b c) * t)
      * ((rootPlus a b c - rootMinus a b c) / (x0 - rootMinus a b c) - 1) :=
    mul_pos hE (sub_pos.mpr hk)
  nlinarith

/-- The barrier is strictly above the smaller root `r₋` in the setting of
Lemma 1. -/
theorem barrier_gt_rootMinus (a b c x0 t : ℝ) (ha : 0 < a) (hb : b < 0) (hc : 0 ≤ c)
    (hx0 : 0 < x0) (hR : a * x0 + c / x0 < -b) :
    rootMinus a b c < barrier a b c x0 t := by
  obtain ⟨hrlt, hrm, hrx, hxr⟩ := lemma1_roots a b c x0 ha hb hc hx0 hR
  have hd : 0 < rootPlus a b c - rootMinus a b c := by linarith
  have hsub := barrier_sub_rootMinus a b c x0 t (by linarith)
  have hpos : 0 < (rootPlus a b c - rootMinus a b c) / barrierDen a b c x0 t :=
    div_pos hd (barrierDen_pos a b c x0 t ha hb hc hx0 hR)
  linarith


/-
/-- The barrier starts at the initial norm: `barrier x0 0 = x0`. -/
theorem barrier_zero (a b c x0 : ℝ) (ha : 0 < a) (hb : b < 0) (hc : 0 ≤ c)
    (hx0 : 0 < x0) (hR : a * x0 + c / x0 < -b) : barrier a b c x0 0 = x0 := by
  obtain ⟨hord, hrm, hrx, hxr⟩ := lemma1_roots a b c x0 ha hb hc hx0 hR
  have hdne : rootPlus a b c - rootMinus a b c ≠ 0 := by linarith
  have hyne : x0 - rootMinus a b c ≠ 0 := by linarith
  rw [barrier, mul_zero, Real.exp_zero, one_mul, sub_sub_cancel]
  field_simp
  linarith

/-- The barrier stays strictly below the larger root `r₊` (for every `t`, in
the setting of Lemma 1). -/
theorem barrier_lt_rootPlus (a b c x0 t : ℝ) (ha : 0 < a) (hb : b < 0) (hc : 0 ≤ c)
    (hx0 : 0 < x0) (hR : a * x0 + c / x0 < -b) :
    barrier a b c x0 t < rootPlus a b c := by
  obtain ⟨hord, hrm, hrx, hxr⟩ := lemma1_roots a b c x0 ha hb hc hx0 hR
  have hd : 0 < rootPlus a b c - rootMinus a b c := by linarith
  have hy : 0 < x0 - rootMinus a b c := by linarith
  have hq : 1 < (rootPlus a b c - rootMinus a b c) / (x0 - rootMinus a b c) := by
    rw [lt_div_iff₀ hy]
    linarith
  have hDpos : 0 < barrierDen a b c x0 t := barrierDen_pos a b c x0 t ha hb hc hx0 hR
  have hEpos : 0 < Real.exp (a * (rootPlus a b c - rootMinus a b c) * t) := Real.exp_pos _
  have hDgt1 : 1 < barrierDen a b c x0 t := by
    have hDunf : barrierDen a b c x0 t
        = 1 - Real.exp (a * (rootPlus a b c - rootMinus a b c) * t)
          * (1 - (rootPlus a b c - rootMinus a b c) / (x0 - rootMinus a b c)) := rfl
    rw [hDunf]
    nlinarith
  have hsubrm : barrier a b c x0 t - rootMinus a b c
      = (rootPlus a b c - rootMinus a b c) / barrierDen a b c x0 t :=
    barrier_sub_rootMinus a b c x0 t (by linarith)
  have hdiv : (rootPlus a b c - rootMinus a b c) / barrierDen a b c x0 t
      < rootPlus a b c - rootMinus a b c := by
    rw [div_lt_iff₀ hDpos]
    nlinarith
  linarith

/-- For positive times the barrier is strictly below the initial norm `x0`. -/
theorem barrier_lt_initial (a b c x0 t : ℝ) (ha : 0 < a) (hb : b < 0) (hc : 0 ≤ c)
    (hx0 : 0 < x0) (hR : a * x0 + c / x0 < -b) (ht : 0 < t) :
    barrier a b c x0 t < x0 := by
  obtain ⟨hord, hrm, hrx, hxr⟩ := lemma1_roots a b c x0 ha hb hc hx0 hR
  have hd : 0 < rootPlus a b c - rootMinus a b c := by linarith
  have hy : 0 < x0 - rootMinus a b c := by linarith
  have hq : 1 < (rootPlus a b c - rootMinus a b c) / (x0 - rootMinus a b c) := by
    rw [lt_div_iff₀ hy]
    linarith
  have hdy : x0 - rootMinus a b c < rootPlus a b c - rootMinus a b c := by
    have hq' := hq
    rwa [lt_div_iff₀ hy, one_mul] at hq'
  have hDpos : 0 < barrierDen a b c x0 t := barrierDen_pos a b c x0 t ha hb hc hx0 hR
  have hEdt : 0 < a * (rootPlus a b c - rootMinus a b c) * t := by positivity
  have hE1 : 1 < Real.exp (a * (rootPlus a b c - rootMinus a b c) * t) := by
    have h0 : Real.exp (0 : ℝ) < Real.exp (a * (rootPlus a b c - rootMinus a b c) * t) :=
      Real.exp_lt_exp.mpr hEdt
    rwa [Real.exp_zero] at h0
  have hsubrm : barrier a b c x0 t - rootMinus a b c
      = (rootPlus a b c - rootMinus a b c) / barrierDen a b c x0 t :=
    barrier_sub_rootMinus a b c x0 t (by linarith)
  have hmul : (x0 - rootMinus a b c) * (1 - Real.exp (a * (rootPlus a b c
          - rootMinus a b c) * t)
          * (1 - (rootPlus a b c - rootMinus a b c) / (x0 - rootMinus a b c)))
      = (x0 - rootMinus a b c) + Real.exp (a * (rootPlus a b c - rootMinus a b c) * t)
          * ((rootPlus a b c - rootMinus a b c) - (x0 - rootMinus a b c)) := by
    have hqmul : (x0 - rootMinus a b c)
        * (1 - (rootPlus a b c - rootMinus a b c) / (x0 - rootMinus a b c))
        = (x0 - rootMinus a b c) - (rootPlus a b c - rootMinus a b c) := by
      field_simp
    linear_combination -(Real.exp (a * (rootPlus a b c - rootMinus a b c) * t)) * hqmul
  have hdiv : (rootPlus a b c - rootMinus a b c) / barrierDen a b c x0 t
      < x0 - rootMinus a b c := by
    rw [div_lt_iff₀ hDpos]
    have h2 : (x0 - rootMinus a b c) * barrierDen a b c x0 t
        = (x0 - rootMinus a b c) + Real.exp (a * (rootPlus a b c - rootMinus a b c) * t)
            * ((rootPlus a b c - rootMinus a b c) - (x0 - rootMinus a b c)) := hmul
    rw [h2]
    nlinarith [hdy, hE1, hd, hy]
  linarith

 -/
/-- The closed-form barrier (4.9) solves the comparison ODE: its derivative is
`φ (barrier a b c y t) = a (barrier)² + b (barrier) + c`. -/
theorem barrier_hasDerivAt (a b c y t : ℝ) (ha : 0 < a) (hb : b < 0) (hc : 0 ≤ c)
    (hy : 0 < y) (hR : a * y + c / y < -b) :
    HasDerivAt (barrier a b c y)
      (a * barrier a b c y t ^ 2 + b * barrier a b c y t + c) t := by
  obtain ⟨hord, hrm, hry, hyrp⟩ := lemma1_roots a b c y ha hb hc hy hR
  have hd : 0 < rootPlus a b c - rootMinus a b c := by linarith
  have hdnen : barrierDen a b c y t ≠ 0 :=
    ne_of_gt (barrierDen_pos a b c y t ha hb hc hy hR)
  have hdnen' : ∀ s : ℝ, barrierDen a b c y s ≠ 0 := fun s =>
    ne_of_gt (barrierDen_pos a b c y s ha hb hc hy hR)
  set d := rootPlus a b c - rootMinus a b c with hddef
  set k := 1 - d / (y - rootMinus a b c) with hkdef
  set E := Real.exp (a * d * t) with hEdef
  have hEk : E * k = 1 - barrierDen a b c y t := by
    rw [hkdef, barrierDen]
    ring
  have hEpos : 0 < E := Real.exp_pos _
  have hdE : HasDerivAt (fun s => Real.exp (a * d * s)) (E * (a * d)) t := by
    simpa using ((hasDerivAt_id t).const_mul (a * d)).exp
  have hbar : barrier a b c y = fun s => d / barrierDen a b c y s
      + rootMinus a b c := by
    funext s
    show barrier a b c y s = d / barrierDen a b c y s + rootMinus a b c
    rw [barrier, barrierDen]
  have hden : HasDerivAt (fun s => barrierDen a b c y s)
      (0 - E * (a * d) * k) t := by
    have hunf : (fun s => barrierDen a b c y s)
        = fun s => 1 - Real.exp (a * d * s) * k := by
      funext s
      rw [barrierDen]
    rw [hunf]
    have hmul : HasDerivAt (fun s => Real.exp (a * d * s) * k) (E * (a * d) * k) t := by
      simpa [mul_assoc] using hdE.mul_const k
    exact (hasDerivAt_const t (1 : ℝ)).sub hmul
  have hdiv : HasDerivAt (fun s => d / barrierDen a b c y s)
      ((0 * barrierDen a b c y t - d * (0 - E * (a * d) * k))
        / barrierDen a b c y t ^ 2) t :=
    (hasDerivAt_const t d).div hden (hdnen' t)
  have hsum : HasDerivAt (fun s => d / barrierDen a b c y s + rootMinus a b c)
      ((0 * barrierDen a b c y t - d * (0 - E * (a * d) * k))
        / barrierDen a b c y t ^ 2 + 0) t :=
    hdiv.add (hasDerivAt_const t (rootMinus a b c))
  -- value identity: the produced derivative equals φ(barrier)
  have hsubrm : barrier a b c y t - rootMinus a b c = d / barrierDen a b c y t :=
    barrier_sub_rootMinus a b c y t (by linarith)
  have hval : a * barrier a b c y t ^ 2 + b * barrier a b c y t + c
      = ((0 * barrierDen a b c y t - d * (0 - E * (a * d) * k))
        / barrierDen a b c y t ^ 2 + 0) := by
    have hφ : a * barrier a b c y t ^ 2 + b * barrier a b c y t + c
        = a * (barrier a b c y t - rootMinus a b c)
            * (barrier a b c y t - rootPlus a b c) :=
      (quad_factor a b c (barrier a b c y t) ha hord).symm
    have hsubrp : barrier a b c y t - rootPlus a b c
        = d * (1 - barrierDen a b c y t) / barrierDen a b c y t := by
      have h1 : rootPlus a b c - rootMinus a b c = d := by rw [hddef]
      calc barrier a b c y t - rootPlus a b c
          = (barrier a b c y t - rootMinus a b c)
              - (rootPlus a b c - rootMinus a b c) := by ring
        _ = d / barrierDen a b c y t
              - (rootPlus a b c - rootMinus a b c) := by rw [hsubrm]
        _ = d / barrierDen a b c y t - d := by rw [← hddef]
        _ = d * (1 - barrierDen a b c y t) / barrierDen a b c y t := by
            field_simp
    rw [hφ, hsubrm, hsubrp, ← hEk]
    field_simp
    ring
  rw [hval, hbar]
  exact hsum


/-
/-- **Lemma 1 for the norm of a solution (4.10).**  If `ρ` is continuous and
nonnegative on `[0,T]`, `ρ(0)=‖u_in‖`, and it satisfies the differential
inequality (4.3) `ρ' ≤ aρ² + bρ + c` from the right, then
`ρ t < ‖u_in‖` and `ρ t < r₊` for every `t > 0` in `[0, T]`.

The proof is a two-stage fencing argument on the right derivative:

* Stage 1 compares `ρ` with the affine supersolution `x0 + σ s` (with
  `σ = (r₊ - x0)/(T+1)`, so it stays below `r₊` on `[0,T]`): at a contact
  point `ρ = x0 + σ s ∈ (r₋, r₊)`, so `ρ' ≤ φ(ρ) < 0 < σ`, and the fencing
  theorem bounds `ρ < r₊` everywhere;
* Stage 2 compares `ρ` with the exponential Wazewski perturbation
  `barrier x0 + ν exp(2Λ s)` of the exact comparison solution: at a contact
  point Stage 1 keeps the argument inside `(r₋, r₊)`, where
  `quad_sub` gives `φ(x) ≤ φ(barrier) + Λ(x - barrier)`, making the
  perturbation a strict supersolution; letting `ν → 0` lands
  `ρ ≤ barrier x0`, strictly below `x0` and `r₊` for positive times by the
  closed algebra.

This completes the previously-open `lemma1_norm_barrier` of the original
development of this material.  The passage from the vector ODE (2.1) to the
scalar inequality (4.3) — the estimates (4.2) — remains a paper-boundary task. -/
theorem lemma1_norm_barrier (a b c x0 T : ℝ) (ha : 0 < a) (hb : b < 0) (hc : 0 ≤ c)
    (hx0 : 0 < x0) (hR : a * x0 + c / x0 < -b)
    (ρ ρ' : ℝ → ℝ) (hcont : ContinuousOn ρ (Icc 0 T)) (hρ0 : ρ 0 = x0)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt ρ (ρ' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 T, ρ' t ≤ a * ρ t ^ 2 + b * ρ t + c)
    (_hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ ρ t) :
    ∀ t ∈ Icc 0 T, 0 < t → ρ t < x0 ∧ ρ t < rootPlus a b c := by
  obtain ⟨hord, hrm, hrx, hxr⟩ := lemma1_roots a b c x0 ha hb hc hx0 hR
  rcases Classical.em (0 ≤ T) with _hTpos | hTneg
  set rm := rootMinus a b c with hrmdef
  set rp := rootPlus a b c with hrpdef
  set d := rp - rm with hddef
  set Λ := a * d with hΛdef
  have hd : 0 < d := by rw [hddef]; linarith
  have hΛpos : 0 < Λ := mul_pos ha hd
  -- Stage 1: ρ < rp on [0, T] via the affine supersolution x0 + σ s.
  have hstage1 : ∀ s ∈ Icc 0 T, ρ s < rp := by
    set σ := (rp - x0) / (T + 1) with hσdef
    have hσpos : 0 < σ := by
      rw [hσdef]
      have hrpx0 : x0 < rp := by rw [hrpdef]; linarith
      exact div_pos (by rw [hrpdef]; linarith) (by linarith)
    have hfence := image_le_of_deriv_right_lt_deriv_boundary'
      (f := ρ) (f' := ρ') hcont hderiv
      (B := fun s => σ * s + x0) (B' := fun _ => σ)
      (by
        show ρ 0 ≤ σ * 0 + x0
        rw [hρ0]
        simp only [mul_zero, zero_add]
        exact le_refl _)
      (by fun_prop)
      (by
        intro s _
        have h1 : HasDerivAt (fun s => σ * s) σ s := by
          simpa using (hasDerivAt_id s).const_mul σ
        exact (h1.add_const x0).hasDerivWithinAt)
      (by
        intro s _hs heq
        have hlt : ρ s < rp := by
          rw [heq]
          have h1 : s ≤ T := le_of_lt _hs.2
          have h2 : σ * s ≤ σ * T := mul_le_mul_of_nonneg_left h1 (le_of_lt hσpos)
          have h3 : σ * (T + 1) = rp - x0 := by
            rw [hσdef]
            field_simp
          nlinarith
        have hgt : rm < ρ s := by
          rw [heq]
          have hxrm : rm < x0 := by rw [hrmdef]; linarith
          have hs0 : 0 ≤ s := _hs.1
          have hσs : 0 ≤ σ * s := mul_nonneg (le_of_lt hσpos) hs0
          linarith
        have hφ : a * ρ s ^ 2 + b * ρ s + c < 0 := quad_neg a b c (ρ s) ha hord hgt hlt
        have hρ' := hbound s _hs
        linarith)
    intro s hs
    have h1 := hfence hs
    have h3 : σ * (T + 1) = rp - x0 := by
      rw [hσdef]
      field_simp
    have h2 : σ * s < rp - x0 := by
      have h1s : s ≤ T := hs.2
      have h4 : σ * s ≤ σ * T := mul_le_mul_of_nonneg_left h1s (le_of_lt hσpos)
      linarith
    linarith
  -- Stage 2: for every ν > 0, ρ ≤ barrier(x0) + ν exp(2Λ s) on [0, T].
  have hstage2 : ∀ ν : ℝ, 0 < ν → ∀ s ∈ Icc 0 T,
      ρ s ≤ barrier a b c x0 s + ν * Real.exp (2 * Λ * s) := by
    intro ν hν
    have hfence := image_le_of_deriv_right_lt_deriv_boundary'
      (f := ρ) (f' := ρ') hcont hderiv
      (B := fun s => barrier a b c x0 s + ν * Real.exp (2 * Λ * s))
      (B' := fun s => a * barrier a b c x0 s ^ 2 + b * barrier a b c x0 s + c
        + ν * (Real.exp (2 * Λ * s) * (2 * Λ)))
      (by
        show ρ 0 ≤ barrier a b c x0 0 + ν * Real.exp (2 * Λ * 0)
        rw [barrier_zero a b c x0 ha hb hc hx0 hR, hρ0]
        simp only [mul_zero, Real.exp_zero, mul_one]
        linarith)
      (by
        intro s _
        have h1 : ContinuousAt (fun s => barrier a b c x0 s) s :=
          (barrier_hasDerivAt a b c x0 s ha hb hc hx0 hR).continuousAt
        have h2 : ContinuousAt (fun s => Real.exp (2 * Λ * s)) s := by fun_prop
        exact (h1.add (h2.const_mul ν)).continuousWithinAt)
      (by
        intro s _
        have h1 : HasDerivAt (fun s => barrier a b c x0 s)
            (a * barrier a b c x0 s ^ 2 + b * barrier a b c x0 s + c) s :=
          barrier_hasDerivAt a b c x0 s ha hb hc hx0 hR
        have h5 : HasDerivAt (fun s => Real.exp (2 * Λ * s))
            (Real.exp (2 * Λ * s) * (2 * Λ)) s := by
          have h6 := (hasDerivAt_id s).const_mul (2 * Λ)
          simpa using h6.exp
        have h2 : HasDerivAt (fun s => ν * Real.exp (2 * Λ * s))
            (ν * (Real.exp (2 * Λ * s) * (2 * Λ))) s := h5.const_mul ν
        exact (h1.add h2).hasDerivWithinAt)
      (by
        intro s hs heq
        have hyrm : rm < barrier a b c x0 s :=
          barrier_gt_rootMinus a b c x0 s ha hb hc hx0 hR
        have hyrp : barrier a b c x0 s < rp :=
          barrier_lt_rootPlus a b c x0 s ha hb hc hx0 hR
        have hxrp : ρ s < rp := hstage1 s ⟨hs.1, le_of_lt hs.2⟩
        have hxy : barrier a b c x0 s ≤ ρ s := by
          rw [heq]
          have h1 : 0 < ν * Real.exp (2 * Λ * s) := by positivity
          nlinarith
        have hrmρ : rootMinus a b c ≤ ρ s := by linarith
        have hqs := quad_sub a b c (ρ s) (barrier a b c x0 s) ha hord
          (le_of_lt hyrm) (le_of_lt hyrp) hrmρ (le_of_lt hxrp) hxy
        have hΛeq : a * (rootPlus a b c - rootMinus a b c) = Λ := by
          rw [← hrpdef, ← hrmdef, ← hddef, ← hΛdef]
        rw [hΛeq] at hqs
        have hsub : ρ s - barrier a b c x0 s = ν * Real.exp (2 * Λ * s) := by
          rw [heq]
          ring
        rw [hsub] at hqs
        have hρ' := hbound s hs
        have h1 : 0 < Λ * ν * Real.exp (2 * Λ * s) := by positivity
        have h2 : Λ * ν * Real.exp (2 * Λ * s)
            < 2 * Λ * ν * Real.exp (2 * Λ * s) := by nlinarith
        linarith)
    intro s hs
    exact hfence hs
  -- Final step: ν → 0 lands ρ t ≤ barrier(x0)(t) < x0 and < rp for t > 0.
  intro t ht_mem ht
  have hle : ρ t ≤ barrier a b c x0 t := by
    by_contra hcontra
    have hcontra' : barrier a b c x0 t < ρ t := by
      by_contra h
      exact hcontra (not_lt.mp h)
    have hexp : 0 < Real.exp (2 * Λ * t) := Real.exp_pos _
    have hν := hstage2 ((ρ t - barrier a b c x0 t) / (2 * Real.exp (2 * Λ * t)))
      (by
        have h1 : 0 < 2 * Real.exp (2 * Λ * t) := by positivity
        exact div_pos (sub_pos.mpr hcontra') h1) t ht_mem
    have hcalc : ((ρ t - barrier a b c x0 t) / (2 * Real.exp (2 * Λ * t)))
        * Real.exp (2 * Λ * t) = (ρ t - barrier a b c x0 t) / 2 := by
      field_simp
    have hfin : ρ t ≤ barrier a b c x0 t + (ρ t - barrier a b c x0 t) / 2 := by
      rw [← hcalc]
      linarith
    linarith
  have h1 : barrier a b c x0 t < x0 := barrier_lt_initial a b c x0 t ha hb hc hx0 hR ht
  have h2 : barrier a b c x0 t < rp := barrier_lt_rootPlus a b c x0 t ha hb hc hx0 hR
  constructor <;> linarith
  · intro t ht_mem ht
    have hle : t ≤ T := ht_mem.2
    have hT' : T < 0 := lt_of_not_ge hTneg
    linarith

 -/
end Qatlib.Papers.DissipNonlin20.MainResults.NormBarrier
