/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Continuous time search adversary bounds

This module compares normalized evolutions under a common self adjoint driver with and without a
rank one oracle term. It bounds the growth of their total squared distance by 2E√N T and derives
time lower bounds from aggregate, pointwise, or all but one separation hypotheses, following the
continuous search argument of [FarhiGutmann1998a].

## Main statements

* `distance_growth_le`: bound the total squared distance from a common initial state.
* `continuous_sum_lower_bound`: total separation implies T ≥ ε√N/(2E).
* `continuous_except_one_lower_bound`: derive a time bound when one marked index may be
  excluded.

## References

* [Farhi and Gutmann, 1998][FarhiGutmann1998a]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Concepts.QueryComplexity.ContinuousAdv

variable {ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The rank one action obtained by projecting onto basis vector `b i` and scaling by the real
energy `E`. -/
def rankOneAction (b : OrthonormalBasis ι ℂ V) (E : ℝ) (i : ι) (v : V) : V :=
  (E : ℂ) • (inner ℂ (b i) v • b i)

/-- The sum of the rank one actions over the orthonormal basis is scalar multiplication by `E`. -/
theorem sum_rankOneAction (b : OrthonormalBasis ι ℂ V) (E : ℝ) (v : V) :
    (∑ i, rankOneAction b E i v) = (E : ℂ) • v := by
  unfold rankOneAction
  rw [← Finset.smul_sum, b.sum_repr']

/-- The rank one action is self adjoint with respect to the complex inner product. -/
theorem rankOneAction_inner_comm (b : OrthonormalBasis ι ℂ V) (E : ℝ) (i : ι) (x y : V) :
    inner ℂ (rankOneAction b E i x) y = inner ℂ x (rankOneAction b E i y) := by
  unfold rankOneAction
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    inner_smul_left, inner_smul_right, ← inner_conj_symm, Complex.conj_conj]
  ring

/-- The expectation of the rank one action has zero imaginary part. -/
theorem rankOneAction_inner_self_im (b : OrthonormalBasis ι ℂ V) (E : ℝ) (i : ι) (x : V) :
    (inner ℂ x (rankOneAction b E i x)).im = 0 := by
  unfold rankOneAction
  rw [inner_smul_right, inner_smul_right, ← inner_conj_symm]
  rw [mul_comm ((starRingEnd ℂ) (inner ℂ x (b i))), Complex.mul_conj]
  simp

/-- The expectation of the rank one action equals `E` times the squared norm of the
corresponding basis coefficient. -/
theorem rankOneAction_inner_self (b : OrthonormalBasis ι ℂ V) (E : ℝ) (i : ι) (x : V) :
    inner ℂ x (rankOneAction b E i x) = ((E * ‖inner ℂ (b i) x‖ ^ 2 : ℝ) : ℂ) := by
  unfold rankOneAction
  rw [inner_smul_right, inner_smul_right, ← inner_conj_symm]
  rw [mul_comm ((starRingEnd ℂ) (inner ℂ x (b i))), Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.norm_conj]
  push_cast
  ring

/-- For nonnegative energy, the norm of the rank one action is `E` times the norm of the
corresponding basis coefficient. -/
theorem norm_rankOneAction (b : OrthonormalBasis ι ℂ V) (E : ℝ) (i : ι) (x : V)
    (hE : 0 ≤ E) :
    ‖rankOneAction b E i x‖ = E * ‖inner ℂ (b i) x‖ := by
  unfold rankOneAction
  rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE,
    b.norm_eq_one, mul_one]

/-- For a self adjoint driver, the real inner product determining squared distance growth
reduces to the imaginary part of the oracle coupling. -/
theorem distance_deriv_value (b : OrthonormalBasis ι ℂ V) (E : ℝ) (i : ι)
    (HD : V →L[ℂ] V) (hHD : ∀ u v, inner ℂ (HD u) v = inner ℂ u (HD v)) (ψw ψ : V) :
    (inner ℂ (ψw - ψ)
        (((-Complex.I) • (rankOneAction b E i ψw + HD ψw)) - ((-Complex.I) • (HD ψ)))).re
      = (inner ℂ ψw (rankOneAction b E i ψ)).im := by
  simp only [inner_sub_left, inner_sub_right, inner_smul_right, inner_add_right]
  have ha : (inner ℂ ψw (rankOneAction b E i ψw)).im = 0 :=
    rankOneAction_inner_self_im b E i ψw
  have hb : (inner ℂ ψw (HD ψw)).im = 0 := by
    have hz : (starRingEnd ℂ) (inner ℂ ψw (HD ψw)) = inner ℂ ψw (HD ψw) :=
      (inner_conj_symm (𝕜 := ℂ) (HD ψw) ψw).trans (hHD ψw ψw)
    have := congr_arg Complex.im hz
    rw [Complex.conj_im] at this
    linarith
  have hf : (inner ℂ ψ (HD ψ)).im = 0 := by
    have hz : (starRingEnd ℂ) (inner ℂ ψ (HD ψ)) = inner ℂ ψ (HD ψ) :=
      (inner_conj_symm (𝕜 := ℂ) (HD ψ) ψ).trans (hHD ψ ψ)
    have := congr_arg Complex.im hz
    rw [Complex.conj_im] at this
    linarith
  have he : (inner ℂ ψ (HD ψw)).im = -(inner ℂ ψw (HD ψ)).im := by
    have hz : (starRingEnd ℂ) (inner ℂ ψ (HD ψw)) = inner ℂ ψw (HD ψ) :=
      (inner_conj_symm (𝕜 := ℂ) (HD ψw) ψ).trans (hHD ψw ψ)
    have := congr_arg Complex.im hz
    rw [Complex.conj_im] at this
    linarith
  have hd : (inner ℂ ψ (rankOneAction b E i ψw)).im = -(inner ℂ ψw (rankOneAction b E i ψ)).im := by
    have hz : (starRingEnd ℂ) (inner ℂ ψ (rankOneAction b E i ψw)) =
        inner ℂ ψw (rankOneAction b E i ψ) :=
      (inner_conj_symm (𝕜 := ℂ) (rankOneAction b E i ψw) ψ).trans
        (rankOneAction_inner_comm b E i ψw ψ)
    have := congr_arg Complex.im hz
    rw [Complex.conj_im] at this
    linarith
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, Complex.sub_im, Complex.add_im, zero_mul, zero_sub,
    neg_zero] at *
  linarith

/-- For evolutions with a common self adjoint driver and one rank one oracle term, the
derivative of their squared distance is twice the imaginary part of the oracle coupling. -/
theorem distance_hasDerivAt (b : OrthonormalBasis ι ℂ V) (E : ℝ)
    (HD : ℝ → V →L[ℂ] V) (hHD : ∀ t u v, inner ℂ ((HD t) u) v = inner ℂ u ((HD t) v))
    (ψw : ι → ℝ → V) (ψ : ℝ → V)
    (hψw : ∀ (i : ι) (t : ℝ),
      HasDerivAt (ψw i) ((-Complex.I) • (rankOneAction b E i (ψw i t) + HD t (ψw i t))) t)
    (hψ : ∀ t, HasDerivAt ψ ((-Complex.I) • (HD t (ψ t))) t)
    (i : ι) (t : ℝ) :
    HasDerivAt (fun s => ‖ψw i s - ψ s‖ ^ 2)
      (2 * (inner ℂ (ψw i t) (rankOneAction b E i (ψ t))).im) t := by
  have hu : HasDerivAt (fun s => ψw i s - ψ s)
      (((-Complex.I) • (rankOneAction b E i (ψw i t) + HD t (ψw i t))) -
        ((-Complex.I) • (HD t (ψ t)))) t :=
    (hψw i t).sub (hψ t)
  let uv : V := ((-Complex.I) • (rankOneAction b E i (ψw i t) + HD t (ψw i t))) -
    ((-Complex.I) • (HD t) (ψ t))
  have hval : RCLike.re (inner ℂ (ψw i t - ψ t) uv) =
      (inner ℂ (ψw i t) (rankOneAction b E i (ψ t))).im := by
    change (inner ℂ (ψw i t - ψ t) uv).re = (inner ℂ (ψw i t) (rankOneAction b E i (ψ t))).im
    dsimp only [uv]
    exact distance_deriv_value b E i (HD t) (hHD t) (ψw i t) (ψ t)
  letI : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
  have hnorm := hu.norm_sq
  rw [real_inner_eq_re_inner] at hnorm
  rw [hval] at hnorm
  exact hnorm

/-- The sum of the absolute basis coefficients of a unit vector is at most the square root of
the basis cardinality. -/
theorem sum_norm_inner_le_sqrt_card (b : OrthonormalBasis ι ℂ V) (ψ : V) (hψ : ‖ψ‖ = 1) :
    (∑ i, ‖inner ℂ (b i) ψ‖) ≤ Real.sqrt (Fintype.card ι) := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι))
    (f := fun i => ‖inner ℂ (b i) ψ‖)
  have hparse : (∑ i, ‖inner ℂ (b i) ψ‖ ^ 2) = ‖ψ‖ ^ 2 := b.sum_sq_norm_inner_right ψ
  rw [hparse, hψ, one_pow, mul_one] at hcs
  have hF : 0 ≤ ∑ i, ‖inner ℂ (b i) ψ‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hN : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  have hle : (∑ i, ‖inner ℂ (b i) ψ‖) ^ 2 ≤ (Real.sqrt (Fintype.card ι)) ^ 2 := by
    rw [Real.sq_sqrt hN]
    exact hcs
  calc (∑ i, ‖inner ℂ (b i) ψ‖) = |∑ i, ‖inner ℂ (b i) ψ‖| := (abs_of_nonneg hF).symm
    _ ≤ Real.sqrt (Fintype.card ι) := abs_le_of_sq_le_sq hle (Real.sqrt_nonneg _)

/-- For nonnegative energy and a unit marked state, the squared distance derivative term is at
most twice the energy times the corresponding reference basis coefficient norm. -/
theorem distance_deriv_term_le (b : OrthonormalBasis ι ℂ V) (E : ℝ) (i : ι)
    (ψw ψ : V) (hE : 0 ≤ E) (hψw : ‖ψw‖ = 1) :
    2 * (inner ℂ ψw (rankOneAction b E i ψ)).im ≤ 2 * E * ‖inner ℂ (b i) ψ‖ := by
  have h1 : (inner ℂ ψw (rankOneAction b E i ψ)).im ≤
      ‖inner ℂ ψw (rankOneAction b E i ψ)‖ := Complex.im_le_norm _
  have h2 : ‖inner ℂ ψw (rankOneAction b E i ψ)‖ ≤
      ‖ψw‖ * ‖rankOneAction b E i ψ‖ := norm_inner_le_norm _ _
  have h3 : ‖rankOneAction b E i ψ‖ = E * ‖inner ℂ (b i) ψ‖ := norm_rankOneAction b E i ψ hE
  rw [h3, hψw, one_mul] at h2
  linarith

/-- For unit marked states and a unit reference state, the sum of squared distance derivative
terms is at most 2E√N for nonnegative energy. -/
theorem distance_deriv_le (b : OrthonormalBasis ι ℂ V) (E : ℝ) (ψw : ι → V) (ψ : V)
    (hE : 0 ≤ E) (hψw : ∀ i, ‖ψw i‖ = 1) (hψ : ‖ψ‖ = 1) :
    (∑ i, 2 * (inner ℂ (ψw i) (rankOneAction b E i ψ)).im) ≤
      2 * E * Real.sqrt (Fintype.card ι) := by
  have hterm : ∀ i, 2 * (inner ℂ (ψw i) (rankOneAction b E i ψ)).im ≤
      2 * E * ‖inner ℂ (b i) ψ‖ :=
    fun i => distance_deriv_term_le b E i (ψw i) ψ hE (hψw i)
  have hstep : (∑ i, 2 * (inner ℂ (ψw i) (rankOneAction b E i ψ)).im) ≤
      ∑ i, 2 * E * ‖inner ℂ (b i) ψ‖ := Finset.sum_le_sum (fun i _ => hterm i)
  have hfac : (∑ i, 2 * E * ‖inner ℂ (b i) ψ‖) = 2 * E * ∑ i, ‖inner ℂ (b i) ψ‖ := by
    rw [Finset.mul_sum]
  have hcs : (∑ i, ‖inner ℂ (b i) ψ‖) ≤ Real.sqrt (Fintype.card ι) :=
    sum_norm_inner_le_sqrt_card b ψ hψ
  rw [hfac] at hstep
  nlinarith [hstep, hcs]

/-- For normalized evolutions starting from a common state and sharing a self adjoint driver,
the total squared distance at nonnegative time `T` is at most 2E√N T when the rank one
oracle energy is nonnegative. This is the growth estimate behind the continuous search bound
in [FarhiGutmann1998a]. -/
theorem distance_growth_le (b : OrthonormalBasis ι ℂ V) (E : ℝ) (hE : 0 ≤ E)
    (HD : ℝ → V →L[ℂ] V) (hHD : ∀ t u v, inner ℂ ((HD t) u) v = inner ℂ u ((HD t) v))
    (ψw : ι → ℝ → V) (ψ : ℝ → V)
    (hψw_norm : ∀ i t, ‖ψw i t‖ = 1) (hψ_norm : ∀ t, ‖ψ t‖ = 1)
    (h_init : ∀ i, ψw i 0 = ψ 0)
    (hψw : ∀ (i : ι) (t : ℝ),
      HasDerivAt (ψw i) ((-Complex.I) • (rankOneAction b E i (ψw i t) + HD t (ψw i t))) t)
    (hψ : ∀ t, HasDerivAt ψ ((-Complex.I) • (HD t (ψ t))) t)
    {T : ℝ} (hT : 0 ≤ T) :
    (∑ i, ‖ψw i T - ψ T‖ ^ 2) ≤ 2 * E * Real.sqrt (Fintype.card ι) * T := by
  let F : ℝ → ℝ := fun t => ∑ i, ‖ψw i t - ψ t‖ ^ 2
  let d : ℝ → ℝ := fun t => ∑ i, 2 * (inner ℂ (ψw i t) (rankOneAction b E i (ψ t))).im
  have hFderiv : ∀ t, HasDerivAt F (d t) t := by
    intro t
    have h := HasDerivAt.sum (u := Finset.univ)
      (fun i _ => distance_hasDerivAt b E HD hHD ψw ψ hψw hψ i t)
    convert! h using 1
    ext s
    rw [Finset.sum_apply]
  have hFcont : ContinuousOn F (Set.Icc 0 T) :=
    fun x _ => (hFderiv x).continuousAt.continuousWithinAt
  have hd : ∀ t ∈ Set.Ico 0 T, d t ≤ 2 * E * Real.sqrt (Fintype.card ι) := by
    intro t _
    exact distance_deriv_le b E (fun i => ψw i t) (ψ t) hE (fun i => hψw_norm i t) (hψ_norm t)
  have hF0 : F 0 ≤ 2 * E * Real.sqrt (Fintype.card ι) * 0 := by
    have : F 0 = 0 := by
      simp only [F]
      simp [h_init]
    rw [this]
    simp
  have hBcont : ContinuousOn (fun t => 2 * E * Real.sqrt (Fintype.card ι) * t) (Set.Icc 0 T) := by
    fun_prop
  have hBderiv : ∀ x ∈ Set.Ico 0 T,
      HasDerivWithinAt (fun t => 2 * E * Real.sqrt (Fintype.card ι) * t)
        (2 * E * Real.sqrt (Fintype.card ι)) (Set.Ici x) x := by
    intro x _
    simpa using ((hasDerivAt_id x).const_mul (2 * E * Real.sqrt (Fintype.card ι))).hasDerivWithinAt
  have hmain : F T ≤ 2 * E * Real.sqrt (Fintype.card ι) * T :=
    image_le_of_deriv_right_le_deriv_boundary hFcont
      (fun x _ => (hFderiv x).hasDerivWithinAt) hF0 hBcont hBderiv hd
      (show T ∈ Set.Icc 0 T from ⟨hT, le_rfl⟩)
  simpa [F] using hmain

/-- If the total squared distance at nonnegative time `T` is at least Nε, normalized evolutions
with positive oracle energy and a common initial state satisfy T ≥ ε√N/(2E), under the
stated evolution equations. -/
theorem continuous_sum_lower_bound [Nonempty ι]
    (b : OrthonormalBasis ι ℂ V) {E ε T : ℝ} (hE : 0 < E) (_hε : 0 ≤ ε)
    (HD : ℝ → V →L[ℂ] V) (hHD : ∀ t u v, inner ℂ ((HD t) u) v = inner ℂ u ((HD t) v))
    (ψw : ι → ℝ → V) (ψ : ℝ → V)
    (hψw_norm : ∀ i t, ‖ψw i t‖ = 1) (hψ_norm : ∀ t, ‖ψ t‖ = 1)
    (h_init : ∀ i, ψw i 0 = ψ 0)
    (hψw : ∀ (i : ι) (t : ℝ),
      HasDerivAt (ψw i) ((-Complex.I) • (rankOneAction b E i (ψw i t) + HD t (ψw i t))) t)
    (hψ : ∀ t, HasDerivAt ψ ((-Complex.I) • (HD t (ψ t))) t)
    (hsep_sum : (Fintype.card ι : ℝ) * ε ≤ ∑ i, ‖ψw i T - ψ T‖ ^ 2) (hT : 0 ≤ T) :
    ε * Real.sqrt (Fintype.card ι) / (2 * E) ≤ T := by
  have hgrowth := distance_growth_le b E hE.le HD hHD ψw ψ hψw_norm hψ_norm h_init hψw hψ hT
  have hmain : (Fintype.card ι : ℝ) * ε ≤ 2 * E * Real.sqrt (Fintype.card ι) * T :=
    le_trans hsep_sum hgrowth
  have hNposNat : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr inferInstance
  have hNpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hNposNat
  have hsqrtpos : 0 < Real.sqrt (Fintype.card ι) := Real.sqrt_pos.2 hNpos
  have hNsq : (Fintype.card ι : ℝ) =
      Real.sqrt (Fintype.card ι) * Real.sqrt (Fintype.card ι) := by
    nth_rewrite 1 [← Real.sq_sqrt hNpos.le]
    ring
  have hsq : Real.sqrt (Fintype.card ι) * Real.sqrt (Fintype.card ι) * ε ≤
      (2 * E * Real.sqrt (Fintype.card ι)) * T := by
    calc Real.sqrt (Fintype.card ι) * Real.sqrt (Fintype.card ι) * ε
        = (Fintype.card ι : ℝ) * ε := by rw [← hNsq]
      _ ≤ 2 * E * Real.sqrt (Fintype.card ι) * T := hmain
  have hdiv : Real.sqrt (Fintype.card ι) * ε ≤ 2 * E * T := by
    have hre : Real.sqrt (Fintype.card ι) * (Real.sqrt (Fintype.card ι) * ε) ≤
        Real.sqrt (Fintype.card ι) * (2 * E * T) := by nlinarith [hsq]
    exact (mul_le_mul_iff_of_pos_left hsqrtpos).1 hre
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * E)]
  nlinarith [hdiv]

/-- If each marked evolution has squared distance at least ε from the reference at nonnegative
time `T`, the stated normalized evolutions with positive energy satisfy T ≥ ε√N/(2E). -/
theorem continuous_pointwise_lower_bound [Nonempty ι]
    (b : OrthonormalBasis ι ℂ V) {E ε T : ℝ} (hE : 0 < E) (hε : 0 ≤ ε)
    (HD : ℝ → V →L[ℂ] V) (hHD : ∀ t u v, inner ℂ ((HD t) u) v = inner ℂ u ((HD t) v))
    (ψw : ι → ℝ → V) (ψ : ℝ → V)
    (hψw_norm : ∀ i t, ‖ψw i t‖ = 1) (hψ_norm : ∀ t, ‖ψ t‖ = 1)
    (h_init : ∀ i, ψw i 0 = ψ 0)
    (hψw : ∀ (i : ι) (t : ℝ),
      HasDerivAt (ψw i) ((-Complex.I) • (rankOneAction b E i (ψw i t) + HD t (ψw i t))) t)
    (hψ : ∀ t, HasDerivAt ψ ((-Complex.I) • (HD t (ψ t))) t)
    (hsep : ∀ i, ε ≤ ‖ψw i T - ψ T‖ ^ 2) (hT : 0 ≤ T) :
    ε * Real.sqrt (Fintype.card ι) / (2 * E) ≤ T := by
  apply continuous_sum_lower_bound b hE hε HD hHD ψw ψ hψw_norm hψ_norm h_init hψw hψ
    (hT := hT)
  calc (Fintype.card ι : ℝ) * ε = ∑ _i : ι, ε := by simp
       _ ≤ ∑ i, ‖ψw i T - ψ T‖ ^ 2 := Finset.sum_le_sum (fun i _ => hsep i)

/-- If every marked evolution except possibly one has squared distance at least ε from the
reference at nonnegative time `T`, the stated normalized evolutions with positive energy
satisfy T ≥ ε(N − 1)/(2E√N). -/
theorem continuous_except_one_lower_bound
    (b : OrthonormalBasis ι ℂ V) {E ε T : ℝ} (hE : 0 < E)
    (HD : ℝ → V →L[ℂ] V) (hHD : ∀ t u v, inner ℂ ((HD t) u) v = inner ℂ u ((HD t) v))
    (ψw : ι → ℝ → V) (ψ : ℝ → V)
    (hψw_norm : ∀ i t, ‖ψw i t‖ = 1) (hψ_norm : ∀ t, ‖ψ t‖ = 1)
    (h_init : ∀ i, ψw i 0 = ψ 0)
    (hψw : ∀ (i : ι) (t : ℝ),
      HasDerivAt (ψw i) ((-Complex.I) • (rankOneAction b E i (ψw i t) + HD t (ψw i t))) t)
    (hψ : ∀ t, HasDerivAt ψ ((-Complex.I) • (HD t (ψ t))) t)
    (e : ι) (hsep : ∀ i, i ≠ e → ε ≤ ‖ψw i T - ψ T‖ ^ 2) (hT : 0 ≤ T) :
    ε * ((Fintype.card ι : ℝ) - 1) / (2 * E * Real.sqrt (Fintype.card ι)) ≤ T := by
  classical
  have hN : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨e⟩
  have hsqrt : 0 < Real.sqrt (Fintype.card ι) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast (show 0 < Fintype.card ι from hN)
  have hcount : (∑ _i ∈ (Finset.univ.erase e : Finset ι), ε) =
      ((Fintype.card ι : ℝ) - 1) * ε := by
    simp [Finset.card_erase_of_mem, Nat.cast_sub hN]
  have hsep_sum : ((Fintype.card ι : ℝ) - 1) * ε ≤ ∑ i, ‖ψw i T - ψ T‖ ^ 2 := by
    rw [← hcount]
    calc (∑ _i ∈ (Finset.univ.erase e : Finset ι), ε)
        ≤ ∑ i ∈ (Finset.univ.erase e : Finset ι), ‖ψw i T - ψ T‖ ^ 2 :=
          Finset.sum_le_sum (fun i hi => hsep i (Finset.ne_of_mem_erase hi))
      _ ≤ ∑ i, ‖ψw i T - ψ T‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset e Finset.univ)
            (fun i _ _ => sq_nonneg _)
  have hgrowth := distance_growth_le b E hE.le HD hHD ψw ψ hψw_norm hψ_norm h_init hψw hψ hT
  rw [div_le_iff₀ (by positivity : 0 < 2 * E * Real.sqrt (Fintype.card ι))]
  nlinarith [hsep_sum.trans hgrowth]

end Qatlib.Concepts.QueryComplexity.ContinuousAdv
