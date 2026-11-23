/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.WalkFind.GroverInterp.GroverInterpClaims
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

@[expose] public section

/-!
# The positive-phase coefficient decomposition of Claim 5

Fixed source: [Ambainis2007ElementDistinctness], Claim 5
(quant-ph/0311001v9, pp. 15--16).  In the real spectral expansion of the search
walk, the vector

`v_β = α i cot (β / 2) • start + v_end + v_β''`

is normalized and split into the start direction and the end direction

`u₁ = c_start i • start + c_end • psi_end + u₁'`

with positive real `c_start`, `c_end` and residual `‖u₁'‖ ≤ 3 β / ε`.
This module proves the positive-phase decomposition and a uniform residual
bound from the abstract orthonormal spectral data. The trigonometric estimate
controls cotangents at phases separated by `β`. Identifying the supplied
expansion (3) with the resolvent vector in Claim 4 and treating the negative
phase are separate steps.

## Main statements

* `claim5_two_vector_decomposition`: a uniform bound on the Euclidean
  residual for `β > 0` and a positive phase gap. The proof uses the witness
  `C = 3`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Qatlib.Papers.QWalkAmbainis03.GroverInterp.TwoVectorDecomposition

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.WalkFind.GroverInterp
open scoped BigOperators

noncomputable section

/-- Splitting a finite sum over `Option α` into the `none` term and the sum
over the `some` terms. -/
theorem sum_option {α M : Type*} [Fintype α] [AddCommMonoid M]
    (f : Option α → M) :
    (∑ x, f x) = f none + ∑ a, f (some a) := by
  classical
  have hset : (Finset.univ : Finset (Option α)) =
      insert none (Finset.univ.image (some : α → Option α)) := by
    ext x
    cases x <;> simp
  rw [hset, Finset.sum_insert (by simp)]
  congr 1
  rw [Finset.sum_image]
  intro a _ b _ h
  exact Option.some.inj h

/-- The Pythagorean identity for a finite orthonormal family in complex
Euclidean space: the squared norm of a linear combination is the sum of the
squared coefficient norms. -/
theorem norm_sq_sum_smul {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (b : ι → EuclideanSpace ℂ (Fin m)) (c : ι → ℂ)
    (hb : ∀ x y, inner (𝕜 := ℂ) (b x) (b y) = if x = y then (1 : ℂ) else 0) :
    ‖∑ x, c x • b x‖ ^ 2 = ∑ x, ‖c x‖ ^ 2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)
    (x := ∑ x, c x • b x)]
  have hinner : inner (𝕜 := ℂ) (∑ x, c x • b x) (∑ y, c y • b y) =
      ∑ x, star (c x) * c x := by
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, hb]
    have hcollapse : ∀ x : ι,
        (∑ y, (starRingEnd ℂ) (c y) * (if y = x then (1 : ℂ) else 0)) =
          star (c x) := by
      intro x
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _ hyx
        simp [hyx]
      · simp
    simp only [hcollapse]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [mul_comm]
  rw [hinner]
  simp only [map_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  exact Complex.ofReal_re _

/-- The paired spectral basis: the start direction together with the two
real eigenvectors attached to each eigenphase. -/
def basisVec {m l : ℕ} (w : Fin l → Bool → Fin m → ℂ) (start : Fin m → ℂ) :
    Option (Fin l × Bool) → Fin m → ℂ
  | none => start
  | some (j, s) => w j s

/-- Coefficients of the spectral vector `v_β` of equation (3). -/
def cBeta {l : ℕ} (α β : ℝ) (a : Fin l → ℝ) (θ : Fin l → ℝ) :
    Option (Fin l × Bool) → ℂ
  | none => (α : ℂ) * (1 + Complex.I * (Real.cot (β / 2) : ℂ))
  | some (j, true) => (a j : ℂ) * (1 + Complex.I * (Real.cot ((β - θ j) / 2) : ℂ))
  | some (j, false) => (a j : ℂ) * (1 + Complex.I * (Real.cot ((β + θ j) / 2) : ℂ))

/-- Coefficients of the end vector of equation (7). -/
def cEnd {l : ℕ} (a : Fin l → ℝ) (θ : Fin l → ℝ) : Option (Fin l × Bool) → ℂ
  | none => 0
  | some (j, true) => (a j : ℂ) * (1 + Complex.I * (Real.cot (-(θ j) / 2) : ℂ))
  | some (j, false) => (a j : ℂ) * (1 + Complex.I * (Real.cot (θ j / 2) : ℂ))

/-- Coefficients of the residual `v_β''` of equation (8). -/
def cRes {l : ℕ} (α β : ℝ) (a : Fin l → ℝ) (θ : Fin l → ℝ) :
    Option (Fin l × Bool) → ℂ
  | none => (α : ℂ)
  | some (j, true) =>
      (a j : ℂ) * Complex.I *
        ((Real.cot ((β - θ j) / 2) - Real.cot (-(θ j) / 2) : ℝ) : ℂ)
  | some (j, false) =>
      (a j : ℂ) * Complex.I *
        ((Real.cot ((β + θ j) / 2) - Real.cot (θ j / 2) : ℝ) : ℂ)

/-- The spectral vector `v_β`. -/
def vBeta {m l : ℕ} (α β : ℝ) (a : Fin l → ℝ) (θ : Fin l → ℝ)
    (w : Fin l → Bool → Fin m → ℂ) (start : Fin m → ℂ) : Fin m → ℂ :=
  ∑ x, cBeta α β a θ x • basisVec w start x

/-- The end vector `v_end`. -/
def vEnd {m l : ℕ} (a : Fin l → ℝ) (θ : Fin l → ℝ)
    (w : Fin l → Bool → Fin m → ℂ) (start : Fin m → ℂ) : Fin m → ℂ :=
  ∑ x, cEnd a θ x • basisVec w start x

/-- The residual `v_β''`. -/
def vBetaResidual {m l : ℕ} (α β : ℝ) (a : Fin l → ℝ) (θ : Fin l → ℝ)
    (w : Fin l → Bool → Fin m → ℂ) (start : Fin m → ℂ) : Fin m → ℂ :=
  ∑ x, cRes α β a θ x • basisVec w start x

/-- Coefficients of the pure start contribution. -/
def cStart {l : ℕ} (α β : ℝ) : Option (Fin l × Bool) → ℂ
  | none => (α * Real.cot (β / 2) : ℂ) * Complex.I
  | some _ => 0

/-- The regrouping identity of Claim 5: `v_β` is the start contribution plus
the end vector plus the residual `v_β''`. -/
theorem vBeta_decomposition {m l : ℕ} (α β : ℝ) (a : Fin l → ℝ)
    (θ : Fin l → ℝ) (w : Fin l → Bool → Fin m → ℂ) (start : Fin m → ℂ) :
    vBeta α β a θ w start =
      (∑ x, cStart α β x • basisVec w start x) + vEnd a θ w start +
        vBetaResidual α β a θ w start := by
  classical
  have hcoef : ∀ x, cBeta α β a θ x = cStart α β x + cEnd a θ x + cRes α β a θ x := by
    intro x
    rcases x with _ | ⟨j, s⟩
    · simp only [cBeta, cStart, cEnd, cRes]
      ring
    · cases s <;> simp only [cBeta, cStart, cEnd, cRes] <;> push_cast <;> ring
  simp only [vBeta, vEnd, vBetaResidual, hcoef, add_smul, Finset.sum_add_distrib]

/-- The start contribution is the coordinatewise vector `α i cot (β/2) • start`. -/
theorem cStart_sum_eq {m l : ℕ} (α β : ℝ) (w : Fin l → Bool → Fin m → ℂ)
    (start : Fin m → ℂ) :
    (∑ x, cStart (l := l) α β x • basisVec w start x) =
      fun i => (α * Real.cot (β / 2) : ℂ) * Complex.I * start i := by
  classical
  funext i
  rw [sum_option]
  simp [cStart, basisVec, Finset.sum_const_zero]

/-- The paired spectral basis is orthonormal whenever the start direction and
the real eigenbasis are orthonormal. -/
theorem basisVec_orthonormal {m l : ℕ} (w : Fin l → Bool → Fin m → ℂ)
    (start : Fin m → ℂ)
    (hsn : (∑ i, ‖start i‖ ^ 2) = 1)
    (hwn : ∀ j s, (∑ i, ‖w j s i‖ ^ 2) = 1)
    (horth : ∀ (j j' : Fin l) (s s' : Bool), (j, s) ≠ (j', s') →
      (∑ i, star (w j s i) * w j' s' i) = 0)
    (hws : ∀ j s, (∑ i, star (w j s i) * start i) = 0) :
    ∀ x y, (∑ i, star (basisVec w start x i) * basisVec w start y i) =
      if x = y then 1 else 0 := by
  intro x y
  rcases x with _ | ⟨j, s⟩ <;> rcases y with _ | ⟨j', s'⟩
  · rw [ite_eq_left rfl]
    change (∑ i, star (start i) * start i) = (1 : ℂ)
    have h := jw_star_dot_self m start
    change (∑ i, star (start i) * start i) = ((∑ i, ‖start i‖ ^ 2 : ℝ) : ℂ) at h
    rw [h, hsn]
    simp
  · rw [ite_eq_right (by simp)]
    have h := congrArg star (hws j' s')
    simpa [basisVec, star_sum, star_mul, mul_comm] using h
  · rw [ite_eq_right (by simp)]
    exact hws j s
  · by_cases hxy : (j, s) = (j', s')
    · rw [ite_eq_left (by simp [hxy])]
      cases hxy
      change (∑ i, star (w j s i) * w j s i) = (1 : ℂ)
      have h := jw_star_dot_self m (w j s)
      change (∑ i, star (w j s i) * w j s i) = ((∑ i, ‖w j s i‖ ^ 2 : ℝ) : ℂ) at h
      rw [h, hwn j s]
      simp
    · rw [ite_eq_right (by simpa using hxy)]
      exact horth j j' s s' hxy

/-- `toEuclidean_fromVec` commutes with finite linear combinations. -/
theorem toEuclidean_sum_smul {ι : Type*} [Fintype ι] {m : ℕ}
    (c : ι → ℂ) (v : ι → Fin m → ℂ) :
    toEuclidean_fromVec (∑ x, c x • v x) =
      ∑ x, c x • toEuclidean_fromVec (v x) := by
  ext i
  simp [toEuclidean_fromVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- `toEuclidean_fromVec` is additive. -/
theorem toEuclidean_add {m : ℕ} (u v : Fin m → ℂ) :
    toEuclidean_fromVec (u + v) =
      toEuclidean_fromVec u + toEuclidean_fromVec v := by
  ext i
  rfl

/-- `toEuclidean_fromVec` commutes with scalar multiplication. -/
theorem toEuclidean_smul {m : ℕ} (c : ℂ) (v : Fin m → ℂ) :
    toEuclidean_fromVec (c • v) = c • toEuclidean_fromVec v := by
  ext i
  rfl

/-- Squared Euclidean norm of the spectral vector as the sum of squared
coefficient norms. -/
theorem norm_sq_vBeta_eq {m l : ℕ} (α β : ℝ) (a : Fin l → ℝ) (θ : Fin l → ℝ)
    (w : Fin l → Bool → Fin m → ℂ) (start : Fin m → ℂ)
    (hB : ∀ x y : Option (Fin l × Bool),
      (∑ i, star (basisVec w start x i) * basisVec w start y i) =
        if x = y then 1 else 0) :
    ‖toEuclidean_fromVec (vBeta α β a θ w start)‖ ^ 2 =
      ∑ x, ‖cBeta α β a θ x‖ ^ 2 := by
  rw [vBeta, toEuclidean_sum_smul]
  refine norm_sq_sum_smul (fun x => toEuclidean_fromVec (basisVec w start x))
    (cBeta α β a θ) ?_
  intro x y
  rw [inner_euclidean_fromVec, Qatlib.Foundations.PureStateMath.inner_apply]
  exact hB x y

/-- Squared Euclidean norm of the end vector. -/
theorem norm_sq_vEnd_eq {m l : ℕ} (a : Fin l → ℝ) (θ : Fin l → ℝ)
    (w : Fin l → Bool → Fin m → ℂ) (start : Fin m → ℂ)
    (hB : ∀ x y : Option (Fin l × Bool),
      (∑ i, star (basisVec w start x i) * basisVec w start y i) =
        if x = y then 1 else 0) :
    ‖toEuclidean_fromVec (vEnd a θ w start)‖ ^ 2 =
      ∑ x, ‖cEnd a θ x‖ ^ 2 := by
  rw [vEnd, toEuclidean_sum_smul]
  refine norm_sq_sum_smul (fun x => toEuclidean_fromVec (basisVec w start x))
    (cEnd a θ) ?_
  intro x y
  rw [inner_euclidean_fromVec, Qatlib.Foundations.PureStateMath.inner_apply]
  exact hB x y

/-- Squared Euclidean norm of the residual vector. -/
theorem norm_sq_vBetaResidual_eq {m l : ℕ} (α β : ℝ) (a : Fin l → ℝ)
    (θ : Fin l → ℝ) (w : Fin l → Bool → Fin m → ℂ) (start : Fin m → ℂ)
    (hB : ∀ x y : Option (Fin l × Bool),
      (∑ i, star (basisVec w start x i) * basisVec w start y i) =
        if x = y then 1 else 0) :
    ‖toEuclidean_fromVec (vBetaResidual α β a θ w start)‖ ^ 2 =
      ∑ x, ‖cRes α β a θ x‖ ^ 2 := by
  rw [vBetaResidual, toEuclidean_sum_smul]
  refine norm_sq_sum_smul (fun x => toEuclidean_fromVec (basisVec w start x))
    (cRes α β a θ) ?_
  intro x y
  rw [inner_euclidean_fromVec, Qatlib.Foundations.PureStateMath.inner_apply]
  exact hB x y

/-! ## Elementary cotangent estimates -/

/-- On a phase window of width `π - ε`, the absolute sine is bounded below by `ε / 3`.
This is the quantitative form of the source's use of Claim 2 in Claim 5. -/
theorem abs_sin_ge_third (ε B : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hB : ε / 2 ≤ |B|) (hBπ : |B| ≤ Real.pi - ε / 2) :
    ε / 3 ≤ |Real.sin B| := by
  have hBle : |B| ≤ Real.pi := by linarith [Real.pi_pos]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hBle]
  set t := |B| with ht
  have ht0 : 0 ≤ t := abs_nonneg B
  have hsinε : ε / 3 ≤ Real.sin (ε / 2) := by
    have hcube := Real.sin_ge_sub_cube (show 0 ≤ ε / 2 by positivity)
    have hε3 : ε ^ 3 / 48 ≤ ε / 6 := by
      have hcube_le : ε ^ 3 ≤ ε := by nlinarith [sq_nonneg ε, hε0, hε1]
      linarith
    nlinarith [hcube, hε3]
  have hmono : Real.sin (ε / 2) ≤ Real.sin t := by
    by_cases ht2 : t ≤ Real.pi / 2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) ht2 hB
    · have ht2' : Real.pi / 2 < t := lt_of_not_ge ht2
      rw [show Real.sin t = Real.sin (Real.pi - t) from (Real.sin_pi_sub t).symm]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_gt_three])
        (by linarith [ht2']) (by linarith)
  linarith

/-- For `0 < |x| ≤ 1/4`, the absolute cotangent is at least `1 / (2 |x|)`. -/
theorem one_div_two_abs_le_abs_cot {x : ℝ} (hx0 : x ≠ 0) (hx : |x| ≤ 1 / 4) :
    1 / (2 * |x|) ≤ |Real.cot x| := by
  have hxpos : 0 < |x| := abs_pos.mpr hx0
  have hxlt : |x| < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hcos : 0 < Real.cos x := by
    rw [← Real.cos_abs]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcos_half : (1 / 2 : ℝ) ≤ Real.cos x := by
    have h := Real.one_sub_sq_div_two_le_cos (x := x)
    have hx2 : x ^ 2 ≤ 1 / 16 := by
      nlinarith [abs_nonneg x, sq_abs x]
    linarith
  have hsinpos : 0 < |Real.sin x| := by
    rw [abs_pos]
    intro hzero
    have hxpi : -Real.pi < x ∧ x < Real.pi := by
      constructor <;> nlinarith [abs_nonneg x, le_abs_self x, neg_abs_le x, Real.pi_gt_three]
    exact hx0 ((Real.sin_eq_zero_iff_of_lt_of_lt hxpi.1 hxpi.2).mp hzero)
  have hsinle : |Real.sin x| ≤ |x| := (Real.abs_sin_lt_abs hx0).le
  have hcot : |Real.cot x| = Real.cos x / |Real.sin x| := by
    rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hcos]
  rw [hcot]
  have h1 : (1 / 2 : ℝ) / |Real.sin x| ≤ Real.cos x / |Real.sin x| := by
    exact div_le_div_of_nonneg_right hcos_half hsinpos.le
  have h2 : 1 / (2 * |x|) ≤ (1 / 2 : ℝ) / |Real.sin x| := by
    have hinv : 1 / |x| ≤ 1 / |Real.sin x| :=
      one_div_le_one_div_of_le hsinpos hsinle
    calc 1 / (2 * |x|) = (1 / 2 : ℝ) * (1 / |x|) := by field_simp
      _ ≤ (1 / 2 : ℝ) * (1 / |Real.sin x|) := by
            exact mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = (1 / 2 : ℝ) / |Real.sin x| := by field_simp
  exact le_trans h2 h1

/-- The uniform constant `3` controls the start coefficient of the residual: for
`0 < |β| ≤ ε / 2` and `0 < ε ≤ 1`,
`1 ≤ (3 |β| / ε) |cot (β / 2)|`. -/
theorem one_le_scale_mul_abs_cot_half (ε β : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hβ0 : β ≠ 0) (hβ : |β| ≤ ε / 2) :
    1 ≤ (3 * |β| / ε) * |Real.cot (β / 2)| := by
  have hβabs : 0 < |β| := abs_pos.mpr hβ0
  have hx0 : β / 2 ≠ 0 := div_ne_zero hβ0 (by norm_num)
  have hxle : |β / 2| ≤ 1 / 4 := by
    rw [abs_div, show |(2 : ℝ)| = 2 by norm_num, div_le_iff₀ (by norm_num)]
    nlinarith [hβ, hε1]
  have hcot := one_div_two_abs_le_abs_cot hx0 hxle
  have hkey : 1 / |β| ≤ |Real.cot (β / 2)| := by
    have hxabs : |β / 2| = |β| / 2 := by
      rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
    rw [hxabs] at hcot
    have : 1 / (2 * (|β| / 2)) = 1 / |β| := by field_simp
    simpa [this] using hcot
  have hmul : (3 * |β| / ε) * (1 / |β|) ≤ (3 * |β| / ε) * |Real.cot (β / 2)| := by
    exact mul_le_mul_of_nonneg_left hkey (by positivity)
  have hone : (3 * |β| / ε) * (1 / |β|) = 3 / ε := by
    field_simp
  have hthree : (3 : ℝ) ≤ 3 / ε := by
    rw [le_div_iff₀ hε0]
    nlinarith [hε1]
  linarith [hmul, hone.symm ▸ hthree]

/-- The absolute value of the complex factor `1 + i cot x` is the reciprocal of
`|sin x|`. -/
theorem norm_one_add_I_cot (x : ℝ) (hsin : Real.sin x ≠ 0) :
    ‖(1 : ℂ) + Complex.I * (Real.cot x : ℂ)‖ = 1 / |Real.sin x| := by
  have hsq : ‖(1 : ℂ) + Complex.I * (Real.cot x : ℂ)‖ ^ 2 =
      (1 / |Real.sin x|) ^ 2 := by
    rw [Complex.sq_norm]
    rw [show (1 : ℂ) + Complex.I * (Real.cot x : ℂ) =
        (1 : ℝ) + (Real.cot x) * Complex.I by push_cast; ring]
    rw [Complex.normSq_add_mul_I, Real.cot_eq_cos_div_sin]
    have habs2 : (1 / |Real.sin x|) ^ 2 = 1 / Real.sin x ^ 2 := by
      rw [div_pow, one_pow, sq_abs]
    rw [habs2]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hnn : 0 ≤ 1 / |Real.sin x| := by positivity
  exact (sq_eq_sq₀ (norm_nonneg _) hnn).mp hsq

/-- The imaginary part of `1 + i cot x` recovers the cotangent, so its modulus
dominates `|cot x|`. -/
theorem abs_cot_le_norm_one_add_I_cot (x : ℝ) :
    |Real.cot x| ≤ ‖(1 : ℂ) + Complex.I * (Real.cot x : ℂ)‖ := by
  have h := Complex.abs_im_le_norm ((1 : ℂ) + Complex.I * (Real.cot x : ℂ))
  have him : (1 + Complex.I * (Real.cot x : ℂ)).im = Real.cot x := by
    simp only [Complex.add_im, Complex.one_im, zero_add, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul]
  rw [him] at h
  exact h

/-- Norm of a real scalar times `i` times a real scalar. -/
theorem norm_mul_I_real_cast (a x : ℝ) :
    ‖(a : ℂ) * Complex.I * ((x : ℝ) : ℂ)‖ = |a| * |x| := by
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real]
  rw [Real.norm_eq_abs, Real.norm_eq_abs]

/-- Norm of a real scalar times `1 + i cot x`. -/
theorem norm_real_mul_one_add_I_cot (a x : ℝ) :
    ‖(a : ℂ) * (1 + Complex.I * (Real.cot x : ℂ))‖ =
      |a| * ‖(1 : ℂ) + Complex.I * (Real.cot x : ℂ)‖ := by
  rw [norm_mul, Complex.norm_real]
  rw [Real.norm_eq_abs]

/-- Norm of the start coefficient of `v_β`. -/
theorem norm_cBeta_none {l : ℕ} (α β : ℝ) (a : Fin l → ℝ) (θ : Fin l → ℝ)
    (hα : 0 < α) :
    ‖cBeta α β a θ none‖ = α * ‖(1 : ℂ) + Complex.I * (Real.cot (β / 2) : ℂ)‖ := by
  simp [cBeta, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]

/-- Norm of the start coefficient of the residual. -/
theorem norm_cRes_none {l : ℕ} (α β : ℝ) (a : Fin l → ℝ) (θ : Fin l → ℝ)
    (hα : 0 < α) : ‖cRes α β a θ none‖ = α := by
  simp [cRes, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]

/-- Norm of the `+` coefficient of `v_β`. -/
theorem norm_cBeta_some_true {l : ℕ} (α β : ℝ) (a : Fin l → ℝ) (θ : Fin l → ℝ)
    (j : Fin l) :
    ‖cBeta α β a θ (some (j, true))‖ =
      |a j| * ‖(1 : ℂ) + Complex.I * (Real.cot ((β - θ j) / 2) : ℂ)‖ := by
  simp only [cBeta]
  rw [norm_real_mul_one_add_I_cot]

/-- Norm of the `-` coefficient of `v_β`. -/
theorem norm_cBeta_some_false {l : ℕ} (α β : ℝ) (a : Fin l → ℝ) (θ : Fin l → ℝ)
    (j : Fin l) :
    ‖cBeta α β a θ (some (j, false))‖ =
      |a j| * ‖(1 : ℂ) + Complex.I * (Real.cot ((β + θ j) / 2) : ℂ)‖ := by
  simp only [cBeta]
  rw [norm_real_mul_one_add_I_cot]

/-- Norm of the `+` residual coefficient. -/
theorem norm_cRes_some_true {l : ℕ} (α β : ℝ) (a : Fin l → ℝ) (θ : Fin l → ℝ)
    (j : Fin l) :
    ‖cRes α β a θ (some (j, true))‖ =
      |a j| * |Real.cot ((β - θ j) / 2) - Real.cot (-(θ j) / 2)| := by
  simp only [cRes]
  rw [norm_mul_I_real_cast]

/-- Norm of the `-` residual coefficient. -/
theorem norm_cRes_some_false {l : ℕ} (α β : ℝ) (a : Fin l → ℝ) (θ : Fin l → ℝ)
    (j : Fin l) :
    ‖cRes α β a θ (some (j, false))‖ =
      |a j| * |Real.cot ((β + θ j) / 2) - Real.cot (θ j / 2)| := by
  simp only [cRes]
  rw [norm_mul_I_real_cast]

/-- The elementary cotangent estimate of Claim 5: shifting a phase by `β / 2` changes
the cotangent by at most `(3 |β| / ε)` times the complex coefficient modulus. -/
theorem abs_cot_shift_sub_le (ε β B : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hβ0 : β ≠ 0) (hβ : |β| ≤ ε / 2)
    (hB : ε / 2 ≤ |B|) (hBπ : |B| ≤ Real.pi - ε / 2) :
    |Real.cot (B + β / 2) - Real.cot B| ≤
      (3 * |β| / ε) * ‖(1 : ℂ) + Complex.I * (Real.cot (B + β / 2) : ℂ)‖ := by
  have hεhalf : 0 < ε / 2 := by positivity
  have hβhalf : |β / 2| ≤ ε / 4 := by
    rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
    nlinarith [hβ]
  have hA : ε / 4 ≤ |B + β / 2| := by
    have hrt := abs_abs_sub_abs_le_abs_sub B (B + β / 2)
    have hsub : |B - (B + β / 2)| = |β / 2| := by
      rw [show B - (B + β / 2) = -(β / 2) by ring, abs_neg]
    rw [hsub] at hrt
    have hle : |B| - |B + β / 2| ≤ |β / 2| :=
      (le_abs_self (|B| - |B + β / 2|)).trans hrt
    linarith
  have hAπ : |B + β / 2| ≤ Real.pi - ε / 4 := by
    calc |B + β / 2| ≤ |B| + |β / 2| := abs_add_le _ _
      _ ≤ (Real.pi - ε / 2) + ε / 4 := by linarith
      _ = Real.pi - ε / 4 := by ring
  have hBne : Real.sin B ≠ 0 := by
    intro hzero
    have hlt : -Real.pi < B ∧ B < Real.pi := by
      constructor <;> nlinarith [abs_nonneg B, le_abs_self B, neg_abs_le B, Real.pi_gt_three]
    have hB0 : B ≠ 0 := abs_pos.mp (by linarith)
    exact hB0 ((Real.sin_eq_zero_iff_of_lt_of_lt hlt.1 hlt.2).mp hzero)
  have hAne : Real.sin (B + β / 2) ≠ 0 := by
    intro hzero
    have hlt : -Real.pi < B + β / 2 ∧ B + β / 2 < Real.pi := by
      constructor <;> nlinarith [abs_nonneg (B + β / 2), le_abs_self (B + β / 2),
        neg_abs_le (B + β / 2), Real.pi_gt_three]
    have hA0 : B + β / 2 ≠ 0 := abs_pos.mp (by linarith)
    exact hA0 ((Real.sin_eq_zero_iff_of_lt_of_lt hlt.1 hlt.2).mp hzero)
  have hidentity : Real.cot (B + β / 2) - Real.cot B =
      -Real.sin (β / 2) / (Real.sin (B + β / 2) * Real.sin B) := by
    have hsinAB : Real.sin (β / 2) =
        Real.sin (B + β / 2) * Real.cos B - Real.cos (B + β / 2) * Real.sin B := by
      have hAB : (B + β / 2) - B = β / 2 := by ring
      nth_rewrite 1 [← hAB]
      rw [Real.sin_sub]
    have hnum : Real.cos (B + β / 2) * Real.sin B -
        Real.sin (B + β / 2) * Real.cos B = -Real.sin (β / 2) := by
      linarith [hsinAB]
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
      div_sub_div _ _ hAne hBne, hnum]
  have habs : |Real.cot (B + β / 2) - Real.cot B| =
      |Real.sin (β / 2)| / (|Real.sin (B + β / 2)| * |Real.sin B|) := by
    rw [hidentity, abs_div, abs_neg, abs_mul]
  rw [habs, norm_one_add_I_cot _ hAne]
  have hsinB_lower : ε / 3 ≤ |Real.sin B| := abs_sin_ge_third ε B hε0 hε1 hB hBπ
  have hsinApos : 0 < |Real.sin (B + β / 2)| := abs_pos.mpr hAne
  have hsinBpos : 0 < |Real.sin B| := abs_pos.mpr hBne
  have hnum : |Real.sin (β / 2)| ≤ |β| / 2 := by
    have h := Real.abs_sin_lt_abs (by exact div_ne_zero hβ0 (by norm_num) :
      β / 2 ≠ 0)
    rw [abs_div, show |(2 : ℝ)| = 2 by norm_num] at h
    linarith [h.le]
  have hratio : |Real.sin (β / 2)| / |Real.sin B| ≤ 3 * |β| / ε := by
    have hstep : |Real.sin (β / 2)| / |Real.sin B| ≤ (|β| / 2) / (ε / 3) := by
      exact div_le_div₀ (by positivity) hnum (by positivity) hsinB_lower
    have heq : (|β| / 2) / (ε / 3) = 3 * |β| / (2 * ε) := by field_simp
    have hle : 3 * |β| / (2 * ε) ≤ 3 * |β| / ε := by
      rw [div_le_div_iff₀ (by positivity) hε0]
      nlinarith [abs_nonneg β, hε1]
    linarith [hstep, heq ▸ hle]
  calc |Real.sin (β / 2)| / (|Real.sin (B + β / 2)| * |Real.sin B|)
      = (|Real.sin (β / 2)| / |Real.sin B|) * (1 / |Real.sin (B + β / 2)|) := by
        field_simp
    _ ≤ (3 * |β| / ε) * (1 / |Real.sin (B + β / 2)|) := by
        exact mul_le_mul_of_nonneg_right hratio (by positivity)

/-- **Claim 5, exact two-vector coefficient decomposition.**

For a real paired orthonormal spectral model with a genuine phase gap, the
normalized spectral vector `u_β = v_β / ‖v_β‖` splits into the start
direction, the end direction, and a residual.  The coefficients are positive
and the Euclidean residual is at most `3 β / ε`.  The constant `3` is uniform
and is placed outside all quantifiers. -/
theorem claim5_two_vector_decomposition :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m l : ℕ) [Nonempty (Fin m)] (ε α β : ℝ)
        (a : Fin l → ℝ) (θ : Fin l → ℝ) (w : Fin l → Bool → Fin m → ℂ)
        (start : Fin m → ℂ),
        0 < l → 2 * l + 1 ≤ m →
        0 < ε → ε ≤ 1 → 0 < α → 0 < β → β ≤ ε / 2 →
        (∑ i, ‖start i‖ ^ 2) = 1 →
        (∀ j s, (∑ i, ‖w j s i‖ ^ 2) = 1) →
        (∀ (j j' : Fin l) (s s' : Bool), (j, s) ≠ (j', s') →
          (∑ i, star (w j s i) * w j' s' i) = 0) →
        (∀ j s, (∑ i, star (w j s i) * start i) = 0) →
        (∀ j, ε ≤ θ j ∧ θ j ≤ 2 * Real.pi - ε ∧ θ j ≠ Real.pi) →
        let vβ := vBeta α β a θ w start
        let vE := vEnd a θ w start
        let vR := vBetaResidual α β a θ w start
        let eβ := toEuclidean_fromVec vβ
        let eS := toEuclidean_fromVec start
        let eE := toEuclidean_fromVec vE
        let eR := toEuclidean_fromVec vR
        vE ≠ 0 →
        vβ = (fun i => (α * Real.cot (β / 2) : ℂ) * Complex.I * start i) + vE + vR ∧
        ∃ cS cE : ℝ, 0 < cS ∧ 0 < cE ∧
          cS = α * Real.cot (β / 2) / ‖eβ‖ ∧
          cE = ‖eE‖ / ‖eβ‖ ∧
          (((‖eβ‖ : ℝ) : ℂ))⁻¹ • eβ =
            ((cS : ℂ) * Complex.I) • eS +
              cE • ((((‖eE‖ : ℝ) : ℂ))⁻¹ • eE) +
                (((‖eβ‖ : ℝ) : ℂ))⁻¹ • eR ∧
          ‖(((‖eβ‖ : ℝ) : ℂ))⁻¹ • eR‖ ≤ C * β / ε := by
  refine ⟨3, by norm_num, ?_⟩
  intro m l _ ε α β a θ w start hl hm hε0 hε1 hα hβpos hβle
    hsn hwn horth hws hθ
  dsimp only
  intro hEnd
  have hβne : β ≠ 0 := ne_of_gt hβpos
  have hβabs : |β| ≤ ε / 2 := by rwa [abs_of_pos hβpos]
  have hβhalfpos : 0 < β / 2 := by positivity
  have hβhalfπ : β / 2 < Real.pi := by
    have hβhalf_le : β / 2 ≤ 1 / 4 := by linarith [hβle, hε1]
    linarith [hβhalf_le, Real.pi_gt_three]
  have hsin : Real.sin (β / 2) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hβhalfpos hβhalfπ)
  have hcot : 0 < Real.cot (β / 2) := by
    rw [Real.cot_eq_cos_div_sin]
    have hβhalf_le : β / 2 ≤ 1 / 4 := by linarith [hβle, hε1]
    have hβhalf_lt : β / 2 < Real.pi / 2 := by
      linarith [hβhalf_le, Real.pi_gt_three]
    exact div_pos
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [hβhalfpos], hβhalf_lt⟩)
      (Real.sin_pos_of_pos_of_lt_pi hβhalfpos hβhalfπ)
  set K : ℝ := 3 * β / ε with hK
  have hKpos : 0 < K := by positivity
  have hB := basisVec_orthonormal w start hsn hwn horth hws
  have hsqβ := norm_sq_vBeta_eq α β a θ w start hB
  have hsqR := norm_sq_vBetaResidual_eq α β a θ w start hB
  set eβ : EuclideanSpace ℂ (Fin m) := toEuclidean_fromVec (vBeta α β a θ w start) with heβ
  set eS : EuclideanSpace ℂ (Fin m) := toEuclidean_fromVec start
  set eE : EuclideanSpace ℂ (Fin m) := toEuclidean_fromVec (vEnd a θ w start)
  set eR : EuclideanSpace ℂ (Fin m) := toEuclidean_fromVec
    (vBetaResidual α β a θ w start)
  have hdec : vBeta α β a θ w start =
      (fun i => (α * Real.cot (β / 2) : ℂ) * Complex.I * start i) +
        vEnd a θ w start + vBetaResidual α β a θ w start := by
    rw [vBeta_decomposition, cStart_sum_eq]
  have hcoef : ∀ x, ‖cRes α β a θ x‖ ≤ K * ‖cBeta α β a θ x‖ := by
    intro x
    rcases x with _ | ⟨j, s⟩
    · rw [norm_cRes_none α β a θ hα, norm_cBeta_none α β a θ hα]
      have hscale : 1 ≤ K * |Real.cot (β / 2)| := by
        simpa [hK, abs_of_pos hβpos] using
          one_le_scale_mul_abs_cot_half ε β hε0 hε1 hβne hβabs
      have habs := abs_cot_le_norm_one_add_I_cot (β / 2)
      have hKn : 1 ≤ K * ‖(1 : ℂ) + Complex.I * (Real.cot (β / 2) : ℂ)‖ :=
        hscale.trans (mul_le_mul_of_nonneg_left habs hKpos.le)
      calc α = α * 1 := by ring
        _ ≤ α * (K * ‖(1 : ℂ) + Complex.I * (Real.cot (β / 2) : ℂ)‖) :=
              mul_le_mul_of_nonneg_left hKn hα.le
        _ = K * (α * ‖(1 : ℂ) + Complex.I * (Real.cot (β / 2) : ℂ)‖) := by ring
    · cases s
      · rw [norm_cRes_some_false, norm_cBeta_some_false]
        have hθj := hθ j
        have hθpos : 0 < θ j := lt_of_lt_of_le hε0 hθj.1
        have hBε : ε / 2 ≤ |θ j / 2| := by
          rw [abs_div, abs_of_pos hθpos]
          norm_num
          linarith [hθj.1]
        have hBπ : |θ j / 2| ≤ Real.pi - ε / 2 := by
          rw [abs_div, abs_of_pos hθpos]
          norm_num
          linarith [hθj.2.1]
        have htrig := abs_cot_shift_sub_le ε β (θ j / 2) hε0 hε1 hβne hβabs hBε hBπ
        have htrig' : |Real.cot ((β + θ j) / 2) - Real.cot (θ j / 2)| ≤
            (3 * |β| / ε) * ‖(1 : ℂ) + Complex.I * (Real.cot ((β + θ j) / 2) : ℂ)‖ := by
          have harg : θ j / 2 + β / 2 = (β + θ j) / 2 := by ring
          rw [harg] at htrig
          exact htrig
        have hmul := mul_le_mul_of_nonneg_left htrig' (abs_nonneg (a j))
        simpa [hK, abs_of_pos hβpos, mul_assoc, mul_left_comm, mul_comm] using hmul
      · rw [norm_cRes_some_true, norm_cBeta_some_true]
        have hθj := hθ j
        have hθpos : 0 < θ j := lt_of_lt_of_le hε0 hθj.1
        have hBε : ε / 2 ≤ |(-(θ j)) / 2| := by
          rw [abs_div, abs_neg, abs_of_pos hθpos]
          norm_num
          linarith [hθj.1]
        have hBπ : |(-(θ j)) / 2| ≤ Real.pi - ε / 2 := by
          rw [abs_div, abs_neg, abs_of_pos hθpos]
          norm_num
          linarith [hθj.2.1]
        have htrig := abs_cot_shift_sub_le ε β (-(θ j) / 2) hε0 hε1 hβne hβabs hBε hBπ
        have htrig' : |Real.cot ((β - θ j) / 2) - Real.cot (-(θ j) / 2)| ≤
            (3 * |β| / ε) * ‖(1 : ℂ) + Complex.I * (Real.cot ((β - θ j) / 2) : ℂ)‖ := by
          have harg : -(θ j) / 2 + β / 2 = (β - θ j) / 2 := by ring
          rw [harg] at htrig
          exact htrig
        have hmul := mul_le_mul_of_nonneg_left htrig' (abs_nonneg (a j))
        simpa [hK, abs_of_pos hβpos, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hsum_le : (∑ x, ‖cRes α β a θ x‖ ^ 2) ≤
      K ^ 2 * ∑ x, ‖cBeta α β a θ x‖ ^ 2 := by
    calc (∑ x, ‖cRes α β a θ x‖ ^ 2) ≤ ∑ x, (K * ‖cBeta α β a θ x‖) ^ 2 := by
          refine Finset.sum_le_sum (fun x _ => ?_)
          exact pow_le_pow_left₀ (norm_nonneg _) (hcoef x) 2
      _ = ∑ x, K ^ 2 * ‖cBeta α β a θ x‖ ^ 2 := by simp_rw [mul_pow]
      _ = K ^ 2 * ∑ x, ‖cBeta α β a θ x‖ ^ 2 := by rw [Finset.mul_sum]
  have hres_sq : ‖eR‖ ^ 2 ≤ K ^ 2 * ‖eβ‖ ^ 2 := by
    rw [hsqR, hsqβ]
    exact hsum_le
  have hres_le : ‖eR‖ ≤ K * ‖eβ‖ := by
    have hsq : ‖eR‖ ^ 2 ≤ (K * ‖eβ‖) ^ 2 := by
      rw [mul_pow]
      exact hres_sq
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hKpos.le (norm_nonneg _))).mp hsq
  have hcBetaPos : 0 < ‖cBeta α β a θ none‖ := by
    rw [norm_cBeta_none α β a θ hα, norm_one_add_I_cot _ hsin]
    exact mul_pos hα (one_div_pos.mpr (abs_pos.mpr hsin))
  have hsum_pos : 0 < ∑ x, ‖cBeta α β a θ x‖ ^ 2 := by
    have hsingle := Finset.single_le_sum
      (s := (Finset.univ : Finset (Option (Fin l × Bool))))
      (f := fun x => ‖cBeta α β a θ x‖ ^ 2)
      (fun x _ => sq_nonneg _) (Finset.mem_univ none)
    exact lt_of_lt_of_le (sq_pos_of_pos hcBetaPos) hsingle
  have hnβ : 0 < ‖eβ‖ := by
    have hsqpos : 0 < ‖eβ‖ ^ 2 := by
      rw [hsqβ]
      exact hsum_pos
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm (sq_pos_iff.mp hsqpos))
  have heE_ne : eE ≠ 0 := by
    intro hzero
    apply hEnd
    have := congrArg toVec_fromEuclidean hzero
    simpa [eE, toEuclidean_fromVec, toVec_fromEuclidean] using this
  have hnE : 0 < ‖eE‖ := norm_pos_iff.mpr heE_ne
  have hdecE : eβ = ((α * Real.cot (β / 2) : ℂ) * Complex.I) • eS + eE + eR := by
    have hstart : toEuclidean_fromVec
        (fun i => (α * Real.cot (β / 2) : ℂ) * Complex.I * start i) =
          ((α * Real.cot (β / 2) : ℂ) * Complex.I) • eS := by
      ext i
      rfl
    rw [show eβ = toEuclidean_fromVec (vBeta α β a θ w start) from rfl, hdec,
      toEuclidean_add, toEuclidean_add, hstart]
  refine ⟨hdec, ?_⟩
  refine ⟨α * Real.cot (β / 2) / ‖eβ‖, ‖eE‖ / ‖eβ‖,
    div_pos (mul_pos hα hcot) hnβ, div_pos hnE hnβ, rfl, rfl, ?_, ?_⟩
  · have hS : ((‖eβ‖ : ℝ) : ℂ)⁻¹ * ((α * Real.cot (β / 2) : ℂ) * Complex.I) =
        ((α * Real.cot (β / 2) / ‖eβ‖ : ℝ) : ℂ) * Complex.I := by
      push_cast
      field_simp [ne_of_gt hnβ]
    have hE : ((‖eβ‖ : ℝ) : ℂ)⁻¹ =
        (‖eE‖ / ‖eβ‖ : ℝ) • ((‖eE‖ : ℝ) : ℂ)⁻¹ := by
      rw [Complex.real_smul, Complex.ofReal_div]
      field_simp [ne_of_gt hnβ, ne_of_gt hnE]
    rw [hdecE, smul_add, smul_add, ← hdecE]
    change ((‖eβ‖ : ℝ) : ℂ)⁻¹ • (((α * Real.cot (β / 2) : ℂ) * Complex.I) • eS) +
        ((‖eβ‖ : ℝ) : ℂ)⁻¹ • eE + ((‖eβ‖ : ℝ) : ℂ)⁻¹ • eR =
      (((α * Real.cot (β / 2) / ‖eβ‖ : ℝ) : ℂ) * Complex.I) • eS +
        ((‖eE‖ / ‖eβ‖ : ℝ) : ℂ) • (((‖eE‖ : ℝ) : ℂ)⁻¹ • eE) +
          ((‖eβ‖ : ℝ) : ℂ)⁻¹ • eR
    rw [smul_smul, hS, ← IsScalarTower.smul_assoc, hE]
    rfl
  · rw [norm_smul, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    have hbound := mul_le_mul_of_nonneg_left hres_le
      (inv_nonneg.mpr (norm_nonneg (eβ)))
    have hcancel : (‖eβ‖)⁻¹ * (K * ‖eβ‖) = K := by
      field_simp [ne_of_gt hnβ]
    linarith

end

end Qatlib.Papers.QWalkAmbainis03.GroverInterp.TwoVectorDecomposition
