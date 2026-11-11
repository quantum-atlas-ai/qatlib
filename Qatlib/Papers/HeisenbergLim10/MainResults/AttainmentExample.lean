/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Attainment of the Heisenberg limit, Eq. (11)

Source: Zwierz, Pérez-Delgado, Kok, *General optimality of the Heisenberg limit
for quantum metrology*, fixed arXiv:1004.3944 (2010), p. 4.

The paper exhibits a single-mode construction that formally reaches the
Heisenberg limit.  In the two-dimensional span of the Fock states `|0⟩` and
`|N⟩`:

* the input state is `|ψ₀⟩ = (|0⟩ + |N⟩)/√2`;
* the phase evolution is `|ψ(φ)⟩ = exp(-i φ n̂²)|ψ₀⟩
  = (|0⟩ + exp(-i N² φ)|N⟩)/√2`;
* the measurement observable is `X = |0⟩⟨N| + |N⟩⟨0|`.

Writing the state in the ordered basis `(|0⟩, |N⟩)` as the pair
`(ψ₀, ψ₁) = (1/√2, exp(-iθ)/√2)` with `θ = N²φ`, the two operators act as

* `X (ψ₀, ψ₁) = (ψ₁, ψ₀)` (the matrix `!![0, 1; 1, 0]`);
* `n̂² (ψ₀, ψ₁) = (0, N² ψ₁)` (the matrix `diag(0, N²)`).

The paper computes `⟨X⟩ = cos(N²φ)`, `ΔX = sin(N²φ)`, and, with the standard
mean-squared-error propagation,

```
δφ = ΔX / |d⟨X⟩/dφ| = 1/N².                                      (11)
```

Since the resource count is `|⟨H⟩| = ⟨n̂²⟩ = N²/2`, the construction attains the
Heisenberg limit.

This module realizes these two-component expectation values explicitly over `ℂ`
and proves the three numerical consequences of Eq. (11): the expectation, the
variance, and the propagated error, together with the resource value.

Note on normalization: the literal numbers displayed in the source give
`δφ · |⟨H⟩| = (1/N²)(N²/2) = 1/2`; we formalize exactly these computed values.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HeisenbergLim10.MainResults

/-- `1/√2`, the amplitude normalizing the single-mode input state. -/
def invSqrtTwo : ℝ := (Real.sqrt 2)⁻¹

/-- The normalizing amplitude squares to `1/2`. -/
lemma invSqrtTwo_sq : invSqrtTwo ^ 2 = (1 : ℝ) / 2 := by
  rw [invSqrtTwo, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The normalizing amplitude is nonzero. -/
lemma invSqrtTwo_ne_zero : invSqrtTwo ≠ 0 := by
  rw [invSqrtTwo]
  exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))

/-- `|0⟩`-component of the evolved state, `1/√2`. -/
def stateZero (_θ : ℝ) : ℂ := ((invSqrtTwo : ℝ) : ℂ)

/-- `|N⟩`-component of the evolved state, `exp(-iθ)/√2`. -/
def stateOne (θ : ℝ) : ℂ := Complex.exp (-(θ * Complex.I)) * ((invSqrtTwo : ℝ) : ℂ)

/-- Expectation `⟨ψ|X|ψ⟩` for `X = |0⟩⟨N| + |N⟩⟨0|`, whose action on the
ordered basis is `(ψ₀, ψ₁) ↦ (ψ₁, ψ₀)`. -/
def xExpectation (θ : ℝ) : ℂ :=
  star (stateZero θ) * stateOne θ + star (stateOne θ) * stateZero θ

/-- Second moment `⟨ψ|X²|ψ⟩`.  Since `X² = 1`, this is the squared norm of the
state. -/
def xSecondMoment (θ : ℝ) : ℂ :=
  star (stateZero θ) * stateZero θ + star (stateOne θ) * stateOne θ

/-- Expectation `⟨ψ|n̂²|ψ⟩` for `n̂² = diag(0, N²)`. -/
def numberSquaredExpectation (N : ℕ) (θ : ℝ) : ℂ :=
  star (stateZero θ) * (0 * stateZero θ) +
    star (stateOne θ) * (((N : ℝ) ^ 2 : ℂ) * stateOne θ)

/-- Mean-squared-error propagation `δφ = ΔX / |d⟨X⟩/dφ|`, Eq. (11). -/
def meanSquaredError (ΔX dmean : ℝ) : ℝ := ΔX / |dmean|

/-- `star (exp(-iθ)) = exp(iθ)`. -/
lemma star_exp_neg_mul_I (θ : ℝ) :
    star (Complex.exp (-(θ * Complex.I))) = Complex.exp (θ * Complex.I) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

/-- The two phases cancel: `exp(iθ) * exp(-iθ) = 1`. -/
lemma exp_mul_exp_neg (θ : ℝ) :
    Complex.exp (θ * Complex.I) * Complex.exp (-(θ * Complex.I)) = 1 := by
  rw [← Complex.exp_add]
  simp

/-- The real amplitude is fixed by conjugation. -/
lemma star_invSqrtTwo : star ((invSqrtTwo : ℝ) : ℂ) = ((invSqrtTwo : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

/-- The squared amplitude is `1/2`. -/
lemma invSqrtTwo_sq_complex : ((invSqrtTwo : ℝ) : ℂ) ^ 2 = (1 / 2 : ℂ) := by
  rw [← Complex.ofReal_pow, invSqrtTwo_sq]
  norm_num

/-- `|ψ₁|² = 1/2`. -/
lemma stateOne_norm_sq (θ : ℝ) :
    star (stateOne θ) * stateOne θ = (1 / 2 : ℂ) := by
  unfold stateOne
  rw [star_mul, star_exp_neg_mul_I θ, star_invSqrtTwo]
  have hcomm : (invSqrtTwo : ℂ) * Complex.exp (θ * Complex.I) *
      (Complex.exp (-(θ * Complex.I)) * (invSqrtTwo : ℂ)) =
      (Complex.exp (θ * Complex.I) * Complex.exp (-(θ * Complex.I))) *
        ((invSqrtTwo : ℂ) * (invSqrtTwo : ℂ)) := by ring
  rw [hcomm, exp_mul_exp_neg, one_mul, ← pow_two, invSqrtTwo_sq_complex]

/-- Fixed arXiv:1004.3944, Eq. (11), p. 4: the state is normalized,
`⟨X²⟩ = |ψ₀|² + |ψ₁|² = 1`. -/
theorem xSecondMoment_eq (θ : ℝ) : xSecondMoment θ = 1 := by
  unfold xSecondMoment stateZero
  rw [star_invSqrtTwo, stateOne_norm_sq θ]
  have h0 : ((invSqrtTwo : ℝ) : ℂ) * ((invSqrtTwo : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    rw [← pow_two, invSqrtTwo_sq_complex]
  rw [h0]
  norm_num

/-- Fixed arXiv:1004.3944, Eq. (11), p. 4: the expectation of
`X = |0⟩⟨N| + |N⟩⟨0|` in the evolved state is `⟨X⟩ = cos(N²φ)`. -/
theorem xExpectation_eq (θ : ℝ) : xExpectation θ = (Real.cos θ : ℂ) := by
  have hcos : (Real.cos θ : ℂ) =
      (Complex.exp (-(θ * Complex.I)) + Complex.exp (θ * Complex.I)) / 2 := by
    have h1 : Complex.exp (-(θ * Complex.I)) =
        Complex.cos (θ : ℂ) - Complex.sin (θ : ℂ) * Complex.I := by
      rw [show -(θ * Complex.I) = (-(θ : ℂ)) * Complex.I by ring]
      rw [Complex.exp_mul_I]
      simp [Complex.cos_neg, Complex.sin_neg]
      ring
    have h2 : Complex.exp (θ * Complex.I) =
        Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I := by
      rw [Complex.exp_mul_I]
    rw [h1, h2, ← Complex.ofReal_cos]
    ring
  -- `⟨X⟩ = c² exp(-iθ) + c² exp(iθ)` with `c = 1/√2`.
  have hval : xExpectation θ =
      ((invSqrtTwo : ℝ) : ℂ) ^ 2 *
        (Complex.exp (-(θ * Complex.I)) + Complex.exp (θ * Complex.I)) := by
    unfold xExpectation stateZero stateOne
    rw [star_mul, star_exp_neg_mul_I θ, star_invSqrtTwo]
    ring
  rw [hval, hcos, invSqrtTwo_sq_complex]
  ring

/-- Fixed arXiv:1004.3944, Eq. (11), p. 4: the variance of `X` is
`(ΔX)² = ⟨X²⟩ - ⟨X⟩² = sin²(N²φ)`. -/
theorem xVariance (θ : ℝ) :
    xSecondMoment θ - (xExpectation θ) ^ 2 = ((Real.sin θ) ^ 2 : ℂ) := by
  rw [xSecondMoment_eq, xExpectation_eq]
  have hreal : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  calc
    (1 : ℂ) - ((Real.cos θ : ℝ) : ℂ) ^ 2
        = ((1 - Real.cos θ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    _ = ((Real.sin θ ^ 2 : ℝ) : ℂ) := by rw [hreal]
    _ = ((Real.sin θ : ℝ) : ℂ) ^ 2 := by push_cast; ring

/-- Fixed arXiv:1004.3944, Eq. (11), p. 4: the resource count of the probe is
`|⟨H⟩| = ⟨n̂²⟩ = N²/2` in the state `(1, exp(-iθ))/√2`. -/
theorem numberSquaredExpectation_eq (N : ℕ) (θ : ℝ) :
    numberSquaredExpectation N θ = (((N : ℝ) ^ 2 / 2 : ℝ) : ℂ) := by
  unfold numberSquaredExpectation stateZero
  rw [zero_mul, mul_zero, zero_add]
  have hN : star (stateOne θ) * (((N : ℝ) ^ 2 : ℂ) * stateOne θ) =
      ((N : ℝ) ^ 2 : ℂ) * (star (stateOne θ) * stateOne θ) := by ring
  rw [hN, stateOne_norm_sq θ]
  have hcast : ((N : ℝ) ^ 2 : ℂ) * (1 / 2 : ℂ) =
      (((N : ℝ) ^ 2 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  exact hcast

/-- The mean phase signal `⟨X⟩(φ) = cos(N²φ)` as a function of the phase. -/
def xMean (N : ℕ) (φ : ℝ) : ℝ := Real.cos ((N : ℝ) ^ 2 * φ)

/-- Fixed arXiv:1004.3944, Eq. (11), p. 4: `d⟨X⟩/dφ = -N² sin(N²φ)`. -/
theorem hasDerivAt_xMean (N : ℕ) (φ : ℝ) :
    HasDerivAt (xMean N) (-((N : ℝ) ^ 2 * Real.sin ((N : ℝ) ^ 2 * φ))) φ := by
  have hlin : HasDerivAt (fun x : ℝ => (N : ℝ) ^ 2 * x) ((N : ℝ) ^ 2) φ := by
    simpa using (hasDerivAt_id φ).const_mul ((N : ℝ) ^ 2)
  have hcos : HasDerivAt Real.cos (-Real.sin ((N : ℝ) ^ 2 * φ)) ((N : ℝ) ^ 2 * φ) :=
    Real.hasDerivAt_cos _
  have hcomp := hcos.comp φ hlin
  convert hcomp using 1 <;> first | rfl | ring

/-- Fixed arXiv:1004.3944, Eq. (11), p. 4.  With variance `ΔX = |sin(N²φ)|` and
derivative magnitude `|d⟨X⟩/dφ| = N²|sin(N²φ)|`, the propagated mean squared
error is `δφ = 1/N²`. -/
theorem eq11_mean_squared_error
    (N : ℕ) (φ : ℝ) (hN : 0 < N)
    (hsin : Real.sin ((N : ℝ) ^ 2 * φ) ≠ 0) :
    meanSquaredError |Real.sin ((N : ℝ) ^ 2 * φ)|
        (-((N : ℝ) ^ 2 * Real.sin ((N : ℝ) ^ 2 * φ))) = 1 / (N : ℝ) ^ 2 := by
  unfold meanSquaredError
  rw [abs_neg, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)]
  have hsin' : |Real.sin ((N : ℝ) ^ 2 * φ)| ≠ 0 := abs_ne_zero.mpr hsin
  have hN' : (N : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (ne_of_gt hN))
  field_simp

/-- The resource value `|⟨H⟩| = N²/2` converts Eq. (11) into
`δφ · |⟨H⟩| = 1/2`. -/
theorem eq11_resource_product (N : ℕ) (hN : 0 < N) :
    (1 / (N : ℝ) ^ 2) * ((N : ℝ) ^ 2 / 2) = 1 / 2 := by
  have hN' : (N : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (ne_of_gt hN))
  field_simp

/-- Fixed arXiv:1004.3944, Eq. (11), p. 4, collected.  For the single-mode
construction with `N > 0` photons and `sin(N²φ) ≠ 0`:

* `⟨X⟩ = cos(N²φ)`;
* `ΔX² = sin²(N²φ)`;
* the resource count is `|⟨H⟩| = ⟨n̂²⟩ = N²/2`;
* the propagated error is `δφ = 1/N²`;
* hence `δφ · |⟨H⟩| = 1/2`.

This is the formal-attainment statement of the paper (the source's literal
values give the factor `1/2` in the product). -/
theorem single_mode_attains_heisenberg_limit
    (N : ℕ) (φ : ℝ) (hN : 0 < N)
    (hsin : Real.sin ((N : ℝ) ^ 2 * φ) ≠ 0) :
    xExpectation ((N : ℝ) ^ 2 * φ) = (Real.cos ((N : ℝ) ^ 2 * φ) : ℂ) ∧
    xSecondMoment ((N : ℝ) ^ 2 * φ) - (xExpectation ((N : ℝ) ^ 2 * φ)) ^ 2 =
      ((Real.sin ((N : ℝ) ^ 2 * φ)) ^ 2 : ℂ) ∧
    numberSquaredExpectation N ((N : ℝ) ^ 2 * φ) =
      (((N : ℝ) ^ 2 / 2 : ℝ) : ℂ) ∧
    meanSquaredError |Real.sin ((N : ℝ) ^ 2 * φ)|
        (-((N : ℝ) ^ 2 * Real.sin ((N : ℝ) ^ 2 * φ))) = 1 / (N : ℝ) ^ 2 ∧
    (1 / (N : ℝ) ^ 2) * ((N : ℝ) ^ 2 / 2) = 1 / 2 :=
  ⟨xExpectation_eq _, xVariance _, numberSquaredExpectation_eq _ _,
    eq11_mean_squared_error N φ hN hsin, eq11_resource_product N hN⟩

end Qatlib.Papers.HeisenbergLim10.MainResults
