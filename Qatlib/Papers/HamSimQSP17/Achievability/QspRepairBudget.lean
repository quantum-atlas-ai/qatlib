/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 2, Eqs. (9)-(11): the rescaling and rotation repair

Source: G. H. Low and I. L. Chuang, *Optimal Hamiltonian Simulation by Quantum
Signal Processing*, arXiv:1606.02685v2 (2016-12-20), pp. 3-4, Eqs. (9)-(11).

Theorem 2 (p. 3) hands us a real Fourier pair `A(θ) + iC(θ)` in
`(cos kθ, sin kθ)`, `k ≤ N/2`, within `ε` of `e^{ih(θ)}` (Eq. (7)).  Such a
pair need not satisfy the admissibility conditions of Theorem 1: condition (1)
`A² + C² ≤ 1` fails by up to `ε` wherever `|e^{ih}| = 1`, and condition (2)
`A(0) = 1` fails by the phase defect `δ`.  The source repairs the pair before
invoking Theorem 1, in two steps.

* Eq. (9): rescale `A₁ = A/(1+ε)`, `C₁ = C/(1+ε)`.  Since the target has unit
  modulus this restores `A₁² + C₁² ≤ 1` and costs `|A₁ + iC₁ - e^{ih}| ≤ 2ε`.
* Eq. (10): complete the pair to a unitary triple through the sum-of-squares
  component `B` (`B² ≤ 1 - A₁² - C₁²`, `B(0)² = 1 - A₁(0)²`, which the source
  obtains from the polynomial sum-of-squares prescription of [8]) and rotate
  the real part, `A₂ = A₁ cos δ + B sin δ` with `cos δ = A₁(0)`,
  `sin δ = |B(0)|`.  This restores `A₂(0) = 1` and keeps `A₂² + C₁² ≤ 1`,
  at the cost of `|A₂ - A₁| ≤ 6ε`.

Adding the two budgets gives Eq. (11): `|A₂ + iC₁ - e^{ih}| ≤ 8ε`, hence by the
projection of Eq. (6) a success probability `p ≥ (1-8ε)² ≥ 1-16ε`.

This module formalizes exactly that arithmetic, at the source's own function
level `θ ↦ (A(θ), C(θ))`.  The realizable completion (a genuine sum-of-squares
pair with the parity and degree structure of Theorem 1 conditions (3), (4)) is
not rebuilt here: that step is the frozen `lcEndpointNormalize` /
`lcSourceCompilation` construction in the polynomial variable `x = cos(θ/2)`,
and efficient phase synthesis remains open.  What is proved here is the
budget bookkeeping `2ε + 6ε = 8ε` and `(1-8ε)² ≥ 1-16ε`, together with the
admissibility of the repaired pair, which the frozen construction assumes.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HamSimQSP17.Achievability

/-- The real Fourier pair `A(θ) + iC(θ)` of Theorem 2 evaluated at the angle
`θ` (Eq. (1) entry, as used by Eq. (7)). -/
def fourierPair (A C : ℝ → ℝ) (θ : ℝ) : ℂ := (A θ : ℂ) + Complex.I * (C θ : ℂ)

/-- The ideal eigenphase factor `e^{ih(θ)}` of Eq. (2). -/
def phaseTarget (h : ℝ → ℝ) (θ : ℝ) : ℂ := Complex.exp (Complex.I * (h θ : ℂ))

/-- Eq. (9): the rescaled real part `A₁ = A/(1+ε)`. -/
def rescale (ε : ℝ) (A : ℝ → ℝ) : ℝ → ℝ := fun θ => A θ / (1 + ε)

/-- The pointwise sum-of-squares completion `B = √(1 - A₁² - C₁²)` with which the
rotation of Eq. (10) restores the endpoint condition. -/
def completion (ε : ℝ) (A C : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => Real.sqrt (1 - rescale ε A θ ^ 2 - rescale ε C θ ^ 2)

/-- Eq. (10): the axis rotation `A₂ = A₁ cos δ + B sin δ` of the real part. -/
def rotate (A B : ℝ → ℝ) (δ : ℝ) : ℝ → ℝ :=
  fun θ => A θ * Real.cos δ + B θ * Real.sin δ

variable {A C h : ℝ → ℝ} {ε : ℝ}

/-! ## Elementary consequences of Eq. (7) -/

/-- The target phase factor has unit modulus; this is the `1` in every
triangle-inequality budget of Eqs. (9)-(11). -/
theorem norm_phaseTarget (h : ℝ → ℝ) (θ : ℝ) : ‖phaseTarget h θ‖ = 1 := by
  rw [phaseTarget, Complex.norm_exp]
  simp

/-- The squared modulus of the pair is the sum of the squares of its two real
Fourier components (the quantity measured by the success probability of
Eq. (6)). -/
theorem norm_pair_sq (A C : ℝ → ℝ) (θ : ℝ) :
    ‖fourierPair A C θ‖ ^ 2 = A θ ^ 2 + C θ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [fourierPair, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Eq. (9) as a single complex division: the rescaled pair is the original
pair divided by `1 + ε`. -/
theorem fourierPair_rescale (ε : ℝ) (A C : ℝ → ℝ) (θ : ℝ) :
    fourierPair (rescale ε A) (rescale ε C) θ
      = fourierPair A C θ / ((1 + ε : ℝ) : ℂ) := by
  simp only [fourierPair, rescale, Complex.ofReal_div]
  rw [← mul_div_assoc, ← add_div]

/-- `|A + iC| ≤ 1 + ε` under the approximation hypothesis of Eq. (7). -/
theorem norm_pair_le (_hε : 0 < ε)
    (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε) (θ : ℝ) :
    ‖fourierPair A C θ‖ ≤ 1 + ε := by
  have h := norm_add_le (phaseTarget h θ) (fourierPair A C θ - phaseTarget h θ)
  rw [add_sub_cancel, norm_phaseTarget] at h
  linarith [happrox θ]

/-- `1 - ε ≤ |A + iC|` under the approximation hypothesis of Eq. (7). -/
theorem norm_pair_ge (_hε : 0 < ε)
    (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε) (θ : ℝ) :
    1 - ε ≤ ‖fourierPair A C θ‖ := by
  have h := abs_norm_sub_norm_le (fourierPair A C θ) (phaseTarget h θ)
  rw [norm_phaseTarget, abs_le] at h
  linarith [h.1, happrox θ]

/-! ## Eq. (9): the rescaling step -/

/-- **Eq. (9), first assertion: `A₁² + C₁² ≤ 1`.**  The rescaled pair is inside
the unit disc, so the amplitude condition (1) of Theorem 1 holds. -/
theorem rescale_norm_le (hε : 0 < ε)
    (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε) (θ : ℝ) :
    ‖fourierPair (rescale ε A) (rescale ε C) θ‖ ≤ 1 := by
  have hd : (0 : ℝ) < 1 + ε := by linarith
  rw [fourierPair_rescale, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd,
    div_le_one hd]
  exact norm_pair_le hε happrox θ

/-- **Eq. (9): the rescaling costs at most `2ε`.**  The source reports
`|A₁ + iC₁ - e^{ih}| ≤ ε/(1+ε) + ε ≤ 2ε`; the same bound holds verbatim. -/
theorem rescale_error (hε : 0 < ε)
    (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε) (θ : ℝ) :
    ‖fourierPair (rescale ε A) (rescale ε C) θ - phaseTarget h θ‖ ≤ 2 * ε := by
  have hd : (0 : ℝ) < 1 + ε := by linarith
  have hdnorm : ‖((1 + ε : ℝ) : ℂ)‖ = 1 + ε := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  have hsplit : fourierPair (rescale ε A) (rescale ε C) θ - phaseTarget h θ
      = (fourierPair A C θ - phaseTarget h θ - phaseTarget h θ * (ε : ℂ))
          / ((1 + ε : ℝ) : ℂ) := by
    have hpos : (1 + ε : ℝ) ≠ 0 := by positivity
    have hdc : ((1 + ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos
    rw [fourierPair_rescale, eq_div_iff hdc, sub_mul, div_mul_cancel₀ _ hdc]
    have hd1 : phaseTarget h θ * ((1 + ε : ℝ) : ℂ) = phaseTarget h θ + phaseTarget h θ * (ε : ℂ) := by
      push_cast
      ring
    rw [hd1]
    ring
  have hnum : ‖fourierPair A C θ - phaseTarget h θ - phaseTarget h θ * (ε : ℂ)‖ ≤ 2 * ε := by
    have hphase : ‖phaseTarget h θ * (ε : ℂ)‖ = ε := by
      rw [norm_mul, norm_phaseTarget, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      ring
    have h := norm_sub_le (fourierPair A C θ - phaseTarget h θ) (phaseTarget h θ * (ε : ℂ))
    rw [hphase] at h
    linarith [happrox θ]
  rw [hsplit, norm_div, hdnorm]
  refine le_trans (div_le_div_of_nonneg_right hnum (le_of_lt hd)) ?_
  rw [div_le_iff₀ hd]
  nlinarith [hε.le, mul_nonneg hε.le hε.le]

/-- **The rescaled pair still clears the lower amplitude bound.**  From
`|A + iC| ≥ 1 - ε` and the rescaling we get `|A₁ + iC₁| ≥ (1-ε)/(1+ε)`; this
is the constant that bounds the completion `B` in Eq. (10). -/
theorem rescale_norm_ge (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε) (θ : ℝ) :
    (1 - ε) / (1 + ε) ≤ ‖fourierPair (rescale ε A) (rescale ε C) θ‖ := by
  have hd : (0 : ℝ) < 1 + ε := by linarith
  rw [fourierPair_rescale, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd,
    le_div_iff₀ hd]
  have h1 : (1 - ε) / (1 + ε) * (1 + ε) = 1 - ε := by field_simp
  rw [h1]
  exact norm_pair_ge hε happrox θ

/-- The lower amplitude bound of `rescale_norm_ge`, squared. -/
theorem rescale_normSq_ge (hε : 0 < ε) (hε1 : ε ≤ 1)
    (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε) (θ : ℝ) :
    ((1 - ε) / (1 + ε)) ^ 2
      ≤ rescale ε A θ ^ 2 + rescale ε C θ ^ 2 := by
  have hd : (0 : ℝ) < 1 + ε := by linarith
  have hnn : (0 : ℝ) ≤ (1 - ε) / (1 + ε) := div_nonneg (by linarith) (le_of_lt hd)
  have h := rescale_norm_ge hε hε1 happrox θ
  have hsq := pow_le_pow_left₀ hnn h 2
  rwa [norm_pair_sq] at hsq

/-! ## Eq. (10): the endpoint repair -/

/-- **The endpoint defect of Eq. (9).**  Because `C` is a sine series
(condition (4) of Theorem 1) it vanishes at `θ = 0`, so Eq. (7) at `θ = 0`
reads `|A(0) - 1| ≤ ε`; after rescaling `(1-ε)/(1+ε) ≤ A₁(0) ≤ 1`. -/
theorem rescale_zero_bounds (hε : 0 < ε) (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε)
    (hC0 : C 0 = 0) (h0 : h 0 = 0) :
    (1 - ε) / (1 + ε) ≤ rescale ε A 0 ∧ rescale ε A 0 ≤ 1 := by
  have hd : (0 : ℝ) < 1 + ε := by linarith
  have hphase : phaseTarget h 0 = 1 := by
    rw [phaseTarget, h0]
    simp
  have hpair : fourierPair A C 0 = ((A 0 : ℝ) : ℂ) := by
    simp [fourierPair, hC0]
  have hA : |A 0 - 1| ≤ ε := by
    have h := happrox 0
    rw [hpair, hphase, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at h
    exact h
  rw [abs_le] at hA
  constructor
  · simp only [rescale]
    rw [div_le_iff₀ hd]
    have h2 : A 0 / (1 + ε) * (1 + ε) = A 0 := by field_simp
    rw [h2]
    linarith [hA.1]
  · simp only [rescale]
    rw [div_le_one hd]
    linarith [hA.2]

/-- **`B(0) = √(1 - A₁(0)²)`.**  At `θ = 0` the completion reduces to the
complement of the real part because `C₁(0) = 0`. -/
theorem completion_zero_sq (hε : 0 < ε) (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε)
    (hC0 : C 0 = 0) :
    completion ε A C 0 ^ 2 = 1 - rescale ε A 0 ^ 2 := by
  have hx : 0 ≤ 1 - rescale ε A 0 ^ 2 - rescale ε C 0 ^ 2 := by
    have h := rescale_norm_le hε happrox 0
    have hsq : rescale ε A 0 ^ 2 + rescale ε C 0 ^ 2 ≤ 1 := by
      rw [← norm_pair_sq]
      nlinarith [h, norm_nonneg (fourierPair (rescale ε A) (rescale ε C) 0)]
    linarith
  simp only [completion]
  rw [Real.sq_sqrt hx]
  simp [rescale, hC0]

/-- **The completion is bounded by the discarded amplitude.**  Pointwise
`B² ≤ 1 - A₁² - C₁²`; the sum-of-squares prescription of [8] produces a
realizable `B` with exactly this bound. -/
theorem completion_sq_le (hε : 0 < ε)
    (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε) (θ : ℝ) :
    completion ε A C θ ^ 2 ≤ 1 - rescale ε A θ ^ 2 - rescale ε C θ ^ 2 := by
  have hx : 0 ≤ 1 - rescale ε A θ ^ 2 - rescale ε C θ ^ 2 := by
    have h := rescale_norm_le hε happrox θ
    have hsq : rescale ε A θ ^ 2 + rescale ε C θ ^ 2 ≤ 1 := by
      rw [← norm_pair_sq]
      nlinarith [h, norm_nonneg (fourierPair (rescale ε A) (rescale ε C) θ)]
    linarith
  simp only [completion]
  rw [Real.sq_sqrt hx]

/-- **The amplitude gap is `4ε/(1+ε)²`.**  Subtracting the squared lower
bound of `rescale_normSq_ge` from `1` gives exactly the constant whose square
root the source writes as `√(2ε)/(1+ε)` in Eq. (10). -/
theorem gap_le (hε : 0 < ε) (hε1 : ε ≤ 1)
    (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε) (θ : ℝ) :
    1 - rescale ε A θ ^ 2 - rescale ε C θ ^ 2 ≤ 4 * ε / (1 + ε) ^ 2 := by
  have hd : (0 : ℝ) < 1 + ε := by linarith
  have hlow := rescale_normSq_ge hε hε1 happrox θ
  have hkey : 1 - ((1 - ε) / (1 + ε)) ^ 2 = 4 * ε / (1 + ε) ^ 2 := by
    field_simp
    ring
  linarith [hlow, hkey]

/-- A square root below the `√(2ε)/(1+ε)`-scale constant. -/
theorem sqrt_gap_le (hε : 0 < ε) (x : ℝ) (_hx0 : 0 ≤ x) (hx : x ≤ 4 * ε / (1 + ε) ^ 2) :
    Real.sqrt x ≤ 2 * Real.sqrt ε / (1 + ε) := by
  have hd : (0 : ℝ) < 1 + ε := by linarith
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc x ≤ 4 * ε / (1 + ε) ^ 2 := hx
    _ = (2 * Real.sqrt ε / (1 + ε)) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hε.le]
        norm_num

/-- **`B(0) ≤ 2√ε/(1+ε)`.**  Inserting the lower amplitude bound of
`rescale_normSq_ge` into `B(0)² = 1 - A₁(0)²` leaves the source's constant
`4ε/(1+ε)²`. -/
theorem completion_zero_le (hε : 0 < ε) (hε1 : ε ≤ 1)
    (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε) (hC0 : C 0 = 0)
    (_h0 : h 0 = 0) :
    completion ε A C 0 ≤ 2 * Real.sqrt ε / (1 + ε) := by
  have hC10 : rescale ε C 0 = 0 := by simp [rescale, hC0]
  have hx0 : 0 ≤ 1 - rescale ε A 0 ^ 2 - rescale ε C 0 ^ 2 := by
    have h := rescale_norm_le hε happrox 0
    have hsq : rescale ε A 0 ^ 2 + rescale ε C 0 ^ 2 ≤ 1 := by
      rw [← norm_pair_sq]
      nlinarith [h, norm_nonneg (fourierPair (rescale ε A) (rescale ε C) 0)]
    linarith
  have hx : 1 - rescale ε A 0 ^ 2 - rescale ε C 0 ^ 2 ≤ 4 * ε / (1 + ε) ^ 2 := by
    have hgap := gap_le hε hε1 happrox 0
    rw [hC10] at hgap ⊢
    linarith [hgap]
  simpa only [completion] using
    sqrt_gap_le hε (1 - rescale ε A 0 ^ 2 - rescale ε C 0 ^ 2) hx0 hx

/-- **The rotation angle.**  With `δ = arcsin B(0)` we have `sin δ = B(0)` and
`cos δ = A₁(0)`, the two facts used to evaluate `A₂(0)` and to bound
`|A₂ - A₁|`. -/
theorem cos_sin_rotationAngle (hε : 0 < ε) (hε1 : ε ≤ 1)
    (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε) (hC0 : C 0 = 0)
    (h0 : h 0 = 0) :
    Real.sin (Real.arcsin (completion ε A C 0)) = completion ε A C 0 ∧
      Real.cos (Real.arcsin (completion ε A C 0)) = rescale ε A 0 := by
  have hB1 : completion ε A C 0 ≤ 1 := by
    refine le_trans (completion_zero_le hε hε1 happrox hC0 h0) ?_
    rw [div_le_one (by linarith : (0 : ℝ) < 1 + ε)]
    nlinarith [Real.sq_sqrt hε.le, hε1, Real.sqrt_nonneg ε]
  have hB0 : 0 ≤ completion ε A C 0 := Real.sqrt_nonneg _
  constructor
  · exact Real.sin_arcsin (by linarith) hB1
  · rw [Real.cos_arcsin]
    have hsq := completion_zero_sq hε happrox hC0
    have hA0 := (rescale_zero_bounds hε happrox hC0 h0).1
    have hA1 : rescale ε A 0 ≤ 1 := (rescale_zero_bounds hε happrox hC0 h0).2
    have hnn : 0 ≤ rescale ε A 0 := by
      have hd : (0 : ℝ) < 1 + ε := by linarith
      have := div_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε) (le_of_lt hd)
      linarith
    rw [show 1 - completion ε A C 0 ^ 2 = rescale ε A 0 ^ 2 by linarith]
    exact Real.sqrt_sq hnn

/-- **Eq. (10): the repaired real part hits the endpoint `A₂(0) = 1`.**
`A₁(0)² + B(0)² = 1` and the rotation sends `(A₁(0), B(0))` to `(1, 0)` at
`θ = 0`, which is condition (2) of Theorem 1. -/
theorem rotate_zero (hε : 0 < ε) (hε1 : ε ≤ 1)
    (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε) (hC0 : C 0 = 0)
    (h0 : h 0 = 0) :
    rotate (rescale ε A) (completion ε A C) (Real.arcsin (completion ε A C 0)) 0 = 1 := by
  obtain ⟨hsin, hcos⟩ := cos_sin_rotationAngle hε hε1 happrox hC0 h0
  have hsq := completion_zero_sq hε happrox hC0
  simp only [rotate, hsin, hcos]
  nlinarith [hsq]

/-- **Eq. (10): the rotation keeps the amplitude bound `A₂² + C₁² ≤ 1`.**
This is Cauchy-Schwarz on `(A₁, B)·(cos δ, sin δ)` together with
`A₁² + B² ≤ 1 - C₁²`. -/
theorem rotate_admissible (hε : 0 < ε)
    (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε) (θ : ℝ) :
    rotate (rescale ε A) (completion ε A C) (Real.arcsin (completion ε A C 0)) θ ^ 2
        + rescale ε C θ ^ 2 ≤ 1 := by
  have hB := completion_sq_le hε happrox θ
  have htrig : Real.cos (Real.arcsin (completion ε A C 0)) ^ 2
      + Real.sin (Real.arcsin (completion ε A C 0)) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have hcs : (rescale ε A θ * Real.cos (Real.arcsin (completion ε A C 0))
        + completion ε A C θ * Real.sin (Real.arcsin (completion ε A C 0))) ^ 2
      ≤ (rescale ε A θ ^ 2 + completion ε A C θ ^ 2) * (Real.cos (Real.arcsin (completion ε A C 0)) ^ 2
        + Real.sin (Real.arcsin (completion ε A C 0)) ^ 2) := by
    nlinarith [sq_nonneg (rescale ε A θ * Real.sin (Real.arcsin (completion ε A C 0))
        - completion ε A C θ * Real.cos (Real.arcsin (completion ε A C 0)))]
  rw [htrig, mul_one] at hcs
  simp only [rotate]
  nlinarith [hcs, hB]

/-- **Eq. (10): the rotation costs at most `6ε`.**  Splitting
`A₂ - A₁ = A₁(cos δ - 1) + B sin δ` gives `|cos δ - 1| = 1 - A₁(0) ≤ 2ε` and
`|B| sin δ ≤ (2√ε/(1+ε))² = 4ε/(1+ε)² ≤ 4ε`, matching the source's
`|A₂ - A₁| ≤ 6ε`. -/
theorem rotate_error (hε : 0 < ε) (hε1 : ε ≤ 1)
    (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε) (hC0 : C 0 = 0)
    (h0 : h 0 = 0) (θ : ℝ) :
    |rotate (rescale ε A) (completion ε A C) (Real.arcsin (completion ε A C 0)) θ
        - rescale ε A θ| ≤ 6 * ε := by
  obtain ⟨hsin, hcos⟩ := cos_sin_rotationAngle hε hε1 happrox hC0 h0
  have hd : (0 : ℝ) < 1 + ε := by linarith
  have hA0 := (rescale_zero_bounds hε happrox hC0 h0).1
  have hA1 : rescale ε A θ ^ 2 + rescale ε C θ ^ 2 ≤ 1 := by
    rw [← norm_pair_sq]
    nlinarith [rescale_norm_le hε happrox θ,
      norm_nonneg (fourierPair (rescale ε A) (rescale ε C) θ)]
  have hB := completion_sq_le hε happrox θ
  have hB0 := completion_zero_le hε hε1 happrox hC0 h0
  have hcos1 : 1 - Real.cos (Real.arcsin (completion ε A C 0)) ≤ 2 * ε := by
    rw [hcos]
    have hde : 1 - rescale ε A 0 = (1 - ε) / (1 + ε) - rescale ε A 0
        + (1 - (1 - ε) / (1 + ε)) := by ring
    have htail : 1 - (1 - ε) / (1 + ε) = 2 * ε / (1 + ε) := by
      field_simp
      ring
    have hfrac : 2 * ε / (1 + ε) ≤ 2 * ε := by
      rw [div_le_iff₀ hd]
      nlinarith [hε.le, mul_nonneg hε.le hε.le]
    rw [hde, htail]
    nlinarith [hA0, hfrac]
  have hAabs : |rescale ε A θ| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [hA1, sq_nonneg (rescale ε C θ)]
  have hBnn : (0 : ℝ) ≤ completion ε A C θ := by
    simp only [completion]
    exact Real.sqrt_nonneg _
  have hBabs : |completion ε A C θ| ≤ 2 * Real.sqrt ε / (1 + ε) := by
    rw [abs_of_nonneg hBnn]
    have hx0 : 0 ≤ 1 - rescale ε A θ ^ 2 - rescale ε C θ ^ 2 := by
      have h := rescale_norm_le hε happrox θ
      have hsq : rescale ε A θ ^ 2 + rescale ε C θ ^ 2 ≤ 1 := by
        rw [← norm_pair_sq]
        nlinarith [h, norm_nonneg (fourierPair (rescale ε A) (rescale ε C) θ)]
      linarith
    simpa only [completion] using
      sqrt_gap_le hε (1 - rescale ε A θ ^ 2 - rescale ε C θ ^ 2) hx0
        (gap_le hε hε1 happrox θ)
  have hBs : Real.sin (Real.arcsin (completion ε A C 0)) = completion ε A C 0 := hsin
  simp only [rotate]
  rw [hcos]
  have hsplit : rescale ε A θ * rescale ε A 0
        + completion ε A C θ * Real.sin (Real.arcsin (completion ε A C 0)) - rescale ε A θ
      = rescale ε A θ * (rescale ε A 0 - 1)
        + completion ε A C θ * Real.sin (Real.arcsin (completion ε A C 0)) := by ring
  rw [hsplit]
  have h1 : |rescale ε A θ * (rescale ε A 0 - 1)| ≤ 2 * ε := by
    rw [abs_mul]
    have hA1' : rescale ε A 0 ≤ 1 := (rescale_zero_bounds hε happrox hC0 h0).2
    have hfrac : (1 - ε) / (1 + ε) - 1 = -(2 * ε / (1 + ε)) := by
      field_simp
      ring
    have hfrac' : 2 * ε / (1 + ε) ≤ 2 * ε := by
      rw [div_le_iff₀ hd]
      nlinarith [hε.le, mul_nonneg hε.le hε.le]
    have : |rescale ε A 0 - 1| ≤ 2 * ε := by
      rw [abs_le]
      constructor
      · nlinarith [hA0, hfrac, hfrac']
      · linarith [hA1']
    nlinarith [hAabs, this, hε.le, abs_nonneg (rescale ε A θ), abs_nonneg (rescale ε A 0 - 1)]
  have h2 : |completion ε A C θ * Real.sin (Real.arcsin (completion ε A C 0))| ≤ 4 * ε := by
    rw [abs_mul, hBs]
    have hB0abs : |completion ε A C 0| ≤ 2 * Real.sqrt ε / (1 + ε) := by
      rw [abs_of_nonneg (by simp only [completion]; exact Real.sqrt_nonneg _)]
      exact hB0
    calc |completion ε A C θ| * |completion ε A C 0|
        ≤ (2 * Real.sqrt ε / (1 + ε)) * (2 * Real.sqrt ε / (1 + ε)) :=
          mul_le_mul hBabs hB0abs (abs_nonneg (completion ε A C 0)) (by positivity)
      _ = (2 * Real.sqrt ε / (1 + ε)) ^ 2 := (sq _).symm
      _ ≤ 4 * ε := by
          rw [div_pow, mul_pow, Real.sq_sqrt hε.le]
          have h1e : (0 : ℝ) < 1 + ε := by linarith
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + ε) ^ 2)]
          nlinarith [hε.le, mul_nonneg hε.le hε.le]
  calc |rescale ε A θ * (rescale ε A 0 - 1)
        + completion ε A C θ * Real.sin (Real.arcsin (completion ε A C 0))|
      ≤ |rescale ε A θ * (rescale ε A 0 - 1)|
        + |completion ε A C θ * Real.sin (Real.arcsin (completion ε A C 0))| := abs_add_le _ _
    _ ≤ 6 * ε := by linarith

/-! ## Eq. (11): the repaired pair satisfies Theorem 1 and approximates the target -/

/-- **Eq. (11): `|A₂ + iC₁ - e^{ih}| ≤ 8ε`.**  The `6ε` of Eq. (10) and the
`2ε` of Eq. (9) add up to the source's `8ε` trace-distance constant. -/
theorem repair_error (hε : 0 < ε) (hε1 : ε ≤ 1)
    (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε) (hC0 : C 0 = 0)
    (h0 : h 0 = 0) (θ : ℝ) :
    ‖fourierPair (rotate (rescale ε A) (completion ε A C) (Real.arcsin (completion ε A C 0)))
        (rescale ε C) θ - phaseTarget h θ‖ ≤ 8 * ε := by
  have hrot := rotate_error hε hε1 happrox hC0 h0 θ
  have hres := rescale_error hε happrox θ
  have hdiff : fourierPair (rotate (rescale ε A) (completion ε A C)
        (Real.arcsin (completion ε A C 0))) (rescale ε C) θ
      - fourierPair (rescale ε A) (rescale ε C) θ
      = ((rotate (rescale ε A) (completion ε A C) (Real.arcsin (completion ε A C 0)) θ
          - rescale ε A θ : ℝ) : ℂ) := by
    simp only [fourierPair, Complex.ofReal_sub]
    ring
  have hnorm : ‖fourierPair (rotate (rescale ε A) (completion ε A C)
        (Real.arcsin (completion ε A C 0))) (rescale ε C) θ
      - fourierPair (rescale ε A) (rescale ε C) θ‖ ≤ 6 * ε := by
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs]
    exact hrot
  have htri := norm_sub_le (fourierPair (rotate (rescale ε A) (completion ε A C)
      (Real.arcsin (completion ε A C 0))) (rescale ε C) θ)
    (fourierPair (rescale ε A) (rescale ε C) θ)
  have hsub : fourierPair (rotate (rescale ε A) (completion ε A C)
        (Real.arcsin (completion ε A C 0))) (rescale ε C) θ - phaseTarget h θ
      = (fourierPair (rotate (rescale ε A) (completion ε A C) (Real.arcsin (completion ε A C 0)))
          (rescale ε C) θ - fourierPair (rescale ε A) (rescale ε C) θ)
        + (fourierPair (rescale ε A) (rescale ε C) θ - phaseTarget h θ) := by ring
  rw [hsub]
  have := norm_add_le (fourierPair (rotate (rescale ε A) (completion ε A C)
      (Real.arcsin (completion ε A C 0))) (rescale ε C) θ
      - fourierPair (rescale ε A) (rescale ε C) θ)
    (fourierPair (rescale ε A) (rescale ε C) θ - phaseTarget h θ)
  linarith

/-- **Eq. (11): the success probability is `p ≥ (1-8ε)²`.**  The projection of
Eq. (6) succeeds with the squared modulus of the repaired amplitude; the
`8ε` of `repair_error` is subtracted from the unit target modulus. -/
theorem repair_success (hε : 0 < ε) (hε1 : ε ≤ 1/16)
    (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε) (hC0 : C 0 = 0)
    (h0 : h 0 = 0) (θ : ℝ) :
    (1 - 8 * ε) ^ 2
      ≤ ‖fourierPair (rotate (rescale ε A) (completion ε A C) (Real.arcsin (completion ε A C 0)))
          (rescale ε C) θ‖ ^ 2 := by
  have h8 : 8 * ε ≤ 1 := by nlinarith
  have herr := repair_error hε (by nlinarith) happrox hC0 h0 θ
  have hge : 1 - 8 * ε ≤ ‖fourierPair (rotate (rescale ε A) (completion ε A C)
      (Real.arcsin (completion ε A C 0))) (rescale ε C) θ‖ := by
    have h := abs_norm_sub_norm_le (fourierPair (rotate (rescale ε A) (completion ε A C)
        (Real.arcsin (completion ε A C 0))) (rescale ε C) θ) (phaseTarget h θ)
    rw [norm_phaseTarget, abs_le] at h
    linarith [h.1, herr]
  exact pow_le_pow_left₀ (by linarith) hge 2

/-- **Eq. (11): `p ≥ 1 - 16ε`.**  The elementary `(1-8ε)² ≥ 1-16ε` closes the
source's success-probability bookkeeping. -/
theorem repair_success_linear (hε : 0 < ε) (hε1 : ε ≤ 1/16)
    (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε) (hC0 : C 0 = 0)
    (h0 : h 0 = 0) (θ : ℝ) :
    1 - 16 * ε
      ≤ ‖fourierPair (rotate (rescale ε A) (completion ε A C) (Real.arcsin (completion ε A C 0)))
          (rescale ε C) θ‖ ^ 2 := by
  refine le_trans ?_ (repair_success hε hε1 happrox hC0 h0 θ)
  nlinarith [sq_nonneg ε]

/-- **Theorem 2, Eqs. (9)-(11), as one statement.**  A real pair `(A, C)` with
`C(0) = 0` that approximates the odd phase function `h` to `ε` (Eq. (7)) can be
repaired into a pair `(A₂, C₁)` that satisfies the amplitude and endpoint
conditions (1), (2) of Theorem 1, is within `8ε` of `e^{ih}`, and succeeds with
probability at least `(1-8ε)² ≥ 1-16ε`.  The remaining Theorem 1 conditions
(3), (4) -- the parity and degree structure -- are the job of the sum-of-squares
completion and are not claimed here. -/
theorem theorem2_repair (hε : 0 < ε) (hε1 : ε ≤ 1/16)
    (happrox : ∀ θ, ‖fourierPair A C θ - phaseTarget h θ‖ ≤ ε) (hC0 : C 0 = 0)
    (h0 : h 0 = 0) :
    rotate (rescale ε A) (completion ε A C) (Real.arcsin (completion ε A C 0)) 0 = 1 ∧
      (∀ θ, rotate (rescale ε A) (completion ε A C)
          (Real.arcsin (completion ε A C 0)) θ ^ 2 + rescale ε C θ ^ 2 ≤ 1) ∧
      (∀ θ, ‖fourierPair (rotate (rescale ε A) (completion ε A C)
          (Real.arcsin (completion ε A C 0))) (rescale ε C) θ - phaseTarget h θ‖ ≤ 8 * ε) ∧
      (∀ θ, (1 - 8 * ε) ^ 2
        ≤ ‖fourierPair (rotate (rescale ε A) (completion ε A C)
            (Real.arcsin (completion ε A C 0))) (rescale ε C) θ‖ ^ 2) ∧
      (∀ θ, 1 - 16 * ε
        ≤ ‖fourierPair (rotate (rescale ε A) (completion ε A C)
            (Real.arcsin (completion ε A C 0))) (rescale ε C) θ‖ ^ 2) :=
  ⟨rotate_zero hε (by nlinarith) happrox hC0 h0,
   fun θ => rotate_admissible hε happrox θ,
   fun θ => repair_error hε (by nlinarith) happrox hC0 h0 θ,
   fun θ => repair_success hε hε1 happrox hC0 h0 θ,
   fun θ => repair_success_linear hε hε1 happrox hC0 h0 θ⟩

end Qatlib.Papers.HamSimQSP17.Achievability
