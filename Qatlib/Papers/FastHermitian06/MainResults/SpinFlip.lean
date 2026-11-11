/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FastHermitian06.MainResults.Defs
import Qatlib.Papers.ThermalDrift26.ThermalSampling.Intake.ThermalSourceExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Two-level spin-flip evolution

`sigmaN` normalizes the centered Hamiltonian `H2`, allowing the matrix exponential `evolution`
to be evaluated on `ket0`. The resulting state formula gives an explicit spin-flip time and
parameter choices with fixed positive gap and arbitrarily small positive time expression. See
[BenderEtAl2007].

## Main statements

* `evolution13`: gives the angle-parameter state formula.
* `spin_flip_time`: evaluates the state at the specified flip time.
* `optimal_time_arbitrarily_small`: constructs arbitrarily small positive time expressions at
  fixed gap.

## References

* [Bender et al., 2007][BenderEtAl2007]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix ComplexOrder

open Qatlib.Papers.FastHermitian06.MainResults.Defs

namespace Qatlib.Papers.FastHermitian06.MainResults.SpinFlip

/-- The normalized traceless two-level matrix with diagonal entries `±I * 2 * r * sin θ / omega`
and off-diagonal entries `2 * s / omega`. -/
def sigmaN (r s θ : ℝ) : Mat2 :=
  !![ Complex.I * (((2 * r * Real.sin θ) / omega r s θ : ℝ) : ℂ),
      (((2 * s) / omega r s θ : ℝ) : ℂ);
      (((2 * s) / omega r s θ : ℝ) : ℂ),
      -(Complex.I * (((2 * r * Real.sin θ) / omega r s θ : ℝ) : ℂ)) ]

/-- The matrix exponential of `(-I * t / ħ)` times `H2 r s θ`. -/
def evolution (r s θ ħ t : ℝ) : Mat2 :=
  NormedSpace.exp ((-(Complex.I * ((t / ħ : ℝ) : ℂ))) • H2 r s θ)

/-- The scalar exponent `-I * t * r * cos θ / ħ`. -/
def phase (r _s θ ħ t : ℝ) : ℂ :=
  (-(Complex.I * ((t / ħ : ℝ) : ℂ))) * (((r * Real.cos θ : ℝ)) : ℂ)

/-- The half-gap exponent `-I * t * omega r s θ / (2 * ħ)`. -/
def halfPhase (r s θ ħ t : ℝ) : ℂ :=
  (-(Complex.I * ((t / ħ : ℝ) : ℂ))) * (((omega r s θ / 2 : ℝ)) : ℂ)

/-- Multiplication by `-I` cancels a preceding factor of `I`. -/
theorem neg_I_mul_I_mul (z : ℂ) : (-Complex.I) * (Complex.I * z) = z := by
  rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

/-- The square of `I * a` is `-a^2`. -/
theorem I_mul_sq (a : ℂ) : (Complex.I * a) * (Complex.I * a) = -a ^ 2 := by
  rw [show (Complex.I * a) * (Complex.I * a) = (Complex.I * Complex.I) * (a * a) by ring,
    Complex.I_mul_I]
  ring

/-- The square of `-(I * a)` is `-a^2`. -/
theorem neg_I_mul_sq (a : ℂ) : (-(Complex.I * a)) * (-(Complex.I * a)) = -a ^ 2 := by
  rw [neg_mul_neg]
  exact I_mul_sq a

/-- In the unbroken region, `sigmaN` squares to the identity. -/
theorem sigmaN_sq (r s θ : ℝ) (hunb : unbrokenPT r s θ) :
    sigmaN r s θ * sigmaN r s θ = (1 : Mat2) := by
  have hω : omega r s θ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hunb)
  have hsq : omega r s θ ^ 2 = omegaSq r s θ := omega_sq r s θ hunb
  have hq : (2 * s) ^ 2 - (2 * r * Real.sin θ) ^ 2 = omegaSq r s θ := by
    unfold omegaSq; ring
  have hqp : ((2 * s) / omega r s θ) ^ 2 - ((2 * r * Real.sin θ) / omega r s θ) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← sub_div, hq, hsq]
    exact div_self (ne_of_gt hunb)
  have hqpC : (2 * (s : ℂ) / (omega r s θ : ℂ)) ^ 2
      - (2 * (r : ℂ) * (Real.sin θ : ℂ) / (omega r s θ : ℂ)) ^ 2 = 1 := by
    have hp := congrArg ((↑) : ℝ → ℂ) hqp
    push_cast at hp ⊢
    exact hp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaN, Matrix.mul_apply, Fin.sum_univ_two]
  · ring_nf
    rw [show Complex.I ^ 2 = (-1 : ℂ) from Defs.I_sq, ← Complex.ofReal_sin]
    linear_combination hqpC
  · ring
  · ring
  · ring_nf
    rw [show Complex.I ^ 2 = (-1 : ℂ) from Defs.I_sq, ← Complex.ofReal_sin]
    linear_combination hqpC

/-- In the unbroken region, decomposes `H2` into its scalar part and half the gap times
`sigmaN`. -/
theorem H2_decomp (r s θ : ℝ) (hunb : unbrokenPT r s θ) :
    H2 r s θ = (((r * Real.cos θ : ℝ) : ℂ)) • (1 : Mat2)
      + (((omega r s θ / 2 : ℝ) : ℂ)) • sigmaN r s θ := by
  have hω : omega r s θ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hunb)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H2, sigmaN, cis_eq, Matrix.smul_apply]
  all_goals field_simp [hω]

/-- The matrix exponential of a scalar multiple of the identity is the scalar exponential times
the identity. -/
theorem exp_smul_one (c : ℂ) :
    NormedSpace.exp (c • (1 : Mat2)) = Complex.exp c • (1 : Mat2) := by
  have h : c • (1 : Mat2) = Matrix.diagonal (fun _ : Fin 2 => c) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.diagonal, Matrix.smul_apply, hij]
  rw [h, Matrix.exp_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal, Matrix.smul_apply, ← Complex.exp_eq_exp_ℂ]
  · simp [Matrix.diagonal, Matrix.smul_apply, hij]

/-- In the unbroken region, separates the evolution into a scalar phase and a hyperbolic
combination of the identity and `sigmaN`. -/
theorem evolution_decomp (r s θ ħ t : ℝ) (hunb : unbrokenPT r s θ) :
    evolution r s θ ħ t
      = Complex.exp (phase r s θ ħ t) •
          (Complex.cosh (halfPhase r s θ ħ t) • (1 : Mat2)
            + Complex.sinh (halfPhase r s θ ħ t) • sigmaN r s θ) := by
  have hsplit : (-(Complex.I * ((t / ħ : ℝ) : ℂ))) • H2 r s θ
      = phase r s θ ħ t • (1 : Mat2) + halfPhase r s θ ħ t • sigmaN r s θ := by
    rw [H2_decomp r s θ hunb, smul_add, smul_smul, smul_smul]
    rfl
  have hcomm : Commute (phase r s θ ħ t • (1 : Mat2))
      (halfPhase r s θ ħ t • sigmaN r s θ) :=
    Commute.smul_left (Commute.one_left (halfPhase r s θ ħ t • sigmaN r s θ)) _
  rw [evolution, hsplit, Matrix.exp_add_of_commute _ _ hcomm, exp_smul_one,
    Qatlib.Papers.ThermalDrift26.ThermalSampling.reflection_exp
      (sigmaN r s θ) (sigmaN_sq r s θ hunb) (halfPhase r s θ ħ t)]
  rw [Matrix.smul_mul, Matrix.one_mul]

/-- Evaluates `sigmaN` on `ket0` as its explicit first column. -/
theorem sigmaN_mulVec_ket0 (r s θ : ℝ) :
    sigmaN r s θ *ᵥ ket0
      = ![ Complex.I * (((2 * r * Real.sin θ) / omega r s θ : ℝ) : ℂ),
          (((2 * s) / omega r s θ : ℝ) : ℂ) ] := by
  ext i
  fin_cases i <;>
    simp [sigmaN, ket0, Matrix.mulVec]

/-- The hyperbolic cosine of `halfPhase` equals the cosine of the real half-gap time. -/
theorem cosh_halfPhase (r s θ ħ t : ℝ) :
    Complex.cosh (halfPhase r s θ ħ t)
      = ((Real.cos (omega r s θ * t / (2 * ħ)) : ℝ) : ℂ) := by
  have hz : halfPhase r s θ ħ t
      = -(((((omega r s θ * t / (2 * ħ)) : ℝ)) : ℂ) * Complex.I) := by
    unfold halfPhase
    push_cast
    ring
  rw [hz, Complex.cosh_neg, Complex.cosh_mul_I, ← Complex.ofReal_cos]

/-- The hyperbolic sine of `halfPhase` equals `-I` times the sine of the real half-gap time. -/
theorem sinh_halfPhase (r s θ ħ t : ℝ) :
    Complex.sinh (halfPhase r s θ ħ t)
      = (-Complex.I) * ((Real.sin (omega r s θ * t / (2 * ħ)) : ℝ) : ℂ) := by
  have hz : halfPhase r s θ ħ t
      = -(((((omega r s θ * t / (2 * ħ)) : ℝ)) : ℂ) * Complex.I) := by
    unfold halfPhase
    push_cast
    ring
  rw [hz, Complex.sinh_neg, Complex.sinh_mul_I, ← Complex.ofReal_sin]
  ring

/-- Evaluates the evolved `ket0` as a scalar exponential times an explicit two-coordinate
trigonometric vector. -/
theorem evolvedVector_eq_pq (r s θ ħ t : ℝ) (hunb : unbrokenPT r s θ) :
    evolution r s θ ħ t *ᵥ ket0
      = Complex.exp (phase r s θ ħ t) •
          ![ ((Real.cos (omega r s θ * t / (2 * ħ)) : ℝ) : ℂ)
                + (((2 * r * Real.sin θ) / omega r s θ : ℝ) : ℂ)
                    * ((Real.sin (omega r s θ * t / (2 * ħ)) : ℝ) : ℂ),
              (-Complex.I) * (((((2 * s) / omega r s θ : ℝ) : ℂ))
                    * ((Real.sin (omega r s θ * t / (2 * ħ)) : ℝ) : ℂ)) ] := by
  rw [evolution_decomp r s θ ħ t hunb, Matrix.smul_mulVec,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    sigmaN_mulVec_ket0, cosh_halfPhase, sinh_halfPhase]
  funext i
  fin_cases i <;>
    simp only [ket0, Pi.smul_apply, Pi.add_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_fin_one, smul_eq_mul, mul_one, mul_zero,
      zero_add]
  · linear_combination
      (-(Complex.exp (phase r s θ ħ t)
          * (Real.sin (omega r s θ * t / (2 * ħ)) : ℂ)
          * (((2 * r * Real.sin θ) / omega r s θ : ℝ) : ℂ))) * Complex.I_mul_I
  · ring

/-- For positive `s` in the unbroken region, the square of `(r / s) * sin θ` is less than one. -/
theorem ratio_sq_lt_one (r s θ : ℝ) (hs : 0 < s) (hunb : unbrokenPT r s θ) :
    ((r / s) * Real.sin θ) ^ 2 < 1 := by
  have hs2 : (0:ℝ) < s ^ 2 := pow_pos hs 2
  have hunb' : 0 < omegaSq r s θ := hunb
  unfold omegaSq at hunb'
  have h1 : r ^ 2 * (Real.sin θ) ^ 2 < s ^ 2 := by nlinarith [hunb']
  rw [show ((r / s) * Real.sin θ) ^ 2 = (r * Real.sin θ) ^ 2 / s ^ 2 by
    rw [mul_pow, div_pow]
    ring]
  rw [div_lt_one hs2]
  nlinarith [h1]

/-- For positive `s` in the unbroken region, the gap equals `2 * s * cos (alphaAngle r s θ)`. -/
theorem omega_eq_two_s_cos (r s θ : ℝ) (hs : 0 < s) (hunb : unbrokenPT r s θ) :
    omega r s θ = 2 * s * Real.cos (alphaAngle r s θ) := by
  have hsq : omega r s θ ^ 2 = omegaSq r s θ := omega_sq r s θ hunb
  have hc : Real.cos (alphaAngle r s θ)
      = Real.sqrt (1 - ((r / s) * Real.sin θ) ^ 2) := by
    unfold alphaAngle
    exact Real.cos_arcsin _
  have hnonneg : 0 ≤ 2 * s * Real.cos (alphaAngle r s θ) :=
    mul_nonneg (by positivity) (Real.cos_arcsin_nonneg ((r / s) * Real.sin θ))
  have hsq2 : (2 * s * Real.cos (alphaAngle r s θ)) ^ 2 = omegaSq r s θ := by
    rw [hc]
    have hinner : 0 ≤ 1 - ((r / s) * Real.sin θ) ^ 2 := by
      nlinarith [ratio_sq_lt_one r s θ hs hunb]
    have hsqr : (Real.sqrt (1 - ((r / s) * Real.sin θ) ^ 2)) ^ 2
        = 1 - ((r / s) * Real.sin θ) ^ 2 := Real.sq_sqrt hinner
    unfold omegaSq
    rw [mul_pow, hsqr]
    field_simp
    ring
  rw [omega, ← hsq2, Real.sqrt_sq hnonneg]

/-- For positive `s` in the unbroken region, the sine of `alphaAngle` is `(r / s) * sin θ`. -/
theorem sin_alphaAngle (r s θ : ℝ) (hs : 0 < s) (hunb : unbrokenPT r s θ) :
    Real.sin (alphaAngle r s θ) = (r / s) * Real.sin θ := by
  unfold alphaAngle
  have h2 : ((r / s) * Real.sin θ) ^ 2 < 1 := ratio_sq_lt_one r s θ hs hunb
  have hlow : -1 ≤ (r / s) * Real.sin θ := by nlinarith [h2]
  have hhigh : (r / s) * Real.sin θ ≤ 1 := by nlinarith [h2]
  exact Real.sin_arcsin hlow hhigh

/-- For positive `ħ` and `s` in the unbroken region, expresses the evolved state using
`alphaAngle` as in equation (13) of [BenderEtAl2007]. -/
theorem evolution13 (r s θ ħ t : ℝ) (_hħ : 0 < ħ) (hs : 0 < s)
    (hunb : unbrokenPT r s θ) :
    evolution r s θ ħ t *ᵥ ket0
      = (Complex.exp (-(Complex.I * ((t * r * Real.cos θ / ħ : ℝ) : ℂ)))
            / ((Real.cos (alphaAngle r s θ) : ℝ) : ℂ))
          • ![ (Real.cos (omega r s θ * t / (2 * ħ) - alphaAngle r s θ) : ℂ),
               (-Complex.I) * (Real.sin (omega r s θ * t / (2 * ħ)) : ℂ) ] := by
  have hunb' : unbrokenPT r s θ := hunb
  have hωpos : 0 < omega r s θ := Real.sqrt_pos.mpr hunb
  have homega : omega r s θ = 2 * s * Real.cos (alphaAngle r s θ) :=
    omega_eq_two_s_cos r s θ hs hunb
  have hsinα : Real.sin (alphaAngle r s θ) = (r / s) * Real.sin θ :=
    sin_alphaAngle r s θ hs hunb
  have hcosα_ne : Real.cos (alphaAngle r s θ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at homega
    exact (ne_of_gt hωpos) homega
  have hp : ((2 * r * Real.sin θ) / omega r s θ : ℝ)
      = Real.sin (alphaAngle r s θ) / Real.cos (alphaAngle r s θ) := by
    rw [homega, hsinα]
    field_simp
  have hq : ((2 * s) / omega r s θ : ℝ) = 1 / Real.cos (alphaAngle r s θ) := by
    rw [homega]
    field_simp
  rw [evolvedVector_eq_pq r s θ ħ t hunb']

  have hphase : phase r s θ ħ t
      = -(Complex.I * ((t * r * Real.cos θ / ħ : ℝ) : ℂ)) := by
    unfold phase
    push_cast
    ring
  rw [hphase, hp, hq]

  have hcossub : Real.cos (omega r s θ * t / (2 * ħ) - alphaAngle r s θ)
      = Real.cos (omega r s θ * t / (2 * ħ)) * Real.cos (alphaAngle r s θ)
        + Real.sin (omega r s θ * t / (2 * ħ)) * Real.sin (alphaAngle r s θ) := by
    rw [Real.cos_sub]
  have hcc : (((Real.cos (alphaAngle r s θ) : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast hcosα_ne
  have hcc2 : Complex.cos ((alphaAngle r s θ : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos]
    exact hcc
  ext i
  fin_cases i <;>
    simp only [Pi.smul_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_fin_one, smul_eq_mul]
  · rw [hcossub]
    push_cast
    field_simp [hcc2]
  · push_cast
    field_simp [hcc]

/-- At time `(2 * alphaAngle r s θ + π) * ħ / omega r s θ`, the evolution sends `ket0` to the
displayed phase multiple of `ket1`. -/
theorem spin_flip_time (r s θ ħ : ℝ) (hħ : 0 < ħ) (hs : 0 < s)
    (hunb : unbrokenPT r s θ) :
    let τ : ℝ := (2 * alphaAngle r s θ + Real.pi) * ħ / omega r s θ
    evolution r s θ ħ τ *ᵥ ket0
      = ((-Complex.I) * Complex.exp (-(Complex.I * ((τ * r * Real.cos θ / ħ : ℝ) : ℂ)))
            • (1 : ℂ)) • ket1 := by
  intro τ
  have hunb' : unbrokenPT r s θ := hunb
  have hωpos : 0 < omega r s θ := Real.sqrt_pos.mpr hunb
  have homega : omega r s θ = 2 * s * Real.cos (alphaAngle r s θ) :=
    omega_eq_two_s_cos r s θ hs hunb
  have hcosα_ne : Real.cos (alphaAngle r s θ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at homega
    exact (ne_of_gt hωpos) homega
  have harg : omega r s θ * τ / (2 * ħ) = alphaAngle r s θ + Real.pi / 2 := by
    unfold τ
    field_simp [ne_of_gt hħ, ne_of_gt hωpos]
  rw [evolution13 r s θ ħ τ hħ hs hunb', harg]
  simp only [add_sub_cancel_left, Real.sin_add_pi_div_two, Real.cos_pi_div_two]
  have hcc : (((Real.cos (alphaAngle r s θ) : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast hcosα_ne
  ext i
  fin_cases i <;>
    simp only [Pi.smul_apply, ket1, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_fin_one, smul_eq_mul, Complex.ofReal_zero, mul_zero]
  all_goals field_simp [hcc]

/-- For any fixed positive `ħ` and gap, parameters and an angle satisfying the stated sine
relation give a positive time expression below any positive bound. This is the small-time
parameter construction of [BenderEtAl2007]. -/
theorem optimal_time_arbitrarily_small (ħ ω₀ : ℝ) (hħ : 0 < ħ) (hω₀ : 0 < ω₀) :
    ∀ ε : ℝ, 0 < ε → ∃ (r s θ α : ℝ),
      unbrokenPT r s θ ∧ omega r s θ = ω₀ ∧
      Real.sin α = (r / s) * Real.sin θ ∧
      0 < (2 * α + Real.pi) * ħ / omega r s θ ∧
      (2 * α + Real.pi) * ħ / omega r s θ < ε := by
  intro ε hε
  set δ : ℝ := min (Real.pi / 4) (ε * ω₀ / (4 * ħ)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (by positivity) (div_pos (mul_pos hε hω₀) (by positivity))
  have hδle1 : δ ≤ Real.pi / 4 := by rw [hδdef]; exact min_le_left _ _
  have hδle2 : δ ≤ ε * ω₀ / (4 * ħ) := by rw [hδdef]; exact min_le_right _ _
  have hδlt : δ < Real.pi := by
    have : Real.pi / 4 < Real.pi := by have hpi := Real.pi_pos; linarith
    linarith
  have hsinδ : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδpos hδlt
  set s : ℝ := ω₀ / (2 * Real.sin δ) with hsdef
  have hs : 0 < s := by rw [hsdef]; positivity
  set α : ℝ := δ - Real.pi / 2 with hαdef
  set r : ℝ := s * Real.sin α with hrdef
  refine ⟨r, s, Real.pi / 2, α, ?_, ?_, ?_, ?_, ?_⟩
  · unfold unbrokenPT omegaSq
    have hsinθ : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    have hcosα : Real.cos α = Real.sin δ := by
      rw [hαdef, Real.cos_sub_pi_div_two]
    have hsinα : Real.sin α = -Real.cos δ := by
      rw [hαdef, Real.sin_sub_pi_div_two]
    have hs_sinα : r = s * Real.sin α := hrdef
    rw [hsinθ]
    have hnum : 4 * s ^ 2 - 4 * r ^ 2 * 1 ^ 2 = (2 * s * Real.cos α) ^ 2 := by
      rw [hs_sinα]
      nlinarith [Real.sin_sq_add_cos_sq α]
    rw [hnum, hcosα]
    have : (2 * s * Real.sin δ) ^ 2 = ω₀ ^ 2 := by
      rw [hsdef]; field_simp [ne_of_gt hsinδ]
    rw [this]
    exact pow_pos hω₀ 2
  · unfold omega
    have hsinθ : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    have hcosα : Real.cos α = Real.sin δ := by
      rw [hαdef, Real.cos_sub_pi_div_two]
    have hsinα : Real.sin α = -Real.cos δ := by
      rw [hαdef, Real.sin_sub_pi_div_two]
    have hsinδpos : 0 < Real.sin δ := hsinδ
    have hsq : omegaSq r s (Real.pi / 2) = ω₀ ^ 2 := by
      have hsinδ2 : Real.sin δ ^ 2 = 1 - Real.sin α ^ 2 := by
        have hcos2 : Real.cos α ^ 2 = Real.sin δ ^ 2 := by rw [hcosα]
        have hsin2 : Real.sin α ^ 2 = Real.cos δ ^ 2 := by rw [hsinα]; ring
        nlinarith [Real.sin_sq_add_cos_sq α]
      unfold omegaSq
      rw [hsinθ]
      have hs_sinα : r = s * Real.sin α := hrdef
      rw [hs_sinα, hsdef]
      field_simp [ne_of_gt hsinδ]
      nlinarith [hsinδ2]
    rw [hsq, Real.sqrt_sq hω₀.le]
  · rw [hrdef, Real.sin_pi_div_two, mul_one,
      mul_div_cancel_left₀ (Real.sin α) (ne_of_gt hs)]
  · have homega : omega r s (Real.pi / 2) = ω₀ := by
      unfold omega
      have hsinθ : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
      have hs_sinα : r = s * Real.sin α := hrdef
      have hcosα : Real.cos α = Real.sin δ := by
        rw [hαdef, Real.cos_sub_pi_div_two]
      have hsinα : Real.sin α = -Real.cos δ := by
        rw [hαdef, Real.sin_sub_pi_div_two]
      have hsq : omegaSq r s (Real.pi / 2) = ω₀ ^ 2 := by
        have hsinδ2 : Real.sin δ ^ 2 = 1 - Real.sin α ^ 2 := by
          have hcos2 : Real.cos α ^ 2 = Real.sin δ ^ 2 := by rw [hcosα]
          have hsin2 : Real.sin α ^ 2 = Real.cos δ ^ 2 := by rw [hsinα]; ring
          nlinarith [Real.sin_sq_add_cos_sq α]
        unfold omegaSq
        rw [hsinθ, hs_sinα, hsdef]
        field_simp [ne_of_gt hsinδ]
        nlinarith [hsinδ2]
      rw [hsq, Real.sqrt_sq hω₀.le]
    rw [homega]
    have : 2 * α + Real.pi = 2 * δ := by rw [hαdef]; ring
    rw [this]
    positivity
  · have homega : omega r s (Real.pi / 2) = ω₀ := by
      unfold omega
      have hsinθ : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
      have hs_sinα : r = s * Real.sin α := hrdef
      have hcosα : Real.cos α = Real.sin δ := by
        rw [hαdef, Real.cos_sub_pi_div_two]
      have hsinα : Real.sin α = -Real.cos δ := by
        rw [hαdef, Real.sin_sub_pi_div_two]
      have hsq : omegaSq r s (Real.pi / 2) = ω₀ ^ 2 := by
        have hsinδ2 : Real.sin δ ^ 2 = 1 - Real.sin α ^ 2 := by
          have hcos2 : Real.cos α ^ 2 = Real.sin δ ^ 2 := by rw [hcosα]
          have hsin2 : Real.sin α ^ 2 = Real.cos δ ^ 2 := by rw [hsinα]; ring
          nlinarith [Real.sin_sq_add_cos_sq α]
        unfold omegaSq
        rw [hsinθ, hs_sinα, hsdef]
        field_simp [ne_of_gt hsinδ]
        nlinarith [hsinδ2]
      rw [hsq, Real.sqrt_sq hω₀.le]
    rw [homega]
    have h2 : 2 * α + Real.pi = 2 * δ := by rw [hαdef]; ring
    rw [h2]
    have hlt : 2 * δ * ħ / ω₀ < ε := by
      have hδ' : δ * (4 * ħ) ≤ ε * ω₀ := by
        have h4 : (0:ℝ) < 4 * ħ := by positivity
        rw [le_div_iff₀ h4] at hδle2
        exact hδle2
      rw [div_lt_iff₀ hω₀]
      nlinarith [hδ', mul_pos hε hω₀]
    calc 2 * δ * ħ / ω₀ = (2 * δ) * ħ / ω₀ := by ring
      _ < ε := hlt

end Qatlib.Papers.FastHermitian06.MainResults.SpinFlip
