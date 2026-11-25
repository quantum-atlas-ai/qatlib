/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.Nucleation.TailExpansion
public import Qatlib.Papers.SuperfoilLift19.QuantumCirc.PhaseCirculation

import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Controlled algebraic nucleation-number estimate

[Musser2019Superfoil], equation (4), and Supplemental Material equations
(5)--(8), [arXiv:1904.04908v3](https://arxiv.org/abs/1904.04908v3).
On a physical cutoff circle of radius `r`, the exact inverse Joukowski branch
gives `|z-a|²=r|z|`.  The leading squared speed is
`a(Γ_KJ-Γ)²/(16π²R²r)`.  The scaled difference between the exact ideal speed
and this truncation is proved to be `O(√r)`; at fixed chord this is the
supplement's unscaled `O(√(L/r))` remainder.  The thin-chord approximation
remains outside the proved statements.

Equation (3) then gives an exact algebraic threshold within this model.  With
`Γ=nκ` and `n_KJ=Γ_KJ/κ`, the continuous estimate is
`Δn²=16π²R²r(U²+2c²)/(3aκ²)`.  Defining the displayed fit constant makes this
identically `C L/(3ξ)`.  At zero speed, in the thin scaling `L=4a`, and with
`κ²=8π²c²ξ²` together with `R=a`, it reduces to the supplement's `C=r/ξ`.
Integer rounding and
actual Gross--Pitaevskii vortex emission are separate phenomenological steps.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfoilLift19.Nucleation

open Filter Topology Asymptotics
open Qatlib.Papers.SuperfoilLift19.QuantumCirc

/-- First-term squared ideal speed on a physical cutoff circle of radius `r`,
using the inverse-map relation `|z-a|²≈ar`. -/
def physicalTailLeadingSpeedSq (a radius cutoff speed alpha circulation : ℝ) : ℝ :=
  a * (kuttaCirculation radius speed alpha - circulation) ^ 2 /
    (16 * Real.pi ^ 2 * radius ^ 2 * cutoff)

/-- The squared circulation defect at the compressibility threshold. -/
def circulationDefectThreshold (a radius cutoff farSoundSq farSpeed : ℝ) : ℝ :=
  16 * Real.pi ^ 2 * radius ^ 2 * cutoff * (farSpeed ^ 2 + 2 * farSoundSq) / (3 * a)

/-- The continuous squared vortex-number defect at the threshold. -/
def nucleationDefectSqEstimate (a radius cutoff farSoundSq farSpeed quantum : ℝ) : ℝ :=
  circulationDefectThreshold a radius cutoff farSoundSq farSpeed / quantum ^ 2

/-- The coefficient in `Δn²=C L/(3ξ)`, before suppressing its speed and shape
dependence by a fit. -/
def nucleationFitConstant
    (a radius cutoff farSoundSq farSpeed quantum chord healingLength : ℝ) : ℝ :=
  16 * Real.pi ^ 2 * radius ^ 2 * cutoff * healingLength *
    (farSpeed ^ 2 + 2 * farSoundSq) / (a * quantum ^ 2 * chord)

/-- The supplement's integer prediction, obtained only after the continuous
estimate and its fitting approximations have been chosen. -/
def analyticVortexNumberPrediction (kuttaNumber fitConstant chord healingLength : ℝ) : ℤ :=
  round (kuttaNumber - Real.sqrt (fitConstant * chord / (3 * healingLength)))

/-- The physical-cutoff model is the circle-plane coefficient divided by `a*r`. -/
theorem physicalTailLeadingSpeedSq_eq_coefficient_div {a radius cutoff speed alpha circulation : ℝ}
    (ha : a ≠ 0) (hcutoff : cutoff ≠ 0) :
    physicalTailLeadingSpeedSq a radius cutoff speed alpha circulation =
      tailLeadingSpeedSqCoefficient a radius speed alpha circulation / (a * cutoff) := by
  unfold physicalTailLeadingSpeedSq tailLeadingSpeedSqCoefficient
  field_simp [ha, hcutoff]

/-- Multiplication by the cutoff radius turns the first-term model into the
physical-plane leading coefficient. -/
theorem cutoff_mul_physicalTailLeadingSpeedSq {a radius cutoff speed alpha circulation : ℝ}
    (ha : a ≠ 0) (hcutoff : cutoff ≠ 0) :
    cutoff * physicalTailLeadingSpeedSq a radius cutoff speed alpha circulation =
      physicalTailSpeedSqCoefficient a radius speed alpha circulation := by
  unfold physicalTailLeadingSpeedSq physicalTailSpeedSqCoefficient tailLeadingSpeedSqCoefficient
  field_simp [ha, hcutoff]

/-- The exact ideal speed on the explicit inverse branch differs from the
nucleation-number truncation by `O(√r)` after physical rescaling. -/
theorem isBigO_outerTailInverse_scaled_speed_sq_sub_truncation
    {a offset speed alpha circulation : ℝ} (ha : 0 < a)
    (hradius : ((a + offset : ℝ) : ℂ) ≠ 0) :
    (fun w : ℂ => ‖w‖ *
        ‖idealComplexVelocity a offset speed alpha circulation (outerTailInverse a w)‖ ^ 2 -
      ‖w‖ * physicalTailLeadingSpeedSq a (a + offset) ‖w‖ speed alpha circulation) =O[
        nhdsWithin 0 ({0}ᶜ)] fun w => Real.sqrt ‖w‖ := by
  refine (isBigO_outerTailInverse_scaled_speed_sq_sub (speed := speed) (alpha := alpha)
    (circulation := circulation) ha hradius).congr' ?_ EventuallyEq.rfl
  show (fun w : ℂ => ‖w‖ *
        ‖idealComplexVelocity a offset speed alpha circulation (outerTailInverse a w)‖ ^ 2 -
      physicalTailSpeedSqCoefficient a (a + offset) speed alpha circulation) =ᶠ[
        nhdsWithin 0 ({0}ᶜ)]
    (fun w : ℂ => ‖w‖ *
        ‖idealComplexVelocity a offset speed alpha circulation (outerTailInverse a w)‖ ^ 2 -
      ‖w‖ * physicalTailLeadingSpeedSq a (a + offset) ‖w‖ speed alpha circulation)
  filter_upwards [self_mem_nhdsWithin] with w hw
  rw [cutoff_mul_physicalTailLeadingSpeedSq ha.ne' (by simpa using hw)]

/-- Equation (3)'s residual, evaluated on the leading cutoff speed, is an
explicit rational function of the circulation defect. -/
theorem compressibilityResidual_physicalTailLeadingSpeedSq
    (a radius cutoff farSoundSq farSpeed alpha circulation : ℝ)
    (hradius : radius ≠ 0) (hcutoff : cutoff ≠ 0) :
    compressibilityResidual farSoundSq
      (physicalTailLeadingSpeedSq a radius cutoff farSpeed alpha circulation) (farSpeed ^ 2) =
    (3 * a * (kuttaCirculation radius farSpeed alpha - circulation) ^ 2 -
      16 * Real.pi ^ 2 * radius ^ 2 * cutoff * (farSpeed ^ 2 + 2 * farSoundSq)) /
      (16 * Real.pi ^ 2 * radius ^ 2 * cutoff) := by
  unfold compressibilityResidual physicalTailLeadingSpeedSq
  field_simp [hradius, hcutoff, Real.pi_ne_zero]
  ring

/-- Within the leading cutoff model, equation (3) is equivalent to the squared
circulation defect exceeding its explicit positive-denominator threshold. -/
theorem compressibilityRatio_physicalTailLeadingSpeedSq_pos_iff
    {a radius cutoff farSoundSq farSpeed alpha circulation : ℝ}
    (ha : 0 < a) (hradius : 0 < radius) (hcutoff : 0 < cutoff) (hc : 0 < farSoundSq) :
    0 < compressibilityRatio farSoundSq
      (physicalTailLeadingSpeedSq a radius cutoff farSpeed alpha circulation) (farSpeed ^ 2) ↔
      circulationDefectThreshold a radius cutoff farSoundSq farSpeed <
        (kuttaCirculation radius farSpeed alpha - circulation) ^ 2 := by
  have hden : 0 < 16 * Real.pi ^ 2 * radius ^ 2 * cutoff := by positivity
  rw [compressibilityRatio_pos_iff hc,
    compressibilityResidual_physicalTailLeadingSpeedSq a radius cutoff farSoundSq farSpeed alpha
      circulation hradius.ne' hcutoff.ne',
    div_pos_iff_of_pos_right hden]
  unfold circulationDefectThreshold
  rw [div_lt_iff₀ (show 0 < 3 * a by positivity)]
  constructor <;> intro h <;> nlinarith

/-- Quantizing `Γ=nκ` and setting `n_KJ=Γ_KJ/κ` converts the threshold into
the continuous squared vortex-number estimate. -/
theorem compressibilityRatio_physicalTailLeadingSpeedSq_pos_iff_quantized
    {a radius cutoff farSoundSq farSpeed alpha quantum kuttaNumber n : ℝ}
    (ha : 0 < a) (hradius : 0 < radius) (hcutoff : 0 < cutoff) (hc : 0 < farSoundSq)
    (hquantum : 0 < quantum)
    (hkuttaNumber : kuttaNumber = kuttaCirculation radius farSpeed alpha / quantum) :
    0 < compressibilityRatio farSoundSq
      (physicalTailLeadingSpeedSq a radius cutoff farSpeed alpha (n * quantum)) (farSpeed ^ 2) ↔
      nucleationDefectSqEstimate a radius cutoff farSoundSq farSpeed quantum <
        (kuttaNumber - n) ^ 2 := by
  rw [compressibilityRatio_physicalTailLeadingSpeedSq_pos_iff ha hradius hcutoff hc]
  have hdefect : kuttaCirculation radius farSpeed alpha - n * quantum =
      quantum * (kuttaNumber - n) := by
    rw [hkuttaNumber]
    field_simp [hquantum.ne']
  rw [hdefect]
  unfold nucleationDefectSqEstimate circulationDefectThreshold
  rw [div_lt_iff₀ (sq_pos_of_pos hquantum)]
  constructor <;> intro h <;> nlinarith

/-- For nonzero scale, quantum, chord, and healing length, the fit constant
makes the continuous estimate exactly `C L/(3ξ)`, with no sign, cubic-power,
or denominator ambiguity. -/
theorem nucleationDefectSqEstimate_eq_fitConstant
    (a radius cutoff farSoundSq farSpeed quantum chord healingLength : ℝ)
    (ha : a ≠ 0) (hquantum : quantum ≠ 0) (hchord : chord ≠ 0) (hhealing : healingLength ≠ 0) :
    nucleationDefectSqEstimate a radius cutoff farSoundSq farSpeed quantum =
      nucleationFitConstant a radius cutoff farSoundSq farSpeed quantum chord healingLength *
        chord / (3 * healingLength) := by
  unfold nucleationDefectSqEstimate circulationDefectThreshold nucleationFitConstant
  field_simp [ha, hquantum, hchord, hhealing]

/-- At zero speed and in the thin scaling `L=4a` with `R=a`, the
quantum/healing-length relation gives the supplement's limiting fit constant
`C=r/ξ`. -/
theorem nucleationFitConstant_zero_speed_thin
    {a radius cutoff farSoundSq quantum chord healingLength : ℝ}
    (ha : a ≠ 0) (hfarSoundSq : farSoundSq ≠ 0) (hhealing : healingLength ≠ 0)
    (hchord : chord = 4 * a) (hradius : radius = a)
    (hquantumSq : quantum ^ 2 = 8 * Real.pi ^ 2 * farSoundSq * healingLength ^ 2) :
    nucleationFitConstant a radius cutoff farSoundSq 0 quantum chord healingLength =
      cutoff / healingLength := by
  unfold nucleationFitConstant
  rw [hchord, hradius, hquantumSq]
  field_simp [ha, hfarSoundSq, hhealing, Real.pi_ne_zero]
  ring

/-- The circulation quantum and healing length obey `κ²=8π²c²ξ²` when
`ℏ²=2m²c²ξ²`, the squared form of the article's definitions. -/
theorem circulationQuantum_sq_of_healingLength {hbar mass farSoundSq healingLength : ℝ}
    (hmass : mass ≠ 0)
    (hhealing : hbar ^ 2 = 2 * mass ^ 2 * farSoundSq * healingLength ^ 2) :
    circulationQuantum hbar mass ^ 2 =
      8 * Real.pi ^ 2 * farSoundSq * healingLength ^ 2 := by
  unfold circulationQuantum
  calc
    (2 * Real.pi * hbar / mass) ^ 2 = 4 * Real.pi ^ 2 * hbar ^ 2 / mass ^ 2 := by ring
    _ = 8 * Real.pi ^ 2 * farSoundSq * healingLength ^ 2 := by
      rw [hhealing]
      field_simp [hmass]
      ring

/-- If the unrounded analytic prediction is exactly an integer, the rounding
step returns that integer. -/
theorem analyticVortexNumberPrediction_of_exact {kuttaNumber fitConstant chord healingLength : ℝ}
    {n : ℤ} (h : kuttaNumber - Real.sqrt (fitConstant * chord / (3 * healingLength)) = n) :
    analyticVortexNumberPrediction kuttaNumber fitConstant chord healingLength = n := by
  unfold analyticVortexNumberPrediction
  rw [h]
  exact round_intCast n

end Qatlib.Papers.SuperfoilLift19.Nucleation
