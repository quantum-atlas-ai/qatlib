/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.QuantumCirc.PhaseCirculation
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-!
# Vortex impulse and ideal lift steps

[Musser2019Superfoil], pp. 154502-1 and 154502-4, compares filtered superfluid
lift with the ideal Kutta--Joukowski law. See
[the published article](https://doi.org/10.1103/PhysRevLett.123.154502).

This module treats a planar point-vortex impulse and differentiates it along a
prescribed trajectory. The convention is `I_y = -rho Gamma_wake x` and force on
the foil is `-d I_y / dt`; with opposite bound and wake circulation this gives
`L = -rho U Gamma_bound`, as in the article. Circulation quantization is supplied
by `Qatlib.Papers.SuperfoilLift19.QuantumCirc.phase_integral_quantized`.
No derivation of the point-vortex approximation from the Gross--Pitaevskii PDE,
stress-tensor contour theorem, nucleation threshold fit, or stall simulation is
claimed.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfoilLift19.LiftForce

open Qatlib.Papers.SuperfoilLift19.QuantumCirc

/-- Transverse impulse per unit span for a point vortex at streamwise position
`x`, with the planar orientation used in this module. -/
def vortexImpulse (density wakeCirculation x : ℝ) : ℝ :=
  -density * wakeCirculation * x

/-- The ideal Kutta--Joukowski lift for the article's circulation orientation. -/
def idealLift (density speed boundCirculation : ℝ) : ℝ :=
  -density * speed * boundCirculation

/-- A fixed-circulation point vortex has impulse derivative proportional to its
streamwise velocity, derived using the product rule. -/
theorem impulse_has_deriv_at (density wakeCirculation t speed : ℝ)
    (position : ℝ → ℝ) (hposition : HasDerivAt position speed t) :
    HasDerivAt (fun s => vortexImpulse density wakeCirculation (position s))
      (-density * wakeCirculation * speed) t := by
  exact hposition.const_mul (-density * wakeCirculation)

/-- Opposite bound and wake circulations turn the negative wake-impulse
derivative into the ideal lift. The only trajectory hypothesis specifies its
ordinary derivative. -/
theorem impulse_derivative_lift (density boundCirculation t speed : ℝ)
    (position : ℝ → ℝ) (hposition : HasDerivAt position speed t) :
    deriv (fun s => vortexImpulse density (-boundCirculation) (position s)) t =
      -idealLift density speed boundCirculation := by
  rw [(impulse_has_deriv_at density (-boundCirculation) t speed position hposition).deriv]
  unfold idealLift
  ring

/-- With an integer winding, ideal lift is an integer multiple of one lift
quantum. This exact result concerns the ideal impulse model. -/
theorem ideal_lift_quantized (density speed hbar mass : ℝ) (n : ℤ) :
    idealLift density speed (quantizedCirculation hbar mass n) =
      (-density * speed * circulationQuantum hbar mass) * (n : ℝ) := by
  unfold idealLift quantizedCirculation
  ring

/-- Increasing the winding by one changes ideal lift by exactly one signed
lift quantum, independently of the initial winding. -/
theorem ideal_lift_step (density speed hbar mass : ℝ) (n : ℤ) :
    idealLift density speed (quantizedCirculation hbar mass (n + 1)) -
        idealLift density speed (quantizedCirculation hbar mass n) =
      -density * speed * circulationQuantum hbar mass := by
  simp only [idealLift, quantizedCirculation, Int.cast_add, Int.cast_one]
  ring

/-- Any finite winding change produces the corresponding exact integer lift
difference. -/
theorem ideal_lift_difference (density speed hbar mass : ℝ) (m n : ℤ) :
    idealLift density speed (quantizedCirculation hbar mass m) -
        idealLift density speed (quantizedCirculation hbar mass n) =
      (-density * speed * circulationQuantum hbar mass) * ((m - n : ℤ) : ℝ) := by
  simp only [idealLift, quantizedCirculation, Int.cast_sub]
  ring

/-- Positive density, speed, Planck scale, and mass give a nonzero lift step;
different integer windings are therefore distinguishable in this model. -/
theorem ideal_lift_step_neg {density speed hbar mass : ℝ}
    (hdensity : 0 < density) (hspeed : 0 < speed) (hhbar : 0 < hbar)
    (hmass : 0 < mass) :
    -density * speed * circulationQuantum hbar mass < 0 := by
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hdensity) hspeed)
    (circulation_quantum_pos hhbar hmass)

end Qatlib.Papers.SuperfoilLift19.LiftForce
