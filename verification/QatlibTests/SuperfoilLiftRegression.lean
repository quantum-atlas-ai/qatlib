/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.QuantumCirc.PhaseCirculation
public import Qatlib.Papers.SuperfoilLift19.LiftForce.ImpulseLift

@[expose] public section

/-!
# Consumers of the phase-circulation and impulse-lift interfaces

The tests instantiate nonzero positive and negative windings, a nonconstant
phase lift, a differentiable vortex trajectory, and exact lift steps. They
exercise the ideal hypotheses of [Musser2019Superfoil]; experimental and PDE
claims remain outside this consumer.
-/

set_option autoImplicit false

noncomputable section

namespace QatlibTests.SuperfoilLiftRegression

open Qatlib.Papers.SuperfoilLift19.QuantumCirc
open Qatlib.Papers.SuperfoilLift19.LiftForce

/-- Zero amplitude can identify distinct phases; the nonzero-amplitude
condition in the source bridge is therefore necessary. -/
example : polarWave 0 0 = polarWave 0 Real.pi ∧ phaseFactor Real.pi ≠ phaseFactor 0 := by
  norm_num [polarWave, phaseFactor, Complex.exp_pi_mul_I]

/-- A nonzero polar wave closes precisely with an integer phase increment. -/
example (a b : ℝ) : polarWave 2 b = polarWave 2 a ↔
    ∃ n : ℤ, b - a = 2 * Real.pi * (n : ℝ) :=
  polar_wave_closure_iff_winding (by norm_num) a b

/-- A three-turn polar state is single valued after the loop closes. -/
example (phase : ℝ) : phaseFactor (phase + 2 * Real.pi * (3 : ℤ)) = phaseFactor phase :=
  phase_factor_integer_turn phase 3

/-- A nonconstant phase lift on a unit parameter interval has three circulation
quanta, by the analytic integral theorem. -/
example (hbar mass : ℝ) :
    (∫ _t in (0 : ℝ)..1, (hbar / mass) * (6 * Real.pi)) =
      quantizedCirculation hbar mass 3 := by
  apply phase_integral_quantized hbar mass 0 1 (fun t => 6 * Real.pi * t)
    (fun _ => 6 * Real.pi) 3
  · intro t _
    simpa using (hasDerivAt_id t).const_mul (6 * Real.pi)
  · exact intervalIntegrable_const
  · norm_num
    ring

/-- Three bound circulation units and three opposite wake units cancel. -/
example (hbar mass : ℝ) :
    quantizedCirculation hbar mass 3 + quantizedCirculation hbar mass (-3) = 0 :=
  starting_vortex_cancellation hbar mass 3

/-- Shedding two negative winding units preserves the total circulation. -/
example (hbar mass : ℝ) :
    quantizedCirculation hbar mass 5 + quantizedCirculation hbar mass (-4) =
      quantizedCirculation hbar mass 3 + quantizedCirculation hbar mass (-2) := by
  simpa using shedding_preserves_total_circulation hbar mass 3 (-2) (-2)

/-- A linearly moving wake vortex produces the signed ideal force. -/
example (density circulation speed t : ℝ) :
    deriv (fun s => vortexImpulse density (-circulation) (speed * s)) t =
      -idealLift density speed circulation := by
  apply impulse_derivative_lift
  simpa using (hasDerivAt_id t).const_mul speed

/-- A winding transition from negative two to negative one has one lift step. -/
example (density speed hbar mass : ℝ) :
    idealLift density speed (quantizedCirculation hbar mass (-1)) -
        idealLift density speed (quantizedCirculation hbar mass (-2)) =
      -density * speed * circulationQuantum hbar mass := by
  simpa using ideal_lift_step density speed hbar mass (-2)

/-- A nonzero phase winding cannot have zero circulation when the physical
normalization is positive. -/
example {hbar mass : ℝ} (hhbar : 0 < hbar) (hmass : 0 < mass) :
    quantizedCirculation hbar mass 3 ≠ quantizedCirculation hbar mass 0 := by
  intro h
  have := quantized_circulation_injective (ne_of_gt (circulation_quantum_pos hhbar hmass)) h
  norm_num at this

end QatlibTests.SuperfoilLiftRegression
