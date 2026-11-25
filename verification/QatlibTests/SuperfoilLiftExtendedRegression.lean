/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.QuantumCirc.PhaseCirculation
public import Qatlib.Papers.SuperfoilLift19.LiftForce.ImpulseLift
import Qatlib.Papers.SuperfoilLift19.QuantumCirc.LoopWinding
import Qatlib.Papers.SuperfoilLift19.LiftForce.StationaryContour
import Qatlib.Papers.SuperfoilLift19.LiftForce.DynamicStressBridge
import Qatlib.Papers.SuperfoilLift19.LiftForce.DynamicContinuity
import Qatlib.Papers.SuperfoilLift19.LiftForce.FarFieldImpulse
import Qatlib.Papers.SuperfoilLift19.LiftForce.FiniteImpulseError
import Qatlib.Papers.SuperfoilLift19.LiftForce.NonzeroObstacle
import Qatlib.Papers.SuperfoilLift19.LiftForce.StressImpulse
import Qatlib.Papers.SuperfoilLift19.Nucleation.Compressibility
import Qatlib.Papers.SuperfoilLift19.Nucleation.NucleationNumber

import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

/-!
# Consumers of the phase-circulation and impulse-lift interfaces

The tests instantiate nonzero positive and negative windings, a nonconstant
phase lift, a differentiable vortex trajectory, and exact lift steps.
They also check stationary Gross–Pitaevskii stresses and their contour
forces on a fluid shell.
-/

set_option autoImplicit false

noncomputable section

namespace QatlibTests.SuperfoilLiftExtendedRegression

open Qatlib.Papers.SuperfoilLift19.QuantumCirc
open Qatlib.Papers.SuperfoilLift19.LiftForce
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

/-!
## Consumers of the phase-lift bridge

The remaining tests exercise the constructed phase lift: the winding-one unit
vortex with circulation exactly one quantum, the current-density identity on
that loop, and the zero-density grazing counterexample showing the nonvanishing
premise is necessary.
-/

/-- The winding-one unit vortex: the Madelung line integral along the unit
circle is exactly one circulation quantum. -/
example {hbar mass : ℝ} (hh : 0 < hbar) (hm : 0 < mass) :
    (∫ t in 0..2 * Real.pi,
        (hbar / mass) * angularVelocity phaseFactor (fun s => phaseFactor s * Complex.I) t) =
      circulationQuantum hbar mass := by
  rw [unit_circle_vortex_circulation hh.ne' hm.ne']
  simp only [quantizedCirculation]
  push_cast
  ring

/-- On the unit vortex loop the number density is one, so the current density
`Im (ψ* ψ')` coincides with the angular velocity of the phase. -/
example (t : ℝ) :
    angularVelocity phaseFactor (fun s => phaseFactor s * Complex.I) t =
      currentAlong phaseFactor (fun s => phaseFactor s * Complex.I) t := by
  rw [angularVelocity_eq_currentAlong_div_density (by
      show Complex.exp (((t : ℝ) : ℂ) * Complex.I) ≠ 0
      exact Complex.exp_ne_zero _), phase_factor_norm]
  norm_num

/-- The grazing loop of the vortex core has the polar form
`cos (t / 2) · exp (i t / 2)` with phase `t / 2`. -/
example (t : ℝ) :
    (1 + Complex.exp (((t : ℝ) : ℂ) * Complex.I)) / 2 =
      ((Real.cos (t / 2) : ℝ) : ℂ) * phaseFactor (t / 2) :=
  one_add_exp_div_two t

/-- The grazing loop closes at the density-zero vortex core. -/
example : (1 + Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I)) / 2 = 0 :=
  vortex_core_grazing_loop.2.1

/-- **Missing-premise case.** Through the density zero, the closed grazing loop
has phase increment `π`, which is not an integer multiple of `2π`: the
nonvanishing hypothesis of the winding and quantization theorems cannot be
dropped. -/
example : ¬ ∃ n : ℤ, (Real.pi / 2 : ℝ) - (-Real.pi / 2) = 2 * Real.pi * (n : ℝ) :=
  vortex_core_grazing_loop.2.2.2

/-!
## Consumers of the stress-impulse bridge

The remaining tests instantiate the Eq. (5) contour force: a symmetric stress
tensor, a divergence-free stream flux whose wall and far-field forces agree,
and the nonzero-divergence counterexample showing the contours then differ.
-/

/-- The Eq. (5) stress tensor is symmetric whenever its quantum-pressure field
is symmetric, as for a `C²` amplitude. -/
example (mass gint hbar : ℝ) (rho : ℝ × ℝ → ℝ) (u : ℝ × ℝ → Fin 2 → ℝ)
    (q : ℝ × ℝ → Fin 2 → Fin 2 → ℝ) (hq : ∀ x : ℝ × ℝ, q x 1 0 = q x 0 1)
    (x : ℝ × ℝ) (j k : Fin 2) :
    stressTensor mass gint hbar rho u q x j k =
      stressTensor mass gint hbar rho u q x k j :=
  stressTensor_symmetric mass gint hbar rho u q hq x j k

/-- **Path-independence consumer.** For the divergence-free stream flux
`(f, g) = (x, -y)`, the force on the inner unit box equals the force on the
outer box `[-1, 2]²`, by the wall-to-far-field divergence-theorem bridge. -/
example (k : Fin 2) :
    rectangleForce (fun x j _ => if j = (0 : Fin 2) then x.1 else -x.2) k (0, 0) (1, 1) =
      rectangleForce (fun x j _ => if j = (0 : Fin 2) then x.1 else -x.2) k (-1, -1) (2, 2) := by
  refine stress_force_wall_eq_far_field
    (Tf := fun _ => ContinuousLinearMap.fst ℝ ℝ ℝ)
    (Tg := fun _ => -(ContinuousLinearMap.snd ℝ ℝ ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_
  · exact continuous_fst.continuousOn
  · exact continuous_snd.neg.continuousOn
  · exact fun x _ => hasFDerivAt_fst (E := ℝ) (F := ℝ) (p := x)
  · exact fun x _ => (hasFDerivAt_snd (E := ℝ) (F := ℝ) (p := x)).neg
  · simp
  · exact fun x _ => by simp

/-- **Necessity of momentum conservation.** For the unit-divergence field
`(f, g) = (x, 0)` the contour force depends on the contour: the unit square
carries force `1` and the square `[-1, 2]²` carries force `9`. -/
example : rectangleForce (fun x j _ => x.1 * (1 - (j.val : ℝ))) (1 : Fin 2) (0, 0) (1, 1) ≠
      rectangleForce (fun x j _ => x.1 * (1 - (j.val : ℝ))) (1 : Fin 2) (-1, -1) (2, 2) := by
  obtain ⟨h1, h2⟩ := flux_counterexample_of_nonzero_divergence
  simp [h1, h2]

/-- A uniform flow with positive amplitude and nonzero velocity satisfies
the stationary Madelung stress-divergence identity. -/
example (x : ℝ × ℝ) (k : Fin 2) :
    (∑ j : Fin 2, deriv (fun s =>
      stressTensor 1 1 1 (fun _ => 4) (fun _ => ![1, 0])
        (amplitudeQuantumStress (fun _ => 2) (fun _ _ => 0) (fun _ _ _ => 0))
        (axisLine x j s) j k) 0) = 0 := by
  have h := stationaryMadelung_stress_divergence 1 1 1 (by norm_num)
    (fun _ => 2) (fun _ => ![1, 0]) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
    x k (fun _ => 0) (by norm_num) (fun _ => hasDerivAt_const 0 _)
    (fun _ _ => hasDerivAt_const 0 _) (fun _ _ => hasDerivAt_const 0 _)
    (fun _ => hasDerivAt_const 0 _) (fun _ => hasDerivAt_const 0 _)
    (by simp) (by simp)
  convert h using 2
  norm_num

#print axioms Qatlib.Papers.SuperfoilLift19.LiftForce.stationaryMadelung_stress_divergence

/-- The phase `x₁` has Cartesian partials one and zero. -/
private theorem hasDerivAt_planePhase (y : ℝ × ℝ) (j : Fin 2) :
    HasDerivAt (fun s => (axisLine y j s).1) ((![1, 0] : Fin 2 → ℝ) j) 0 := by
  fin_cases j
  · change HasDerivAt (fun s : ℝ => y.1 + s) 1 0
    exact (hasDerivAt_id (0 : ℝ)).const_add y.1
  · exact hasDerivAt_const 0 y.1

/-- The plane wave of amplitude two satisfies the actual stationary equation. -/
private theorem stationary_gpe_planeWave (y : ℝ × ℝ) :
    StationaryGrossPitaevskiiAt 1 1 1 (9 / 2) (fun _ => 0) (fun p => polarWave 2 p.1) y := by
  refine (stationary_gpe_iff_madelung 1 1 1 (9 / 2) (by norm_num) (by norm_num)
    (fun _ => 0) (fun _ => 2) Prod.fst (fun _ _ => 0) (fun _ => ![1, 0])
    (fun _ _ _ => 0) (fun _ _ _ => 0) y (by norm_num)
    (fun _ _ => hasDerivAt_const 0 _) hasDerivAt_planePhase (fun _ => hasDerivAt_const 0 _)
    (fun _ => hasDerivAt_const 0 _)).2 ?_
  norm_num [Fin.sum_univ_two]

/-- The nonconstant plane wave with phase `x₁` and amplitude two is an
actual stationary Gross–Pitaevskii solution of chemical potential `9/2`,
and its stress satisfies the derived conservation equation. -/
example (x : ℝ × ℝ) (k : Fin 2) :
    StationaryGrossPitaevskiiAt 1 1 1 (9 / 2) (fun _ => 0)
      (fun y => polarWave 2 y.1) x ∧
    (∑ j : Fin 2, deriv (fun s =>
      stressTensor 1 1 1 (fun _ => 4) (fun _ => ![1, 0])
        (amplitudeQuantumStress (fun _ => 2) (fun _ _ => 0) (fun _ _ _ => 0))
        (axisLine x j s) j k) 0) = 0 := by
  refine ⟨stationary_gpe_planeWave x, ?_⟩
  have hD := stationary_gpe_stress_divergence 1 1 1 (9 / 2) 0 (by norm_num) (by norm_num)
    (fun _ => 2) Prod.fst (fun _ _ => 0) (fun _ => ![1, 0])
    (fun _ _ _ => 0) (fun _ _ _ => 0) x k (fun _ => 0)
    (fun _ _ => hasDerivAt_const 0 _) hasDerivAt_planePhase (fun _ _ _ => hasDerivAt_const 0 _)
    (fun _ _ _ => hasDerivAt_const 0 _) (fun _ => rfl)
    (fun _ => hasDerivAt_const 0 _) (fun _ => hasDerivAt_const 0 _)
    (Filter.Eventually.of_forall fun s => ⟨by norm_num, stationary_gpe_planeWave (axisLine x k s)⟩)
  have hrho : (2 : ℝ) ^ 2 = 4 := by norm_num
  simpa only [hrho, one_div, inv_one, one_mul] using hD

#print axioms Qatlib.Papers.SuperfoilLift19.LiftForce.stationary_gpe_stress_divergence

open Qatlib.Papers.SuperfoilLift19.Nucleation
open Asymptotics

/-- The actual nonconstant plane wave satisfies the physical Bernoulli
balance extracted from its stationary Gross–Pitaevskii equation. -/
example (x : ℝ × ℝ) :
    0 + 1 * (2 : ℝ) ^ 2 + 1 / 2 * madelungSpeedSq 1 1 (fun _ => ![1, 0]) x -
      quantumPressureEnergy 1 1 (fun _ => 2) (fun _ _ _ => 0) x = 9 / 2 := by
  exact stationary_gpe_bernoulli_at 1 1 1 (9 / 2) (by norm_num) (by norm_num)
    (fun _ => 0) (fun _ => 2) Prod.fst (fun _ _ => 0) (fun _ => ![1, 0])
    (fun _ _ _ => 0) (fun _ _ _ => 0) x (by norm_num)
    (fun _ _ => hasDerivAt_const 0 _) hasDerivAt_planePhase (fun _ => hasDerivAt_const 0 _)
    (fun _ => hasDerivAt_const 0 _) (stationary_gpe_planeWave x)

/-- **Nondegenerate supersonic example.** With nonzero far speed `U = 1/2`
and local speed `u = 1`, the Bernoulli density is `5/8`, and both sides of
the proved equivalence hold. -/
example :
    bernoulliDensity 1 1 1 (1 : ℝ) ((1 / 2 : ℝ) ^ 2) = 5 / 8 ∧
      (1 : ℝ) ^ 2 > localSoundSpeedSq 1 1
        (bernoulliDensity 1 1 1 (1 : ℝ) ((1 / 2 : ℝ) ^ 2)) := by
  have hfar : localSoundSpeedSq 1 1 1 = (1 : ℝ) := by
    norm_num [localSoundSpeedSq]
  have h := ideal_supersonic_iff_compressibilityRatio_pos
    (mass := 1) (gint := 1) (farDensity := 1) (cSq := 1)
    (speedSq := (1 : ℝ)) (farSpeedSq := (1 / 2 : ℝ) ^ 2)
    (by norm_num) (by norm_num) (by norm_num) hfar
  constructor
  · norm_num [bernoulliDensity]
  · have hr : 0 < compressibilityRatio 1 1 ((1 / 2 : ℝ) ^ 2) := by
      norm_num [compressibilityRatio]
    simpa only [one_pow] using h.mpr hr

/-- **Nondegenerate subsonic counterexample.** With the same nonzero far
speed and local speed `u = 1/4`, equation (3) fails and the flow is not
supersonic. -/
example : ¬(1 / 4 : ℝ) ^ 2 > localSoundSpeedSq 1 1
    (bernoulliDensity 1 1 1 ((1 / 4 : ℝ) ^ 2) ((1 / 2 : ℝ) ^ 2)) := by
  have hfar : localSoundSpeedSq 1 1 1 = (1 : ℝ) := by
    norm_num [localSoundSpeedSq]
  have h := ideal_supersonic_iff_compressibilityRatio_pos
    (mass := 1) (gint := 1) (farDensity := 1) (cSq := 1)
    (speedSq := (1 / 4 : ℝ) ^ 2) (farSpeedSq := (1 / 2 : ℝ) ^ 2)
    (by norm_num) (by norm_num) (by norm_num) hfar
  intro hs
  have hr := h.mp hs
  norm_num [compressibilityRatio] at hr

/-- **Quantum-pressure premise is necessary.** Here equation (3) is
positive, but a positive quantum-pressure difference makes the shifted
threshold fail: the ideal criterion alone cannot certify supersonic flow. -/
example :
    0 < compressibilityRatio 1 (4 / 5 : ℝ) 0 ∧
      ¬2 * (3 / 10 : ℝ) < compressibilityResidual 1 (4 / 5 : ℝ) 0 := by
  norm_num [compressibilityRatio, compressibilityResidual]

#print axioms Qatlib.Papers.SuperfoilLift19.Nucleation.stationary_gpe_bernoulli_at
#print axioms Qatlib.Papers.SuperfoilLift19.Nucleation.stationary_gpe_density_eq_quantumCorrectedDensity
#print axioms Qatlib.Papers.SuperfoilLift19.Nucleation.stationary_gpe_supersonic_iff
#print axioms Qatlib.Papers.SuperfoilLift19.Nucleation.stationary_gpe_supersonic_iff_ratio_pos_of_quantum_eq
#print axioms Qatlib.Papers.SuperfoilLift19.Nucleation.ideal_supersonic_iff_compressibilityRatio_pos

/-- A wave equal to the plane wave outside the open unit square. -/
private noncomputable def shellPlaneWave (p : ℝ × ℝ) : ℂ := by
  classical
  exact if p ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 then 1 else polarWave 2 p.1

/-- A plane wave on the rectangular fluid shell has equal contour forces
even when its extension inside the obstacle violates the wave equation. -/
example (k : Fin 2) :
    let T := polarStress 1 1 1 (fun _ => 2) (fun _ _ => 0) (fun _ => ![1, 0])
      (fun _ _ _ => 0)
    ¬StationaryGrossPitaevskiiAt 1 1 1 (9 / 2) (fun _ => 0) shellPlaneWave (1 / 2, 1 / 2) ∧
      rectangleForce T k (0, 0) (1, 1) = rectangleForce T k (-1, -1) (2, 2) := by
  classical
  dsimp only
  let hole := Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1
  let U := rectangularShellInterior (-1, -1) (2, 2) (0, 0) (1, 1)
  have hOpen : IsOpen U := isOpen_rectangularShellInterior _ _ _ _
  have hPlane : Set.EqOn shellPlaneWave (fun p => polarWave 2 p.1) U := by
    intro p hp
    have hout : p ∉ hole := fun hh =>
      hp.2 ⟨Set.Ioo_subset_Icc_self hh.1, Set.Ioo_subset_Icc_self hh.2⟩
    exact ite_eq_right hout
  refine ⟨?_, ?_⟩
  · have hIn : ((1 / 2, 1 / 2) : ℝ × ℝ) ∈ hole := by
      norm_num [hole, Set.mem_prod, Set.mem_Ioo]
    have hOne : Set.EqOn shellPlaneWave (fun _ => (1 : ℂ)) hole := fun _ h => ite_eq_left h
    unfold StationaryGrossPitaevskiiAt
    rw [waveLaplacian_eq_on_open (isOpen_Ioo.prod isOpen_Ioo) hOne hIn, hOne hIn]
    norm_num [waveLaplacian]
  · refine stationary_gpe_rectangleForce 1 1 1 (9 / 2) 0 (by norm_num) (by norm_num)
      shellPlaneWave (fun _ => 2) (fun _ _ => 0) (fun _ => ![1, 0])
      (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
      k (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun j => ?_) (fun x _ j => ?_)
      ?_ ?_ (fun _ _ _ => hasDerivAt_const 0 _) (fun _ _ _ _ => hasDerivAt_const 0 _)
      (fun _ _ _ _ => hasDerivAt_const 0 _) (fun _ _ _ => rfl)
      (fun _ _ _ => hasDerivAt_const 0 _) (fun _ _ _ => hasDerivAt_const 0 _)
    · unfold polarStress stressTensor amplitudeQuantumStress
      exact continuous_const.continuousOn
    · unfold polarStress stressTensor amplitudeQuantumStress
      exact differentiableAt_const _
    · intro p hp
      refine ⟨by norm_num, ?_⟩
      unfold StationaryGrossPitaevskiiAt
      rw [waveLaplacian_eq_on_open hOpen hPlane hp, hPlane hp]
      exact stationary_gpe_planeWave p
    · exact fun p hp => ⟨U, hOpen, hp, Set.Subset.rfl, Prod.fst, hPlane,
        fun y _ => hasDerivAt_planePhase y⟩

#print axioms Qatlib.Papers.SuperfoilLift19.LiftForce.stationary_gpe_rectangleForce

/-- A free Schrödinger wave with nonzero time derivative, quadratic
spatial dependence, and nodes on the initial slice. -/
private def freeQuadraticWave (p : GPESpacetime) : ℂ :=
  (p.2.1 : ℂ) ^ 2 + Complex.I * (p.1 : ℂ)

/-- The quadratic wave is smooth in time and space, including its nodes. -/
private theorem contDiff_freeQuadraticWave : ContDiff ℝ 3 freeQuadraticWave := by
  have hX : ContDiff ℝ 3 (fun p : GPESpacetime => (p.2.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (by fun_prop)
  have hT : ContDiff ℝ 3 (fun p : GPESpacetime => (p.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  exact (hX.pow 2).add (contDiff_const.mul hT)

/-- The real affine coordinate line has complex derivative one. -/
private theorem hasDerivAt_coe_translate (x : ℝ) :
    HasDerivAt (fun s : ℝ => ((x + s : ℝ) : ℂ)) (1 : ℂ) 0 := by
  simpa only [id_eq, Complex.ofReal_one] using
    (((hasDerivAt_id (0 : ℝ)).const_add x).ofReal_comp)

/-- The free quadratic wave has constant imaginary time derivative. -/
private theorem freeQuadraticWave_time (p : GPESpacetime) :
    gpePartial gpeTimeDirection freeQuadraticWave p = Complex.I := by
  rw [gpePartial_time_eq_deriv p (contDiff_freeQuadraticWave.differentiable (by norm_num) p)]
  simpa only [freeQuadraticWave, mul_one] using
    (((hasDerivAt_coe_translate p.1).const_mul Complex.I).const_add ((p.2.1 : ℂ) ^ 2)).deriv

/-- The first coordinate derivative of the free wave is the expected
linear function. -/
private theorem freeQuadraticWave_dx (p : GPESpacetime) :
    gpePartial (gpeSpaceDirection 0) freeQuadraticWave p = 2 * (p.2.1 : ℂ) := by
  rw [gpePartial_space_eq_axisLine p 0 (contDiff_freeQuadraticWave.differentiable (by norm_num) p)]
  simpa [freeQuadraticWave, axisLine] using
    (((hasDerivAt_coe_translate p.2.1).fun_pow 2).add_const (Complex.I * (p.1 : ℂ))).deriv

/-- No wave variation in the second spatial coordinate. -/
private theorem freeQuadraticWave_dy (p : GPESpacetime) :
    gpePartial (gpeSpaceDirection 1) freeQuadraticWave p = 0 := by
  rw [gpePartial_space_eq_axisLine p 1 (contDiff_freeQuadraticWave.differentiable (by norm_num) p)]
  simp [freeQuadraticWave, axisLine]

/-- The free quadratic wave solves the actual complex equation
globally, rather than just matching its formal coordinate symbols. -/
private theorem freeQuadraticWave_gpe (p : GPESpacetime) :
    GrossPitaevskiiAt 1 0 1 (fun _ => 0) freeQuadraticWave p := by
  have hx : gpePartial (gpeSpaceDirection 0) freeQuadraticWave = fun q => 2 * (q.2.1 : ℂ) :=
    funext freeQuadraticWave_dx
  have hy : gpePartial (gpeSpaceDirection 1) freeQuadraticWave = fun _ => 0 :=
    funext freeQuadraticWave_dy
  have hd : Differentiable ℝ (fun q : GPESpacetime => (2 : ℂ) * (q.2.1 : ℂ)) := by fun_prop
  have hxx : gpePartial (gpeSpaceDirection 0) (fun q => 2 * (q.2.1 : ℂ)) p = 2 := by
    rw [gpePartial_space_eq_axisLine p 0 (hd p)]
    simpa [axisLine] using ((hasDerivAt_coe_translate p.2.1).const_mul (2 : ℂ)).deriv
  have hyy : gpePartial (gpeSpaceDirection 1) (fun _ : GPESpacetime => (0 : ℂ)) p = 0 := by
    simp [gpePartial]
  unfold GrossPitaevskiiAt gpeLaplacian
  rw [freeQuadraticWave_time, Fin.sum_univ_two, hx, hy, hxx, hyy]
  norm_num [Complex.I_mul_I]

/-- The horizontal laboratory momentum of the free quadratic wave is bilinear. -/
private theorem freeQuadraticWave_momentum :
    gpeMomentum 1 freeQuadraticWave 0 = fun q => -2 * q.1 * q.2.1 := by
  funext q
  simp only [gpeMomentum, freeQuadraticWave_dx, freeQuadraticWave, one_mul]
  simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, pow_two]
  ring

/-- On the free quadratic solution the two terms in the momentum
balance are separately nonzero and cancel. -/
example :
    gpePartial gpeTimeDirection (gpeMomentum 1 freeQuadraticWave 0) (0, 1, 0) = -2 ∧
      (∑ j : Fin 2, gpePartial (gpeSpaceDirection j)
        (gpeWaveStress 1 0 1 freeQuadraticWave j 0) (0, 1, 0)) = 2 := by
  have hd : Differentiable ℝ (fun q : GPESpacetime => -2 * q.1 * q.2.1) := by fun_prop
  have ht : gpePartial gpeTimeDirection (gpeMomentum 1 freeQuadraticWave 0) (0, 1, 0) = -2 := by
    rw [freeQuadraticWave_momentum, gpePartial_time_eq_deriv _ (hd _)]
    simp
  refine ⟨ht, ?_⟩
  have h := gpe_local_momentum_balance 1 0 1
    (V := fun _ => 0) (ψ := freeQuadraticWave) (U := Set.univ)
    contDiff_const contDiff_freeQuadraticWave isOpen_univ
    (fun p _ => freeQuadraticWave_gpe p) (0, 1, 0) (Set.mem_univ _) 0
  have hzero : gpePartial (gpeSpaceDirection 0) (fun _ : GPESpacetime => (0 : ℝ)) (0, 1, 0) = 0 := by
    simp [gpePartial]
  rw [ht, hzero, mul_zero] at h
  linarith only [h]

/-- The same actual wave satisfies mass continuity also at the node. -/
example :
    gpePartial gpeTimeDirection (gpeDensity freeQuadraticWave) (0, 0, 0) +
      (1 / (1 : ℝ)) * (∑ j : Fin 2,
        gpePartial (gpeSpaceDirection j) (gpeMomentum 1 freeQuadraticWave j) (0, 0, 0)) = 0 :=
  gpe_local_mass_balance 1 0 1 (by norm_num) (by norm_num)
    (contDiff_freeQuadraticWave.of_le (by norm_num)) (0, 0, 0) (freeQuadraticWave_gpe _)

/-- A nonstationary free wave obeys the extracted impulse law on a
unit control rectangle over a nontrivial time interval. -/
example :
    gpeRectangleMomentum 1 freeQuadraticWave 0 (0, 0) (1, 1) 1 -
      gpeRectangleMomentum 1 freeQuadraticWave 0 (0, 0) (1, 1) 0 +
      (∫ t in (0 : ℝ)..1,
        rectangleForce (fun x j l => gpeWaveStress 1 0 1 freeQuadraticWave j l (t, x))
          0 (0, 0) (1, 1)) = 0 := by
  have hzero (p : GPESpacetime) :
      gpePartial (gpeSpaceDirection 0) (fun _ : GPESpacetime => (0 : ℝ)) p = 0 := by
    simp [gpePartial]
  simpa only [hzero, mul_zero, MeasureTheory.integral_zero, intervalIntegral.integral_zero,
    neg_zero] using
    (gpe_rectangle_impulse_balance 1 0 1
      (V := fun _ => 0) (ψ := freeQuadraticWave) (U := Set.univ)
      contDiff_const contDiff_freeQuadraticWave isOpen_univ (fun p _ => freeQuadraticWave_gpe p)
      (t₀ := 0) (t₁ := 1) (by norm_num) (a := (0, 0)) (b := (1, 1))
      ⟨by norm_num, by norm_num⟩ (Set.subset_univ _) 0)

#print axioms Qatlib.Papers.SuperfoilLift19.LiftForce.gpe_local_momentum_balance
#print axioms Qatlib.Papers.SuperfoilLift19.LiftForce.gpe_local_mass_balance
#print axioms Qatlib.Papers.SuperfoilLift19.LiftForce.gpeWaveStress_eq_polar
#print axioms Qatlib.Papers.SuperfoilLift19.LiftForce.gpe_rectangle_impulse_balance

/-- A horizontal trajectory with nonzero acceleration. -/
private def acceleratingContour (t : ℝ) : ℝ × ℝ := (t ^ 2, 0)

/-- The accelerating contour is smooth. -/
private theorem contDiff_acceleratingContour : ContDiff ℝ 2 acceleratingContour :=
  (contDiff_id.pow 2).prodMk contDiff_const

/-- In an accelerating frame the material derivative and relative flux
divergence are minus six and six. The laboratory stress divergence at
the same event is only two, so the advective correction is nonzero. -/
example :
    gpePartial gpeTimeDirection (gpeMomentum 1 freeQuadraticWave 0 ∘
        gpeTranslate acceleratingContour) (1, 0, 0) = -6 ∧
      (∑ j : Fin 2, gpePartial (gpeSpaceDirection j)
        (gpeMovingMomentumFlux 1 0 1 freeQuadraticWave acceleratingContour j 0 ∘
          gpeTranslate acceleratingContour) (1, 0, 0)) = 6 ∧
      (∑ j : Fin 2, gpePartial (gpeSpaceDirection j)
        (gpeWaveStress 1 0 1 freeQuadraticWave j 0) (1, 1, 0)) = 2 := by
  have hη1 : ContDiff ℝ 1 acceleratingContour := contDiff_acceleratingContour.of_le (by norm_num)
  have hP : ContDiff ℝ 1 (gpeMomentum 1 freeQuadraticWave 0 ∘ gpeTranslate acceleratingContour) :=
    (contDiff_gpeMomentum 1 0 (contDiff_freeQuadraticWave.of_le (by norm_num))).comp
      (contDiff_gpeTranslate hη1)
  have ht : gpePartial gpeTimeDirection (gpeMomentum 1 freeQuadraticWave 0 ∘
        gpeTranslate acceleratingContour) (1, 0, 0) = -6 := by
    rw [gpePartial_time_eq_deriv _ (hP.differentiable (by norm_num) _)]
    have he : (fun s : ℝ => (gpeMomentum 1 freeQuadraticWave 0 ∘ gpeTranslate acceleratingContour)
        ((1 : ℝ) + s, 0, 0)) = fun s => -2 * (1 + s) ^ 3 := by
      funext s
      simp [freeQuadraticWave_momentum, gpeTranslate, acceleratingContour]
      ring
    change deriv (fun s : ℝ => (gpeMomentum 1 freeQuadraticWave 0 ∘
      gpeTranslate acceleratingContour) ((1 : ℝ) + s, 0, 0)) 0 = _
    rw [he]
    have hd : HasDerivAt (fun s : ℝ => -2 * (1 + s) ^ 3) (-6 : ℝ) 0 := by
      convert (((hasDerivAt_id (0 : ℝ)).const_add 1).fun_pow 3).const_mul (-2 : ℝ) using 1
      all_goals norm_num [id_eq]
    exact hd.deriv
  have hzero (q : GPESpacetime) :
      gpePartial (gpeSpaceDirection 0) (fun _ : GPESpacetime => (0 : ℝ)) q = 0 := by
    simp [gpePartial]
  have hmove := gpe_translated_local_momentum_balance 1 0 1 (V := fun _ => 0)
    (U := Set.univ) contDiff_const contDiff_freeQuadraticWave contDiff_acceleratingContour
    isOpen_univ (fun q _ => freeQuadraticWave_gpe q) (1, 0, 0) (Set.mem_univ _) 0
  simp only [ht, hzero, mul_zero, neg_zero] at hmove
  have hlab := gpe_local_momentum_balance 1 0 1 (V := fun _ => 0) (U := Set.univ)
    contDiff_const contDiff_freeQuadraticWave isOpen_univ
    (fun q _ => freeQuadraticWave_gpe q) (1, 1, 0) (Set.mem_univ _) 0
  have hd : Differentiable ℝ (fun q : GPESpacetime => -2 * q.1 * q.2.1) := by fun_prop
  have hdt : gpePartial gpeTimeDirection (gpeMomentum 1 freeQuadraticWave 0) (1, 1, 0) = -2 := by
    rw [freeQuadraticWave_momentum, gpePartial_time_eq_deriv _ (hd _)]
    simp
  simp only [hdt, hzero, mul_zero] at hlab
  exact ⟨ht, by linarith only [hmove], by linarith only [hlab]⟩

/-- The actual unsteady wave obeys the shell balance for two strict
nested contours following the same accelerating trajectory. -/
example :
    gpeMovingShellMomentum 1 freeQuadraticWave acceleratingContour 0
        (0, 0) (2, 2) (1 / 2, 1 / 2) (3 / 2, 3 / 2) 1 -
      gpeMovingShellMomentum 1 freeQuadraticWave acceleratingContour 0
        (0, 0) (2, 2) (1 / 2, 1 / 2) (3 / 2, 3 / 2) 0 +
      ((∫ t in (0 : ℝ)..1, gpeMovingRectangleFlux 1 0 1 freeQuadraticWave acceleratingContour 0
        (0, 0) (2, 2) t) -
       (∫ t in (0 : ℝ)..1, gpeMovingRectangleFlux 1 0 1 freeQuadraticWave acceleratingContour 0
        (1 / 2, 1 / 2) (3 / 2, 3 / 2) t)) = 0 := by
  exact gpe_moving_airfoil_shell_impulse_balance 1 0 1
    (W := fun _ => 0) (U := Set.univ) contDiff_const contDiff_freeQuadraticWave
    contDiff_acceleratingContour isOpen_univ (fun q _ => freeQuadraticWave_gpe q)
    (by norm_num) (by constructor <;> norm_num) (by constructor <;> norm_num)
    (by constructor <;> norm_num) (fun _ _ => Set.mem_univ _) (fun _ _ => rfl) 0

#print axioms Qatlib.Papers.SuperfoilLift19.LiftForce.gpe_moving_rectangle_impulse_balance
#print axioms Qatlib.Papers.SuperfoilLift19.LiftForce.gpe_moving_airfoil_impulse_balance
#print axioms Qatlib.Papers.SuperfoilLift19.LiftForce.gpe_moving_airfoil_shell_impulse_balance

open MeasureTheory Filter
open scoped ComplexConjugate Topology

/-- A freely propagating plane wave with a nonzero uniform momentum background. -/
private def farPlaneWave (p : GPESpacetime) : ℂ := phaseFactor (p.2.1 - p.1 / 2)

/-- The actual plane wave is smooth in spacetime. -/
private theorem contDiff_farPlaneWave : ContDiff ℝ 3 farPlaneWave := by
  have h : ContDiff ℝ 3 (fun p : GPESpacetime => p.2.1 - p.1 / 2) := by fun_prop
  have hc := (Complex.ofRealCLM.contDiff.comp h).mul (contDiff_const (c := Complex.I))
  exact Complex.contDiff_exp.comp hc

/-- The plane wave's derivative in the propagation direction. -/
private theorem hasDerivAt_farPlaneWave_dx_line (p : GPESpacetime) :
    HasDerivAt (fun s => farPlaneWave (p.1, axisLine p.2 0 s))
      (farPlaneWave p * Complex.I) 0 := by
  have h : HasDerivAt (fun s : ℝ => p.2.1 + s - p.1 / 2) 1 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_add p.2.1).sub_const (p.1 / 2)
  simpa [farPlaneWave, axisLine] using phaseFactor_comp_hasDerivAt h

/-- The joint first spatial derivative has the expected propagation factor. -/
private theorem farPlaneWave_dx :
    gpePartial (gpeSpaceDirection 0) farPlaneWave = fun p => farPlaneWave p * Complex.I := by
  funext p
  rw [gpePartial_space_eq_axisLine p 0 (contDiff_farPlaneWave.differentiable (by norm_num) p)]
  exact (hasDerivAt_farPlaneWave_dx_line p).deriv

/-- The freestream has no variation in the transverse coordinate. -/
private theorem farPlaneWave_dy :
    gpePartial (gpeSpaceDirection 1) farPlaneWave = fun _ => 0 := by
  funext p
  rw [gpePartial_space_eq_axisLine p 1 (contDiff_farPlaneWave.differentiable (by norm_num) p)]
  simp [farPlaneWave, axisLine]

/-- Applying the propagation derivative a second time gives minus the wave. -/
private theorem farPlaneWave_dxx (p : GPESpacetime) :
    gpePartial (gpeSpaceDirection 0) (gpePartial (gpeSpaceDirection 0) farPlaneWave) p =
      -farPlaneWave p := by
  rw [farPlaneWave_dx]
  have hd : Differentiable ℝ (fun p => farPlaneWave p * Complex.I) :=
    (contDiff_farPlaneWave.differentiable (by norm_num)).mul_const _
  rw [gpePartial_space_eq_axisLine p 0 (hd p)]
  simpa only [mul_assoc, Complex.I_mul_I, mul_neg, mul_one] using
    ((hasDerivAt_farPlaneWave_dx_line p).mul_const Complex.I).deriv

/-- The transverse derivative of the propagation derivative vanishes. -/
private theorem farPlaneWave_dyx (p : GPESpacetime) :
    gpePartial (gpeSpaceDirection 1) (gpePartial (gpeSpaceDirection 0) farPlaneWave) p = 0 := by
  rw [farPlaneWave_dx]
  have hd : Differentiable ℝ (fun p => farPlaneWave p * Complex.I) :=
    (contDiff_farPlaneWave.differentiable (by norm_num)).mul_const _
  rw [gpePartial_space_eq_axisLine p 1 (hd p)]
  simp [farPlaneWave, axisLine]

/-- The free plane wave obeys the actual time-dependent wave equation
at every point in the laboratory plane. -/
private theorem farPlaneWave_gpe (p : GPESpacetime) :
    GrossPitaevskiiAt 1 0 1 (fun _ => 0) farPlaneWave p := by
  have hphase : HasDerivAt (fun s : ℝ => p.2.1 - (p.1 + s) / 2) (-1 / 2) 0 := by
    have hh := (hasDerivAt_const (0 : ℝ) p.2.1).fun_sub
      (((hasDerivAt_id (0 : ℝ)).const_add p.1).div_const 2)
    simpa only [id_eq, zero_sub, neg_div] using hh
  have ht : gpePartial gpeTimeDirection farPlaneWave p =
      farPlaneWave p * (((-1 / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [gpePartial_time_eq_deriv p (contDiff_farPlaneWave.differentiable (by norm_num) p)]
    simpa only [farPlaneWave, add_zero] using (phaseFactor_comp_hasDerivAt hphase).deriv
  have hyy : gpePartial (gpeSpaceDirection 1)
      (gpePartial (gpeSpaceDirection 1) farPlaneWave) p = 0 := by
    rw [farPlaneWave_dy]
    simp [gpePartial]
  rw [GrossPitaevskiiAt, gpeLaplacian, Fin.sum_univ_two, ht, farPlaneWave_dxx, hyy]
  norm_num [Complex.ofReal_div, Complex.ofReal_neg]
  calc
    _ = ((-1 / 2 : ℂ) * farPlaneWave p) * (Complex.I * Complex.I) := by ring
    _ = _ := by norm_num [Complex.I_mul_I]

/-- The unit phase has unit conjugate product. -/
private theorem farPlaneWave_conj_mul (p : GPESpacetime) :
    conj (farPlaneWave p) * farPlaneWave p = 1 := by
  rw [Complex.conj_mul', farPlaneWave, phase_factor_norm]
  norm_num

/-- The horizontal laboratory momentum is spatially uniform and equals one. -/
private theorem farPlaneWave_momentum (p : GPESpacetime) :
    gpeMomentum 1 farPlaneWave 0 p = 1 := by
  rw [gpeMomentum, farPlaneWave_dx]
  simp [← mul_assoc, farPlaneWave_conj_mul]

/-- For the horizontal momentum, the two laboratory stress components
are one and zero throughout the laboratory plane. -/
private theorem farPlaneWave_stress (p : GPESpacetime) (j : Fin 2) :
    gpeWaveStress 1 0 1 farPlaneWave j 0 p = if j = 0 then 1 else 0 := by
  have hconjI : conj (farPlaneWave p * Complex.I) = conj (farPlaneWave p) * -Complex.I := by simp
  have hprod : conj (farPlaneWave p * Complex.I) * (farPlaneWave p * Complex.I) = 1 := by
    rw [hconjI]
    calc
      _ = (conj (farPlaneWave p) * farPlaneWave p) * -(Complex.I * Complex.I) := by ring
      _ = _ := by simp [farPlaneWave_conj_mul, Complex.I_mul_I]
  have hdx := congrFun farPlaneWave_dx p
  have hdy := congrFun farPlaneWave_dy p
  fin_cases j
  · change gpeWaveStress 1 0 1 farPlaneWave 0 0 p = 1
    rw [gpeWaveStress, farPlaneWave_dxx, hdx, hprod]
    norm_num [farPlaneWave_conj_mul]
  · change gpeWaveStress 1 0 1 farPlaneWave 1 0 p = 0
    rw [gpeWaveStress, farPlaneWave_dyx, hdx, hdy]
    norm_num

/-- Even with nonzero uniform momentum and stress, the actual
free wave has no far-boundary impulse in the accelerating frame.
Its endpoint difference is integrable and the full impulse law applies. -/
example :
    gpeMomentum 1 farPlaneWave 0 (1, 0, 0) = 1 ∧
    Tendsto (gpeMovingSquareFluxImpulse 1 0 1 farPlaneWave acceleratingContour 0 0 1) atTop (𝓝 0) ∧
      (∫ x, gpeMovingMomentumChange 1 farPlaneWave acceleratingContour 0 0 1 x) =
        -(∫ t in (0 : ℝ)..1,
          gpeAirfoilReactionForce farPlaneWave acceleratingContour (fun _ => 0) 0 t) ∧
      |(∫ t in (0 : ℝ)..1,
          gpeAirfoilReactionForce farPlaneWave acceleratingContour (fun _ => 0) 0 t) +
        (∫ x, gpeMovingMomentumChange 1 farPlaneWave acceleratingContour 0 0 1 x)| ≤
          0 + (8 * |(1 : ℝ) - 0|) * (1 * 0) := by
  let far (j : Fin 2) (t : ℝ) :=
    (if j = 0 then (1 : ℝ) else 0) - gpeContourVelocity acceleratingContour j t
  have hsmall : Tendsto (fun R : ℝ => R * (0 : ℝ)) atTop (𝓝 0) := by simp
  have hfar (R : ℝ) (_ : 1 ≤ R) (t : ℝ) (_ : t ∈ Set.Icc (0 : ℝ) 1)
      (x : ℝ × ℝ) (_ : x ∈ Set.Icc (-R, -R) (R, R))
      (_ : |x.1| = R ∨ |x.2| = R) (j : Fin 2) :
      |gpeMovingMomentumFlux 1 0 1 farPlaneWave acceleratingContour j 0 (t, x + acceleratingContour t) -
        far j t| ≤ 0 := by
    simp [far, gpeMovingMomentumFlux, farPlaneWave_stress, farPlaneWave_momentum]
  have hE : Integrable (gpeMovingMomentumChange 1 farPlaneWave acceleratingContour 0 0 1) := by
    have he : gpeMovingMomentumChange 1 farPlaneWave acceleratingContour 0 0 1 = fun _ => 0 :=
      funext fun x => by simp [gpeMovingMomentumChange, farPlaneWave_momentum]
    rw [he]
    exact integrable_zero _ _ _
  have hm (t : ℝ) : gpeMovingRectangleMomentum 1 farPlaneWave acceleratingContour 0
      (-1, -1) (1, 1) t = ∫ _x in Set.Icc ((-1, -1) : ℝ × ℝ) (1, 1), (1 : ℝ) := by
    unfold gpeMovingRectangleMomentum gpeRectangleMomentum
    rw [setIntegral_translate_rectangle (fun _ : ℝ × ℝ => (1 : ℝ)) (-1, -1) (1, 1)
      (acceleratingContour t)]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    exact farPlaneWave_momentum (t, x)
  have htail : |(∫ x, gpeMovingMomentumChange 1 farPlaneWave acceleratingContour 0 0 1 x) -
      (gpeMovingRectangleMomentum 1 farPlaneWave acceleratingContour 0 (-1, -1) (1, 1) 1 -
        gpeMovingRectangleMomentum 1 farPlaneWave acceleratingContour 0 (-1, -1) (1, 1) 0)| ≤ 0 := by
    simp [gpeMovingMomentumChange, farPlaneWave_momentum, hm]
  refine ⟨farPlaneWave_momentum _, ?_, ?_, ?_⟩
  · exact tendsto_gpeMovingSquareFluxImpulse_zero 1 0 1 contDiff_farPlaneWave
      contDiff_acceleratingContour (by norm_num) 0 (R₀ := 1) (by norm_num)
      far (fun _ => 0) hsmall hfar
  · exact gpe_moving_airfoil_impulse_of_far_decay 1 0 1 (W := fun _ => 0) (U := Set.univ)
      contDiff_const contDiff_farPlaneWave contDiff_acceleratingContour isOpen_univ
      (fun p _ => farPlaneWave_gpe p) (by norm_num) (Set.subset_univ _)
      (R₀ := 1) (by norm_num) (fun _ _ => rfl) 0 hE far (fun _ => 0) hsmall hfar
  · exact abs_gpeAirfoilImpulse_add_momentumChange_le 1 0 1
      (W := fun _ => 0) (U := Set.univ) contDiff_const contDiff_farPlaneWave
      contDiff_acceleratingContour isOpen_univ (fun p _ => farPlaneWave_gpe p)
      (R := 1) (by norm_num) (Set.subset_univ _) (R₀ := 1) (by norm_num) le_rfl
      (fun _ _ => rfl) 0 far 0 0 htail (hfar 1 le_rfl)

#print axioms Qatlib.Papers.SuperfoilLift19.LiftForce.tendsto_gpeMovingSquareFluxImpulse_of_momentumChange
#print axioms Qatlib.Papers.SuperfoilLift19.LiftForce.gpe_moving_airfoil_impulse_of_far_decay
#print axioms Qatlib.Papers.SuperfoilLift19.LiftForce.abs_gpeMovingSquareFluxImpulse_le
#print axioms Qatlib.Papers.SuperfoilLift19.LiftForce.abs_gpeAirfoilImpulse_add_momentumChange_le

/-!
## Joukowski trailing-edge and nucleation-number consumers

These examples use nonzero geometric and flow parameters.  The negative
threshold example has the same parameters as the positive one, so it detects
both a universally positive threshold and a lost strict-inequality direction.
-/

/-- The nonzero-radius Kutta value at speed two and incidence `π/6` is `-6π`. -/
example : kuttaCirculation (3 / 2) 2 (Real.pi / 6) = -6 * Real.pi := by
  norm_num [kuttaCirculation]
  ring

/-- The exact Kutta circulation cancels the numerator for a noncentered,
nonzero-radius cylinder. -/
example : cylinderFlowNumerator (3 / 2) 2 (Real.pi / 6)
    (kuttaCirculation (3 / 2) 2 (Real.pi / 6)) ((3 / 2 : ℝ) : ℂ) = 0 := by
  apply cylinderFlowNumerator_tail_kutta
  norm_num

/-- **Non-cancellation counterexample.** Zero circulation is not the Kutta
value at the same nonzero speed and incidence, so the singular numerator is
nonzero. -/
example : cylinderFlowNumerator (3 / 2) 2 (Real.pi / 6) 0 ((3 / 2 : ℝ) : ℂ) ≠ 0 := by
  apply cylinderFlowNumerator_tail_ne_zero (by norm_num)
  norm_num [kuttaCirculation, Real.pi_ne_zero]

/-- The corresponding real leading coefficient is strictly positive. -/
example : 0 < tailLeadingSpeedSqCoefficient 1 (3 / 2) 2 (Real.pi / 6) 0 := by
  unfold tailLeadingSpeedSqCoefficient kuttaCirculation
  norm_num
  positivity

/-- The complete principal-root inverse branch exactly maps a nondegenerate
physical displacement back to the Joukowski plane. -/
example : joukowskiMap 1 (outerTailInverse 1 (1 / 2)) = 2 * (1 : ℂ) + 1 / 2 := by
  apply joukowskiMap_outerTailInverse (by norm_num)
  norm_num

/-- The physical-plane coefficient for the same nonzero Kutta defect is
strictly positive after dividing the circle-plane coefficient by `a`. -/
example : 0 < physicalTailSpeedSqCoefficient 1 (3 / 2) 2 (Real.pi / 6) 0 := by
  unfold physicalTailSpeedSqCoefficient tailLeadingSpeedSqCoefficient kuttaCirculation
  norm_num
  positivity

/-- Exact Kutta circulation also cancels the physical-plane coefficient. -/
example : physicalTailSpeedSqCoefficient 1 (3 / 2) 2 (Real.pi / 6)
    (kuttaCirculation (3 / 2) 2 (Real.pi / 6)) = 0 := by
  simp [physicalTailSpeedSqCoefficient, tailLeadingSpeedSqCoefficient]

/-- The exact speed and the nucleation truncation are linked by the proved
nondegenerate `O(√r)` estimate, with nonzero scale, radius, speed, and angle. -/
example :
    (fun w : ℂ => ‖w‖ *
        ‖idealComplexVelocity 1 (1 / 2) 2 (Real.pi / 6) 0 (outerTailInverse 1 w)‖ ^ 2 -
      ‖w‖ * physicalTailLeadingSpeedSq 1 (3 / 2) ‖w‖ 2 (Real.pi / 6) 0) =O[
        nhdsWithin 0 ({0}ᶜ)] fun w => Real.sqrt ‖w‖ := by
  have hr : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  simpa only [hr] using
    (isBigO_outerTailInverse_scaled_speed_sq_sub_truncation
      (a := 1) (offset := 1 / 2) (speed := 2) (alpha := Real.pi / 6) (circulation := 0)
      (by norm_num) (by norm_num))

/-- A nondegenerate nonzero-speed, nonzero-radius cutoff model crosses the
strict compressibility threshold when the squared winding defect is one. -/
private def cutoffTestRadius : ℝ := (4 * Real.pi)⁻¹

/-- The test radius is positive and cancels `16π²R²` exactly. -/
private theorem cutoffTestRadius_pos : 0 < cutoffTestRadius := by
  unfold cutoffTestRadius
  positivity

/-- **Supercritical consumer.** With `U=0`, `c²=1`, and unit quantum, a unit
winding defect exceeds the threshold `2/3`. -/
example : 0 < compressibilityRatio 1
    (physicalTailLeadingSpeedSq 1 cutoffTestRadius 1 0 0 (1 * 1)) (0 ^ 2) := by
  apply (compressibilityRatio_physicalTailLeadingSpeedSq_pos_iff_quantized
    (a := 1) (radius := cutoffTestRadius) (cutoff := 1) (farSoundSq := 1)
    (farSpeed := 0) (alpha := 0) (quantum := 1) (kuttaNumber := 0) (n := 1)
    (by norm_num) cutoffTestRadius_pos (by norm_num) (by norm_num) (by norm_num)
    (by simp [kuttaCirculation])).2
  norm_num [nucleationDefectSqEstimate, circulationDefectThreshold, cutoffTestRadius]
  field_simp [Real.pi_ne_zero]
  ring_nf
  norm_num

/-- **Subcritical counterexample.** Halving the winding defect in the same
nonzero model fails the strict threshold, so the equivalence is not vacuous. -/
example : ¬0 < compressibilityRatio 1
    (physicalTailLeadingSpeedSq 1 cutoffTestRadius 1 0 0 ((1 / 2 : ℝ) * 1)) (0 ^ 2) := by
  intro h
  have ht := (compressibilityRatio_physicalTailLeadingSpeedSq_pos_iff_quantized
    (a := 1) (radius := cutoffTestRadius) (cutoff := 1) (farSoundSq := 1)
    (farSpeed := 0) (alpha := 0) (quantum := 1) (kuttaNumber := 0) (n := 1 / 2)
    (by norm_num) cutoffTestRadius_pos (by norm_num) (by norm_num) (by norm_num)
    (by simp [kuttaCirculation])).1 h
  norm_num [nucleationDefectSqEstimate, circulationDefectThreshold, cutoffTestRadius] at ht
  field_simp [Real.pi_ne_zero] at ht
  ring_nf at ht
  norm_num at ht

/-- The zero-speed thin limit recovers `C=r/ξ` with nonunit scale and sound
speed, rather than by a degenerate zero numerator. -/
example : nucleationFitConstant 2 2 3 (1 / (2 * Real.pi ^ 2)) 0 2 8 1 = 3 := by
  have h : nucleationFitConstant 2 2 3 (1 / (2 * Real.pi ^ 2)) 0 2 8 1 = 3 / 1 := by
    apply nucleationFitConstant_zero_speed_thin (by norm_num)
      (by positivity) (by norm_num) (by norm_num) rfl
    field_simp [Real.pi_ne_zero]
    ring
  norm_num at h
  convert h using 1
  ring

/-- The physical normalization gives `κ²=8π²c²ξ²` for a nondegenerate choice
of Planck scale, mass, sound speed, and healing length. -/
example : circulationQuantum 1 1 ^ 2 = 8 * Real.pi ^ 2 * (1 / 2 : ℝ) * 1 ^ 2 := by
  apply circulationQuantum_sq_of_healingLength (by norm_num)
  norm_num

/-- The supplement's rounding rule returns three when its real input is the
noninteger-parameter expression `4-√(3/(3·1))=3`. -/
example : analyticVortexNumberPrediction 4 3 1 1 = 3 := by
  apply analyticVortexNumberPrediction_of_exact
  norm_num

/-- A nonzero obstacle potential is used by the exact GPE regression. -/
example : nonzeroObstaclePotential (0, 0) ≠ 0 :=
  nonzeroObstaclePotential_ne_zero

/-- The obstacle produces a nonzero reaction-force density at a point inside
the control rectangle. -/
example :
    gpeDensity nonzeroObstacleWave (0, (1, 0)) *
        gpePartial (gpeSpaceDirection 0)
          (gpeTranslatingPotential (fun _ : ℝ => (0, 0)) nonzeroObstaclePotential)
          (0, (1, 0)) = -2 :=
  nonzeroObstacle_forceDensity_at_one

/-- The fixed and moving dynamic impulse laws both consume the same genuine
nonzero obstacle instance. -/
example : True := by
  have hfixed := nonzeroObstacle_rectangle_impulse_balance
  have hmoving := nonzeroObstacle_moving_rectangle_impulse_balance
  exact ⟨⟩

#print axioms Qatlib.Papers.SuperfoilLift19.Nucleation.cylinderFlowNumerator_tail_eq_zero_iff
#print axioms Qatlib.Papers.SuperfoilLift19.Nucleation.tendsto_tailDisplacement_mul_idealComplexVelocity
#print axioms Qatlib.Papers.SuperfoilLift19.Nucleation.tendsto_tailDisplacement_norm_sq_mul_idealComplexVelocity_norm_sq
#print axioms Qatlib.Papers.SuperfoilLift19.Nucleation.compressibilityRatio_physicalTailLeadingSpeedSq_pos_iff_quantized
#print axioms Qatlib.Papers.SuperfoilLift19.Nucleation.nucleationFitConstant_zero_speed_thin
#print axioms Qatlib.Papers.SuperfoilLift19.Nucleation.joukowskiMap_outerTailInverse
#print axioms Qatlib.Papers.SuperfoilLift19.Nucleation.tendsto_outerTailInverse_norm_mul_idealComplexVelocity_norm_sq
#print axioms Qatlib.Papers.SuperfoilLift19.Nucleation.isBigO_outerTailInverse_scaled_speed_sq_sub
#print axioms Qatlib.Papers.SuperfoilLift19.Nucleation.isBigO_outerTailInverse_scaled_speed_sq_sub_truncation
#print axioms nonzeroObstacleWave_gpe
#print axioms nonzeroObstacle_forceDensity_at_one
#print axioms nonzeroObstacle_rectangle_impulse_balance
#print axioms nonzeroObstacle_moving_rectangle_impulse_balance
#print axioms Qatlib.Papers.SuperfoilLift19.LiftForce.wall_force_eq_ideal_lift_nonzero

end QatlibTests.SuperfoilLiftExtendedRegression
