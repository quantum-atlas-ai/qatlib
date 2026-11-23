/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Physical momentum coordinates and propagation phase

In arXiv:1205.3782v2 Eq. (45)-(47), p1 is total momentum and p2 is relative momentum.
The individual momenta are -p1/2-p2 and -p1/2+p2. Their actual free hopping energy is therefore
4 cos(p1/2) cos(p2). This file derives that coordinate bridge and the exact unit-modulus time
phase; neither a scattering eigenvector field nor a zero-sum generalized state is used.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UniversalWalk12.MainResults.Model

/-- The free energy in the center-of-mass and relative momentum coordinates of Eq. (45). -/
def physicalEnergy (p1 p2 : ℝ) : ℝ := 4 * Real.cos (p1 / 2) * Real.cos p2

/-- The physical two-particle energy equals the sum of the two individual unit-hopping energies. -/
theorem energy_individual (p1 p2 : ℝ) :
    physicalEnergy p1 p2 = 2 * Real.cos (-p1 / 2 - p2) + 2 * Real.cos (-p1 / 2 + p2) := by
  unfold physicalEnergy
  rw [Real.cos_sub, Real.cos_add]
  have hneg : -p1 / 2 = -(p1 / 2) := by ring
  rw [hneg, Real.cos_neg, Real.sin_neg]
  ring

/-- Exact propagation by the physical two-particle free energy. -/
def physicalPhase (t p1 p2 : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (t : ℂ) * ((physicalEnergy p1 p2 : ℝ) : ℂ))

/-- Propagation starts at the identity phase. -/
theorem phase_zero (p1 p2 : ℝ) : physicalPhase 0 p1 p2 = 1 := by
  simp [physicalPhase]

/-- Successive physical propagation times compose exactly. -/
theorem phase_add (s t p1 p2 : ℝ) :
    physicalPhase (s + t) p1 p2 = physicalPhase s p1 p2 * physicalPhase t p1 p2 := by
  unfold physicalPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The physical time phase preserves the norm of every spectral amplitude. -/
theorem phase_norm (t p1 p2 : ℝ) : ‖physicalPhase t p1 p2‖ = 1 := by
  simp [physicalPhase, Complex.norm_exp]

/-- Reversing physical time inverts its propagation phase. -/
theorem phase_inverse (t p1 p2 : ℝ) :
    physicalPhase (-t) p1 p2 * physicalPhase t p1 p2 = 1 := by
  rw [← phase_add, neg_add_cancel, phase_zero]

/-- The exact window phase is Eq. (47), with the entire total momentum divided by two. -/
theorem phase_window (t φ1 φ2 : ℝ) :
    physicalPhase t (Real.pi / 4 + φ1) (3 * Real.pi / 8 + φ2) =
      Complex.exp (-(4 : ℂ) * Complex.I * (t : ℂ) *
        ((Real.cos ((Real.pi / 4 + φ1) / 2) : ℝ) : ℂ) *
        ((Real.cos (3 * Real.pi / 8 + φ2) : ℝ) : ℂ)) := by
  unfold physicalPhase physicalEnergy
  congr 1
  push_cast
  ring

end Qatlib.Papers.UniversalWalk12.MainResults.Model
