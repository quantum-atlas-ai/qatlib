/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.UniversalWalk12.MainResults.Fourier.Character
public import Qatlib.Papers.UniversalWalk12.MainResults.Model.Evolution

@[expose] public section

/-!
# Concrete finite-packet propagation endpoints

The source's graph-scattering asymptotics remain open here. We do prove two exact
properties of the nonzero finite two-particle packet already represented by the
Fourier kernel: its time-zero coefficient endpoint and conservation of its normalized
spectral mass under the actual free propagation phase.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.UniversalWalk12.MainResults.Fourier

open Qatlib.Papers.UniversalWalk12.MainResults.Model
open Qatlib.Papers.UniversalWalk12.MainResults.Model

/-- The actual freely propagated finite packet in spectral coordinates. -/
def evolvedKernel (M L : ℕ) (t p1 p2 : ℝ) : ℂ :=
  physicalPhase t p1 p2 * AmpA M L p1 p2

/-- At time zero, the propagated packet has exactly its finite position support. -/
theorem evolvedKernel_zero_endpoint (M L : ℕ) (u v : ℤ) :
    average₂ (fun p1 p2 =>
      evolvedKernel M L 0 p1 p2 * star (latticeChar u v p1 p2)) =
      if (u, v) ∈ packetSupport M L then ((1 / (L : ℝ) : ℝ) : ℂ) else 0 := by
  simpa only [evolvedKernel, phase_zero, one_mul] using kernel_inversion M L u v

/-- Free propagation preserves the exact normalized spectral mass for every positive packet. -/
theorem evolvedKernel_energy (M L : ℕ) (hL : 0 < L) (t : ℝ) :
    average₂ (fun p1 p2 =>
      ((‖evolvedKernel M L t p1 p2‖ ^ 2 : ℝ) : ℂ)) = 1 := by
  have hpoint (p1 p2 : ℝ) :
      ((‖evolvedKernel M L t p1 p2‖ ^ 2 : ℝ) : ℂ) =
        ((‖AmpA M L p1 p2‖ ^ 2 : ℝ) : ℂ) := by
    simp [evolvedKernel, physicalPhase, Complex.norm_exp]
  simp_rw [hpoint]
  exact kernel_parseval M L hL

end Qatlib.Papers.UniversalWalk12.MainResults.Fourier
