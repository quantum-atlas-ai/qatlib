/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ManyBodySim96.MainResults.KineticLedger

@[expose] public section

/-!
# Signed Fourier labels for a kinetic layer

Use centered integer labels for the discrete momentum modes of the position grid. The
squared label supplies the energy consumed by the exact Fourier kinetic evolution.
This choice fixes a labeling convention and absorbs the spacing into momentum units.
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Papers.ManyBodySim96.MainResults

namespace Qatlib.Papers.ManyBodySim96.MainResults

/-- Center the Fourier index in the interval from minus half the grid size to its positive
endpoint, wrapping the upper half of the original labels. -/
def signedMomentum (k : ℕ) (p : Fin (2 ^ k)) : ℤ :=
  if p.val < 2 ^ (k - 1) then (p.val : ℤ) else (p.val : ℤ) - (2 : ℤ) ^ k

/-- On a grid with at least two sites, the centered labels lie in the half-open signed range. -/
theorem signedMomentum_range {k : ℕ} (hk : 0 < k) (p : Fin (2 ^ k)) :
    -(2 : ℤ) ^ (k - 1) ≤ signedMomentum k p ∧ signedMomentum k p < (2 : ℤ) ^ (k - 1) := by
  have hscale : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
    calc
      _ = (2 : ℤ) ^ ((k - 1) + 1) := congrArg (fun j : ℕ => (2 : ℤ) ^ j) (by omega)
      _ = _ := by rw [pow_succ, mul_comm]
  have hp : (p.val : ℤ) < (2 : ℤ) ^ k := by exact_mod_cast p.isLt
  have hh : 0 < (2 : ℤ) ^ (k - 1) := by positivity
  unfold signedMomentum
  split
  · rename_i h
    have h' : (p.val : ℤ) < (2 : ℤ) ^ (k - 1) := by exact_mod_cast h
    omega
  · rename_i h
    have h' : (2 : ℤ) ^ (k - 1) ≤ (p.val : ℤ) := by exact_mod_cast Nat.le_of_not_gt h
    omega

/-- Discrete kinetic dispersion in units in which the signed mode is the momentum label. -/
noncomputable def signedKineticEnergy (k : ℕ) (mass : ℝ) (p : Fin (2 ^ k)) : ℝ :=
  (signedMomentum k p : ℝ) ^ 2 / (2 * mass)

/-- The Fourier layer for the signed dispersion is exact kinetic evolution and unitary. -/
theorem kinetic_actual_qft_signed (k : ℕ) (mass dt : ℝ) :
    HamiltonianEvolution (kineticHamiltonian (QFTMatrix (2 ^ k)) (signedKineticEnergy k mass)) dt =
        kineticLayer (QFTMatrix (2 ^ k)) (signedKineticEnergy k mass) dt ∧
      kineticLayer (QFTMatrix (2 ^ k)) (signedKineticEnergy k mass) dt ∈
        Matrix.unitaryGroup (Fin (2 ^ k)) ℂ :=
  kinetic_actual_qft k (signedKineticEnergy k mass) dt

end Qatlib.Papers.ManyBodySim96.MainResults
