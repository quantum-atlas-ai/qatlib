/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GroverArbAmp98.MainResults.TwoMeasurements
public import Qatlib.Concepts.SearchStopping.RestartLaw.Section3RestartExpectedSubgoal

@[expose] public section

/-!
# Readout and restart bounds for arbitrary initial amplitudes

Transfers the two-time profile estimate in [BihamEtAl1999] to the actual iterate
at integer times satisfying the stated spacing. Also evaluates the expected
number of independent attempts when each attempt succeeds with probability
`Pmax`.
-/

set_option autoImplicit false

open Qatlib.Papers.GroverArbAmp98.MainResults
open Qatlib.Papers.GroverArbAmp98.MainResults.TwoMeasurements
open Qatlib.Concepts.SearchStopping.RestartLaw

namespace Qatlib.Papers.GroverArbAmp98.MainResults

/-- At two integer iteration counts with the required half-period spacing,
one actual marked probability is at least half the continuous profile maximum. -/
theorem two_iterates_success_lower_bound {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m)
    (x0 : Dynamics.Amps r m) (T1 T2 : ℕ) (hω : Dynamics.omega r m ≠ 0)
    (hgap : (T2 : ℝ) = (T1 : ℝ) + Real.pi / (2 * Dynamics.omega r m)) :
    Dynamics.Pmax x0 / 2 ≤
      max (Dynamics.probMarked (Dynamics.orbit x0 T1))
        (Dynamics.probMarked (Dynamics.orbit x0 T2)) := by
  rw [probMarked_eq_phase r m hr hm x0 T1, probMarked_eq_phase r m hr hm x0 T2, hgap]
  exact source_two_measurement_dynamics r m x0 (Dynamics.omega r m) (T1 : ℝ) hω

/-- If independent attempts each succeed with probability `Pmax x0`, the
geometric model has expected attempt count `1 / Pmax x0`. -/
theorem expected_attempts_at_pmax {r m : ℕ} (x0 : Dynamics.Amps r m)
    (hpos : 0 < Dynamics.Pmax x0) (hprob : Dynamics.Pmax x0 ≤ 1) :
    (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * ((1 - Dynamics.Pmax x0) ^ k * Dynamics.Pmax x0)) =
      1 / Dynamics.Pmax x0 := by
  simpa only [mul_one] using geometric_restart_expectation (Dynamics.Pmax x0) 1 hpos hprob

end Qatlib.Papers.GroverArbAmp98.MainResults
