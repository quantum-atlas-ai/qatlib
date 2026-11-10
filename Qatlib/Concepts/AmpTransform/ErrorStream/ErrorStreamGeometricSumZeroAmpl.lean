/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.ErrorStreamGeometricSumZeroStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.AmpTransform.NoiseEnvelope

set_option autoImplicit false
open scoped Classical BigOperators

namespace Qatlib.Concepts.AmpTransform.ErrorStream

theorem errorStreamGeometricSumZero : ErrorStreamGeometricSumZero := by
  intro N y hN hy
  have hndvd : ¬ (N : ℤ) ∣ -(y : ℤ) := by
    simpa only [dvd_neg, Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero] using hy
  have hphase (z : ℕ) : aqPhase N z y = primRoot N ^ (-(y : ℤ) * (z : ℤ)) := by
    rw [primRoot_zpow_eq_exp]
    unfold aqPhase
    congr 1
    push_cast
    ring
  simp_rw [hphase]
  rw [← Fin.sum_univ_eq_sum_range (fun z : ℕ => primRoot N ^ (-(y : ℤ) * (z : ℤ))) N]
  exact sum_primRoot_zpow hN hndvd

end Qatlib.Concepts.AmpTransform.ErrorStream
