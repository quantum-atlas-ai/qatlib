/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroverSearch96.MainResults.Counterexamples

/-!
# Inversion about the mean on a quantum register

The average projection is idempotent and the register diffusion matrix is unitary.
`source_inversion_about_mean` expresses its action on arbitrary complex amplitudes as twice the
mean minus the original amplitude.

`source_exact_amplitude_update` specializes an actual Grover step to a vector with one marked
amplitude and a common ordinary amplitude. See [Grover1997].

## Main statements

* `source_inversion_about_mean`: Diffusion replaces each complex amplitude by its negative plus
  twice the mean amplitude over the `2^n` register states.
* `source_exact_amplitude_update`: A singleton Grover step sends real amplitudes `a,b` to
  `distinguishedAfter (2^n) (-a) b` and `ordinaryAfter (2^n) (-a) b`.

## References

* [Grover, 1997][Grover1997]
-/

set_option warningAsError false

set_option autoImplicit false

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Papers.GroverSearch97.MainResults

/-- The average projection on `Reg n` is idempotent. See [Grover1997]. -/
theorem source_average_projection (n : ℕ) :
    AverageProjection (Reg n) * AverageProjection (Reg n) = AverageProjection (Reg n) :=
  averageProjection_mul_self Fintype.card_pos

/-- The register diffusion matrix belongs to the matrix unitary group. See [Grover1997]. -/
theorem source_diffusion_unitary (n : ℕ) :
    Diffusion (Reg n) ∈ Matrix.unitaryGroup (Reg n) ℂ :=
  diffusion_unitary Fintype.card_pos

/-- Diffusion replaces each complex amplitude by its negative plus twice the mean amplitude over
the `2^n` register states. See [Grover1997]. -/
theorem source_inversion_about_mean (n : ℕ) (ψ : QState (Reg n)) (i : Reg n) :
    ApplyGate (Diffusion (Reg n)) ψ i =
      -ψ i + 2 * ((∑ j, ψ j) / (2 ^ n : ℂ)) := by
  simpa only [card_reg, Nat.cast_pow, Nat.cast_ofNat] using applyGate_diffusion ψ i

/-- A singleton Grover step sends real amplitudes `a,b` to `distinguishedAfter (2^n) (-a) b` and
`ordinaryAfter (2^n) (-a) b`. See [Grover1997]. -/
theorem source_exact_amplitude_update (n : ℕ) (w : Reg n) (a b : ℝ) :
    Run (SetOracle {w}) (GroverStep (Reg n)) (MarkedVector {w} (a : ℂ) (b : ℂ)) =
      MarkedVector {w} (distinguishedAfter (2 ^ n) (-a) b : ℂ)
        (ordinaryAfter (2 ^ n) (-a) b : ℂ) :=
  Qatlib.Papers.GroverSearch96.MainResults.run_singleton_real_step n w a b

end Qatlib.Papers.GroverSearch97.MainResults
