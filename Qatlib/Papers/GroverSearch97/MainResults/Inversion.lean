/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroverSearch96.MainResults.Counterexamples
set_option warningAsError false

set_option autoImplicit false

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Papers.GroverSearch97.MainResults

theorem source_average_projection (n : ℕ) :
    AverageProjection (Reg n) * AverageProjection (Reg n) = AverageProjection (Reg n) :=
  averageProjection_mul_self Fintype.card_pos

theorem source_diffusion_unitary (n : ℕ) :
    Diffusion (Reg n) ∈ Matrix.unitaryGroup (Reg n) ℂ :=
  diffusion_unitary Fintype.card_pos

theorem source_inversion_about_mean (n : ℕ) (ψ : QState (Reg n)) (i : Reg n) :
    ApplyGate (Diffusion (Reg n)) ψ i =
      -ψ i + 2 * ((∑ j, ψ j) / (2 ^ n : ℂ)) := by
  simpa only [card_reg, Nat.cast_pow, Nat.cast_ofNat] using applyGate_diffusion ψ i

theorem source_exact_amplitude_update (n : ℕ) (w : Reg n) (a b : ℝ) :
    Run (SetOracle {w}) (GroverStep (Reg n)) (MarkedVector {w} (a : ℂ) (b : ℂ)) =
      MarkedVector {w} (distinguishedAfter (2 ^ n) (-a) b : ℂ)
        (ordinaryAfter (2 ^ n) (-a) b : ℂ) :=
  Qatlib.Papers.GroverSearch96.MainResults.run_singleton_real_step n w a b

end Qatlib.Papers.GroverSearch97.MainResults
