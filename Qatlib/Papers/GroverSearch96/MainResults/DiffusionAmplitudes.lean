/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Theorem2Afas
import Qatlib.Concepts.SearchStopping.KnownCount.Corollary21CorrectedAfas
import Qatlib.Concepts.SearchStopping.KnownCount.Corollary22Afas
import Qatlib.Concepts.SearchStopping.KnownCount.Corollary22RealRestrictedAfas

/-!
# Diffusion updates for marked register amplitudes

This module computes the diffusion operator on register vectors with one distinguished amplitude
and a common ordinary amplitude, over both the real and complex numbers. The corrected
positivity statement requires at least three qubits.

The algebraic square identity `corollary2_2_markedRegister_complex` is complemented by
`diffusion_preserves_probability`, which states preservation of the total Born probability for
arbitrary complex states. See [Grover1996].

## Main statements

* `theorem2_complex_register`: Diffusion on a register vector with complex marked and ordinary
  amplitudes is given by `distinguishedAfterC` and `ordinaryAfterC`.
* `corollary2_1_markedRegister`: For `n ≥ 3`, diffusion makes both amplitudes positive if `k < 0
  < l` and `|k/l| < sqrt (2^n)`.
* `diffusion_preserves_probability`: Applying diffusion preserves the sum of Born probabilities
  of an arbitrary register state.

## References

* [Grover, 1996][Grover1996]
-/

set_option autoImplicit false

namespace Qatlib.Papers.GroverSearch96.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SearchStopping.KnownCount

/-- Diffusion on a register vector with real marked and ordinary amplitudes is given by
`distinguishedAfter` and `ordinaryAfter`. See [Grover1996]. -/
theorem theorem2_markedRegister (n : ℕ) (w : Reg n) (k l : ℝ) :
    ApplyGate (Diffusion (Reg n)) (MarkedVector {w} (k : ℂ) (l : ℂ)) =
      MarkedVector {w} (distinguishedAfter (2 ^ n) k l : ℂ)
        (ordinaryAfter (2 ^ n) k l : ℂ) := by
  simpa [card_reg] using diffusion_singleton_amplitudes (I := Reg n) w k l

/-- Diffusion on a register vector with complex marked and ordinary amplitudes is given by
`distinguishedAfterC` and `ordinaryAfterC`. See [Grover1996]. -/
theorem theorem2_complex_register (n : ℕ) (w : Reg n) (k l : ℂ) :
    ApplyGate (Diffusion (Reg n)) (MarkedVector {w} k l) =
      MarkedVector {w} (distinguishedAfterC (2^n) k l) (ordinaryAfterC (2^n) k l) := by
  simpa only [card_reg] using theorem2 (Reg n) w k l

/-- For `n ≥ 3`, diffusion makes both amplitudes positive if `k < 0 < l` and `|k/l| < sqrt
(2^n)`. See [Grover1996]. -/
theorem corollary2_1_markedRegister (n : ℕ) (hn : 3 ≤ n) (k l : ℝ)
    (hk : k < 0) (hl : 0 < l) (hratio : |k / l| < Real.sqrt (2 ^ n : ℝ)) :
    0 < distinguishedAfter (2 ^ n) k l ∧ 0 < ordinaryAfter (2 ^ n) k l := by
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hratio' : |k / l| < Real.sqrt ((2 ^ n : ℕ) : ℝ) := by
    simpa [Nat.cast_pow] using hratio
  exact corollary2_1Corrected (2 ^ n) h8 k l hk hl hratio'

/-- The real diffusion amplitude update preserves `twoAmplitudeMass` on `2^n` states. See
[Grover1996]. -/
theorem corollary2_2_markedRegister (n : ℕ) (k l : ℝ) :
    twoAmplitudeMass (2 ^ n) (distinguishedAfter (2 ^ n) k l)
        (ordinaryAfter (2 ^ n) k l) = twoAmplitudeMass (2 ^ n) k l :=
  corollary2_2 (2 ^ n) (pow_pos (by norm_num) n) k l

/-- The complex diffusion amplitude update preserves the weighted sum of algebraic squares `k^2
+ (2^n - 1) * l^2`. See [Grover1996]. -/
theorem corollary2_2_markedRegister_complex (n : ℕ) (k l : ℂ) :
    (distinguishedAfterC (2 ^ n) k l) ^ 2 +
        (((2 : ℂ) ^ n) - 1) * (ordinaryAfterC (2 ^ n) k l) ^ 2 =
      k ^ 2 + (((2 : ℂ) ^ n) - 1) * l ^ 2 := by
  have h := corollary2_2_complex (2 ^ n) (pow_pos (by norm_num) n) k l
  simpa [Nat.cast_pow] using h

/-- Applying diffusion preserves the sum of Born probabilities of an arbitrary register state.
See [Grover1996]. -/
theorem diffusion_preserves_probability (n : ℕ) (ψ : QState (Reg n)) :
    (∑ i, BornProb (ApplyGate (Diffusion (Reg n)) ψ) i) =
      ∑ i, BornProb ψ i :=
  diffusion_preserves_bornMass (I := Reg n) Fintype.card_pos ψ

end Qatlib.Papers.GroverSearch96.MainResults
