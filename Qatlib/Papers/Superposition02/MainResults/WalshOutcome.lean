/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ExactSimon97.MainResults.FourierCoset
import Qatlib.Concepts.WalshMoment.Forrelation.BooleanHadamardPhase
import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Walsh outcome weights of a square-root encoding

Computes the single-outcome weight in [GroverRudolph2002], Equation (8).
-/

set_option autoImplicit false

open Qatlib.Papers.ExactSimon97.MainResults

namespace Qatlib.Papers.Superposition02.MainResults

/-- The character of a binary dot product is the corresponding real sign, cast to
`ℂ`. -/
private theorem binary_character_real_sign (z : ZMod 2) :
    ZMod.stdAddChar z = ((if z = 0 then 1 else -1 : ℝ) : ℂ) := by
  fin_cases z
  · change ZMod.stdAddChar (0 : ZMod 2) = ((if (0 : ZMod 2) = 0 then 1 else -1 : ℝ) : ℂ)
    simp
  · change ZMod.stdAddChar (1 : ZMod 2) = ((if (1 : ZMod 2) = 0 then 1 else -1 : ℝ) : ℂ)
    simp [Qatlib.Concepts.WalshMoment.Forrelation.zmod2_stdAddChar_one]

/-- The squared amplitude at `j` after a Walsh transform is the squared real signed sum
divided by the binary register size. For a probability distribution `p` this is its
transformed Born probability as in [GroverRudolph2002]. -/
theorem walsh_sqrt_mass_born {n : ℕ} (p : BoolVec n → ℝ) (j : BoolVec n) :
    ‖walshHadamard (fun i => (Real.sqrt (p i) : ℂ)) j‖ ^ 2 =
      (1 / (2 : ℝ) ^ n) * (∑ i, (if dot j i = 0 then (1 : ℝ) else -1) * Real.sqrt (p i)) ^ 2 := by
  have amplitude : walshHadamard (fun i => (Real.sqrt (p i) : ℂ)) j =
      (((Real.sqrt ((2 : ℝ) ^ n))⁻¹ *
        ∑ i, (if dot j i = 0 then (1 : ℝ) else -1) * Real.sqrt (p i) : ℝ) : ℂ) := by
    simp only [walshHadamard, ambientNorm, charFun_apply, binary_character_real_sign,
      Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sum]
  rw [amplitude, Complex.sq_norm, Complex.normSq_ofReal, ← pow_two, mul_pow, inv_pow,
    Real.sq_sqrt (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n), one_div]

end Qatlib.Papers.Superposition02.MainResults
