/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.ResidueGcdBranchStat

/-!
# Residue factor soundness and bit-width bounds

Proves soundness of the classical residue factor routine and the power-of-two window for the
chosen residue bit width. These auxiliary results support fair-bit residue sampling and
factoring attempts in the framework associated with [Shor1997].

## Main statements

* `residue_classical_factor_sound`: Proves soundness of a returned classical factor.
* `residue_bit_width_window`: Bounds the chosen sampler capacity between `N` and `2 * N`.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PopulationGap
set_option autoImplicit false
open Qatlib
open scoped Classical

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

/-- If the classical residue factor routine returns `d`, then `1 < d < N` and `d` divides `N`. -/
theorem residue_classical_factor_sound (N : ℕ) [NeZero N] (y : ZMod N) (d : ℕ)
    (hd : residueClassicalFactor N y = some d) : 1 < d ∧ d < N ∧ d ∣ N := by
  unfold residueClassicalFactor at hd
  split at hd
  · rename_i h
    cases hd
    exact ⟨h.1, h.2, Nat.gcd_dvd_right _ _⟩
  · cases hd
end Qatlib.Concepts.PeriodSampling.FactorAlgorithm

set_option autoImplicit false
open Qatlib
open scoped Classical
namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm.Shor1997

/-- For positive `N`, the chosen residue bit width satisfies `N ≤ 2 ^ shorResidueBits N < 2 *
N`. -/
theorem residue_bit_width_window (N : ℕ) (hN : 0 < N) :
    N ≤ 2^shorResidueBits N ∧ 2^shorResidueBits N < 2*N := by
  have hlo := Nat.pow_log_le_self 2 hN.ne'
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) N
  rw [← Nat.log2_eq_log_two] at hlo hhi
  unfold shorResidueBits
  by_cases h : 2^Nat.log2 N < N
  · rw [if_pos h]
    constructor
    · exact hhi.le
    · rw [pow_succ]
      omega
  · rw [if_neg h, Nat.add_zero]
    constructor
    · omega
    · omega
end Qatlib.Concepts.PeriodSampling.FactorAlgorithm.Shor1997
