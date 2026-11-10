/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.ResidueGcdBranchStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PopulationGap
set_option autoImplicit false
open Qatlib
open scoped Classical

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

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
