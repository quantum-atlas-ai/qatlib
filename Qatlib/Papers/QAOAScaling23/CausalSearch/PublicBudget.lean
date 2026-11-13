/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.CausalSearch.NativeOracle
import Qatlib.Papers.QAOAScaling23.SearchFees.ActualFees

/-!
# Public search schedule and budget constants

`publicSchedule` interleaves plain trials with a geometric search schedule determined by the
budget and size parameter, and `publicOracle` uses it for strict improvement. The numerical
lemmas verify a sufficient amplification cap and the confidence union bound.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `public_budget_cap`: If `0 < p ≤ Q`, `C,N ≥ 1`, and `B ≥ 15 * C * N / sqrt p`, then `B * sqrt
  Q ≥ 1`.
* `public_confidence_union`: For every natural `N`, the union expression `2^N * (25/32)^(8 * (N
  + 1))` is at most `1/6`.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.CausalSearch
open scoped Classical
open Qatlib.Concepts.WalkSearch.QuantumAccess
open SearchFees

/-- The interleaved geometric search schedule with cap `B` and repetition parameter `5 * B + 8 *
(N + 1)`. -/
def publicSchedule (B N : ℕ) : List ℕ :=
  interleavePlain (geometricSearchSchedule B (5*B+8*(N+1)))

/-- The native strict-improvement oracle using `publicSchedule B N`. -/
def publicOracle {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (B N : ℕ) (current : I) :=
  oracleCode U hU seed cost (publicSchedule B N) current

/-- If `0 < p ≤ Q`, `C,N ≥ 1`, and `B ≥ 15 * C * N / sqrt p`, then `B * sqrt Q ≥ 1`. See
[ShaydulinEtAl2024]. -/
theorem public_budget_cap (p Q C N : ℝ) (hp : 0<p) (hpQ : p≤Q)
    (hC : 1≤C) (hN : 1≤N) (B : ℕ)
    (hB : 15*C*N/Real.sqrt p≤(B:ℝ)) : 1≤(B:ℝ)*Real.sqrt Q := by
  have hs : 0<Real.sqrt p := Real.sqrt_pos.2 hp
  have hCN : 1≤C*N := by nlinarith
  have hb : 15*C*N≤(B:ℝ)*Real.sqrt p := (div_le_iff₀ hs).mp hB
  have hsq : Real.sqrt p≤Real.sqrt Q := Real.sqrt_le_sqrt hpQ
  have hmono := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg B : (0:ℝ)≤B)
  linarith

/-- For every natural `N`, the union expression `2^N * (25/32)^(8 * (N + 1))` is at most `1/6`. -/
theorem public_confidence_union (N : ℕ) :
    (2:ℝ)^N*(25/32:ℝ)^(8*(N+1))≤1/6 := by
  have hb : (25/32:ℝ)^8≤1/6 := by norm_num
  rw [pow_mul]
  have hp := pow_le_pow_left₀ (by positivity : 0≤(25/32:ℝ)^8) hb (N+1)
  calc
    (2:ℝ)^N*((25/32:ℝ)^8)^(N+1)≤(2:ℝ)^N*(1/6:ℝ)^(N+1) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _=(1/6:ℝ)*(1/3:ℝ)^N := by rw [pow_succ,show (1/3:ℝ)=2*(1/6) by norm_num,mul_pow]; ring
    _≤(1/6:ℝ)*1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (by norm_num : (0:ℝ)≤1/3) (by norm_num)) (by norm_num)
    _=1/6 := by ring
end Qatlib.Papers.QAOAScaling23.CausalSearch
