/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalanceFixedPointStat
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Stationarity from quantum detailed balance

This module proves that a density operator satisfying quantum detailed balance for a quantum
channel is a fixed point. The proof uses the square-root identity for density operators and does
not require invertibility, matching the stationarity implication in [TemmeEtAl2011].

## Main statements

* `densSqrt_mul_self`: Squaring the square root recovers a density operator.
* `quantumDetailedBalanceFixedPoint`: Detailed balance implies stationarity for quantum
  channels.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuantumGibbs.DetailedBalance

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

/-- The product of `densSqrt sigma` with itself is `sigma` whenever `sigma` is a density
operator. -/
theorem densSqrt_mul_self {D : ℕ} (sigma : Operator D) (hs : IsDensityOperator sigma) :
    densSqrt sigma * densSqrt sigma = sigma := by
  have hp : 0 ≤ sigma := Matrix.nonneg_iff_posSemidef.mpr hs.1
  unfold densSqrt
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt sigma hp]
  exact CFC.sqrt_mul_sqrt_self sigma hp

/-- Every density operator satisfying quantum detailed balance for a quantum channel is fixed by
that channel, including singular density operators. This proves the stationarity implication
of [Temme et al., Section 6][TemmeEtAl2011]. -/
theorem quantumDetailedBalanceFixedPoint : QuantumDetailedBalanceFixedPoint := by
  intro D T sigma hs hdb
  have hsq := densSqrt_mul_self sigma hs
  have he : (T.map sigma)ᴴ = sigma := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro phi
    have h := hdb 1 phi
    simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hsq] at h
    rw [T.tracePreserving] at h
    rw [Matrix.trace_mul_cycle, hsq] at h
    exact h.symm
  have h := congrArg Matrix.conjTranspose he
  simpa only [Matrix.conjTranspose_conjTranspose, hs.1.isHermitian.eq] using h

end Qatlib.Concepts.QuantumGibbs.DetailedBalance
