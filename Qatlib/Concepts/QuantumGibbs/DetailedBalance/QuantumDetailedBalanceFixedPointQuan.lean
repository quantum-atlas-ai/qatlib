/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalanceFixedPointStat
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuantumGibbs.DetailedBalance

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

theorem densSqrt_mul_self {D : ℕ} (sigma : Operator D) (hs : IsDensityOperator sigma) :
    densSqrt sigma * densSqrt sigma = sigma := by
  have hp : 0 ≤ sigma := Matrix.nonneg_iff_posSemidef.mpr hs.1
  unfold densSqrt
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt sigma hp]
  exact CFC.sqrt_mul_sqrt_self sigma hp

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
