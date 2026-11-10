/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.NoSignalCode.NoSignallingMessageCount
import Qatlib.Concepts.MixedFidelity.FidelityMetric.ChannelHelpers.FinitePOVMTraceDistance
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.QuditTeleport.NoSignalCode

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance

theorem povm_weight_nonneg {X : Type} [Fintype X] [DecidableEq X] {d : ℕ}
    (E : FinitePOVM X d) (A : Operator d) (hA : A.PosSemidef) (x : X) :
    0 ≤ (Matrix.trace (E.effect x * A)).re := by
  have h := (record_positive E hA).diag_nonneg (i := x)
  change 0 ≤ (Matrix.diagonal (fun o => Matrix.trace (E.effect o * A))) x x at h
  simp only [Matrix.diagonal_apply_eq] at h
  exact (Complex.nonneg_iff.mp h).1

theorem quantum_assemblage_message_count
    {X M : Type} [Fintype X] [DecidableEq X] [Fintype M] {d : ℕ}
    (x₀ : X) (τ : X → M → Operator d) (σ : Operator d)
    (E : M → FinitePOVM X d)
    (hτ : ∀ x m, (τ x m).PosSemidef)
    (hsum : ∀ x, ∑ m, τ x m = σ)
    (htrace : Matrix.trace σ = 1)
    (hexact : ∀ x, ∑ m, (Matrix.trace ((E m).effect x * τ x m)).re = 1) :
    Fintype.card X ≤ Fintype.card M := by
  classical
  let p : X → M → M → X → ℝ :=
    fun x s m y => (Matrix.trace ((E s).effect y * τ x m)).re
  apply no_signalling_exact_code_card_le x₀ p
  · exact fun x s m y => povm_weight_nonneg (E s) (τ x m) (hτ x m) y
  · intro s
    change ∑ m, ∑ y, (Matrix.trace ((E s).effect y * τ x₀ m)).re = 1
    have hcomplex : (∑ m, ∑ y, Matrix.trace ((E s).effect y * τ x₀ m)) = 1 := by
      calc
        _ = ∑ m, Matrix.trace ((∑ y, (E s).effect y) * τ x₀ m) := by
          simp_rw [Finset.sum_mul, Matrix.trace_sum]
        _ = Matrix.trace (∑ m, τ x₀ m) := by
          simp_rw [(E s).effect_sum, Matrix.one_mul, Matrix.trace_sum]
        _ = 1 := by rw [hsum, htrace]
    have h := congrArg Complex.re hcomplex
    simpa using h
  · intro x s y
    change (∑ m, (Matrix.trace ((E s).effect y * τ x m)).re) =
      ∑ m, (Matrix.trace ((E s).effect y * τ x₀ m)).re
    have hcomplex : (∑ m, Matrix.trace ((E s).effect y * τ x m)) =
        ∑ m, Matrix.trace ((E s).effect y * τ x₀ m) := by
      rw [← Matrix.trace_sum, ← Matrix.trace_sum, ← Matrix.mul_sum, ← Matrix.mul_sum,
        hsum, hsum]
    simpa using congrArg Complex.re hcomplex
  · exact hexact

end Qatlib.Concepts.QuditTeleport.NoSignalCode
