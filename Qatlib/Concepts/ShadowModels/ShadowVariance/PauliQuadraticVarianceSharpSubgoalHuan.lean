/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowVariance.PauliQuadraticVarianceSharpSubgoalStat
import Qatlib.Concepts.ShadowModels.ShadowVariance.PauliPairSharpVariance

/-!
# Proof of the sharp quadratic Pauli variance bounds

This module proves `PauliQuadraticVarianceSharpSubgoal` using the support-sensitive Pauli pair
variance bounds. It also handles the zero-qubit case by showing that both variances vanish,
completing the variance input to quadratic shadow estimates [HuangKuengPreskill2020].

## Main statements

* `pauliQuadraticVarianceSharp_zero_qubits`: both pair variances vanish on zero qubits.
* `pauliQuadraticVarianceSharpSubgoal`: the full sharp variance statement.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.UStatBackend

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.ShadowModels.ShadowVariance
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false

/-- For a zero-qubit density operator, the conditional and kernel variances of every Pauli pair
shadow kernel are zero. -/
theorem pauliQuadraticVarianceSharp_zero_qubits (q : ℕ) (ww : Fin q → pauliPairWord 0)
    (c : Fin q → ℚ) (ρ : Operator (2^0)) (hρ : IsDensityOperator ρ) :
    let p := tensorPauliLaw 0 ρ hρ
    let h := quadraticShadowKernel 0 (pauliPairObservable 0 q ww c)
    pairConditionalVariance p h = 0 ∧ pairKernelVariance p h = 0 := by
  (try dsimp only)
  have hk (a b : Fin 0 → Fin 3 × Bool) :
      quadraticShadowKernel 0 (pauliPairObservable 0 q ww c) a b = ∑ j, (c j : ℝ) := by
    rw [pauli_pair_kernel_formula]
    simp only [tensorPauliValue, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
      ]
    rw [← Finset.sum_mul]
    ring
  have hμ : pairKernelMean (tensorPauliLaw 0 ρ hρ)
      (quadraticShadowKernel 0 (pauliPairObservable 0 q ww c)) = ∑ j, (c j : ℝ) := by
    simp only [pairKernelMean, hk, mul_assoc, ← Finset.mul_sum,
      ← Finset.sum_mul, FinDist.sum_one, one_mul]
  constructor
  · simp only [pairConditionalVariance, hk, ← Finset.sum_mul, FinDist.sum_one,
      one_mul, hμ, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]
  · simp only [pairKernelVariance, hk, hμ, sub_self, zero_pow (by decide : 2 ≠ 0),
      mul_zero, Finset.sum_const_zero]

/-- The sharp quadratic Pauli variance proposition holds for all supported rational Pauli pair
observables satisfying the norm lower bound. -/
theorem pauliQuadraticVarianceSharpSubgoal : PauliQuadraticVarianceSharpSubgoal := by
  intro n q ww c S₁ S₂ ρ hρ hs hn
  exact pauli_pair_sharp_variances n q ww c S₁ S₂ ρ hρ hs hn

end Qatlib.Concepts.ShadowModels.ShadowVariance
