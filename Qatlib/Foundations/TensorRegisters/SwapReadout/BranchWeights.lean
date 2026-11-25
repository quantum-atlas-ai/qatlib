/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.TensorRegisters.SwapReadout
public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Computational-basis readout of the SWAP-test ancilla

Unitary preservation of squared norm gives the total weight of the two ancilla branches.
For normalized input factors the total is one, and the existing interference identity
gives the difference as the squared Hermitian overlap. The two equations determine the
individual probabilities.
-/

set_option autoImplicit false

open Matrix
open scoped BigOperators
open Qatlib.Foundations.TensorRegisters.SwapReadout
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.TensorRegisters.SwapReadout

/-- For two normalized complex states, the Hadamard–controlled-SWAP–Hadamard circuit
returns zero with the symmetric weight and one with the antisymmetric weight. -/
theorem normalized_outcome_weights {I : Type*} [Fintype I] [DecidableEq I]
    (u v : I → ℂ) (hu : ∑ i, Complex.normSq (u i) = 1)
    (hv : ∑ i, Complex.normSq (v i) = 1) :
    outcomeWeight u v false = (1 + Complex.normSq (star u ⬝ᵥ v)) / 2 ∧
    outcomeWeight u v true = (1 - Complex.normSq (star u ⬝ᵥ v)) / 2 := by
  have htotal := sum_normSq_mulVec_of_mem_unitaryGroup circuit_unitary (input u v)
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, input] at htotal
  simp only [Bool.false_eq_true, ↓reduceIte, Complex.normSq_zero, Finset.sum_const_zero,
    zero_add, map_mul] at htotal
  change outcomeWeight u v true + outcomeWeight u v false =
    ∑ i, ∑ j, Complex.normSq (u i) * Complex.normSq (v j) at htotal
  rw [← Fintype.sum_mul_sum, hu, hv, one_mul] at htotal
  have hoverlap := actual_born_overlap u v
  constructor <;> linarith

end Qatlib.Foundations.TensorRegisters.SwapReadout
