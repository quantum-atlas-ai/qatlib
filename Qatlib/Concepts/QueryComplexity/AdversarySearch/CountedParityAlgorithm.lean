/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
import Qatlib.Foundations.BornMetrics.EventProbability
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial

/-!
# Counted parity query algorithm

This module constructs `countedParityCircuit`, which records the XOR of each adjacent pair using
one query and handles an unpaired final bit separately. For positive input length, the circuit
computes parity exactly with ⌈N/2⌉ queries and at most 12N + 12 gates, and the polynomial lower
bound proves optimality even for error at most 1/3, as in [BealsEtAl2001].

## Main statements

* `countedParity_measureProb`: the circuit accepts exactly the inputs of odd Hamming weight.
* `parity_query_complexity_tight`: the explicit parity circuit attains the bounded error query
  lower bound.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.BornMetrics.EventProbability

namespace Qatlib.Concepts.QueryComplexity.AdversarySearch

open Matrix

set_option autoImplicit false

section Helpers

variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

/-- Applying a gate commutes with scalar multiplication of a state. -/
theorem parity_applyGate_smul (U : Matrix I I ℂ) (c : ℂ) (ψ : QState I) :
    ApplyGate U (c • ψ) = c • ApplyGate U ψ := by
  unfold ApplyGate
  rw [Matrix.mulVec_smul]

omit [Fintype I] [DecidableEq I] in

/-- Scaling the left factor of a tensor state scales the tensor state by the same complex
scalar. -/
theorem parity_tensorState_smul_left {J : Type} [Fintype J] [DecidableEq J] (c : ℂ)
    (ψ : QState I) (φ : QState J) : TensorState (c • ψ) φ = c • TensorState ψ φ := by
  funext p
  simp only [TensorState, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype I] [DecidableEq I] in

/-- Scaling the right factor of a tensor state scales the tensor state by the same complex
scalar. -/
theorem parity_tensorState_smul_right {J : Type} [Fintype J] [DecidableEq J] (c : ℂ)
    (ψ : QState I) (φ : QState J) : TensorState ψ (c • φ) = c • TensorState ψ φ := by
  funext p
  simp only [TensorState, Pi.smul_apply, smul_eq_mul]
  ring

/-- The Boolean phase, equal to −1 for `true` and 1 for `false`. -/
def phaseOf (b : Bool) : ℂ := if b then (-1 : ℂ) else 1

/-- Every Boolean phase has complex norm one. -/
@[simp] theorem phaseOf_norm (b : Bool) : ‖phaseOf b‖ = 1 := by
  cases b <;> simp [phaseOf]

/-- The phase oracle multiplies the basis state at `x` by `phaseOf (f x)`. -/
theorem applyGate_phaseOracle_ket (f : I → Bool) (x : I) :
    ApplyGate (PhaseOracle f) (Ket x) = phaseOf (f x) • Ket x := by
  funext y
  rw [applyGate_phaseOracle]
  by_cases h : y = x <;> simp [Ket, phaseOf, h]

/-- Updating a function at an argument with its existing value leaves the function unchanged. -/
private theorem update_self_eq {α : Type} {β : Type} [DecidableEq α] (f : α → β) (a : α) :
    Function.update f a (f a) = f := by
  funext x
  by_cases h : x = a <;> simp [Function.update, h]

/-- Two successive updates at the same argument reduce to the last update. -/
private theorem update_update_eq {α : Type} {β : Type} [DecidableEq α] (f : α → β) (a : α)
    (b c : β) : Function.update (Function.update f a b) a c = Function.update f a c := by
  funext x
  by_cases h : x = a <;> simp [Function.update, h]

end Helpers

section PairMixer

/-- The lower index 2j of a complete adjacent pair in `Fin N`. -/
def pairLo (N : ℕ) (j : ℕ) (hj : 2 * j + 1 < N) : Fin N := ⟨2 * j, by omega⟩

/-- The upper index 2j + 1 of a complete adjacent pair in `Fin N`. -/
def pairHi (N : ℕ) (j : ℕ) (hj : 2 * j + 1 < N) : Fin N := ⟨2 * j + 1, by omega⟩

/-- The underlying natural number of `pairLo N j hj` is 2j. -/
@[simp] theorem pairLo_val {N : ℕ} {j : ℕ} {hj : 2 * j + 1 < N} :
    (pairLo N j hj).val = 2 * j := rfl

/-- The underlying natural number of `pairHi N j hj` is 2j + 1. -/
@[simp] theorem pairHi_val {N : ℕ} {j : ℕ} {hj : 2 * j + 1 < N} :
    (pairHi N j hj).val = 2 * j + 1 := rfl

/-- The two indices of a complete adjacent pair are distinct. -/
theorem pairLo_ne_pairHi {N : ℕ} {j : ℕ} (hj : 2 * j + 1 < N) :
    pairLo N j hj ≠ pairHi N j hj := by
  intro h
  have hval := congrArg Fin.val h
  simp only [pairLo_val, pairHi_val] at hval
  omega

/-- The Hadamard matrix on the two indices of pair `j`, extended by the identity on all other
indices. -/
noncomputable def pairHadamardIdx (N : ℕ) (j : ℕ) (hj : 2 * j + 1 < N) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun x y =>
    if x = pairHi N j hj ∧ y = pairHi N j hj then -(Real.sqrt 2 : ℂ)⁻¹
    else if (x = pairLo N j hj ∨ x = pairHi N j hj) ∧ (y = pairLo N j hj ∨ y = pairHi N j hj)
      then (Real.sqrt 2 : ℂ)⁻¹
    else if x = y then 1 else 0

/-- Twice the square of the complex inverse of √2 equals one. -/
theorem two_mul_invSqrt2_sq : 2 * ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1 := by
  have h : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (2 : ℂ)⁻¹ := by
    rw [inv_pow, sqrt2_sq]
  rw [h, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)]

/-- The product of two complex inverse square roots of two equals the inverse of two. -/
theorem invSqrt2_mul_self : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
  linear_combination two_mul_invSqrt2_sq / 2

/-- A finite sum supported on two distinct indices equals the sum of the two corresponding
values. -/
private theorem sum_pair_univ {N : ℕ} (a b : Fin N) (hne : a ≠ b) (g : Fin N → ℂ)
    (h : ∀ z, z ≠ a → z ≠ b → g z = 0) : ∑ z, g z = g a + g b := by
  rw [← Finset.sum_subset (Finset.subset_univ ({a, b} : Finset (Fin N)))
      (fun z _ hz => h z (fun e => hz (by simp [e])) (fun e => hz (by simp [e]))),
    Finset.sum_pair hne]

/-- The lower diagonal entry of the pair Hadamard matrix is 1/√2. -/
@[simp] theorem pairHadamardIdx_lo_lo {N : ℕ} {j : ℕ} {hj : 2 * j + 1 < N} :
    pairHadamardIdx N j hj (pairLo N j hj) (pairLo N j hj) = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [pairHadamardIdx, pairLo_ne_pairHi hj]

/-- The lower row, upper column entry of the pair Hadamard matrix is 1/√2. -/
@[simp] theorem pairHadamardIdx_lo_hi {N : ℕ} {j : ℕ} {hj : 2 * j + 1 < N} :
    pairHadamardIdx N j hj (pairLo N j hj) (pairHi N j hj) = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [pairHadamardIdx, pairLo_ne_pairHi hj]

/-- The upper row, lower column entry of the pair Hadamard matrix is 1/√2. -/
@[simp] theorem pairHadamardIdx_hi_lo {N : ℕ} {j : ℕ} {hj : 2 * j + 1 < N} :
    pairHadamardIdx N j hj (pairHi N j hj) (pairLo N j hj) = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [pairHadamardIdx, pairLo_ne_pairHi hj]

/-- The upper diagonal entry of the pair Hadamard matrix is −1/√2. -/
@[simp] theorem pairHadamardIdx_hi_hi {N : ℕ} {j : ℕ} {hj : 2 * j + 1 < N} :
    pairHadamardIdx N j hj (pairHi N j hj) (pairHi N j hj) = -(Real.sqrt 2 : ℂ)⁻¹ := by
  simp [pairHadamardIdx]

/-- A pair Hadamard entry vanishes when its row belongs to the pair and its column lies outside
the pair. -/
theorem pairHadamardIdx_apply_left_mem {N : ℕ} {j : ℕ} {hj : 2 * j + 1 < N} {x y : Fin N}
    (hx : x = pairLo N j hj ∨ x = pairHi N j hj) (hy : y ≠ pairLo N j hj)
    (hy' : y ≠ pairHi N j hj) : pairHadamardIdx N j hj x y = 0 := by
  have h1 : ¬ (pairLo N j hj = y) := fun e => hy e.symm
  have h2 : ¬ (pairHi N j hj = y) := fun e => hy' e.symm
  rcases hx with hx | hx <;>
    simp [pairHadamardIdx, hx, hy, hy', h1, h2, pairLo_ne_pairHi hj]

/-- A pair Hadamard entry vanishes when its column belongs to the pair and its row lies outside
the pair. -/
theorem pairHadamardIdx_apply_right_mem {N : ℕ} {j : ℕ} {hj : 2 * j + 1 < N} {x y : Fin N}
    (hy : y = pairLo N j hj ∨ y = pairHi N j hj) (hx : x ≠ pairLo N j hj)
    (hx' : x ≠ pairHi N j hj) : pairHadamardIdx N j hj x y = 0 := by
  rcases hy with hy | hy <;>
    simp [pairHadamardIdx, hy, hx, hx', pairLo_ne_pairHi hj]

/-- Outside the selected pair, the pair Hadamard matrix has the entries of the identity matrix. -/
theorem pairHadamardIdx_apply_off {N : ℕ} {j : ℕ} {hj : 2 * j + 1 < N} {x y : Fin N}
    (hx : x ≠ pairLo N j hj) (hx' : x ≠ pairHi N j hj) (hy : y ≠ pairLo N j hj)
    (hy' : y ≠ pairHi N j hj) : pairHadamardIdx N j hj x y = if x = y then 1 else 0 := by
  simp [pairHadamardIdx, hx, hx', hy, hy']

/-- The square of the pair Hadamard matrix is the identity. -/
theorem pairHadamardIdx_mul_self {N : ℕ} {j : ℕ} (hj : 2 * j + 1 < N) :
    pairHadamardIdx N j hj * pairHadamardIdx N j hj = 1 := by
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hx : x = pairLo N j hj ∨ x = pairHi N j hj
  · by_cases hy : y = pairLo N j hj ∨ y = pairHi N j hj
    · have hzero : ∀ z : Fin N, z ≠ pairLo N j hj → z ≠ pairHi N j hj →
          (pairHadamardIdx N j hj x z * pairHadamardIdx N j hj z y) = 0 := by
        intro z hz1 hz2
        rw [pairHadamardIdx_apply_left_mem hx hz1 hz2]
        ring
      rw [sum_pair_univ (pairLo N j hj) (pairHi N j hj) (pairLo_ne_pairHi hj)
        (fun z => pairHadamardIdx N j hj x z * pairHadamardIdx N j hj z y) hzero]
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst hx <;> subst hy <;>
        simp only [pairHadamardIdx_lo_lo, pairHadamardIdx_lo_hi, pairHadamardIdx_hi_lo,
          pairHadamardIdx_hi_hi]
      · show ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹)
            + ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) = 1
        rw [invSqrt2_mul_self]
        norm_num
      · rw [ite_eq_right (pairLo_ne_pairHi hj)]
        show ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹)
            + ((Real.sqrt 2 : ℂ)⁻¹ * -((Real.sqrt 2 : ℂ)⁻¹)) = 0
        ring
      · rw [ite_eq_right (fun e => pairLo_ne_pairHi hj e.symm)]
        show ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹)
            + (-((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹) = 0
        ring
      · show ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹)
            + (-((Real.sqrt 2 : ℂ)⁻¹) * -((Real.sqrt 2 : ℂ)⁻¹)) = 1
        rw [neg_mul_neg, invSqrt2_mul_self]
        norm_num
    · have hxy : ¬ (x = y) := by
        intro e
        subst e
        exact hy hx
      rw [ite_eq_right hxy]
      apply Finset.sum_eq_zero
      intro z _
      by_cases hz : z = pairLo N j hj ∨ z = pairHi N j hj
      · rw [pairHadamardIdx_apply_left_mem hz (fun e => hy (Or.inl e))
          (fun e => hy (Or.inr e))]
        ring
      · rw [pairHadamardIdx_apply_left_mem hx (fun e => hz (Or.inl e))
          (fun e => hz (Or.inr e))]
        ring
  · by_cases hy : y = pairLo N j hj ∨ y = pairHi N j hj
    · have hxy : ¬ (x = y) := by
        intro e
        subst e
        exact hx hy
      rw [ite_eq_right hxy]
      apply Finset.sum_eq_zero
      intro z _
      by_cases hz : z = pairLo N j hj ∨ z = pairHi N j hj
      · rw [pairHadamardIdx_apply_right_mem hz (fun e => hx (Or.inl e))
          (fun e => hx (Or.inr e))]
        ring
      · rw [pairHadamardIdx_apply_right_mem hy (fun e => hz (Or.inl e))
          (fun e => hz (Or.inr e))]
        ring
    · have hxl : x ≠ pairLo N j hj := fun e => hx (Or.inl e)
      have hxh : x ≠ pairHi N j hj := fun e => hx (Or.inr e)
      have hyl : y ≠ pairLo N j hj := fun e => hy (Or.inl e)
      have hyh : y ≠ pairHi N j hj := fun e => hy (Or.inr e)
      rw [Finset.sum_eq_single x]
      · rw [pairHadamardIdx_apply_off hxl hxh hxl hxh,
        pairHadamardIdx_apply_off hxl hxh hyl hyh, ite_eq_left rfl, one_mul]
      · intro z _ hzx
        by_cases hz : z = pairLo N j hj ∨ z = pairHi N j hj
        · rw [pairHadamardIdx_apply_left_mem hz hyl hyh, mul_zero]
        · have hzl : z ≠ pairLo N j hj := fun e => hz (Or.inl e)
          have hzh : z ≠ pairHi N j hj := fun e => hz (Or.inr e)
          rw [pairHadamardIdx_apply_off hxl hxh hzl hzh, ite_eq_right (fun e : x = z => hzx e.symm)]
          ring
      · intro hcon
        exact absurd (Finset.mem_univ x) hcon

/-- The pair Hadamard matrix equals its conjugate transpose. -/
theorem pairHadamardIdx_conjTranspose {N : ℕ} {j : ℕ} (hj : 2 * j + 1 < N) :
    (pairHadamardIdx N j hj)ᴴ = pairHadamardIdx N j hj := by
  ext x y
  have hconj : (starRingEnd ℂ) ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    rw [map_inv₀]
    congr 1
    exact Complex.conj_ofReal _
  have hconj' : (starRingEnd ℂ) (-(Real.sqrt 2 : ℂ)⁻¹) = -((Real.sqrt 2 : ℂ)⁻¹) := by
    rw [map_neg, hconj]
  simp only [Matrix.conjTranspose_apply, RCLike.star_def]
  by_cases hx : x = pairLo N j hj ∨ x = pairHi N j hj
  · by_cases hy : y = pairLo N j hj ∨ y = pairHi N j hj
    · rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst hx <;> subst hy <;>
        simp [pairHadamardIdx, hconj, hconj', pairLo_ne_pairHi hj]
    · have hyl : y ≠ pairLo N j hj := fun e => hy (Or.inl e)
      have hyh : y ≠ pairHi N j hj := fun e => hy (Or.inr e)
      rcases hx with hx | hx
      · rw [hx, pairHadamardIdx_apply_right_mem (Or.inl rfl) hyl hyh,
          pairHadamardIdx_apply_left_mem (Or.inl rfl) hyl hyh, map_zero]
      · rw [hx, pairHadamardIdx_apply_right_mem (Or.inr rfl) hyl hyh,
          pairHadamardIdx_apply_left_mem (Or.inr rfl) hyl hyh, map_zero]
  · by_cases hy : y = pairLo N j hj ∨ y = pairHi N j hj
    · have hxl : x ≠ pairLo N j hj := fun e => hx (Or.inl e)
      have hxh : x ≠ pairHi N j hj := fun e => hx (Or.inr e)
      rcases hy with hy | hy
      · rw [hy, pairHadamardIdx_apply_left_mem (Or.inl rfl) hxl hxh,
          pairHadamardIdx_apply_right_mem (Or.inl rfl) hxl hxh, map_zero]
      · rw [hy, pairHadamardIdx_apply_left_mem (Or.inr rfl) hxl hxh,
          pairHadamardIdx_apply_right_mem (Or.inr rfl) hxl hxh, map_zero]
    · have hxl : x ≠ pairLo N j hj := fun e => hx (Or.inl e)
      have hxh : x ≠ pairHi N j hj := fun e => hx (Or.inr e)
      have hyl : y ≠ pairLo N j hj := fun e => hy (Or.inl e)
      have hyh : y ≠ pairHi N j hj := fun e => hy (Or.inr e)
      by_cases hxy : x = y
      · subst hxy
        rw [pairHadamardIdx_apply_off hxl hxh hxl hxh, ite_eq_left rfl, map_one]
      · rw [pairHadamardIdx_apply_off hyl hyh hxl hxh, ite_eq_right (fun e => hxy e.symm),
          pairHadamardIdx_apply_off hxl hxh hyl hyh, ite_eq_right hxy, map_zero]

/-- The pair Hadamard matrix is unitary. -/
theorem pairHadamardIdx_unitary {N : ℕ} {j : ℕ} (hj : 2 * j + 1 < N) :
    pairHadamardIdx N j hj ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    pairHadamardIdx_conjTranspose hj]
  exact pairHadamardIdx_mul_self hj

/-- The equal superposition of the two basis states indexed by pair `j`, with amplitudes 1/√2. -/
noncomputable def pairSup (N : ℕ) (j : ℕ) (hj : 2 * j + 1 < N) : QState (Fin N) :=
  fun x => if x = pairLo N j hj ∨ x = pairHi N j hj then (Real.sqrt 2 : ℂ)⁻¹ else 0

/-- The superposition on pair `j` with lower amplitude 1/√2 and upper amplitude −1/√2. -/
noncomputable def pairSupMinus (N : ℕ) (j : ℕ) (hj : 2 * j + 1 < N) : QState (Fin N) :=
  fun x => if x = pairLo N j hj then (Real.sqrt 2 : ℂ)⁻¹
    else if x = pairHi N j hj then -(Real.sqrt 2 : ℂ)⁻¹ else 0

/-- The lower amplitude of `pairSup` is 1/√2. -/
@[simp] theorem pairSup_lo {N : ℕ} {j : ℕ} {hj : 2 * j + 1 < N} :
    pairSup N j hj (pairLo N j hj) = (Real.sqrt 2 : ℂ)⁻¹ := by simp [pairSup]

/-- The upper amplitude of `pairSup` is 1/√2. -/
@[simp] theorem pairSup_hi {N : ℕ} {j : ℕ} {hj : 2 * j + 1 < N} :
    pairSup N j hj (pairHi N j hj) = (Real.sqrt 2 : ℂ)⁻¹ := by simp [pairSup]

/-- The state `pairSup` vanishes outside its selected pair. -/
theorem pairSup_off {N : ℕ} {j : ℕ} {hj : 2 * j + 1 < N} {x : Fin N}
    (h1 : x ≠ pairLo N j hj) (h2 : x ≠ pairHi N j hj) : pairSup N j hj x = 0 := by
  simp [pairSup, h1, h2]

/-- The lower amplitude of `pairSupMinus` is 1/√2. -/
@[simp] theorem pairSupMinus_lo {N : ℕ} {j : ℕ} {hj : 2 * j + 1 < N} :
    pairSupMinus N j hj (pairLo N j hj) = (Real.sqrt 2 : ℂ)⁻¹ := by simp [pairSupMinus]

/-- The upper amplitude of `pairSupMinus` is −1/√2. -/
@[simp] theorem pairSupMinus_hi {N : ℕ} {j : ℕ} {hj : 2 * j + 1 < N} :
    pairSupMinus N j hj (pairHi N j hj) = -(Real.sqrt 2 : ℂ)⁻¹ := by
  simp [pairSupMinus, Ne.symm (pairLo_ne_pairHi hj)]

/-- The state `pairSupMinus` vanishes outside its selected pair. -/
theorem pairSupMinus_off {N : ℕ} {j : ℕ} {hj : 2 * j + 1 < N} {x : Fin N}
    (h1 : x ≠ pairLo N j hj) (h2 : x ≠ pairHi N j hj) : pairSupMinus N j hj x = 0 := by
  simp [pairSupMinus, h1, h2]

/-- The pair Hadamard sends the lower basis state to the equal pair superposition. -/
theorem applyGate_pairHadamardIdx_ket_lo {N : ℕ} {j : ℕ} (hj : 2 * j + 1 < N) :
    ApplyGate (pairHadamardIdx N j hj) (Ket (pairLo N j hj)) = pairSup N j hj := by
  funext x
  have hsum : ∑ y : Fin N, pairHadamardIdx N j hj x y * Ket (pairLo N j hj) y
      = pairHadamardIdx N j hj x (pairLo N j hj) := by
    rw [Finset.sum_eq_single (pairLo N j hj)]
    · rw [ket_self, mul_one]
    · intro y _ hylo
      rw [ket_ne (fun e => hylo e), mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  simp only [ApplyGate, Matrix.mulVec, dotProduct]
  rw [hsum]
  by_cases hx : x = pairLo N j hj ∨ x = pairHi N j hj
  · rcases hx with hx | hx <;> simp [pairHadamardIdx, hx, pairSup, pairLo_ne_pairHi hj]
  · rw [pairHadamardIdx_apply_right_mem (Or.inl rfl) (fun e => hx (Or.inl e))
      (fun e => hx (Or.inr e)),
    pairSup_off (fun e => hx (Or.inl e)) (fun e => hx (Or.inr e))]

/-- The pair Hadamard sends the equal pair superposition to the lower basis state. -/
theorem applyGate_pairHadamardIdx_pairSup {N : ℕ} {j : ℕ} (hj : 2 * j + 1 < N) :
    ApplyGate (pairHadamardIdx N j hj) (pairSup N j hj) = Ket (pairLo N j hj) := by
  funext x
  by_cases hx : x = pairLo N j hj ∨ x = pairHi N j hj
  · have hzero : ∀ z : Fin N, z ≠ pairLo N j hj → z ≠ pairHi N j hj →
        (pairHadamardIdx N j hj x z * pairSup N j hj z) = 0 := by
      intro z hz1 hz2
      rw [pairHadamardIdx_apply_left_mem hx hz1 hz2]
      ring
    have hsum : ∑ z : Fin N, pairHadamardIdx N j hj x z * pairSup N j hj z
        = pairHadamardIdx N j hj x (pairLo N j hj) * pairSup N j hj (pairLo N j hj)
          + pairHadamardIdx N j hj x (pairHi N j hj) * pairSup N j hj (pairHi N j hj) :=
      sum_pair_univ (pairLo N j hj) (pairHi N j hj) (pairLo_ne_pairHi hj)
        (fun z => pairHadamardIdx N j hj x z * pairSup N j hj z) hzero
    rcases hx with hx | hx
    · subst hx
      simp only [ApplyGate, Matrix.mulVec, dotProduct, hsum, pairHadamardIdx_lo_lo,
        pairHadamardIdx_lo_hi, pairSup_lo, pairSup_hi, ket_self]
      rw [invSqrt2_mul_self]
      norm_num
    · subst hx
      simp only [ApplyGate, Matrix.mulVec, dotProduct, hsum, pairHadamardIdx_hi_lo,
        pairHadamardIdx_hi_hi, pairSup_lo, pairSup_hi, Ket,
        ite_eq_right (Ne.symm (pairLo_ne_pairHi hj))]
      ring
  · rw [ket_ne (fun e => hx (Or.inl e))]
    simp only [ApplyGate, Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hz : z = pairLo N j hj ∨ z = pairHi N j hj
    · rw [pairHadamardIdx_apply_right_mem hz (fun e => hx (Or.inl e))
        (fun e => hx (Or.inr e))]
      ring
    · rw [pairSup_off (fun e => hz (Or.inl e)) (fun e => hz (Or.inr e)), mul_zero]

/-- The pair Hadamard sends the pair superposition with opposite signs to the upper basis state. -/
theorem applyGate_pairHadamardIdx_pairSupMinus {N : ℕ} {j : ℕ} (hj : 2 * j + 1 < N) :
    ApplyGate (pairHadamardIdx N j hj) (pairSupMinus N j hj) = Ket (pairHi N j hj) := by
  funext x
  by_cases hx : x = pairLo N j hj ∨ x = pairHi N j hj
  · have hzero : ∀ z : Fin N, z ≠ pairLo N j hj → z ≠ pairHi N j hj →
        (pairHadamardIdx N j hj x z * pairSupMinus N j hj z) = 0 := by
      intro z hz1 hz2
      rw [pairHadamardIdx_apply_left_mem hx hz1 hz2]
      ring
    have hsum : ∑ z : Fin N, pairHadamardIdx N j hj x z * pairSupMinus N j hj z
        = pairHadamardIdx N j hj x (pairLo N j hj) * pairSupMinus N j hj (pairLo N j hj)
          + pairHadamardIdx N j hj x (pairHi N j hj) * pairSupMinus N j hj (pairHi N j hj) :=
      sum_pair_univ (pairLo N j hj) (pairHi N j hj) (pairLo_ne_pairHi hj)
        (fun z => pairHadamardIdx N j hj x z * pairSupMinus N j hj z) hzero
    rcases hx with hx | hx
    · subst hx
      simp only [ApplyGate, Matrix.mulVec, dotProduct, hsum, pairHadamardIdx_lo_lo,
        pairHadamardIdx_lo_hi, pairSupMinus_lo, pairSupMinus_hi, Ket,
        ite_eq_right (pairLo_ne_pairHi hj)]
      ring
    · subst hx
      simp only [ApplyGate, Matrix.mulVec, dotProduct, hsum, pairHadamardIdx_hi_lo,
        pairHadamardIdx_hi_hi, pairSupMinus_lo, pairSupMinus_hi, ket_self]
      rw [neg_mul_neg, invSqrt2_mul_self]
      norm_num
  · rw [ket_ne (fun e => hx (Or.inr e))]
    simp only [ApplyGate, Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hz : z = pairLo N j hj ∨ z = pairHi N j hj
    · rw [pairHadamardIdx_apply_right_mem hz (fun e => hx (Or.inl e))
        (fun e => hx (Or.inr e))]
      ring
    · rw [pairSupMinus_off (fun e => hz (Or.inl e)) (fun e => hz (Or.inr e)), mul_zero]

/-- A phase query changes the equal pair superposition according to the XOR of the two input
bits, with global phase given by the lower bit. -/
theorem applyGate_phaseOracle_pairSup {N : ℕ} (f : Fin N → Bool) {j : ℕ}
    (hj : 2 * j + 1 < N) :
    ApplyGate (PhaseOracle f) (pairSup N j hj)
      = phaseOf (f (pairLo N j hj)) •
        (if f (pairLo N j hj) ^^ f (pairHi N j hj)
          then pairSupMinus N j hj else pairSup N j hj) := by
  funext x
  rw [applyGate_phaseOracle]
  by_cases hx : x = pairLo N j hj
  · subst hx
    cases flo : f (pairLo N j hj) <;> cases fhi : f (pairHi N j hj) <;>
      simp [phaseOf, pairSup, pairSupMinus]
  · by_cases hx' : x = pairHi N j hj
    · subst hx'
      cases flo : f (pairLo N j hj) <;> cases fhi : f (pairHi N j hj) <;>
        simp [phaseOf, pairSup, pairSupMinus, hx]
    · by_cases hP : f (pairLo N j hj) ^^ f (pairHi N j hj) <;>
        simp [phaseOf, pairSup, pairSupMinus, hx, hx', hP]

/-- The pair Hadamard decodes the pair XOR into the upper basis state when it is true and the
lower basis state otherwise. -/
theorem applyGate_pairHadamardIdx_pairSup_ite {N : ℕ} (f : Fin N → Bool) {j : ℕ}
    (hj : 2 * j + 1 < N) :
    ApplyGate (pairHadamardIdx N j hj)
        (if f (pairLo N j hj) ^^ f (pairHi N j hj)
          then pairSupMinus N j hj else pairSup N j hj) =
      Ket (if f (pairLo N j hj) ^^ f (pairHi N j hj)
        then pairHi N j hj else pairLo N j hj) := by
  by_cases hP : f (pairLo N j hj) ^^ f (pairHi N j hj)
  · rw [ite_eq_left hP, ite_eq_left hP, applyGate_pairHadamardIdx_pairSupMinus hj]
  · rw [ite_eq_right hP, ite_eq_right hP, applyGate_pairHadamardIdx_pairSup hj]

end PairMixer

section Workspace

/-- The parity workspace consisting of an index, an oracle target bit, a Boolean record
register, and an answer bit. -/
abbrev ParityWS (N : ℕ) := PolynomialWorkspace (Fin N) (Reg N × Bool)

/-- A parity workspace basis state factors as the tensor product of its four component basis
states. -/
theorem ket_workspace_eq (N : ℕ) (i : Fin N) (t : Bool) (r : Reg N) (a : Bool) :
    Ket ((i, t), (r, a)) =
      TensorState (TensorState (Ket i) (Ket t)) (TensorState (Ket r) (Ket a)) := by
  funext p
  obtain ⟨⟨i', t'⟩, r', a'⟩ := p
  simp only [TensorState, Ket]
  by_cases h1 : i' = i <;> by_cases h2 : t' = t <;> by_cases h3 : r' = r <;>
    by_cases h4 : a' = a <;> simp [h1, h2, h3, h4]

/-- Extend an index gate to the parity workspace by tensoring with identity matrices on the
other registers. -/
noncomputable def onIdx (N : ℕ) (U : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (ParityWS N) (ParityWS N) ℂ :=
  TensorGate (TensorGate U (1 : Matrix Bool Bool ℂ)) (1 : Matrix (Reg N × Bool) (Reg N × Bool) ℂ)

/-- Extend a target bit gate to the parity workspace by tensoring with identity matrices on the
other registers. -/
noncomputable def onTgt (N : ℕ) (V : Matrix Bool Bool ℂ) :
    Matrix (ParityWS N) (ParityWS N) ℂ :=
  TensorGate (TensorGate (1 : Matrix (Fin N) (Fin N) ℂ) V)
    (1 : Matrix (Reg N × Bool) (Reg N × Bool) ℂ)

/-- Extending a unitary index gate with `onIdx` gives a unitary workspace gate. -/
theorem onIdx_unitary {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    onIdx N U ∈ Matrix.unitaryGroup (ParityWS N) ℂ :=
  tensorGate_unitary (tensorGate_unitary hU (Submonoid.one_mem _)) (Submonoid.one_mem _)

/-- Extending a unitary target bit gate with `onTgt` gives a unitary workspace gate. -/
theorem onTgt_unitary {N : ℕ} {V : Matrix Bool Bool ℂ}
    (hV : V ∈ Matrix.unitaryGroup Bool ℂ) :
    onTgt N V ∈ Matrix.unitaryGroup (ParityWS N) ℂ :=
  tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) hV) (Submonoid.one_mem _)

/-- On a tensor state, `onIdx` applies its gate to the index factor. -/
theorem applyGate_onIdx {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (φ : QState (Fin N))
    (τ : QState Bool) (χ : QState (Reg N × Bool)) :
    ApplyGate (onIdx N U) (TensorState (TensorState φ τ) χ) =
      TensorState (TensorState (ApplyGate U φ) τ) χ := by
  rw [onIdx, applyGate_tensorGate, applyGate_tensorGate, applyGate_one, applyGate_one]

/-- On a tensor state, `onTgt` applies its gate to the target bit factor. -/
theorem applyGate_onTgt {N : ℕ} (V : Matrix Bool Bool ℂ) (φ : QState (Fin N))
    (τ : QState Bool) (χ : QState (Reg N × Bool)) :
    ApplyGate (onTgt N V) (TensorState (TensorState φ τ) χ) =
      TensorState (TensorState φ (ApplyGate V τ)) χ := by
  rw [onTgt, applyGate_tensorGate, applyGate_tensorGate, applyGate_one, applyGate_one]

/-- Exchange two specified indices and fix every other index. -/
def swapFin {N : ℕ} (a b i : Fin N) : Fin N := if i = a then b else if i = b then a else i

/-- Exchanging two indices twice returns the original index. -/
theorem swapFin_involutive {N : ℕ} (a b : Fin N) : Function.Involutive (swapFin a b) := by
  intro i
  unfold swapFin
  by_cases h1 : i = a <;> by_cases h2 : i = b <;> simp [h1, h2]

/-- The index after processing `m` pairs: 2m when available, with a fallback to the last
processed lower index at the even endpoint. -/
def idxAt {N : ℕ} (hN : 0 < N) (m : ℕ) (hm : m ≤ N / 2) : Fin N :=
  if h : 2 * m < N then ⟨2 * m, h⟩
  else if hm0 : 0 < m then ⟨2 * m - 2, by omega⟩ else ⟨0, hN⟩

/-- Before processing any pairs, `idxAt` is the zero index. -/
@[simp] theorem idxAt_zero {N : ℕ} (hN : 0 < N) : idxAt hN 0 (by omega) = ⟨0, hN⟩ := by
  simp only [idxAt, dite_eq_left (by omega : (2 : ℕ) * 0 < N), Nat.mul_zero]

/-- The XOR of the input bits in adjacent pair `j`, or `false` when that pair is incomplete. -/
def pairParityBit {N : ℕ} (f : Fin N → Bool) (j : ℕ) : Bool :=
  if h : 2 * j + 1 < N then f ⟨2 * j, by omega⟩ ^^ f ⟨2 * j + 1, by omega⟩ else false

/-- For a complete pair, `pairParityBit` equals the XOR of the lower and upper input bits. -/
theorem pairParityBit_eq {N : ℕ} {f : Fin N → Bool} {j : ℕ} (hj : 2 * j + 1 < N) :
    pairParityBit f j = (f (pairLo N j hj) ^^ f (pairHi N j hj)) := by
  exact dite_eq_left hj

/-- The record register containing the first `m` pair XOR values and `false` in the remaining
positions. -/
def pairRecAfter {N : ℕ} (f : Fin N → Bool) (m : ℕ) : Reg N :=
  fun k => if (k : ℕ) < m then pairParityBit f (k : ℕ) else false

/-- Processing one further complete pair updates exactly its record position with that pair's
XOR. -/
theorem pairRecAfter_succ {N : ℕ} (f : Fin N → Bool) (m : ℕ) (hm : m < N / 2) :
    pairRecAfter f (m + 1) = Function.update (pairRecAfter f m) ⟨m, by omega⟩
      (pairParityBit f m) := by
  funext k
  by_cases hk : k = ⟨m, by omega⟩
  · subst hk
    rw [Function.update_self]
    show (if m < m + 1 then pairParityBit f m else false) = pairParityBit f m
    rw [ite_eq_left (by omega)]
  · rw [Function.update_of_ne hk]
    have hkm : (k : ℕ) ≠ m := by
      intro e
      exact hk (by ext; simpa using e)
    by_cases hlt : (k : ℕ) < m + 1
    · show (if (k : ℕ) < m + 1 then pairParityBit f (k : ℕ) else false)
        = (if (k : ℕ) < m then pairParityBit f (k : ℕ) else false)
      rw [ite_eq_left hlt, ite_eq_left (by omega)]
    · show (if (k : ℕ) < m + 1 then pairParityBit f (k : ℕ) else false)
        = (if (k : ℕ) < m then pairParityBit f (k : ℕ) else false)
      rw [ite_eq_right hlt, ite_eq_right (by omega)]

/-- The record register index assigned to pair `j`. -/
def pairRecBit {N : ℕ} (j : ℕ) (hj : 2 * j + 1 < N) : Fin N := ⟨j, by omega⟩

/-- The natural number underlying the record index for pair `j` is `j`. -/
@[simp] theorem pairRecBit_val {N : ℕ} {j : ℕ} {hj : 2 * j + 1 < N} :
    (pairRecBit j hj).val = j := rfl

/-- Flip the record bit for pair `j` when the index register is at that pair's upper index. -/
def parityCopyFlip {N : ℕ} (j : ℕ) (hj : 2 * j + 1 < N) :
    ParityWS N → ParityWS N :=
  fun p =>
    if p.1.1 = pairHi N j hj
    then ((p.1.1, p.1.2),
      (Function.update p.2.1 (pairRecBit j hj) (! p.2.1 (pairRecBit j hj)), p.2.2))
    else p

/-- The controlled record bit flip `parityCopyFlip` is an involution. -/
theorem parityCopyFlip_involutive {N : ℕ} {j : ℕ} (hj : 2 * j + 1 < N) :
    Function.Involutive (parityCopyFlip j hj) := by
  intro p
  by_cases hp : p.1.1 = pairHi N j hj
  · have h1 : Function.update p.2.1 (pairRecBit j hj)
        (! p.2.1 (pairRecBit j hj)) (pairRecBit j hj)
        = ! p.2.1 (pairRecBit j hj) := Function.update_self _ _ _
    simp only [parityCopyFlip, ite_eq_left hp, update_update_eq, h1, Bool.not_not,
      update_self_eq]
  · simp only [parityCopyFlip, ite_eq_right hp]

/-- Swap the index selected by the recorded pair XOR with the index for the next processing
stage. -/
def parityResetFlip {N : ℕ} (j : ℕ) (hj : 2 * j + 1 < N) :
    ParityWS N → ParityWS N :=
  fun p =>
    ((swapFin (if p.2.1 (pairRecBit j hj) then pairHi N j hj else pairLo N j hj)
      (idxAt (by omega) (j + 1) (by omega)) p.1.1, p.1.2), p.2)

/-- The record controlled index reset `parityResetFlip` is an involution. -/
theorem parityResetFlip_involutive {N : ℕ} {j : ℕ} (hj : 2 * j + 1 < N) :
    Function.Involutive (parityResetFlip j hj) := by
  intro p
  simp only [parityResetFlip]
  exact congrArg (fun i => ((i, p.1.2), p.2)) (swapFin_involutive _ _ p.1.1)

/-- The Boolean value indicating whether a register has odd Hamming weight. -/
def regParity {N : ℕ} (r : Reg N) : Bool := decide ((boolWeight r) % 2 = 1)

/-- XOR the parity of the record register into the answer bit. -/
def parityAcceptFlip {N : ℕ} : ParityWS N → ParityWS N :=
  fun p => ((p.1.1, p.1.2), (p.2.1, p.2.2 ^^ regParity p.2.1))

/-- XOR the oracle target bit into the answer bit. -/
def parityTargetFlip {N : ℕ} : ParityWS N → ParityWS N :=
  fun p => ((p.1.1, p.1.2), (p.2.1, p.2.2 ^^ p.1.2))

/-- XORing the record parity into the answer bit is an involution. -/
theorem parityAcceptFlip_involutive (N : ℕ) : Function.Involutive (parityAcceptFlip (N := N)) := by
  intro p
  simp only [parityAcceptFlip, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- XORing the target bit into the answer bit is an involution. -/
theorem parityTargetFlip_involutive (N : ℕ) : Function.Involutive (parityTargetFlip (N := N)) := by
  intro p
  simp only [parityTargetFlip, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The permutation matrix for `parityAcceptFlip` is unitary. -/
theorem parityAcceptFlip_unitary (N : ℕ) :
    permMatrix (parityAcceptFlip (N := N)) ∈ Matrix.unitaryGroup (ParityWS N) ℂ :=
  permMatrix_unitary (parityAcceptFlip_involutive N)

/-- The permutation matrix for `parityTargetFlip` is unitary. -/
theorem parityTargetFlip_unitary (N : ℕ) :
    permMatrix (parityTargetFlip (N := N)) ∈ Matrix.unitaryGroup (ParityWS N) ℂ :=
  permMatrix_unitary (parityTargetFlip_involutive N)

/-- The target preparation matrix `Hadamard * PauliX`, which sends the zero basis state to
`Minus`. -/
noncomputable def targetMinusMatrix : Matrix Bool Bool ℂ := Hadamard * PauliX

/-- The matrix `PauliX * Hadamard`, used to return `Minus` to the zero basis state. -/
noncomputable def targetZeroMatrix : Matrix Bool Bool ℂ := PauliX * Hadamard

/-- The target preparation matrix `targetMinusMatrix` is unitary. -/
theorem targetMinusMatrix_unitary : targetMinusMatrix ∈ Matrix.unitaryGroup Bool ℂ :=
  (Matrix.unitaryGroup Bool ℂ).mul_mem hadamard_unitary pauliX_unitary

/-- The target reset matrix `targetZeroMatrix` is unitary. -/
theorem targetZeroMatrix_unitary : targetZeroMatrix ∈ Matrix.unitaryGroup Bool ℂ :=
  (Matrix.unitaryGroup Bool ℂ).mul_mem pauliX_unitary hadamard_unitary

/-- The target preparation matrix sends the zero basis state to `Minus`. -/
theorem applyGate_targetMinusMatrix : ApplyGate targetMinusMatrix (Ket false) = Minus := by
  rw [targetMinusMatrix, applyGate_mul, applyGate_pauliX_ket]
  exact applyGate_hadamard_ket_true

/-- The target reset matrix sends `Minus` to the zero basis state. -/
theorem applyGate_targetZeroMatrix : ApplyGate targetZeroMatrix Minus = Ket false := by
  rw [targetZeroMatrix, applyGate_mul]
  have hHM : ApplyGate Hadamard Minus = Ket true := by
    rw [← applyGate_hadamard_ket_true, ← applyGate_mul, hadamard_mul_self, applyGate_one]
  rw [hHM, applyGate_pauliX_ket]
  rfl

end Workspace

section Circuit

/-- The Boolean bit oracle extended by the identity on the record and answer registers. -/
noncomputable def parityOracle (N : ℕ) (f : Fin N → Bool) :
    Matrix (ParityWS N) (ParityWS N) ℂ :=
  TensorGate (BitOracleOn f) (1 : Matrix (Reg N × Bool) (Reg N × Bool) ℂ)

/-- The circuit that uses one oracle query to record the XOR of pair `j` and prepare the index
for the next stage. -/
noncomputable def pairBlock {N : ℕ} (j : ℕ) (hj : 2 * j + 1 < N) : Circuit (ParityWS N) :=
  [Step.gate (onTgt N targetMinusMatrix), Step.gate (onIdx N (pairHadamardIdx N j hj)),
    Step.query, Step.gate (onIdx N (pairHadamardIdx N j hj)),
    Step.gate (onTgt N targetZeroMatrix), Step.gate (permMatrix (parityCopyFlip j hj)),
    Step.gate (permMatrix (parityResetFlip j hj))]

/-- A pair processing block contains exactly one oracle query. -/
theorem queryCount_pairBlock {N : ℕ} {j : ℕ} (hj : 2 * j + 1 < N) :
    QueryCount (pairBlock j hj) = 1 := rfl

/-- A pair processing block contains exactly six gates. -/
theorem gateCount_pairBlock {N : ℕ} {j : ℕ} (hj : 2 * j + 1 < N) :
    GateCount (pairBlock j hj) = 6 := rfl

/-- Every gate in a pair processing block is unitary. -/
theorem isUnitaryCircuit_pairBlock {N : ℕ} {j : ℕ} (hj : 2 * j + 1 < N) :
    IsUnitaryCircuit (pairBlock j hj) := by
  refine (isUnitaryCircuit_gate _ _).mpr ⟨onTgt_unitary targetMinusMatrix_unitary, ?_⟩
  refine (isUnitaryCircuit_gate _ _).mpr ⟨onIdx_unitary (pairHadamardIdx_unitary hj), ?_⟩
  rw [isUnitaryCircuit_query]
  refine (isUnitaryCircuit_gate _ _).mpr ⟨onIdx_unitary (pairHadamardIdx_unitary hj), ?_⟩
  refine (isUnitaryCircuit_gate _ _).mpr ⟨onTgt_unitary targetZeroMatrix_unitary, ?_⟩
  refine (isUnitaryCircuit_gate _ _).mpr
    ⟨permMatrix_unitary (parityCopyFlip_involutive hj), ?_⟩
  exact (isUnitaryCircuit_gate _ _).mpr
    ⟨permMatrix_unitary (parityResetFlip_involutive hj), isUnitaryCircuit_nil⟩

/-- Concatenate the processing blocks for the first `m` complete adjacent pairs. -/
noncomputable def pairsPart {N : ℕ} :
    (m : ℕ) → (∀ j < m, 2 * j + 1 < N) → Circuit (ParityWS N)
  | 0, _ => []
  | m + 1, hm =>
    pairsPart m (fun j hj => hm j (Nat.lt_succ_of_lt hj)) ++ pairBlock m (hm m (Nat.lt_succ_self m))

/-- Processing `m` complete pairs uses exactly `m` oracle queries. -/
theorem queryCount_pairsPart {N : ℕ} : ∀ (m : ℕ) (hm : ∀ j < m, 2 * j + 1 < N),
    QueryCount (pairsPart m hm) = m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    have heq : pairsPart (m + 1) hm
        = pairsPart m (fun j hj => hm j (Nat.lt_succ_of_lt hj))
          ++ pairBlock m (hm m (Nat.lt_succ_self m)) := rfl
    rw [heq, queryCount_append, ih, queryCount_pairBlock]

/-- Processing `m` complete pairs uses exactly 6m gates. -/
theorem gateCount_pairsPart {N : ℕ} : ∀ (m : ℕ) (hm : ∀ j < m, 2 * j + 1 < N),
    GateCount (pairsPart m hm) = 6 * m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    have heq : pairsPart (m + 1) hm
        = pairsPart m (fun j hj => hm j (Nat.lt_succ_of_lt hj))
          ++ pairBlock m (hm m (Nat.lt_succ_self m)) := rfl
    rw [heq, gateCount_append, ih, gateCount_pairBlock]
    ring

/-- The circuit processing any initial collection of complete pairs is unitary. -/
theorem isUnitaryCircuit_pairsPart {N : ℕ} : ∀ (m : ℕ) (hm : ∀ j < m, 2 * j + 1 < N),
    IsUnitaryCircuit (pairsPart m hm) := by
  intro m
  induction m with
  | zero => intro _; exact isUnitaryCircuit_nil
  | succ m ih =>
    intro hm
    have heq : pairsPart (m + 1) hm
        = pairsPart m (fun j hj => hm j (Nat.lt_succ_of_lt hj))
          ++ pairBlock m (hm m (Nat.lt_succ_self m)) := rfl
    rw [heq, isUnitaryCircuit_append]
    exact ⟨ih _, isUnitaryCircuit_pairBlock _⟩

/-- When the designated record bit is initially false, a pair block records the pair XOR and
advances the index, acquiring the phase of the lower input bit. -/
theorem run_pairBlock {N : ℕ} (f : Fin N → Bool) {j : ℕ} (hj : 2 * j + 1 < N)
    (c : ℂ) (rec : Reg N) (hrecj : rec (pairRecBit j hj) = false) (a : Bool) :
    Run (parityOracle N f) (pairBlock j hj)
      (c • Ket ((pairLo N j hj, false), (rec, a))) =
    (c * phaseOf (f (pairLo N j hj))) •
      Ket ((idxAt (by omega) (j + 1) (by omega), false),
        (Function.update rec (pairRecBit j hj) (pairParityBit f j), a)) := by
  have hk : Ket ((pairLo N j hj, false), (rec, a)) =
      TensorState (TensorState (Ket (pairLo N j hj)) (Ket false))
        (TensorState (Ket rec) (Ket a)) := ket_workspace_eq N _ _ _ _
  have h1 : ApplyGate (onTgt N targetMinusMatrix)
      (c • TensorState (TensorState (Ket (pairLo N j hj)) (Ket false))
        (TensorState (Ket rec) (Ket a))) =
      c • TensorState (TensorState (Ket (pairLo N j hj)) Minus)
        (TensorState (Ket rec) (Ket a)) := by
    rw [parity_applyGate_smul, applyGate_onTgt, applyGate_targetMinusMatrix]
  have h2 : ApplyGate (onIdx N (pairHadamardIdx N j hj))
      (c • TensorState (TensorState (Ket (pairLo N j hj)) Minus)
        (TensorState (Ket rec) (Ket a))) =
      c • TensorState (TensorState (pairSup N j hj) Minus)
        (TensorState (Ket rec) (Ket a)) := by
    rw [parity_applyGate_smul, applyGate_onIdx, applyGate_pairHadamardIdx_ket_lo hj]
  have h3 : ApplyGate (parityOracle N f)
      (c • TensorState (TensorState (pairSup N j hj) Minus)
        (TensorState (Ket rec) (Ket a))) =
      (c * phaseOf (f (pairLo N j hj))) •
        TensorState (TensorState (if f (pairLo N j hj) ^^ f (pairHi N j hj)
          then pairSupMinus N j hj else pairSup N j hj) Minus)
          (TensorState (Ket rec) (Ket a)) := by
    rw [parity_applyGate_smul, parityOracle, applyGate_tensorGate, applyGate_one,
      applyGate_bitOracleOn_tensorState_minus, applyGate_phaseOracle_pairSup,
      parity_tensorState_smul_left, parity_tensorState_smul_left, smul_smul]
  have h4 : ApplyGate (onIdx N (pairHadamardIdx N j hj))
      ((c * phaseOf (f (pairLo N j hj))) •
        TensorState (TensorState (if f (pairLo N j hj) ^^ f (pairHi N j hj)
          then pairSupMinus N j hj else pairSup N j hj) Minus)
          (TensorState (Ket rec) (Ket a))) =
      (c * phaseOf (f (pairLo N j hj))) •
        TensorState (TensorState (Ket (if f (pairLo N j hj) ^^ f (pairHi N j hj)
          then pairHi N j hj else pairLo N j hj)) Minus)
          (TensorState (Ket rec) (Ket a)) := by
    rw [parity_applyGate_smul, applyGate_onIdx, applyGate_pairHadamardIdx_pairSup_ite f hj]
  have h5 : ApplyGate (onTgt N targetZeroMatrix)
      ((c * phaseOf (f (pairLo N j hj))) •
        TensorState (TensorState (Ket (if f (pairLo N j hj) ^^ f (pairHi N j hj)
          then pairHi N j hj else pairLo N j hj)) Minus)
          (TensorState (Ket rec) (Ket a))) =
      (c * phaseOf (f (pairLo N j hj))) •
        Ket ((if f (pairLo N j hj) ^^ f (pairHi N j hj)
          then pairHi N j hj else pairLo N j hj, false), (rec, a)) := by
    rw [parity_applyGate_smul, applyGate_onTgt, applyGate_targetZeroMatrix,
      ← ket_workspace_eq N _ _ _ _]
  have h6 : ApplyGate (permMatrix (parityCopyFlip j hj))
      ((c * phaseOf (f (pairLo N j hj))) •
        Ket ((if f (pairLo N j hj) ^^ f (pairHi N j hj)
          then pairHi N j hj else pairLo N j hj, false), (rec, a))) =
      (c * phaseOf (f (pairLo N j hj))) •
        Ket ((if f (pairLo N j hj) ^^ f (pairHi N j hj)
          then pairHi N j hj else pairLo N j hj, false),
          (Function.update rec (pairRecBit j hj) (pairParityBit f j), a)) := by
    rw [parity_applyGate_smul, applyGate_permMatrix_ket (parityCopyFlip_involutive hj)]
    by_cases hP : f (pairLo N j hj) ^^ f (pairHi N j hj)
    · have hbit : pairParityBit f j = true := by
        rw [pairParityBit_eq hj]
        exact hP
      simp [parityCopyFlip, hP, hbit, hrecj]
    · have hbit : pairParityBit f j = false := by simp [pairParityBit_eq hj, hP]
      have hrec' : Function.update rec (pairRecBit j hj) false = rec := by
        rw [← hrecj]
        exact update_self_eq rec (pairRecBit j hj)
      simp [parityCopyFlip, hP, hbit, hrec', pairLo_ne_pairHi hj]
  have h7 : ApplyGate (permMatrix (parityResetFlip j hj))
      ((c * phaseOf (f (pairLo N j hj))) •
        Ket ((if f (pairLo N j hj) ^^ f (pairHi N j hj)
          then pairHi N j hj else pairLo N j hj, false),
          (Function.update rec (pairRecBit j hj) (pairParityBit f j), a))) =
      (c * phaseOf (f (pairLo N j hj))) •
        Ket ((idxAt (by omega) (j + 1) (by omega), false),
          (Function.update rec (pairRecBit j hj) (pairParityBit f j), a)) := by
    rw [parity_applyGate_smul, applyGate_permMatrix_ket (parityResetFlip_involutive hj)]
    have hrk : (Function.update rec (pairRecBit j hj) (pairParityBit f j))
        (pairRecBit j hj) = pairParityBit f j := Function.update_self _ _ _
    simp only [parityResetFlip, hrk]
    by_cases hP : f (pairLo N j hj) ^^ f (pairHi N j hj)
    · have hbit : pairParityBit f j = true := by
        rw [pairParityBit_eq hj]
        exact hP
      simp [hP, hbit, swapFin]
    · have hbit : pairParityBit f j = false := by simp [pairParityBit_eq hj, hP]
      simp [hP, hbit, swapFin]
  simp only [pairBlock, run_gate, run_query, run_nil]
  rw [hk, h1, h2, h3, h4, h5, h6, h7]

/-- Starting from the empty record, the first `m` pair blocks produce `pairRecAfter f m` and the
stage index `idxAt`, up to a scalar of norm one. -/
theorem run_pairsPart {N : ℕ} (hN : 0 < N) (f : Fin N → Bool) :
    ∀ (m : ℕ) (hm : m ≤ N / 2) (hm' : ∀ j < m, 2 * j + 1 < N) (a : Bool),
      ∃ c : ℂ, ‖c‖ = 1 ∧
      Run (parityOracle N f) (pairsPart m hm')
        (Ket ((idxAt hN 0 (by omega), false), (pairRecAfter f 0, a))) =
      c • Ket ((idxAt hN m hm, false), (pairRecAfter f m, a)) := by
  intro m
  induction m with
  | zero =>
    intro _ _ a
    refine ⟨1, by simp, ?_⟩
    simp only [pairsPart, run_nil, one_smul]
  | succ m ih =>
    intro hm hm' a
    have hm0 : m ≤ N / 2 := Nat.le_trans (Nat.le_succ m) hm
    have hm0' : ∀ j < m, 2 * j + 1 < N := fun j hj => hm' j (Nat.lt_succ_of_lt hj)
    obtain ⟨c, hc, hrun⟩ := ih hm0 hm0' a
    have hlt : 2 * m < N := by omega
    have hidx : idxAt hN m hm0 = pairLo N m (hm' m (Nat.lt_succ_self m)) := by
      simp only [idxAt, dite_eq_left hlt]
      rfl
    have hrecm : pairRecAfter f m (pairRecBit m (hm' m (Nat.lt_succ_self m))) = false := by
      simp only [pairRecAfter, pairRecBit_val]
      exact ite_eq_right (by omega)
    have heq : pairsPart (m + 1) hm'
        = pairsPart m hm0' ++ pairBlock m (hm' m (Nat.lt_succ_self m)) := rfl
    refine ⟨c * phaseOf (f (pairLo N m (hm' m (Nat.lt_succ_self m)))), ?_, ?_⟩
    · rw [norm_mul, hc, phaseOf_norm]
      norm_num
    · rw [heq, run_append, hrun, hidx, run_pairBlock f (hm' m (Nat.lt_succ_self m)) c
        (pairRecAfter f m) hrecm a, pairRecAfter_succ f m (by omega)]
      rfl

end Circuit

section Arithmetic

/-- Convert a Boolean value to the natural number 0 or 1. -/
private def b2n (b : Bool) : ℕ := if b then 1 else 0

/-- The integer value of XOR plus twice the product of the two bit values equals their sum. -/
private theorem b2n_xor_add (x y : Bool) :
    b2n (x ^^ y) + 2 * (b2n x * b2n y) = b2n x + b2n y := by
  cases x <;> cases y <;> rfl

/-- The integer value of XOR equals the sum of the bit values modulo two. -/
private theorem b2n_xor_mod (x y : Bool) : b2n (x ^^ y) = (b2n x + b2n y) % 2 := by
  cases x <;> cases y <;> rfl

/-- The Hamming weight of a Boolean register equals the sum of its bit values. -/
theorem boolWeight_eq_sum {N : ℕ} (r : Reg N) : boolWeight r = ∑ k, b2n (r k) := by
  simp only [boolWeight, boolSupp, b2n]
  rw [Finset.card_filter]

/-- A sum indexed by `Fin N` equals the sum over natural numbers below `N`, using the
corresponding bounded indices. -/
private theorem sum_fin_eq_range {N : ℕ} (F : Fin N → ℕ) :
    ∑ k, F k = ∑ k ∈ Finset.range N, (if h : k < N then F ⟨k, h⟩ else 0) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => if h : k < N then F ⟨k, h⟩ else 0) N]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dite_eq_left i.isLt]

/-- A finite sum splits into sums over adjacent pairs and a final term when the length is odd. -/
private theorem sum_range_split (g : ℕ → ℕ) : ∀ N : ℕ,
    ∑ k ∈ Finset.range N, g k
        = (∑ j ∈ Finset.range (N / 2), (g (2 * j) + g (2 * j + 1)))
          + (if N % 2 = 1 then g (N - 1) else 0) := by
  have key : ∀ m : ℕ,
      (∑ k ∈ Finset.range (2 * m), g k
        = ∑ j ∈ Finset.range m, (g (2 * j) + g (2 * j + 1))) ∧
      (∑ k ∈ Finset.range (2 * m + 1), g k
        = (∑ j ∈ Finset.range m, (g (2 * j) + g (2 * j + 1))) + g (2 * m)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have heven : ∑ k ∈ Finset.range (2 * (m + 1)), g k
          = ∑ j ∈ Finset.range (m + 1), (g (2 * j) + g (2 * j + 1)) := by
        rw [Finset.sum_range_succ (fun j => g (2 * j) + g (2 * j + 1)) m,
          show 2 * (m + 1) = 2 * m + 2 from by ring, Finset.sum_range_succ, ih.2]
        ring
      refine ⟨heven, ?_⟩
      rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring, Finset.sum_range_succ,
        show 2 * m + 2 = 2 * (m + 1) from by ring, heven]
  intro N
  rcases Nat.even_or_odd N with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have he0 : ¬ ((m + m) % 2 = 1) := by omega
    have hd2 : (m + m) / 2 = m := by omega
    simp only [ite_eq_right he0, hd2, add_zero]
    rw [show m + m = 2 * m from by ring]
    exact (key m).1
  · have he1 : (2 * m + 1) % 2 = 1 := by omega
    have hd2 : (2 * m + 1) / 2 = m := by omega
    simp only [ite_eq_left he1, hd2, show 2 * m + 1 - 1 = 2 * m from rfl]
    exact (key m).2

/-- The natural number value of input bit `k`, extended by zero beyond the input length. -/
private def bitAt {N : ℕ} (f : Fin N → Bool) (k : ℕ) : ℕ :=
  if h : k < N then b2n (f ⟨k, h⟩) else 0

/-- The last input bit when the input length is odd, and `false` when it is even. -/
def oddTailBit {N : ℕ} (f : Fin N → Bool) : Bool :=
  if h : N % 2 = 1 then f ⟨N - 1, by omega⟩ else false

/-- The XOR of the parity of the completed pair record with the unpaired final input bit. -/
def countedParityBit {N : ℕ} (f : Fin N → Bool) : Bool :=
  regParity (pairRecAfter f (N / 2)) ^^ oddTailBit f

/-- For a nonempty input, the Hamming weight splits into the sum of the complete pair weights
and the value of `oddTailBit`. -/
theorem boolWeight_eq_pairSum {N : ℕ} (hN : 0 < N) (f : Fin N → Bool) :
    boolWeight f = ((∑ j ∈ Finset.range (N / 2),
        (bitAt f (2 * j) + bitAt f (2 * j + 1)))) + b2n (oddTailBit f) := by
  have h1 : boolWeight f = ∑ k ∈ Finset.range N, bitAt f k := by
    rw [boolWeight_eq_sum, sum_fin_eq_range (fun k => b2n (f k))]
    exact Finset.sum_congr rfl fun k _ => rfl
  have h2 := sum_range_split (bitAt f) N
  have hodd : (if N % 2 = 1 then bitAt f (N - 1) else 0) = b2n (oddTailBit f) := by
    unfold oddTailBit bitAt
    by_cases hNo : N % 2 = 1
    · rw [ite_eq_left hNo, dite_eq_left hNo, dite_eq_left (by omega)]
    · rw [ite_eq_right hNo, dite_eq_right hNo]
      rfl
  rw [h1, h2, hodd]

/-- The Hamming weight of the record after `m` pairs is the sum of the first `m` pair XOR
values. -/
theorem boolWeight_pairRecAfter {N : ℕ} (f : Fin N → Bool) (m : ℕ) (hm : m ≤ N / 2) :
    boolWeight (pairRecAfter f m) = ∑ j ∈ Finset.range m, b2n (pairParityBit f j) := by
  have hzero : ∀ k ∈ Finset.range N, m ≤ k →
      (if h : k < N then b2n (pairRecAfter f m ⟨k, h⟩) else 0) = 0 := by
    intro k hkN hge
    have hkn : k < N := Finset.mem_range.mp hkN
    rw [dite_eq_left hkn]
    show b2n (if k < m then pairParityBit f k else false) = 0
    have hkm : ¬ (k < m) := by omega
    rw [ite_eq_right hkm]
    rfl
  rw [boolWeight_eq_sum, sum_fin_eq_range (fun k => b2n (pairRecAfter f m k)),
    ← Finset.sum_subset (show Finset.range m ⊆ Finset.range N from
        fun x hx => Finset.mem_range.mpr (by
          have hxm := Finset.mem_range.mp hx
          omega))
      (fun k hkN hk => by
        have hkm : ¬ (k < m) := fun hlt => hk (Finset.mem_range.mpr hlt)
        exact hzero k hkN (by omega))]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j < m := Finset.mem_range.mp hj
  have hjn : j < N := by omega
  show (if h : j < N then b2n (pairRecAfter f m ⟨j, h⟩) else 0) = b2n (pairParityBit f j)
  rw [dite_eq_left hjn]
  show b2n (if j < m then pairParityBit f j else false) = b2n (pairParityBit f j)
  rw [ite_eq_left hjm]

/-- For a nonempty input, `countedParityBit` is true exactly when the input has odd Hamming
weight. -/
theorem countedParityBit_eq {N : ℕ} (hN : 0 < N) (f : Fin N → Bool) :
    countedParityBit f = decide ((boolWeight f) % 2 = 1) := by
  have hper : ∀ j ∈ Finset.range (N / 2),
      b2n (pairParityBit f j) + 2 * (bitAt f (2 * j) * bitAt f (2 * j + 1))
        = bitAt f (2 * j) + bitAt f (2 * j + 1) := by
    intro j hj
    have hjm : j < N / 2 := Finset.mem_range.mp hj
    have h1 : 2 * j < N := by omega
    have h2 : 2 * j + 1 < N := by omega
    have hbit : pairParityBit f j = (f ⟨2 * j, h1⟩ ^^ f ⟨2 * j + 1, h2⟩) := by
      show (if h : 2 * j + 1 < N
          then f ⟨2 * j, by omega⟩ ^^ f ⟨2 * j + 1, by omega⟩ else false) = _
      rw [dite_eq_left h2]
    simp only [bitAt, dite_eq_left h1, dite_eq_left h2, hbit]
    exact b2n_xor_add _ _
  have hsumrel : (∑ j ∈ Finset.range (N / 2), b2n (pairParityBit f j))
      + 2 * (∑ j ∈ Finset.range (N / 2), bitAt f (2 * j) * bitAt f (2 * j + 1))
      = ∑ j ∈ Finset.range (N / 2), (bitAt f (2 * j) + bitAt f (2 * j + 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hper
  have hcomb : boolWeight (pairRecAfter f (N / 2))
      + 2 * (∑ j ∈ Finset.range (N / 2), bitAt f (2 * j) * bitAt f (2 * j + 1))
      + b2n (oddTailBit f) = boolWeight f := by
    have hW := boolWeight_pairRecAfter f (N / 2) (Nat.le_refl _)
    have hS := boolWeight_eq_pairSum hN f
    rw [hW, hsumrel] at *
    omega
  have hreg : b2n (regParity (pairRecAfter f (N / 2)))
      = boolWeight (pairRecAfter f (N / 2)) % 2 := by
    unfold regParity b2n
    rcases Nat.mod_two_eq_zero_or_one (boolWeight (pairRecAfter f (N / 2))) with h | h
    · rw [h]
      simp
    · rw [h]
      simp
  have hfin : b2n (countedParityBit f) = boolWeight f % 2 := by
    unfold countedParityBit
    rw [b2n_xor_mod, hreg]
    omega
  cases hb : countedParityBit f with
  | true =>
    rw [hb] at hfin
    simp only [b2n, ite_true] at hfin
    simp [show boolWeight f % 2 = 1 from hfin.symm]
  | false =>
    rw [hb] at hfin
    simp only [b2n, Bool.false_eq_true, ite_false] at hfin
    simp [show ¬ (boolWeight f % 2 = 1) from by omega]

end Arithmetic

section Main

/-- Every pair indexed below `N / 2` is a complete pair of input indices. -/
theorem lt_half_pairs (N : ℕ) : ∀ j < N / 2, 2 * j + 1 < N := by
  intro j hj
  omega

/-- The parity circuit consisting of all complete pair blocks, an extra query for an odd tail,
and a final answer gate. -/
noncomputable def countedParityCircuit (N : ℕ) :
    Circuit (PolynomialWorkspace (Fin N) (Reg N × Bool)) :=
  pairsPart (N / 2) (lt_half_pairs N) ++
    (if N % 2 = 1 then [Step.query, Step.gate (permMatrix (parityTargetFlip (N := N)))] else []) ++
    [Step.gate (permMatrix (parityAcceptFlip (N := N)))]

/-- The basis state with index zero and all target, record, and answer bits false. -/
def countedParityInitial (N : ℕ) (hN : 0 < N) :
    QState (PolynomialWorkspace (Fin N) (Reg N × Bool)) :=
  Ket ((⟨0, hN⟩, false), (ZeroStr N, false))

/-- The initial state of the counted parity circuit is normalized. -/
theorem normalized_countedParityInitial (N : ℕ) (hN : 0 < N) :
    Normalized (countedParityInitial N hN) := normalized_ket _

/-- The set of parity workspace basis states whose answer bit is true. -/
def countedParityAccept (N : ℕ) : Finset (PolynomialWorkspace (Fin N) (Reg N × Bool)) :=
  Finset.univ.filter fun p => p.2.2 = true

/-- The counted parity circuit uses exactly ⌈N/2⌉ oracle queries, expressed as `(N + 1) / 2`. -/
theorem queryCount_countedParityCircuit (N : ℕ) :
    QueryCount (countedParityCircuit N) = (N + 1) / 2 := by
  have h1 : QueryCount (countedParityCircuit N)
      = QueryCount (pairsPart (N / 2) (lt_half_pairs N))
        + QueryCount (if N % 2 = 1
          then [Step.query, Step.gate (permMatrix (parityTargetFlip (N := N)))] else [])
        + QueryCount [Step.gate (permMatrix (parityAcceptFlip (N := N)))] := by
    simp only [countedParityCircuit, ← queryCount_append]
  rw [h1, queryCount_pairsPart]
  by_cases hodd : N % 2 = 1
  · rw [ite_eq_left hodd]
    show N / 2 + 1 + 0 = (N + 1) / 2
    omega
  · rw [ite_eq_right hodd]
    show N / 2 + 0 + 0 = (N + 1) / 2
    omega

/-- The counted parity circuit uses at most 12N + 12 gates. -/
theorem gateCount_countedParityCircuit (N : ℕ) :
    GateCount (countedParityCircuit N) ≤ 12 * N + 12 := by
  have h1 : GateCount (countedParityCircuit N)
      = GateCount (pairsPart (N / 2) (lt_half_pairs N))
        + GateCount (if N % 2 = 1
          then [Step.query, Step.gate (permMatrix (parityTargetFlip (N := N)))] else [])
        + GateCount [Step.gate (permMatrix (parityAcceptFlip (N := N)))] := by
    simp only [countedParityCircuit, ← gateCount_append]
  rw [h1, gateCount_pairsPart]
  by_cases hodd : N % 2 = 1
  · rw [ite_eq_left hodd]
    show 6 * (N / 2) + 1 + 1 ≤ 12 * N + 12
    omega
  · rw [ite_eq_right hodd]
    show 6 * (N / 2) + 0 + 1 ≤ 12 * N + 12
    omega

/-- The counted parity circuit is unitary. -/
theorem isUnitaryCircuit_countedParityCircuit (N : ℕ) :
    IsUnitaryCircuit (countedParityCircuit N) := by
  have h1 : countedParityCircuit N
      = pairsPart (N / 2) (lt_half_pairs N)
        ++ ((if N % 2 = 1
          then [Step.query, Step.gate (permMatrix (parityTargetFlip (N := N)))] else [])
          ++ [Step.gate (permMatrix (parityAcceptFlip (N := N)))]) := by
    simp only [countedParityCircuit, List.append_assoc]
  rw [h1, isUnitaryCircuit_append]
  refine ⟨isUnitaryCircuit_pairsPart _ _, ?_⟩
  by_cases hodd : N % 2 = 1
  · rw [ite_eq_left hodd, isUnitaryCircuit_append, isUnitaryCircuit_query]
    exact ⟨(isUnitaryCircuit_gate _ _).mpr ⟨parityTargetFlip_unitary N, isUnitaryCircuit_nil⟩,
      (isUnitaryCircuit_gate _ _).mpr ⟨parityAcceptFlip_unitary N, isUnitaryCircuit_nil⟩⟩
  · rw [ite_eq_right hodd, List.nil_append]
    exact (isUnitaryCircuit_gate _ _).mpr ⟨parityAcceptFlip_unitary N, isUnitaryCircuit_nil⟩

/-- Querying a basis state with a false target and then applying `parityTargetFlip` stores the
queried input bit in the target and XORs it into the answer. -/
theorem run_oddTail {N : ℕ} (f : Fin N → Bool) (c : ℂ) (i : Fin N) (rec : Reg N)
    (a : Bool) :
    Run (parityOracle N f) [Step.query, Step.gate (permMatrix (parityTargetFlip (N := N)))]
      (c • Ket ((i, false), (rec, a))) = c • Ket ((i, f i), (rec, a ^^ f i)) := by
  have hsplit : Ket ((i, false), (rec, a)) = TensorState (Ket (i, false)) (Ket (rec, a)) :=
    (tensorState_ket_ket (i, false) (rec, a)).symm
  simp only [run_query, run_gate]
  rw [parity_applyGate_smul, hsplit, parityOracle, applyGate_tensorGate, applyGate_one,
    applyGate_bitOracleOn_ket, tensorState_ket_ket, parity_applyGate_smul,
    applyGate_permMatrix_ket (parityTargetFlip_involutive N), parityTargetFlip,
    Bool.false_xor]
  rfl

/-- On a nonempty input, the counted parity circuit produces the completed pair record, odd tail
bit, and parity answer, up to a scalar of norm one. -/
theorem countedParityCircuit_run (N : ℕ) (hN : 0 < N) (f : Fin N → Bool) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
    Run (parityOracle N f) (countedParityCircuit N) (countedParityInitial N hN) =
      c • Ket ((idxAt hN (N / 2) (Nat.le_refl (N / 2)), oddTailBit f),
        (pairRecAfter f (N / 2), countedParityBit f)) := by
  obtain ⟨c, hc, hrun⟩ :=
    run_pairsPart hN f (N / 2) (Nat.le_refl _) (by intro j hj; omega) false
  have hinit : countedParityInitial N hN
      = Ket ((idxAt hN 0 (by omega), false), (pairRecAfter f 0, false)) := by
    simp only [countedParityInitial, idxAt_zero]
    have hzero : pairRecAfter f 0 = ZeroStr N := by
      funext k
      simp [pairRecAfter, ZeroStr]
    rw [hzero]
  by_cases hodd : N % 2 = 1
  · have hlast : idxAt hN (N / 2) (Nat.le_refl _) = ⟨N - 1, by omega⟩ := by
      ext
      simp only [idxAt, dite_eq_left (by omega : 2 * (N / 2) < N), Fin.val_mk]
      omega
    have hoddT : oddTailBit f = f ⟨N - 1, by omega⟩ := by
      simp only [oddTailBit, dite_eq_left hodd]
    have hfidx : f (idxAt hN (N / 2) (Nat.le_refl _)) = oddTailBit f := by
      rw [hlast]
      exact hoddT.symm
    refine ⟨c, hc, ?_⟩
    rw [show countedParityCircuit N = pairsPart (N / 2) (lt_half_pairs N)
        ++ ([Step.query, Step.gate (permMatrix (parityTargetFlip (N := N)))]
          ++ [Step.gate (permMatrix (parityAcceptFlip (N := N)))]) from by
        simp only [countedParityCircuit, ite_eq_left hodd, List.append_assoc],
      run_append, run_append, hinit, hrun, run_oddTail f c _ _ false, hfidx,
      run_gate, parity_applyGate_smul, applyGate_permMatrix_ket (parityAcceptFlip_involutive N),
      run_nil]
    have haccFinal : countedParityBit f
        = ((false ^^ oddTailBit f) ^^ regParity (pairRecAfter f (N / 2))) := by
      unfold countedParityBit
      cases regParity (pairRecAfter f (N / 2)) <;> simp
    simp only [parityAcceptFlip, ← haccFinal]
  · have hoddT : oddTailBit f = false := by
      simp only [oddTailBit, dite_eq_right hodd]
    refine ⟨c, hc, ?_⟩
    rw [show countedParityCircuit N = pairsPart (N / 2) (lt_half_pairs N)
        ++ [Step.gate (permMatrix (parityAcceptFlip (N := N)))] from by
        simp only [countedParityCircuit, ite_eq_right hodd, List.append_assoc,
          List.nil_append],
      run_append, hinit, hrun, run_gate, parity_applyGate_smul,
      applyGate_permMatrix_ket (parityAcceptFlip_involutive N), run_nil]
    have hcb : countedParityBit f = regParity (pairRecAfter f (N / 2)) := by
      unfold countedParityBit
      rw [hoddT]
      simp
    simp only [parityAcceptFlip, hoddT, hcb, Bool.false_xor]

/-- On a nonempty input, the counted parity circuit accepts with probability one for odd Hamming
weight and zero for even Hamming weight. -/
theorem countedParity_measureProb {N : ℕ} (hN : 0 < N) (f : Fin N → Bool) :
    MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix (Reg N × Bool) (Reg N × Bool) ℂ))
        (countedParityCircuit N) (countedParityInitial N hN)) (countedParityAccept N) =
      if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1 then 1 else 0 := by
  obtain ⟨c, hc, hrun⟩ := countedParityCircuit_run N hN f
  rw [show TensorGate (BitOracleOn f) (1 : Matrix (Reg N × Bool) (Reg N × Bool) ℂ)
      = parityOracle N f from rfl, hrun, measureProb_smul_ket hc]
  by_cases hmem : ((idxAt hN (N / 2) (Nat.le_refl (N / 2)), oddTailBit f),
      (pairRecAfter f (N / 2), countedParityBit f)) ∈ countedParityAccept N
  · rw [ite_eq_left hmem]
    have hb : countedParityBit f = true := by
      simpa [countedParityAccept] using hmem
    have hw : boolWeight f = (Finset.univ.filter (fun i => f i = true)).card := rfl
    have h2 : (Finset.univ.filter (fun i => f i = true)).card % 2 = 1 := by
      have h3 := countedParityBit_eq hN f
      rw [hb, hw] at h3
      simpa using h3
    rw [ite_eq_left h2]
  · rw [ite_eq_right hmem]
    have hb : countedParityBit f = false := by
      have : ¬ (countedParityBit f = true) := by
        intro hcon
        exact hmem (by simp [countedParityAccept, hcon])
      cases hc2 : countedParityBit f <;> simp_all
    have hw : boolWeight f = (Finset.univ.filter (fun i => f i = true)).card := rfl
    have h2 : ¬ ((Finset.univ.filter (fun i => f i = true)).card % 2 = 1) := by
      have h3 := countedParityBit_eq hN f
      rw [hb, hw] at h3
      simpa using h3
    rw [ite_eq_right h2]

/-- For positive `N`, the counted parity circuit is unitary, starts in a normalized state,
computes parity exactly, uses ⌈N/2⌉ queries, and uses at most 12N + 12 gates. This realizes
the parity upper bound associated with [Beals et al., Proposition 6.4][BealsEtAl2001]. -/
theorem parity_actual_pairwise_query_upper_consumer (N : ℕ) (hN : 0 < N) :
    IsUnitaryCircuit (countedParityCircuit N) ∧ Normalized (countedParityInitial N hN) ∧
      QueryCount (countedParityCircuit N) = (N + 1) / 2 ∧
      GateCount (countedParityCircuit N) ≤ 12 * N + 12 ∧
      ∀ f : Fin N → Bool,
        MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix (Reg N × Bool) (Reg N × Bool) ℂ))
          (countedParityCircuit N) (countedParityInitial N hN)) (countedParityAccept N) =
        if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1 then 1 else 0 :=
  ⟨isUnitaryCircuit_countedParityCircuit N, normalized_countedParityInitial N hN,
    queryCount_countedParityCircuit N, gateCount_countedParityCircuit N,
    fun f => countedParity_measureProb hN f⟩

/-- For positive `N`, the counted circuit computes parity exactly with ⌈N/2⌉ queries and at most
12N + 12 gates, while every normalized unitary circuit on the same workspace approximating
parity within 1/3 needs at least ⌈N/2⌉ queries. See [Beals et al., Proposition
6.4][BealsEtAl2001]. -/
theorem parity_query_complexity_tight (N : ℕ) (hN : 0 < N) :
    (∀ f : Fin N → Bool,
      MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix (Reg N × Bool) (Reg N × Bool) ℂ))
        (countedParityCircuit N) (countedParityInitial N hN)) (countedParityAccept N) =
      if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1 then 1 else 0) ∧
    QueryCount (countedParityCircuit N) = (N + 1) / 2 ∧
    GateCount (countedParityCircuit N) ≤ 12 * N + 12 ∧
    (∀ (C : Circuit (PolynomialWorkspace (Fin N) (Reg N × Bool)))
      (ψ : QState (PolynomialWorkspace (Fin N) (Reg N × Bool)))
      (E : Finset (PolynomialWorkspace (Fin N) (Reg N × Bool))),
      IsUnitaryCircuit C → Normalized ψ →
      (∀ f : Fin N → Bool,
        |MeasureProb (Run (TensorGate (BitOracleOn f)
            (1 : Matrix (Reg N × Bool) (Reg N × Bool) ℂ)) C ψ) E
          - (if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1
            then (1 : ℝ) else 0)| ≤ 1 / 3) →
      (N + 1) / 2 ≤ QueryCount C) := by
  refine ⟨fun f => countedParity_measureProb hN f, queryCount_countedParityCircuit N,
    gateCount_countedParityCircuit N, ?_⟩
  intro C ψ E hU hψ hyp
  have hcard : Fintype.card (Fin N) = N := Fintype.card_fin _
  have hlow := parity_actual_bounded_error_query_lower_bound
    (I := Fin N) (W := Reg N × Bool) C ψ E hU hψ hyp
  rw [hcard] at hlow
  omega

end Main

end Qatlib.Concepts.QueryComplexity.AdversarySearch
