/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.FairBitSampling.FairBitQDrift
import Qatlib.Concepts.ChannelTheory.Stinespring.ShadowEstimator

/-!
# Computed budgets for fair-bit qDRIFT

This module chooses explicit step and rejection-fuel budgets for fair-bit qDRIFT and derives
reference-assisted trace-norm and observable-error estimates. The weighted Pauli example
simulates `pauliX + 2 • pauliZ` and records pathwise quantum and classical resource counts.

The mathematical background is described in [Campbell2019].

## Main statements

* `fairQdrift_computed_budget_trace`: error at most `2⁻ˢ` times the input trace norm.
* `fair_bit_qdrift_computed_budget_observable`: the corresponding observable estimate.
* `fairQdrift_weighted_xz_path_ledger`: resource counts for the weighted Pauli example.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ChannelTheory.Stinespring

open Qatlib.Concepts.RandCompile.FairBitSampling

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.RandCompile.ChannelBudget
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The positive step budget `max 1 (8 * W² * T² * 2^s)` for fair-bit qDRIFT. -/
def fairQdriftSteps (W T s : ℕ) : ℕ := max 1 (8*W^2*T^2*2^s)

/-- The rejection-sampling fuel `s + clog 2 (max 1 n) + 2` for a fair-bit qDRIFT run. -/
def fairQdriftFuel (n s : ℕ) : ℕ := s + Nat.clog 2 (max 1 n) + 2

/-- The computed step and fuel budgets are positive and bound each of the simulation and
sampling error terms by `2⁻ˢ / 2`. -/
private theorem fairQdrift_budget_bound (W T s : ℕ) (t : ℝ) (ht : |t| ≤ T) :
    let n := fairQdriftSteps W T s
    let R := fairQdriftFuel n s
    0 < n ∧ 4*(W : ℝ)^2*t^2/(n : ℝ) ≤ ((2 : ℝ)⁻¹)^s/2 ∧
      2*n*((2 : ℝ)⁻¹)^R ≤ ((2 : ℝ)⁻¹)^s/2 := by
  let n := fairQdriftSteps W T s
  let c := Nat.clog 2 (max 1 n)
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hl : 8*(W : ℝ)^2*(T : ℝ)^2*(2 : ℝ)^s ≤ (n : ℝ) := by
    exact_mod_cast Nat.le_max_right 1 (8*W^2*T^2*2^s)
  have hp : (n : ℝ) ≤ (2 : ℝ)^c := by
    exact_mod_cast (Nat.le_max_right 1 n).trans (Nat.le_pow_clog (by decide) (max 1 n))
  have htt : t^2 ≤ (T : ℝ)^2 := by
    have h := mul_self_le_mul_self (abs_nonneg t) ht
    simpa only [← sq, sq_abs] using h
  refine ⟨hn, ?_, ?_⟩
  · apply (div_le_iff₀ hnR).mpr
    calc
      4*(W : ℝ)^2*t^2 ≤ 4*(W : ℝ)^2*(T : ℝ)^2 := by gcongr
      _ = (((2 : ℝ)⁻¹)^s/2)*(8*(W : ℝ)^2*(T : ℝ)^2*2^s) := by
        simp only [inv_pow]
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
  · change 2*(n : ℝ)*((2 : ℝ)⁻¹)^(s+c+2) ≤ _
    rw [pow_add, pow_add]
    calc
      2*(n : ℝ)*(((2 : ℝ)⁻¹)^s*((2 : ℝ)⁻¹)^c*((2 : ℝ)⁻¹)^2) ≤
          2*(2 : ℝ)^c*(((2 : ℝ)⁻¹)^s*((2 : ℝ)⁻¹)^c*((2 : ℝ)⁻¹)^2) := by gcongr
      _ = _ := by
        simp only [inv_pow]
        field_simp

/-- For weighted Hermitian contractions and bounded time, the computed budgets give
reference-assisted trace-norm error at most `2⁻ˢ * traceNorm X`; see [Campbell2019]. -/
theorem fairQdrift_computed_budget_trace (L D T s r : ℕ) (w : Fin L → ℕ)
    (j0 : Fin L) (K : Fin L → Operator D) (t : ℝ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hW : 0 < weightTotal w) (ht : |t| ≤ T)
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) :
    Matrix.traceNorm (fairQdriftReferenceOutput w j0 (fairQdriftSteps (weightTotal w) T s)
      (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) K t r X -
      TensorGate (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r) * X *
        (TensorGate (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r))ᴴ) ≤
      ((2 : ℝ)⁻¹)^s*Matrix.traceNorm X := by
  have hb := fairQdrift_budget_bound (weightTotal w) T s t ht
  have he := fair_bit_qdrift_derived_sampling_and_analytic_error L D
    (fairQdriftSteps (weightTotal w) T s)
    (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) r w j0 K t X hW hb.1 hK
  refine he.trans (mul_le_mul_of_nonneg_right ?_ (Matrix.traceNorm_nonneg X))
  linarith [hb.2.1, hb.2.2]

/-- The computed positive step and fuel budgets bound the real observable trace error by `‖O‖ *
2⁻ˢ * traceNorm X`; see [Campbell2019]. -/
theorem fair_bit_qdrift_computed_budget_observable (L D T s r : ℕ)
    (w : Fin L → ℕ) (j0 : Fin L) (K : Fin L → Operator D) (t : ℝ)
    (X O : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hW : 0 < weightTotal w) (ht : |t| ≤ T)
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) :
    let n := fairQdriftSteps (weightTotal w) T s
    let R := fairQdriftFuel n s
    0 < n ∧ n = max 1 (8*(weightTotal w)^2*T^2*2^s) ∧
      R = s+Nat.clog 2 (max 1 n)+2 ∧
      |(Matrix.trace (O*(fairQdriftReferenceOutput w j0 n R K t r X -
        TensorGate (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r) * X *
          (TensorGate (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r))ᴴ))).re| ≤
        ‖O‖*((2 : ℝ)⁻¹)^s*Matrix.traceNorm X := by
  refine ⟨(fairQdrift_budget_bound (weightTotal w) T s t ht).1, rfl, rfl, ?_⟩
  have he := fairQdrift_computed_budget_trace L D T s r w j0 K t X hW ht hK
  exact ((Complex.abs_re_le_norm _).trans (Matrix.abs_trace_le_traceNorm _)).trans
    ((Matrix.traceNorm_mul_le_opNorm_traceNorm _ _).trans
      ((mul_le_mul_of_nonneg_left he (norm_nonneg O)).trans_eq (by ring)))

/-- The Pauli-X matrix is Hermitian and has operator norm at most one. -/
private theorem fairQdrift_pauliX_contract : pauliX.IsHermitian ∧ ‖pauliX‖ ≤ 1 := by
  have hh : pauliXᴴ = pauliX := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose_apply]
  refine ⟨hh, l2_norm_unitary_le_one ?_⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hh]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- The Pauli-Z matrix is Hermitian and has operator norm at most one. -/
private theorem fairQdrift_pauliZ_contract : pauliZ.IsHermitian ∧ ‖pauliZ‖ ≤ 1 := by
  have hh : pauliZᴴ = pauliZ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.conjTranspose_apply]
  refine ⟨hh, l2_norm_unitary_le_one ?_⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hh]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- For `pauliX + 2 • pauliZ` and `|t| ≤ 1`, the computed fair-bit sampler has the stated
label-one probability and trace-norm simulation error at most `2⁻ˢ * traceNorm X`. See
[Campbell2019]. -/
theorem fair_bit_qdrift_noncommuting_weighted_consumer (s r : ℕ) (t : ℝ)
    (X : Matrix (Fin 2 × Fin r) (Fin 2 × Fin r) ℂ) (ht : |t| ≤ 1) :
    let w := (![1,2] : Fin 2 → ℕ)
    let K := fun j : Fin 2 => if j=0 then pauliX else pauliZ
    let n := fairQdriftSteps 3 1 s
    let R := fairQdriftFuel n s
    (fairQdriftLaw w 0 R).prob 1 = (2/3)*(1-(1/4 : ℝ)^R) ∧
      Matrix.traceNorm (fairQdriftReferenceOutput w 0 n R K t r X -
        TensorGate (HamiltonianEvolution (pauliX+2 • pauliZ) t) (1 : Operator r) * X *
          (TensorGate (HamiltonianEvolution (pauliX+2 • pauliZ) t) (1 : Operator r))ᴴ) ≤
        ((2 : ℝ)⁻¹)^s*Matrix.traceNorm X := by
  let w := (![1,2] : Fin 2 → ℕ)
  let K := fun j : Fin 2 => if j=0 then pauliX else pauliZ
  let n := fairQdriftSteps 3 1 s
  let R := fairQdriftFuel n s
  have hW : weightTotal w = 3 := by decide
  have hpos : 0 < weightTotal w := by omega
  have hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1 := by
    intro j
    dsimp [K]
    split_ifs
    · exact fairQdrift_pauliX_contract
    · exact fairQdrift_pauliZ_contract
  have hH : (∑ j, (w j : ℂ) • K j) = pauliX+2 • pauliZ := by
    simp [w,K,Fin.sum_univ_two,two_smul]
  constructor
  · have h := fair_bit_qdrift_actual_sampler_law 2 R w 0 hpos 1
    norm_num [hW, w, show Nat.clog 2 3 = 2 from by decide] at h
    rw [h]
    ring
  · have he := fairQdrift_computed_budget_trace 2 2 1 s r w 0 K t X hpos (by simpa using ht) hK
    simpa only [hW, hH] using he

/-- Every random path for the weighted Pauli-X/Z example gives a unitary circuit with zero
queries, exactly `n` gates, and both recorded classical costs at most `2 * n * R`. -/
theorem fairQdrift_weighted_xz_path_ledger (n R : ℕ) (t : ℝ)
    (ω : Fin n → Fin R → Reg (Nat.clog 2 (weightTotal (![1,2] : Fin 2 → ℕ)))) :
    let w := (![1,2] : Fin 2 → ℕ)
    let K := fun j : Fin 2 => if j=0 then pauliX else pauliZ
    IsUnitaryCircuit (fairQdriftCircuit w 0 n R K t ω) ∧
      QueryCount (fairQdriftCircuit w 0 n R K t ω) = 0 ∧
      GateCount (fairQdriftCircuit w 0 n R K t ω) = n ∧
      (∑ k, (fairQdriftPick w 0 R (ω k)).2.1) ≤ n*2*R ∧
      (∑ k, (fairQdriftPick w 0 R (ω k)).2.2) ≤ n*2*R := by
  let w := (![1,2] : Fin 2 → ℕ)
  let K := fun j : Fin 2 => if j=0 then pauliX else pauliZ
  have hK : ∀ j, (K j).IsHermitian := by
    intro j
    dsimp [K]
    split_ifs
    · exact fairQdrift_pauliX_contract.1
    · exact fairQdrift_pauliZ_contract.1
  have h := fair_bit_qdrift_actual_quantum_and_classical_path_counts 2 2 n R w 0 K t ω
    (by decide) hK
  simpa only [show Nat.clog 2 (weightTotal w) = 2 from by decide] using h

end Qatlib.Concepts.RandCompile.ChannelBudget
