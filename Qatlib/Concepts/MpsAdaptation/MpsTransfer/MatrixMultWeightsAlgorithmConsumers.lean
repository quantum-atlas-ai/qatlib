/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixWeights.StoppingRule

/-!
# Two-level matrix multiplicative weights examples

This module evaluates matrix multiplicative weights for the two constraints given by Pauli Z and
the identity. A constant choice of the identity constraint gives scalar exponential weights and
the maximally mixed state at every round. The examples exercise stopping branches in the quantum
semidefinite programming setting of [BrandaoSvore2017].

`mmwSdpTwoLevelLargerInstance` uses thresholds 0 and 1/2 to exhibit persistent violation and
infeasibility. `mmwSdpTwoLevelCompletionInstance` uses unit thresholds to obtain a
density-operator average satisfying the stated approximate constraint bounds.

## Main statements

* `mmwSdpTwoLevelLargerInstance`: an explicit two-level instance of the infeasibility branch.
* `mmwSdpTwoLevelCompletionInstance`: an explicit two-level instance of the completion branch.

## References

* [Brandao and Svore, 2017, Algorithm 3][BrandaoSvore2017]
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixWeights.SdpAlgorithm
open Qatlib.Concepts.MatrixWeights.StoppingRule
open Qatlib.Concepts.MatrixWeights.WeightsCore

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

/-- The pair of two-level constraint matrices consisting of Pauli Z at index 0 and the identity
at index 1. -/
private def mmwTwoConstraints : Fin 2 → Operator 2 := fun i => if i=0 then !![1,0;0,-1] else 1
/-- The maximally mixed two-level density matrix, equal to one half of the identity. -/
private def mmwTwoDensity : Operator 2 := (2 : ℝ)⁻¹ • 1

/-- Each of the two constraint matrices is Hermitian and has operator norm at most 1. -/
private theorem mmw_two_constraints_bound (i : Fin 2) :
    (mmwTwoConstraints i).IsHermitian ∧ ‖mmwTwoConstraints i‖ ≤ 1 := by
  have hZ : (!![1,0;0,-1] : Operator 2).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply]
  have hn : ‖(!![1,0;0,-1] : Operator 2)‖ ≤ 1 := by
    apply l2_norm_unitary_le_one
    rw [Matrix.mem_unitaryGroup_iff]
    change (!![1,0;0,-1] : Operator 2)*(!![1,0;0,-1] : Operator 2)ᴴ = 1
    rw [hZ.eq]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i
  · exact ⟨hZ, hn⟩
  · exact ⟨Matrix.isHermitian_one, l2_norm_one_le⟩

/-- For the constant identity loss sequence, the multiplicative weight matrix at time `t` is
`Real.exp (-η * t)` times the identity. -/
private theorem mmw_two_weight (η : ℝ) (t : ℕ) :
    mmwWeight 2 (fun _ => (1 : Operator 2)) η t = Real.exp (-η*(t : ℝ)) • 1 := by
  have hs : (∑ _s ∈ Finset.range t, (1 : Operator 2)) = (t : ℝ) • (1 : Operator 2) := by
    simp only [Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]
  rw [mmwWeight, hs, smul_smul]
  simpa only [zero_add, NormedSpace.exp_zero] using!
    mmw_exp_scalar_shift 2 0 (-η*(t : ℝ))

/-- For the constant identity loss sequence, every normalized multiplicative weights state is
`mmwTwoDensity`. -/
private theorem mmw_two_state (η : ℝ) (t : ℕ) :
    mmwState 2 (fun _ => (1 : Operator 2)) η t = mmwTwoDensity := by
  rw [mmwState, mmw_two_weight]
  have ht : (Matrix.trace (Real.exp (-η*(t : ℝ)) • (1 : Operator 2))).re =
      2*Real.exp (-η*(t : ℝ)) := by
    have htrace : (Matrix.trace (1 : Operator 2)).re = 2 := by norm_num [Matrix.trace_one]
    rw [Matrix.trace_smul, Complex.smul_re, htrace, smul_eq_mul]
    ring
  rw [ht, ← Complex.ofReal_inv, Complex.coe_smul, smul_smul]
  unfold mmwTwoDensity
  congr 1
  have he : Real.exp (-η*(t : ℝ)) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-- For a positive number of rounds and the constant identity loss sequence, the average state
is `mmwTwoDensity`. -/
private theorem mmw_two_average (η : ℝ) (T : ℕ) (hT : 0 < T) :
    mmwAverage 2 T (fun _ => (1 : Operator 2)) η = mmwTwoDensity := by
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  simp only [mmwAverage, mmw_two_state, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℂ T, smul_smul, inv_mul_cancel₀ hTc, one_smul]

/-- Against the maximally mixed two-level state, the real constraint trace is 0 for Pauli Z and
1 for the identity. -/
private theorem mmw_two_traces (i : Fin 2) :
    (Matrix.trace (mmwTwoConstraints i*mmwTwoDensity)).re = if i=0 then 0 else 1 := by
  fin_cases i <;> norm_num [mmwTwoConstraints, mmwTwoDensity, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace, Fin.sum_univ_two, Complex.smul_re, smul_eq_mul]

/-- For `0 < η ≤ 1` and `η < 1/2`, the specified two-constraint instance has the explicit
exponential weights, constant maximally mixed states, exact selection, and persistent
violation through the stopping horizon. Every density operator violates a constraint; this
is a concrete consumer of the SDP stopping framework associated with [BrandaoSvore2017]. -/
theorem mmwSdpTwoLevelLargerInstance :
(∀ (η : ℝ), 0 < η → η ≤ 1 → η < 1/2 →
    let C : Fin 2 → Operator 2 := fun i => if i = 0 then !![1, 0; 0, -1] else 1
    let b : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1/2
    let a : ℕ → Fin 2 := fun _ => 1
    (∀ t, mmwWeight 2 (fun s => C (a s)) η t = Real.exp (-η*(t:ℝ)) • (1 : Operator 2)) ∧
      (∀ t, mmwState 2 (fun s => C (a s)) η t = (2:ℝ)⁻¹ • (1 : Operator 2)) ∧
      MmwSdpExactSelection 2 2 C b a η ∧
      MmwSdpPersistentViolation 2 2 C b a η (1/2) (mmwSdpStopRounds η (1/2) 2) ∧
      (∀ σ : Operator 2, IsDensityOperator σ → ∃ i, b i < (Matrix.trace (C i * σ)).re)) := by
  intro η hη hη1 hηε
  (try dsimp only)
  let C := mmwTwoConstraints
  let b : Fin 2 → ℝ := fun i => if i=0 then 0 else 1/2
  let a : ℕ → Fin 2 := fun _ => 1
  have hhistory : (fun s => C (a s)) = (fun _ => (1 : Operator 2)) := by
    funext s
    simp [C, a, mmwTwoConstraints]
  have hw (t : ℕ) := mmw_two_weight η t
  have hr (t : ℕ) := mmw_two_state η t
  have hsel : MmwSdpExactSelection 2 2 C b a η := by
    intro t i
    rw [hhistory, mmw_two_state]
    change (Matrix.trace (mmwTwoConstraints i*mmwTwoDensity)).re-b i ≤
      (Matrix.trace (mmwTwoConstraints 1*mmwTwoDensity)).re-b 1
    rw [mmw_two_traces, mmw_two_traces]
    fin_cases i <;> norm_num [b]
  have hviol : MmwSdpPersistentViolation 2 2 C b a η (1/2) (mmwSdpStopRounds η (1/2) 2) := by
    intro t _ht
    rw [hhistory, mmw_two_state]
    change (1/2 : ℝ) ≤ (Matrix.trace (mmwTwoConstraints 1*mmwTwoDensity)).re-b 1
    rw [mmw_two_traces]
    norm_num [b]
  refine ⟨?_, ?_, hsel, hviol, ?_⟩
  · intro t
    simpa only [← hhistory] using! hw t
  · intro t
    simpa only [← hhistory] using! hr t
  · intro σ hσ
    have hb := mmwSdpLargerBranch 2 2 C b a η (1/2) (by norm_num) hη hη1 hηε
      mmw_two_constraints_bound hsel hviol σ hσ
    exact hb.2

/-- For `0 < η ≤ 1` and `η < ε`, the specified two-constraint instance with unit thresholds
produces a density-operator average whose real constraint traces are at most `1 + ε`. This
is a concrete completion-branch consumer in the SDP setting of [BrandaoSvore2017]. -/
theorem mmwSdpTwoLevelCompletionInstance :
(∀ (η ε : ℝ), 0 < η → η ≤ 1 → η < ε →
    let C : Fin 2 → Operator 2 := fun i => if i = 0 then !![1, 0; 0, -1] else 1
    let b : Fin 2 → ℝ := fun _ => 1
    let a : ℕ → Fin 2 := fun _ => 1
    IsDensityOperator (mmwAverage 2 (mmwSdpStopRounds η ε 2) (fun s => C (a s)) η) ∧
      (∀ i, (Matrix.trace (C i * mmwAverage 2 (mmwSdpStopRounds η ε 2)
          (fun s => C (a s)) η)).re ≤ b i + ε)) := by
  intro η ε hη hη1 hηε
  (try dsimp only)
  let C := mmwTwoConstraints
  let b : Fin 2 → ℝ := fun _ => 1
  let a : ℕ → Fin 2 := fun _ => 1
  have hhistory : (fun s => C (a s)) = (fun _ => (1 : Operator 2)) := by
    funext s
    simp [C, a, mmwTwoConstraints]
  have hsel : MmwSdpExactSelection 2 2 C b a η := by
    intro t i
    rw [hhistory, mmw_two_state]
    change (Matrix.trace (mmwTwoConstraints i*mmwTwoDensity)).re-1 ≤
      (Matrix.trace (mmwTwoConstraints 1*mmwTwoDensity)).re-1
    rw [mmw_two_traces, mmw_two_traces]
    split_ifs <;> norm_num at *
  have hfeas (i : Fin 2) : (Matrix.trace (C i*mmwTwoDensity)).re ≤ b i := by
    change (Matrix.trace (mmwTwoConstraints i*mmwTwoDensity)).re ≤ 1
    rw [mmw_two_traces]
    split_ifs <;> norm_num at *
  have hstop := mmwSdpStopRounds_spec η ε 2 hη hηε
  have hσ := mmwAverage_isDensityOperator 2 (mmwSdpStopRounds η ε 2)
    (fun _ => (1 : Operator 2)) η (by norm_num) hstop.1 (fun _ => Matrix.isHermitian_one)
  rw [mmw_two_average η _ hstop.1] at hσ
  exact mmwSdpCompletionBranch 2 2 C b a η ε mmwTwoDensity (by norm_num) hη hη1 hηε
    mmw_two_constraints_bound hσ hfeas hsel

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
