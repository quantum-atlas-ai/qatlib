/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.SampleBudget.QuadraticShadowSourceParametersStat
import Qatlib.Concepts.ShadowModels.ShadowVariance.PauliQuadraticVarianceSharpSubgoalHuan
import Mathlib.Data.Finset.Fold

/-!
# Explicit quadratic shadow sample budgets

This module derives simultaneous error guarantees for quadratic shadow medians using explicit
block and repetition counts. `quadraticShadowSourceParameters_computed_variance` uses
conditional and kernel variances, while `quadraticShadowSourceParametersSubgoal` substitutes
support and operator norm bounds for Pauli pair observables. See [HuangKuengPreskill2020] for
background.

## Main statements

* `quadraticShadowSourceParameters_computed_variance`: a failure bound from computed variance
  parameters.
* `quadraticShadowSourceParametersSubgoal`: the support-based Pauli pair budget guarantee.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.ShadowVariance
open Qatlib.Concepts.ShadowModels.UStatBackend

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ShadowModels.SampleBudget

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false

/-- The median tail factor `2^(2*r+1) * (1/16)^(r+1)` equals `1 / (8 * 4^r)`. -/
private theorem source_median_constant (r : ℕ) :
    (2 : ℝ)^(2*r+1)*(1/16 : ℝ)^(r+1) = 1/(8*(4 : ℝ)^r) := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    have he : 2*(r+1)+1 = (2*r+1)+2 := by omega
    rw [he, pow_add, pow_succ (1/16 : ℝ), pow_succ (4 : ℝ)]
    norm_num
    calc
      _ = ((2 : ℝ)^(2*r+1)*(1/16 : ℝ)^(r+1))/4 := by ring
      _ = _ := by rw [ih]; ring

/-- Choosing `r = Nat.log 4 (8*D*Nat.ceil (1/δ)) + 1` makes `D` times the median tail factor at
most any positive `δ`. -/
private theorem source_group_tail (D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    let r := Nat.log 4 (8*D*Nat.ceil (1/δ))+1
    (D : ℝ)*(2 : ℝ)^(2*r+1)*(1/16 : ℝ)^(r+1) ≤ δ := by
  (try dsimp only)
  rw [mul_assoc, source_median_constant]
  have hc : 1/δ ≤ (Nat.ceil (1/δ) : ℝ) := Nat.le_ceil _
  have hd : (1 : ℝ) ≤ δ*(Nat.ceil (1/δ) : ℝ) :=
    by simpa only [mul_comm] using! (div_le_iff₀ hδ).1 hc
  have hl : (8*D*Nat.ceil (1/δ) : ℕ) < 4^(Nat.log 4 (8*D*Nat.ceil (1/δ))+1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hl' : (8 : ℝ)*D*(Nat.ceil (1/δ) : ℝ) <
      (4 : ℝ)^(Nat.log 4 (8*D*Nat.ceil (1/δ))+1) := by exact_mod_cast hl
  have he := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 8*D by positivity)
  have ht := mul_le_mul_of_nonneg_left (le_of_lt hl') (le_of_lt hδ)
  have hp : (0 : ℝ) < (4 : ℝ)^(Nat.log 4 (8*D*Nat.ceil (1/δ))+1) := by positivity
  rw [mul_one_div, div_le_iff₀ (mul_pos (by norm_num) hp)]
  nlinarith

/-- For a nonempty finite family of Hermitian quadratic observables and `0 < ε ≤ 1`, the
displayed variance-based block size and logarithmic repetition count bound the probability
of any estimation error exceeding `ε` by `δ > 0`. -/
theorem quadraticShadowSourceParameters_computed_variance
    (n D : ℕ)
    (O : Fin D → Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ)
    (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ) (ε δ : ℝ)
    (hO : ∀ z, (O z).IsHermitian) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hD : 0 < D) :
    let f := fun z => max 1 (max
      (pairConditionalVariance (tensorPauliLaw n ρ hρ) (quadraticShadowKernel n (O z)))
      (Real.sqrt (pairKernelVariance (tensorPauliLaw n ρ hρ) (quadraticShadowKernel n (O z)))))
    let B := (Finset.univ : Finset (Fin D)).fold max 0 f
    let m := Nat.ceil (140*B/ε^2)
    let r := Nat.log 4 (8*D*Nat.ceil (1/δ))+1
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool =>
      ∃ z, ε < |quadraticShadowMedian n m r (O z) ω -
        (Matrix.trace (O z * TensorGate ρ ρ)).re|),
      ∏ b, (tensorPauliLaw n ρ hρ).probOf (ω b)) ≤ δ := by
  let f := fun z : Fin D => max 1 (max
    (pairConditionalVariance (tensorPauliLaw n ρ hρ) (quadraticShadowKernel n (O z)))
    (Real.sqrt (pairKernelVariance (tensorPauliLaw n ρ hρ) (quadraticShadowKernel n (O z)))))
  let B := (Finset.univ : Finset (Fin D)).fold max 0 f
  let m := Nat.ceil (140*B/ε^2)
  let r := Nat.log 4 (8*D*Nat.ceil (1/δ))+1
  change (∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool =>
      ∃ z, ε < |quadraticShadowMedian n m r (O z) ω -
        (Matrix.trace (O z*TensorGate ρ ρ)).re|),
      ∏ b, (tensorPauliLaw n ρ hρ).probOf (ω b)) ≤ δ
  have hzB (z : Fin D) : f z ≤ B :=
    (Finset.le_fold_max (f z)).mpr (Or.inr ⟨z, Finset.mem_univ z, le_rfl⟩)
  have hf1 (z : Fin D) : 1 ≤ f z := le_max_left _ _
  have hB1 : 1 ≤ B := (hf1 ⟨0, hD⟩).trans (hzB _)
  have he2 : 0 < ε^2 := sq_pos_of_pos hε
  have he1 : ε^2 ≤ 1 := by nlinarith
  have hmc : 140*B/ε^2 ≤ (m : ℝ) := Nat.le_ceil _
  have hm : 2 ≤ m := by
    have hb : (140 : ℝ) ≤ 140*B/ε^2 := by
      rw [le_div_iff₀ he2]
      nlinarith
    have hm' : (2 : ℝ) ≤ m := by linarith
    exact_mod_cast hm'
  have hbudget (z : Fin D) :
      (O z).IsHermitian ∧
      140 * max
        (pairConditionalVariance (tensorPauliLaw n ρ hρ)
          (quadraticShadowKernel n (O z)))
        (Real.sqrt (pairKernelVariance (tensorPauliLaw n ρ hρ)
          (quadraticShadowKernel n (O z)))) / ε^2 ≤ (m : ℝ) := by
    refine ⟨hO z, ?_⟩
    have hv : max
        (pairConditionalVariance (tensorPauliLaw n ρ hρ)
          (quadraticShadowKernel n (O z)))
        (Real.sqrt (pairKernelVariance (tensorPauliLaw n ρ hρ)
          (quadraticShadowKernel n (O z)))) ≤ B :=
      (le_max_right 1 _).trans (hzB z)
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hv (by norm_num)) (le_of_lt he2)).trans hmc
  convert! (quadratic_same_records_source_budget n m r (Fin D) ρ hρ
    (fun z => O z) ε hm hε hε1 hbudget).trans
      (by simpa only [Fintype.card_fin] using! source_group_tail D δ hδ) using 1
  apply Finset.sum_congr
  · ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro ω _
    rfl

/-- The explicit support and operator norm sample budgets in
`QuadraticShadowSourceParametersSubgoal` give the stated simultaneous quadratic shadow error
guarantee. -/
theorem quadraticShadowSourceParametersSubgoal : QuadraticShadowSourceParametersSubgoal := by
  intro n D q ww c S₁ S₂ ρ hρ ε δ hs hn hε hε1 hδ _hδ1 hD
  let O := fun z : Fin D => pauliPairObservable n q (ww z) (c z)
  let f := fun z : Fin D => (4 : ℝ)^max (S₁ z).card (S₂ z).card * ‖O z‖^2
  let B := (Finset.univ : Finset (Fin D)).fold max 0 f
  let m := Nat.ceil (140 * B / ε^2)
  let r := Nat.log 4 (8 * D * Nat.ceil (1 / δ)) + 1
  change (∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool =>
    ∃ z, ε < |quadraticShadowMedian n m r (O z) ω -
      (Matrix.trace (O z * TensorGate ρ ρ)).re|),
    ∏ b, (tensorPauliLaw n ρ hρ).probOf (ω b)) ≤ δ
  have hzB (z : Fin D) : f z ≤ B :=
    (Finset.le_fold_max (f z)).mpr (Or.inr ⟨z, Finset.mem_univ z, le_rfl⟩)
  have hf1 (z : Fin D) : 1 ≤ f z := by
    have hnorm : 1 ≤ ‖O z‖ := hn z
    have hnorm2 : 1 ≤ ‖O z‖^2 := by nlinarith
    have hpow : 1 ≤ (4 : ℝ)^max (S₁ z).card (S₂ z).card := one_le_pow₀ (by norm_num)
    exact hnorm2.trans (by simpa only [one_mul] using!
      mul_le_mul_of_nonneg_right hpow (sq_nonneg ‖O z‖))
  have hB1 : 1 ≤ B := (hf1 ⟨0, hD⟩).trans (hzB _)
  have he2 : 0 < ε^2 := sq_pos_of_pos hε
  have he1 : ε^2 ≤ 1 := by nlinarith
  have hmc : 140 * B / ε^2 ≤ (m : ℝ) := Nat.le_ceil _
  have hm : 2 ≤ m := by
    have hb : (140 : ℝ) ≤ 140 * B / ε^2 := by
      rw [le_div_iff₀ he2]
      nlinarith
    have hm' : (2 : ℝ) ≤ m := by linarith
    exact_mod_cast hm'
  have hbudget (z : Fin D) : (O z).IsHermitian ∧
      140 * max
        (pairConditionalVariance (tensorPauliLaw n ρ hρ) (quadraticShadowKernel n (O z)))
        (Real.sqrt (pairKernelVariance (tensorPauliLaw n ρ hρ) (quadraticShadowKernel n (O z)))) /
        ε^2 ≤ (m : ℝ) := by
    have hsharp := pauliQuadraticVarianceSharpSubgoal n q (ww z) (c z) (S₁ z) (S₂ z) ρ hρ
      (hs z) (hn z)
    let record0 : Fin n → Fin 3 × Bool := fun _ => (0, false)
    refine ⟨(pauli_pair_kernel_and_estimand n q (ww z) (c z) ρ ρ record0 record0).1, ?_⟩
    have hv : max
        (pairConditionalVariance (tensorPauliLaw n ρ hρ) (quadraticShadowKernel n (O z)))
        (Real.sqrt (pairKernelVariance (tensorPauliLaw n ρ hρ) (quadraticShadowKernel n (O z)))) ≤ B :=
      (max_le hsharp.1 hsharp.2).trans (hzB z)
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv (by norm_num))
      he2.le).trans hmc
  convert! (quadratic_same_records_source_budget n m r (Fin D) ρ hρ O ε hm hε hε1 hbudget).trans
    (by simpa only [Fintype.card_fin] using! source_group_tail D δ hδ) using 1
  apply Finset.sum_congr
  · ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro ω _
    rfl

end Qatlib.Concepts.ShadowModels.SampleBudget
