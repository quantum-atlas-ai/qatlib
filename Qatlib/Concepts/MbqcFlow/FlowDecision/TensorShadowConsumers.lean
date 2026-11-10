/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliShadowStatistics
open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open scoped ComplexOrder

set_option maxHeartbeats 4000000

noncomputable def tensorShadowBellState : QState (Fin 4) :=
  relabelState (bitVecEquiv 2)
    ((Real.sqrt 2 : ℂ)⁻¹ • (Ket (ZeroStr 2) + Ket (fun _ : Fin 2 => true)))

noncomputable def tensorShadowBell : Operator 4 := outerProduct tensorShadowBellState

theorem tensorShadow_relabel_ket {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (x : I) :
    relabelState e (Ket x) = Ket (e x) := by
  ext y
  have he : e.symm y = x ↔ y = e x := by
    constructor
    · intro h
      simpa using congrArg e h
    · intro h
      simp [h]
  simp only [relabelState, Function.comp_apply, Qatlib.Foundations.PureStateMath.Ket, he]

theorem tensorShadowBellState_explicit :
    tensorShadowBellState = ![(Real.sqrt 2 : ℂ)⁻¹, 0, 0, (Real.sqrt 2 : ℂ)⁻¹] := by
  have ht : bitVecEquiv 2 (fun _ : Fin 2 => true) = 3 := rfl
  unfold tensorShadowBellState
  have hr : relabelState (bitVecEquiv 2)
      ((Real.sqrt 2 : ℂ)⁻¹ • (Ket (ZeroStr 2) + Ket (fun _ : Fin 2 => true))) =
      (Real.sqrt 2 : ℂ)⁻¹ •
        (relabelState (bitVecEquiv 2) (Ket (ZeroStr 2)) +
          relabelState (bitVecEquiv 2) (Ket (fun _ : Fin 2 => true))) := rfl
  rw [hr, tensorShadow_relabel_ket, tensorShadow_relabel_ket,
    bitVecEquiv_zeroStr, ht]
  ext i
  fin_cases i <;> simp [Qatlib.Foundations.PureStateMath.Ket]

theorem tensorShadowBell_density : IsDensityOperator tensorShadowBell := by
  apply isDensityOperator_outerProduct
  rw [tensorShadowBellState_explicit]
  unfold Normalized
  simp only [Fin.sum_univ_succ]
  have hs : ‖(Real.sqrt 2 : ℂ)⁻¹‖ ^ 2 = 1 / 2 := by
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

private theorem tensorShadowBits_zero : (bitVecEquiv 2).symm 0 = ![false, false] := by
  apply (bitVecEquiv 2).injective
  rw [Equiv.apply_symm_apply]
  rfl

private theorem tensorShadowBits_one : (bitVecEquiv 2).symm 1 = ![false, true] := by
  apply (bitVecEquiv 2).injective
  rw [Equiv.apply_symm_apply]
  rfl

private theorem tensorShadowBits_two :
    (bitVecEquiv 2).symm ⟨2, by decide⟩ = ![true, false] := by
  apply (bitVecEquiv 2).injective
  rw [Equiv.apply_symm_apply]
  rfl

private theorem tensorShadowBits_three :
    (bitVecEquiv 2).symm ⟨3, by decide⟩ = ![true, true] := by
  apply (bitVecEquiv 2).injective
  rw [Equiv.apply_symm_apply]
  rfl

private theorem tensorShadowPauliTwo : pauliMatrix ⟨2, by decide⟩ = pauliZ := rfl

theorem tensorShadowWordTwo_explicit (a : Fin 3) :
    tensorPauliWord 2 (fun _ => some a) =
      if a = 0 then !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
      else if a = 1 then !![0, 0, 0, -1; 0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0]
      else !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1] := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [tensorPauliWord, tensorPauliWordFactor, tensorPauliProduct, relabelGate,
      pauliProductDensity, Fin.prod_univ_two, tensorShadowBits_zero, tensorShadowBits_one,
      tensorShadowBits_two, tensorShadowBits_three, boolEquivFin2, pauliX, pauliY, pauliZ,
      tensorShadowPauliTwo, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]

theorem tensorShadowBell_word_trace (a : Fin 3) :
    (Matrix.trace (tensorPauliWord 2 (fun _ => some a) * tensorShadowBell)).re =
      if a = 1 then -1 else 1 := by
  have hc := inv_sqrt2_mul_self
  have sum4 : ∀ f : Fin 4 → ℂ, ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
    intro f
    simp [Fin.sum_univ_succ, add_assoc]
  change (∑ i : Fin 4, ∑ j : Fin 4,
    tensorPauliWord 2 (fun _ => some a) i j * tensorShadowBell j i).re = _
  rw [tensorShadowWordTwo_explicit, tensorShadowBell, tensorShadowBellState_explicit]
  simp only [outerProduct_apply, sum4]
  fin_cases a <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, hc] <;> norm_num

theorem tensor_shadow_bell_correlations_consumer :
    IsDensityOperator tensorShadowBell ∧
    (∀ (hBell : IsDensityOperator tensorShadowBell) (a : Fin 3),
      let w := fun _ : Fin 2 => some a
      (tensorPauliLaw 2 tensorShadowBell hBell).expect (tensorPauliValue w) =
        (if a = 1 then -1 else 1) ∧
      (tensorPauliLaw 2 tensorShadowBell hBell).variance (tensorPauliValue w) = 8) := by
  refine ⟨tensorShadowBell_density, ?_⟩
  intro hBell a
  have h := tensor_pauli_word_exact_moments 2 tensorShadowBell hBell (fun _ => some a)
  have hw : tensorPauliWeight (fun _ : Fin 2 => some a) = 2 := by
    norm_num [tensorPauliWeight]
  refine ⟨h.2.1.trans (tensorShadowBell_word_trace a), ?_⟩
  rw [h.2.2.2, hw, tensorShadowBell_word_trace]
  split_ifs <;> norm_num

theorem tensor_shadow_local_energy_consumer (n M L K : ℕ)
    (ρ : Operator (2 ^ n)) (hρ : IsDensityOperator ρ)
    (w : Fin M → Fin n → Option (Fin 3)) (c : Fin M → ℝ) (ε : ℝ)
    (hL : 0 < L) (hK : 0 < K) (hε : 0 < ε)
    (hw : ∀ j, tensorPauliWeight (w j) ≤ 2)
    (hbud : 36 * (M : ℝ) * (∑ j, (c j) ^ 2) ≤ (L : ℝ) * ε ^ 2) :
    let p := tensorPauliLaw n ρ hρ
    let f := fun o => ∑ j, c j * tensorPauliValue (w j) o
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin K → Fin L → (Fin n → Fin 3 × Bool) =>
      ε < |p.medianOfMeans f ω -
        (Matrix.trace ((∑ j, (c j : ℂ) • tensorPauliWord n (w j)) * ρ)).re|),
      ∏ k, p.probOf (ω k)) ≤ 3 ^ (K / 2) / 2 ^ K := by
  let p := tensorPauliLaw n ρ hρ
  let f := fun o => ∑ j, c j * tensorPauliValue (w j) o
  have hstat := tensor_pauli_linear_observable_variance n M ρ hρ w c
  have hpow : ∀ j, (3 : ℝ) ^ tensorPauliWeight (w j) ≤ 9 := by
    intro j
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (hw j)
    norm_num at hh
    exact hh
  have hsum : (∑ j, (c j) ^ 2 * (3 : ℝ) ^ tensorPauliWeight (w j)) ≤
      9 * ∑ j, (c j) ^ 2 := by
    calc _ ≤ ∑ j, (c j) ^ 2 * 9 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpow j) (sq_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hv : 4 * p.variance f ≤ (L : ℝ) * ε ^ 2 := by
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have hh := mul_le_mul_of_nonneg_left hsum hM
    have ht := hstat.2
    change p.variance f ≤ _ at ht
    nlinarith
  have hh := p.median_of_means_concentration f hL hK ε hε hv
  rw [show p.expect f =
    (Matrix.trace ((∑ j, (c j : ℂ) • tensorPauliWord n (w j)) * ρ)).re from hstat.1] at hh
  have hfresh : ∀ ω : Fin K → Fin L → (Fin n → Fin 3 × Bool),
      (∏ k : Fin K, ∏ l : Fin L,
        (Matrix.trace (tensorPauliKraus n (ω k l) * ρ * (tensorPauliKraus n (ω k l))ᴴ)).re) =
        ∏ k : Fin K, p.probOf (ω k) :=
    fun ω => (tensor_pauli_fresh_born_and_cost n L K ρ hρ ω).1
  calc _ = (∑ ω ∈ Finset.univ.filter (fun ω : Fin K → Fin L → (Fin n → Fin 3 × Bool) =>
        ε < |p.medianOfMeans f ω -
          (Matrix.trace ((∑ j, (c j : ℂ) • tensorPauliWord n (w j)) * ρ)).re|),
        ∏ k : Fin K, ∏ l : Fin L,
          (Matrix.trace (tensorPauliKraus n (ω k l) * ρ * (tensorPauliKraus n (ω k l))ᴴ)).re) :=
      Finset.sum_congr rfl fun ω _ => (hfresh ω).symm
    _ ≤ _ := by simpa only [hfresh] using hh

end Qatlib.Concepts.MbqcFlow.FlowDecision
