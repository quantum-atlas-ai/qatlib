/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOASupremacy16.CircuitModel.Source
import Mathlib.Analysis.SpecialFunctions.Complex.Log
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.QAOASupremacy16.LocalGadget

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QAOASupremacy16.CircuitDefs
open Matrix
open scoped BigOperators

variable {ι : Type*}

noncomputable def gadgetDiag (a j : Bool) : ℂ :=
  match a, j with
  | false, false => 1
  | false, true => Complex.I
  | true, false => 1
  | true, true => -Complex.I

def gadgetCost (a j : Bool) : ℕ :=
  match a, j with
  | false, false => 0
  | false, true => 6
  | true, false => 0
  | true, true => 2

theorem gadgetDiag_eq_exp (a j : Bool) :
    gadgetDiag a j
      = Complex.exp (-((Real.pi / 4) * (gadgetCost a j : ℝ)) * Complex.I) := by
  rcases a with _ | _ <;> rcases j with _ | _ <;>
    simp only [gadgetDiag, gadgetCost]
  · simp
  · calc Complex.I = Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) :=
          Complex.exp_pi_div_two_mul_I.symm
      _ = Complex.exp (-((Real.pi / 4) * (6 : ℝ)) * Complex.I) := by
          apply Complex.exp_eq_exp_iff_exists_int.mpr
          exact ⟨1, by push_cast; ring⟩
  · simp
  · calc -Complex.I = Complex.exp (-(Real.pi : ℂ) / 2 * Complex.I) :=
          Complex.exp_neg_pi_div_two_mul_I.symm
      _ = Complex.exp (-((Real.pi / 4) * (2 : ℝ)) * Complex.I) := by
          apply Complex.exp_eq_exp_iff_exists_int.mpr
          exact ⟨0, by push_cast; ring⟩

noncomputable def gadgetState (α : QState (Bool × ι)) : QState (Bool × ι) :=
  fun (a, r) => ∑ j : Bool, Htilde false j * gadgetDiag a j * Plus a * α (j, r)

noncomputable def hadamardOnFst (α : QState (Bool × ι)) : QState (Bool × ι) :=
  fun (a, r) => ∑ j : Bool, Hadamard a j * α (j, r)

theorem hadamardOnFst_smul (c : ℂ) (α : QState (Bool × ι)) :
    hadamardOnFst (c • α) = c • hadamardOnFst α := by
  funext ⟨a, r⟩
  simp only [hadamardOnFst, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gadget_identity (α : QState (Bool × ι)) :
    gadgetState α = ((Real.sqrt 2 : ℂ)⁻¹) • hadamardOnFst α := by
  funext p
  obtain ⟨a, r⟩ := p
  cases a
  · simp [gadgetState, hadamardOnFst, gadgetDiag, Htilde, Hadamard, Plus,
      Pi.smul_apply, smul_eq_mul, mul_assoc]
    ring_nf
    rw [Complex.I_sq]
    ring
  · simp [gadgetState, hadamardOnFst, gadgetDiag, Htilde, Hadamard, Plus,
      Pi.smul_apply, smul_eq_mul, mul_assoc]
    ring_nf
    rw [Complex.I_sq]
    ring

variable [Fintype ι]

noncomputable def normProb (ψ : QState (Bool × ι)) (p : Bool × ι) : ℝ :=
  BornProb ψ p / ∑ q, BornProb ψ q

theorem normProb_smul (c : ℂ) (hc : c ≠ 0) (ψ : QState (Bool × ι))
    (_hZ : 0 < ∑ q, BornProb ψ q) (p : Bool × ι) :
    normProb (c • ψ) p = normProb ψ p := by
  have hk : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  have hnum : ∀ q : Bool × ι, BornProb (c • ψ) q = ‖c‖ ^ 2 * BornProb ψ q := by
    intro q
    have h1 : (c • ψ) q = c * ψ q := by
      rw [Pi.smul_apply, smul_eq_mul]
    unfold BornProb
    rw [h1, norm_mul, mul_pow]
  have hden : (∑ q, BornProb (c • ψ) q) = ‖c‖ ^ 2 * ∑ q, BornProb ψ q := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => hnum q
  unfold normProb
  rw [hnum p, hden, mul_div_mul_left _ _ hk]

theorem gadget_normalized_prob_eq (α : QState (Bool × ι))
    (hZ : 0 < ∑ q, BornProb (hadamardOnFst α) q) (p : Bool × ι) :
    normProb (gadgetState α) p = normProb (hadamardOnFst α) p := by
  have hc : ((Real.sqrt 2 : ℂ)⁻¹) ≠ 0 := by
    have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
    exact inv_ne_zero h2
  rw [gadget_identity]
  exact normProb_smul _ hc _ hZ p

theorem gadget_diagonal_form (a j : Bool) :
    ∃ c : ℕ, c ≤ 6 ∧ gadgetDiag a j
      = Complex.exp (-((Real.pi / 4) * (c : ℝ)) * Complex.I) :=
  ⟨gadgetCost a j, by rcases a <;> rcases j <;> simp [gadgetCost], gadgetDiag_eq_exp a j⟩

end Qatlib.Papers.QAOASupremacy16.LocalGadget
