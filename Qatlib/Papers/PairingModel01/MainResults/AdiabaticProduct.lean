/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PairingModel01.MainResults.Defs
import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.PairingModel01.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator

open Qatlib.Foundations.PureStateMath
  (Operator HamiltonianEvolution hamiltonianEvolution_unitary)
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
  (orderedEvolution orderedEvolution_cocycle orderedEvolution_self)
open Qatlib.Concepts.TrotterFormula.LieStrang (pfComm pfLie)

noncomputable def adiabaticHamiltonian (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ)
    (c : ℝ → ℝ) (t : ℝ) : Operator (2 ^ N) :=
  pairingH0 N ε + ((c t : ℝ) : ℂ) • pairingHI N V

theorem adiabaticHamiltonian_isHermitian (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ)
    (c : ℝ → ℝ) (t : ℝ) : (adiabaticHamiltonian N ε V c t).IsHermitian := by
  show (pairingH0 N ε + ((c t : ℝ) : ℂ) • pairingHI N V)ᴴ
      = (pairingH0 N ε + ((c t : ℝ) : ℂ) • pairingHI N V)
  rw [Matrix.conjTranspose_add, (pairingH0_isHermitian N ε), Matrix.conjTranspose_smul,
    (pairingHI_isHermitian N V)]
  congr 1
  simp

theorem generator_continuous (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ)
    (c : ℝ → ℝ) (hc : Continuous c) :
    Continuous (fun s : ℝ => Complex.I • adiabaticHamiltonian N ε V c s) := by
  unfold adiabaticHamiltonian
  fun_prop

noncomputable def Uad (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ) (c : ℝ → ℝ)
    (t : ℝ) : Operator (2 ^ N) :=
  orderedEvolution (fun s => Complex.I • adiabaticHamiltonian N ε V c s) 0 t

theorem Uad_norm_le_one (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ) (c : ℝ → ℝ)
    (hc : Continuous c) (t : ℝ) : ‖Uad N ε V c t‖ ≤ 1 := by
  have hH : Continuous (fun s : ℝ => adiabaticHamiltonian N ε V c s) := by
    unfold adiabaticHamiltonian
    fun_prop
  have hunit :=
    Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.ordered_evolution_hermitian_unitary
      (Fin (2 ^ N)) (fun u => adiabaticHamiltonian N ε V c u) hH
      (adiabaticHamiltonian_isHermitian N ε V c)
  exact Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one (hunit 0 t)

theorem orderedEvolution_norm_le_one (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ)
    (c : ℝ → ℝ) (hc : Continuous c) (s t : ℝ) :
    ‖orderedEvolution (fun u => Complex.I • adiabaticHamiltonian N ε V c u) s t‖ ≤ 1 := by
  have hH : Continuous (fun s : ℝ => adiabaticHamiltonian N ε V c s) := by
    have hreal : Continuous (fun s : ℝ => ((c s : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hc
    unfold adiabaticHamiltonian
    exact continuous_const.add (hreal.smul continuous_const)
  have hunit :=
    Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.ordered_evolution_hermitian_unitary
      (Fin (2 ^ N)) (fun u => adiabaticHamiltonian N ε V c u) hH
      (adiabaticHamiltonian_isHermitian N ε V c)
  exact Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one (hunit s t)

noncomputable def adiabaticProduct {D : ℕ} (S : ℕ → Operator D) : ℕ → Operator D
  | 0 => 1
  | k + 1 => S k * adiabaticProduct S k

noncomputable def paperFactor (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ) (c : ℝ → ℝ)
    (τ : ℝ) (j : ℕ) : Operator (2 ^ N) :=
  HamiltonianEvolution (adiabaticHamiltonian N ε V c (((j : ℝ) + 1) * τ)) τ

theorem paperFactor_mem_unitaryGroup (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ)
    (c : ℝ → ℝ) (τ : ℝ) (j : ℕ) :
    paperFactor N ε V c τ j ∈ Matrix.unitaryGroup (Fin (2 ^ N)) ℂ := by
  unfold paperFactor
  exact hamiltonianEvolution_unitary
    (H := adiabaticHamiltonian N ε V c (((j : ℝ) + 1) * τ))
    (adiabaticHamiltonian_isHermitian N ε V c _) τ

theorem paperFactor_norm_le_one (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ)
    (c : ℝ → ℝ) (τ : ℝ) (j : ℕ) : ‖paperFactor N ε V c τ j‖ ≤ 1 :=
  Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one
    (paperFactor_mem_unitaryGroup N ε V c τ j)

theorem ordered_product_error_le {D : ℕ} (A : ℝ → Operator D) (hA : Continuous A)
    (S : ℕ → Operator D) (τ δ : ℝ)
    (hS : ∀ j : ℕ, ‖S j‖ ≤ 1) (hU : ∀ s t, ‖orderedEvolution A s t‖ ≤ 1)
    (hlocal : ∀ j : ℕ,
      ‖orderedEvolution A ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) - S j‖ ≤ δ)
    (hδ : 0 ≤ δ) :
    ∀ k : ℕ, ‖orderedEvolution A 0 ((k : ℝ) * τ) - adiabaticProduct S k‖ ≤ (k : ℝ) * δ := by
  intro k
  induction k with
  | zero => simp [adiabaticProduct]
  | succ k ih =>
    have hk1 : ((k + 1 : ℕ) : ℝ) * τ = ((k : ℝ) + 1) * τ := by push_cast; ring
    rw [hk1]
    push_cast
    simp only [adiabaticProduct]
    have hcoc := orderedEvolution_cocycle A hA 0 ((k : ℝ) * τ) (((k : ℝ) + 1) * τ)
    set X := orderedEvolution A ((k : ℝ) * τ) (((k : ℝ) + 1) * τ) with hX
    set Y := orderedEvolution A 0 ((k : ℝ) * τ) with hY
    set P := adiabaticProduct S k with hP
    have hstepk : ‖X - S k‖ ≤ δ := by
      rw [hX]
      exact hlocal k
    have hY1 : ‖Y‖ ≤ 1 := by
      rw [hY]
      exact hU 0 ((k : ℝ) * τ)
    have hcoc' : X * Y = orderedEvolution A 0 (((k : ℝ) + 1) * τ) := by
      rw [hX, hY]
      exact hcoc
    have hid : orderedEvolution A 0 (((k : ℝ) + 1) * τ) - S k * P
        = (X - S k) * Y + S k * (Y - P) := by
      rw [← hcoc']
      noncomm_ring
    rw [hid]
    calc ‖(X - S k) * Y + S k * (Y - P)‖
        ≤ ‖(X - S k) * Y‖ + ‖S k * (Y - P)‖ := norm_add_le _ _
      _ ≤ δ + (k : ℝ) * δ := by
          have h1 : ‖(X - S k) * Y‖ ≤ δ * 1 :=
            (norm_mul_le _ _).trans (mul_le_mul hstepk hY1 (norm_nonneg _) hδ)
          have h2 : ‖S k * (Y - P)‖ ≤ 1 * ‖Y - P‖ :=
            (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (hS k) (norm_nonneg _))
          have h3 : ‖Y - P‖ ≤ (k : ℝ) * δ := by
            rw [hY, hP]
            exact ih
          have hk0 : (0 : ℝ) ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg k) hδ
          linarith [h1, h2, h3, hk0]
      _ = ((k : ℝ) + 1) * δ := by ring

theorem eq3_adiabatic_product (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ) (c : ℝ → ℝ)
    (hc : Continuous c) (τ δ : ℝ) (hδ : 0 ≤ δ)
    (hlocal : ∀ j : ℕ,
      ‖orderedEvolution (fun s => Complex.I • adiabaticHamiltonian N ε V c s)
          ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) - paperFactor N ε V c τ j‖ ≤ δ)
    (k : ℕ) :
    ‖Uad N ε V c ((k : ℝ) * τ) - adiabaticProduct (paperFactor N ε V c τ) k‖
      ≤ (k : ℝ) * δ :=
  ordered_product_error_le (fun s => Complex.I • adiabaticHamiltonian N ε V c s)
    (generator_continuous N ε V c hc) (paperFactor N ε V c τ) τ δ
    (paperFactor_norm_le_one N ε V c τ) (orderedEvolution_norm_le_one N ε V c hc)
    hlocal hδ k

theorem eq3_error_quadratic (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ) (c : ℝ → ℝ)
    (hc : Continuous c) (τ L : ℝ) (hL : 0 ≤ L)
    (hlocal : ∀ j : ℕ,
      ‖orderedEvolution (fun s => Complex.I • adiabaticHamiltonian N ε V c s)
          ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) - paperFactor N ε V c τ j‖ ≤ L * τ ^ 2 / 2)
    (k : ℕ) :
    ‖Uad N ε V c ((k : ℝ) * τ) - adiabaticProduct (paperFactor N ε V c τ) k‖
      ≤ (k : ℝ) * L * τ ^ 2 / 2 := by
  have hδ : 0 ≤ L * τ ^ 2 / 2 := by positivity
  have h := eq3_adiabatic_product N ε V c hc τ (L * τ ^ 2 / 2) hδ hlocal k
  calc ‖Uad N ε V c ((k : ℝ) * τ) - adiabaticProduct (paperFactor N ε V c τ) k‖
      ≤ (k : ℝ) * (L * τ ^ 2 / 2) := h
    _ = (k : ℝ) * L * τ ^ 2 / 2 := by ring

theorem eq3_factor_trotter (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ) (c : ℝ → ℝ)
    (τ : ℝ) (j : ℕ) :
    ‖HamiltonianEvolution (pairingH0 N ε) τ
        * HamiltonianEvolution (((c (((j : ℝ) + 1) * τ) : ℝ) : ℂ) • pairingHI N V) τ
        - HamiltonianEvolution (adiabaticHamiltonian N ε V c (((j : ℝ) + 1) * τ)) τ‖
      ≤ τ ^ 2 / 2 * ‖pfComm (pairingH0 N ε)
          (((c (((j : ℝ) + 1) * τ) : ℝ) : ℂ) • pairingHI N V)‖ := by
  have hsmul : (((c (((j : ℝ) + 1) * τ) : ℝ) : ℂ) • pairingHI N V).IsHermitian := by
    show (((c (((j : ℝ) + 1) * τ) : ℝ) : ℂ) • pairingHI N V)ᴴ
        = ((c (((j : ℝ) + 1) * τ) : ℝ) : ℂ) • pairingHI N V
    rw [Matrix.conjTranspose_smul, (pairingHI_isHermitian N V)]
    congr 1
    simp
  have h := Qatlib.Concepts.TrotterFormula.LieStrang.product_formula_lie_two_term
    (2 ^ N) (((c (((j : ℝ) + 1) * τ) : ℝ) : ℂ) • pairingHI N V) (pairingH0 N ε) τ
    hsmul (pairingH0_isHermitian N ε)
  have h' : ‖pfLie (((c (((j : ℝ) + 1) * τ) : ℝ) : ℂ) • pairingHI N V) (pairingH0 N ε) τ
        - HamiltonianEvolution (pairingH0 N ε
            + ((c (((j : ℝ) + 1) * τ) : ℝ) : ℂ) • pairingHI N V) τ‖
      ≤ τ ^ 2 / 2 * ‖pfComm (pairingH0 N ε)
          (((c (((j : ℝ) + 1) * τ) : ℝ) : ℂ) • pairingHI N V)‖ := by
    rw [add_comm (((c (((j : ℝ) + 1) * τ) : ℝ) : ℂ) • pairingHI N V) (pairingH0 N ε)] at h
    exact h
  simpa [pfLie, adiabaticHamiltonian] using! h'

end Qatlib.Papers.PairingModel01.MainResults
