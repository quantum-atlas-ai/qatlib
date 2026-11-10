/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.CenterTransport.PhysicalCoefficients
import Qatlib.Papers.LowEnergyProd24.LocalModel.FiniteBudget
import Qatlib.Papers.LowEnergyProd24.ImaginaryLeak.NestedLeakage
import Qatlib.Papers.LowEnergyProd24.RetainedError.CutoffChain
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.RetainedError.Physical
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.CenterTransport
open Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}
local instance : NormedAlgebra ℝ (Matrix (Register N) (Register N) ℂ) := .restrictScalars ℝ ℂ _

def nested (h : PhysicalHamiltonian N R M k d J) (seed : Fin M) : List (Fin M) → Matrix (Register N) (Register N) ℂ
  | [] => h.grouped seed
  | a::xs => h.grouped a*nested h seed xs-nested h seed xs*h.grouped a

theorem nested_centered (h : PhysicalHamiltonian N R M k d J) (seed : Fin M) (xs : List (Fin M)) :
    nested h seed xs=RetainedError.nested h.normalized seed xs+
      if xs=[] then (h.groupCenter seed : ℂ) • 1 else 0 := by
  induction xs with
  | nil =>
    simp only [nested, RetainedError.nested]
    rw [h.normalized_grouped]
    exact (sub_add_cancel (h.grouped seed) ((h.groupCenter seed : ℂ) • 1)).symm
  | cons a xs ih =>
    have ha : h.grouped a=h.normalized.grouped a+(h.groupCenter a : ℂ) • 1 := by
      rw [h.normalized_grouped]
      abel
    have hz : Central (if xs=[] then (h.groupCenter seed : ℂ) • (1 : Matrix (Register N) (Register N) ℂ) else 0) := by
      intro A
      split_ifs
      · exact scalar_identity_central _ _
      · exact Commute.zero_left A
    rw [nested, ih, ha]
    change ad (h.normalized.grouped a+(h.groupCenter a : ℂ) • 1)
      (RetainedError.nested h.normalized seed xs+(if xs=[] then (h.groupCenter seed : ℂ) • 1 else 0))=_
    have hza : Central ((h.groupCenter a : ℂ) • (1 : Matrix (Register N) (Register N) ℂ)) := by
      intro A
      exact scalar_identity_central _ A
    rw [ad_add_central_left _ _ _ hza]
    have he := adIter_add_central_right (h.normalized.grouped a) (RetainedError.nested h.normalized seed xs)
      (if xs=[] then (h.groupCenter seed : ℂ) • 1 else 0) hz 1 (by norm_num)
    simpa only [adIter, ad, RetainedError.nested, List.cons_ne_nil, if_false, add_zero] using he

theorem original_offdiagonal_centered (h : PhysicalHamiltonian N R M k d J) (seed : Fin M)
    (xs : List (Fin M)) (Δ Λ : ℝ) (hΔ : Δ ≤ Λ) :
    high h.total h.total_hermitian Λ*nested h seed xs*low h.total h.total_hermitian Δ =
      high h.total h.total_hermitian Λ*RetainedError.nested h.normalized seed xs*low h.total h.total_hermitian Δ := by
  have hz : high h.total h.total_hermitian Λ*
      (if xs=[] then (h.groupCenter seed : ℂ) • (1 : Matrix (Register N) (Register N) ℂ) else 0)*
        low h.total h.total_hermitian Δ=0 := by
    split_ifs
    · simp only [mul_smul_comm, smul_mul_assoc, mul_one]
      rw [separated_orthogonal h.total h.total_hermitian Δ Λ hΔ, smul_zero]
    · simp only [mul_zero, zero_mul]
  rw [nested_centered, mul_add, add_mul, hz, add_zero]

theorem original_nested_leakage (h : PhysicalHamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ) (seed : Fin M)
    (hL : (h.labels seed).card ≤ L) (xs : List (Fin M)) (Δ Λ : ℝ) (hΔ : Δ ≤ Λ) :
    ‖high h.total h.total_hermitian Λ*nested h seed xs*low h.total h.total_hermitian Δ‖ ≤
      Real.exp (-(1/(2*J*k*d))*(Λ-Δ))*sourceEll L k d J xs.length := by
  rw [original_offdiagonal_centered h seed xs Δ Λ hΔ]
  calc
    _ ≤ Real.exp (-(1/(2*J*k*d))*(Λ-Δ))*
        ‖weighted h.total (RetainedError.nested h.normalized seed xs) (1/(2*J*k*d))‖ :=
      weighted_leakage h.total (RetainedError.nested h.normalized seed xs) h.total_hermitian Δ Λ
        (1/(2*J*k*d)) (by positivity)
    _ = Real.exp (-(1/(2*J*k*d))*(Λ-Δ))*
        ‖weighted h.normalized.total (RetainedError.nested h.normalized seed xs) (1/(2*J*k*d))‖ := by
      rw [physical_weight_centered]
    _ ≤ _ := mul_le_mul_of_nonneg_left (actual_weighted_source_ell h.normalized hJ hk hd L seed hL xs) (Real.exp_pos _).le

theorem asBounded_nested (h : PhysicalHamiltonian N R M k d J) (seed : Fin M) (xs : List (Fin M)) :
    RetainedError.nested h.asBounded seed xs=nested h seed xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [RetainedError.nested, nested, ih]; rfl

theorem original_excursion_reverse (h : PhysicalHamiltonian N R M k d J) (seed : Fin M)
    (xs : List (Fin M)) (Δ Λ : ℝ) :
    ‖low h.total h.total_hermitian Δ*nested h seed xs*high h.total h.total_hermitian Λ‖ =
      ‖high h.total h.total_hermitian Λ*nested h seed xs*low h.total h.total_hermitian Δ‖ := by
  have he := RetainedError.actual_excursion_reverse h.asBounded seed xs Δ Λ
  rw [asBounded_nested] at he
  exact he
end Qatlib.Papers.LowEnergyProd24.RetainedError.Physical
