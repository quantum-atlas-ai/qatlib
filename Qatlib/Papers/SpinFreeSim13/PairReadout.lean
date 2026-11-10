/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinFreeSim13.PairProjector
import Qatlib.Foundations.TensorRegisters.SwapReadout
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Papers.SpinFreeSim13.PairReadout
open Matrix
open scoped BigOperators
open Qatlib.Papers.SpinFreeSim13.PairProjector
open Qatlib.Foundations.TensorRegisters
variable {I : Type*} [Fintype I] [DecidableEq I]

def input (ψ : I × I → ℂ) (z : Bool × (I × I)) : ℂ := if z.1 then 0 else ψ z.2

def output (ψ : I × I → ℂ) : Bool × (I × I) → ℂ := SwapReadout.circuit *ᵥ input ψ

theorem output_sector (ψ : I × I → ℂ) (label : Bool) (i j : I) :
    output ψ (label,(i,j)) = (sector label *ᵥ ψ) (i,j) := by
  rw [output, SwapReadout.circuit, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      SwapReadout.hadFirst_apply]
  rw [SwapReadout.controlledSwap_apply, SwapReadout.controlledSwap_apply]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [SwapReadout.hadFirst_apply, SwapReadout.hadFirst_apply, sector_apply]
  cases label <;> simp [input, sign]
  · linear_combination SwapReadout.r_mul_r * (ψ (i,j) + ψ (j,i))
  · linear_combination SwapReadout.r_mul_r * (ψ (i,j) - ψ (j,i))

theorem readout_unitary : SwapReadout.circuit (I:=I) ∈ Matrix.unitaryGroup (Bool × (I × I)) ℂ :=
  SwapReadout.circuit_unitary

def branch (ψ : I × I → ℂ) (label : Bool) : EuclideanSpace ℂ (I × I) :=
  WithLp.toLp 2 (sector label *ᵥ ψ)

def weight (ψ : I × I → ℂ) (label : Bool) : ℝ :=
  ∑ p : I × I, Complex.normSq (output ψ (label,p))

theorem weight_eq_norm (ψ : I × I → ℂ) (label : Bool) :
    weight ψ label = ‖branch ψ label‖^2 := by
  unfold weight
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro p _
  rcases p with ⟨i,j⟩
  rw [output_sector]
  exact (Complex.sq_norm _).symm

omit [DecidableEq I] in

theorem input_norm (ψ : I × I → ℂ) :
    ‖(WithLp.toLp 2 (input ψ) : EuclideanSpace ℂ (Bool × (I × I)))‖^2 =
      ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (I × I))‖^2 := by
  simp [EuclideanSpace.norm_sq_eq, input, Fintype.sum_prod_type]

theorem output_norm (ψ : I × I → ℂ) :
    ‖(WithLp.toLp 2 (output ψ) : EuclideanSpace ℂ (Bool × (I × I)))‖ =
      ‖(WithLp.toLp 2 (input ψ) : EuclideanSpace ℂ (Bool × (I × I)))‖ := by
  change ‖Matrix.toEuclideanCLM (n:=Bool × (I × I)) (𝕜:=ℂ) SwapReadout.circuit
    (WithLp.toLp 2 (input ψ))‖ = _
  apply ContinuousLinearMap.norm_map_of_mem_unitary
  apply Unitary.mem_iff.mpr
  constructor
  · simpa only [← map_star, ← map_mul, map_one] using
      congrArg (Matrix.toEuclideanCLM (n:=Bool × (I × I)) (𝕜:=ℂ))
        (Unitary.star_mul_self_of_mem (readout_unitary (I:=I)))
  · simpa only [← map_star, ← map_mul, map_one] using
      congrArg (Matrix.toEuclideanCLM (n:=Bool × (I × I)) (𝕜:=ℂ))
        (Unitary.mul_star_self_of_mem (readout_unitary (I:=I)))

theorem total_weight (ψ : I × I → ℂ)
    (hψ : ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (I × I))‖=1) :
    weight ψ false + weight ψ true = 1 := by
  have h := input_norm ψ
  rw [hψ] at h
  have ho := output_norm ψ
  have hs : ‖(WithLp.toLp 2 (output ψ) : EuclideanSpace ℂ (Bool × (I × I)))‖^2=1 := by
    rw [ho]; simpa only [one_pow] using h
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_bool] at hs
  simpa only [weight, Complex.sq_norm, add_comm] using hs

def normalizedBranch (ψ : I × I → ℂ) (label : Bool) : EuclideanSpace ℂ (I × I) :=
  ((Real.sqrt (weight ψ label) : ℂ)⁻¹) • branch ψ label

theorem normalizedBranch_norm (ψ : I × I → ℂ) (label : Bool) (hp : 0 < weight ψ label) :
    ‖normalizedBranch ψ label‖=1 := by
  have hn : ‖branch ψ label‖ ≠ 0 := by
    rw [weight_eq_norm] at hp
    exact ne_of_gt (by nlinarith [norm_nonneg (branch ψ label)] : 0 < ‖branch ψ label‖)
  rw [normalizedBranch, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), weight_eq_norm,
    Real.sqrt_sq (norm_nonneg _), inv_mul_cancel₀ hn]

theorem normalizedBranch_symmetry (ψ : I × I → ℂ) (label : Bool) :
    swapMatrix *ᵥ (normalizedBranch ψ label).ofLp =
      sign label • (normalizedBranch ψ label).ofLp := by
  change swapMatrix *ᵥ (((Real.sqrt (weight ψ label) : ℂ)⁻¹) • (sector label *ᵥ ψ)) = _
  rw [Matrix.mulVec_smul, projected_symmetry, smul_comm]
  rfl

def distinctInput : Bool × Bool → ℂ := Pi.single (false,true) 1

theorem distinctInput_norm :
    ‖(WithLp.toLp 2 distinctInput : EuclideanSpace ℂ (Bool × Bool))‖=1 := by
  change ‖(PiLp.single 2 (false,true) (1:ℂ) : EuclideanSpace ℂ (Bool × Bool))‖=1
  simp

theorem distinctInput_weight (label : Bool) : weight distinctInput label = (1:ℝ)/2 := by
  unfold weight
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, output_sector]
  cases label <;> norm_num [sector_apply, distinctInput, sign]
end Qatlib.Papers.SpinFreeSim13.PairReadout
