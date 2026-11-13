/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinFreeSim13.PairProjector
import Qatlib.Foundations.TensorRegisters.SwapReadout

/-!
# Pair-symmetry readout and Born weights

This module identifies the branches of the swap-readout circuit with the pair-symmetry
projections used in [Whitfield2013]. The equality `output_sector` connects circuit amplitudes to
the projectors, while `weight_eq_norm` connects their finite Born weights to Euclidean norms.

Positive branch weight yields a unit-norm conditional vector through `normalizedBranch_norm`.
The distinct-pair example is normalized and has equal weight in the two readout branches.

## Main statements

* `total_weight`: unit-norm input gives total readout weight one.
* `normalizedBranch_symmetry`: the conditional branch has the selected swap symmetry.
* `distinctInput_weight`: each label has weight one half on the distinct-pair input.

## References

* [Whitfield, 2013][Whitfield2013]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Papers.SpinFreeSim13.PairReadout
open Matrix
open scoped BigOperators
open Qatlib.Papers.SpinFreeSim13.PairProjector
open Qatlib.Foundations.TensorRegisters
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Embeds a pair amplitude into the readout register with control value `false` and zero
amplitude at control value `true`. -/
def input (ψ : I × I → ℂ) (z : Bool × (I × I)) : ℂ := if z.1 then 0 else ψ z.2

/-- The amplitude produced by applying `SwapReadout.circuit` to the pair input with zero
control. -/
def output (ψ : I × I → ℂ) : Bool × (I × I) → ℂ := SwapReadout.circuit *ᵥ input ψ

/-- The output amplitude at a readout label equals the corresponding sector-projected pair
amplitude. See [Whitfield2013]. -/
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

/-- The swap-readout circuit belongs to the unitary group on the control-and-pair register. See
[Whitfield2013]. -/
theorem readout_unitary : SwapReadout.circuit (I:=I) ∈ Matrix.unitaryGroup (Bool × (I × I)) ℂ :=
  SwapReadout.circuit_unitary

/-- The sector-projected pair amplitude viewed as a vector in complex Euclidean space. -/
def branch (ψ : I × I → ℂ) (label : Bool) : EuclideanSpace ℂ (I × I) :=
  WithLp.toLp 2 (sector label *ᵥ ψ)

/-- The finite Born weight of a readout label, obtained by summing squared complex norms over
pair indices. -/
def weight (ψ : I × I → ℂ) (label : Bool) : ℝ :=
  ∑ p : I × I, Complex.normSq (output ψ (label,p))

/-- The readout weight of a label equals the squared Euclidean norm of its projected branch. See
[Whitfield2013]. -/
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

/-- Appending a zero-valued readout control preserves the squared Euclidean norm of the pair
amplitude. -/
theorem input_norm (ψ : I × I → ℂ) :
    ‖(WithLp.toLp 2 (input ψ) : EuclideanSpace ℂ (Bool × (I × I)))‖^2 =
      ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (I × I))‖^2 := by
  simp [EuclideanSpace.norm_sq_eq, input, Fintype.sum_prod_type]

/-- The swap-readout circuit preserves the Euclidean norm of the initialized input amplitude. -/
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

/-- For a unit-norm pair input, the two readout weights sum to one. See [Whitfield2013]. -/
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

/-- The projected branch scaled by the inverse square root of its readout weight. -/
def normalizedBranch (ψ : I × I → ℂ) (label : Bool) : EuclideanSpace ℂ (I × I) :=
  ((Real.sqrt (weight ψ label) : ℂ)⁻¹) • branch ψ label

/-- A branch with positive readout weight has norm one after normalization. See [Whitfield2013]. -/
theorem normalizedBranch_norm (ψ : I × I → ℂ) (label : Bool) (hp : 0 < weight ψ label) :
    ‖normalizedBranch ψ label‖=1 := by
  have hn : ‖branch ψ label‖ ≠ 0 := by
    rw [weight_eq_norm] at hp
    exact ne_of_gt (by nlinarith [norm_nonneg (branch ψ label)] : 0 < ‖branch ψ label‖)
  rw [normalizedBranch, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), weight_eq_norm,
    Real.sqrt_sq (norm_nonneg _), inv_mul_cancel₀ hn]

/-- The normalized branch satisfies the swap eigenvalue equation for its selected symmetry sign.
See [Whitfield2013]. -/
theorem normalizedBranch_symmetry (ψ : I × I → ℂ) (label : Bool) :
    swapMatrix *ᵥ (normalizedBranch ψ label).ofLp =
      sign label • (normalizedBranch ψ label).ofLp := by
  change swapMatrix *ᵥ (((Real.sqrt (weight ψ label) : ℂ)⁻¹) • (sector label *ᵥ ψ)) = _
  rw [Matrix.mulVec_smul, projected_symmetry, smul_comm]
  rfl

/-- The pair amplitude supported at the distinct Boolean pair `(false, true)` with value one. -/
def distinctInput : Bool × Bool → ℂ := Pi.single (false,true) 1

/-- The distinct-pair input has Euclidean norm one. See [Whitfield2013]. -/
theorem distinctInput_norm :
    ‖(WithLp.toLp 2 distinctInput : EuclideanSpace ℂ (Bool × Bool))‖=1 := by
  change ‖(PiLp.single 2 (false,true) (1:ℂ) : EuclideanSpace ℂ (Bool × Bool))‖=1
  simp

/-- Each readout label has weight `1 / 2` on the distinct-pair input. See [Whitfield2013]. -/
theorem distinctInput_weight (label : Bool) : weight distinctInput label = (1:ℝ)/2 := by
  unfold weight
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, output_sector]
  cases label <;> norm_num [sector_apply, distinctInput, sign]
end Qatlib.Papers.SpinFreeSim13.PairReadout
