/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.NestedPreparation

/-!
# Flag rotations with cleaned computation registers

This module supplies matrix identities for computing a value, rotating a Boolean payoff flag,
and reversing the computation. `cleanFlagPreparation` combines a uniform coordinate preparation
with selected computations, as used in the Monte Carlo preparation of [KanekoEtAl2020].

The Born-probability theorem identifies the flag probability with a uniform average when the
selected computations map the initial basis state to the specified output basis states.

## Main statements

* `work_preserves_flag`: shows invariance of flag probability under a unitary on the workspace.
* `cleanFlagPreparation_born`: identifies the flag probability with the coordinate average.
* `compute_rotate_uncompute_basis`: describes restoration of a computed basis state.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn

namespace Qatlib.Papers.MonteCarloInt20.MainResults.FlagRotation

/-- Applying a unitary only to the workspace preserves the probability that the Boolean flag is
true. -/
theorem work_preserves_flag {W : Type} [Fintype W] [DecidableEq W]
    (U : Matrix W W ℂ) (hU : U ∈ unitaryGroup W ℂ) (ψ : QState (W × Bool)) :
    MeasureProb (ApplyGate (TensorGate U 1) ψ) (Finset.univ.filter (fun p => p.2=true))=
      MeasureProb ψ (Finset.univ.filter (fun p => p.2=true)) := by
  have ha (w : W) : ApplyGate (TensorGate U 1) ψ (w,true)=ApplyGate U (fun v => ψ (v,true)) w := by
    simp [ApplyGate,Matrix.mulVec,dotProduct,TensorGate,Fintype.sum_prod_type,Matrix.one_apply]
  have h := sum_normSq_mulVec_of_mem_unitaryGroup hU (fun w => ψ (w,true))
  simpa only [MeasureProb,Finset.sum_filter,Fintype.sum_prod_type,Fintype.sum_bool,
    Bool.false_eq_true,↓reduceIte,add_zero,BornProb,ha,Complex.normSq_eq_norm_sq] using! h

/-- Prepare uniform coordinate amplitudes with Hadamards and apply the coordinate-selected
workspace matrices. -/
def computePreparation {W : Type} [Fintype W] [DecidableEq W]
    (d : ℕ) (U : Reg d → Matrix W W ℂ) : Matrix (Reg d × W) (Reg d × W) ℂ :=
  select U*TensorGate (HadamardN d) 1

/-- Each amplitude of the selected computation preparation factors into a Hadamard amplitude and
the corresponding selected workspace amplitude. -/
theorem computePreparation_amplitude {W : Type} [Fintype W] [DecidableEq W]
    (d : ℕ) (U : Reg d → Matrix W W ℂ) (w₀ : W) (i : Reg d) (w : W) :
    ApplyGate (computePreparation d U) (Ket (ZeroStr d,w₀)) (i,w)=
      HadamardN d i (ZeroStr d)*ApplyGate (U i) (Ket w₀) w := by
  rw [apply_ket_column,apply_ket_column]
  simp [computePreparation,Matrix.mul_apply,select,TensorGate,Fintype.sum_prod_type,Matrix.one_apply,mul_comm]

/-- Prepare the coordinate-controlled payoff flag and reverse the selected workspace
computation. -/
def cleanFlagPreparation {W : Type} [Fintype W] [DecidableEq W]
    (d : ℕ) (U : Reg d → Matrix W W ℂ) (f : Reg d × W → ℝ) :
    Matrix ((Reg d × W) × Bool) ((Reg d × W) × Bool) ℂ :=
  TensorGate (select U).conjTranspose 1*payoffPreparation (computePreparation d U) f

/-- The clean flag preparation is unitary when every selected workspace matrix is unitary and
every payoff value lies in `[0, 1]`. -/
theorem cleanFlagPreparation_unitary {W : Type} [Fintype W] [DecidableEq W]
    (d : ℕ) (U : Reg d → Matrix W W ℂ) (hU : ∀ i,U i ∈ unitaryGroup W ℂ)
    (f : Reg d × W → ℝ) (hf : ∀ p,f p ∈ Set.Icc (0:ℝ) 1) :
    cleanFlagPreparation d U f ∈ unitaryGroup ((Reg d × W) × Bool) ℂ :=
  (unitaryGroup _ ℂ).mul_mem
    (tensorGate_unitary (conjTranspose_mem_unitaryGroup (select_unitary U hU)) (by simp))
    (payoffPreparation_mem_unitaryGroup _ _
      ((unitaryGroup _ ℂ).mul_mem (select_unitary U hU)
        (tensorGate_unitary (hadamardN_unitary d) (by simp))) hf)

/-- When each selected unitary maps the initial workspace basis state to `y i`, the clean
preparation has true-flag probability equal to the uniform average of `f (i, y i)`. -/
theorem cleanFlagPreparation_born {W : Type} [Fintype W] [DecidableEq W]
    (d : ℕ) (U : Reg d → Matrix W W ℂ) (hU : ∀ i,U i ∈ unitaryGroup W ℂ)
    (w₀ : W) (y : Reg d → W) (hy : ∀ i,ApplyGate (U i) (Ket w₀)=Ket (y i))
    (f : Reg d × W → ℝ) (hf : ∀ p,f p ∈ Set.Icc (0:ℝ) 1) :
    MeasureProb (ApplyGate (cleanFlagPreparation d U f) (Ket ((ZeroStr d,w₀),false)))
      (Finset.univ.filter (fun p => p.2=true))=(1/(2:ℝ)^d)*∑ i : Reg d,f (i,y i) := by
  have hC : computePreparation d U ∈ unitaryGroup (Reg d × W) ℂ :=
    (unitaryGroup _ ℂ).mul_mem (select_unitary U hU)
      (tensorGate_unitary (hadamardN_unitary d) (by simp))
  rw [cleanFlagPreparation,applyGate_mul,
    work_preserves_flag _ (conjTranspose_mem_unitaryGroup (select_unitary U hU)),
    (payoff_actual_rotation_and_mean (computePreparation d U) (ZeroStr d,w₀) f hC hf).2]
  have hb (i : Reg d) (w : W) :
      BornProb (ApplyGate (computePreparation d U) (Ket (ZeroStr d,w₀))) (i,w)=
        (1/(2:ℝ)^d)*(if w=y i then 1 else 0) := by
    rw [BornProb,computePreparation_amplitude,hy,norm_mul,mul_pow,uniform_hadamard_born]
    by_cases hw : w=y i <;> simp [Ket,hw]
  simp_rw [Fintype.sum_prod_type,hb]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (y i)]
  · simp
  · intro w _ hw
    simp [hw]
  · simp

/-- The Boolean flag vector with false amplitude `√(1 - a)` and true amplitude `√a`. -/
def flagState (a : ℝ) : QState Bool := fun b => if b then (Real.sqrt a:ℂ) else (Real.sqrt (1-a):ℂ)

/-- On a basis workspace state with false flag, the payoff rotation preserves the workspace and
produces `flagState (f y)`. -/
theorem payoffRotation_basis {W : Type} [Fintype W] [DecidableEq W] (f : W → ℝ) (y : W) :
    ApplyGate (payoffRotation f) (Ket (y,false))=TensorState (Ket y) (flagState (f y)) := by
  funext p
  obtain ⟨w,b⟩ := p
  rw [apply_ket_column]
  by_cases hw : w=y
  · subst w
    cases b <;> simp [payoffRotation_apply,TensorState,Ket,flagState]
  · cases b <;> simp [payoffRotation_apply,TensorState,Ket,flagState,hw]

/-- If a unitary maps `Ket x` to `Ket y`, computing, rotating the payoff flag, and uncomputing
restores `Ket x` and leaves `flagState (f y)`. -/
theorem compute_rotate_uncompute_basis {W : Type} [Fintype W] [DecidableEq W]
    (C : Matrix W W ℂ) (hC : C ∈ unitaryGroup W ℂ) (x y : W)
    (hxy : ApplyGate C (Ket x)=Ket y) (f : W → ℝ) :
    ApplyGate (TensorGate C.conjTranspose 1*payoffRotation f*TensorGate C 1) (Ket (x,false))=
      TensorState (Ket x) (flagState (f y)) := by
  have hc : C.conjTranspose*C=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Unitary.star_mul_self_of_mem hC
  have hi : ApplyGate C.conjTranspose (Ket y)=Ket x := by
    rw [← hxy,← applyGate_mul,hc,applyGate_one]
  rw [applyGate_mul,applyGate_mul,← tensorState_ket_ket,applyGate_tensorGate,hxy,applyGate_one,
    tensorState_ket_ket,payoffRotation_basis,applyGate_tensorGate,hi,applyGate_one]

end Qatlib.Papers.MonteCarloInt20.MainResults.FlagRotation
