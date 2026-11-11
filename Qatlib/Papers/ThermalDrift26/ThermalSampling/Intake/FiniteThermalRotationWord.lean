/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalDrift26.ThermalSampling.Intake.DirectThermalPreparationError
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.MbqcFlow.FlowDecision.PureStateOverlap

/-!
# Finite Words for Thermal Rotation Preparation

This module interprets a legal finite gate word as a thermal rotation preparation with a
distinguished signal qubit and an explicit workspace, supporting the source implementation in
[JiangEtAl2026]. `rotationRegisterEquiv` separates these registers, `splitWordState` records the
circuit output, and `targetWordState` pairs the ideal rotation vector with a zero workspace.

`cleanWordErrorSq` measures the squared vector error of the entire output. The reduced signal
density `wordPreparationState` inherits a trace-norm error bound, which
`finiteWord_source_cq_budget` propagates to the joint readout together with an error in the
sampled index distribution.

## Main statements

* `splitWordState_actual_run` identifies the successful finite-word execution and its gate
  count.
* `wordPreparation_error` converts a full vector error bound into a reduced-state trace-norm
  bound.
- `finiteWord_source_cq_budget` bounds half the joint readout trace norm by `epsilon + delta`.

## References

* [Jiang et al., 2026][JiangEtAl2026], *Thermal-Drift Sampling: Generating Thermal Ensembles for
  Learning Many-Body Systems*.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false
noncomputable section
namespace Qatlib.Papers.ThermalDrift26.ThermalSampling
open Qatlib Matrix
open scoped BigOperators ComplexOrder

/-- The equivalence splitting a `(w+1)`-qubit bit register into its first-bit signal value in
`Fin 2` and the remaining `w` workspace bits. -/
def rotationRegisterEquiv (w : ℕ) : Qatlib.Foundations.PureStateMath.Reg (w + 1) ≃ (Fin 2 × Qatlib.Foundations.PureStateMath.Reg w) where
  toFun x := (Qatlib.Foundations.PureStateMath.boolEquivFin2 (x 0), fun i => x i.succ)
  invFun x := Fin.cons (Qatlib.Foundations.PureStateMath.boolEquivFin2.symm x.1) x.2
  left_inv := by
    intro x
    change Fin.cons
        (Qatlib.Foundations.PureStateMath.boolEquivFin2.symm (Qatlib.Foundations.PureStateMath.boolEquivFin2 (x 0))) (fun i => x i.succ) = x
    rw [Equiv.symm_apply_apply]
    exact Fin.cons_self_tail x
  right_inv := by intro x; ext <;> simp

/-- The state obtained by running the decoded finite gate word on the all-zero register with
identity oracle, reindexed as a signal qubit and `w` workspace qubits. -/
def splitWordState (w : ℕ) (gs : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode) : Qatlib.Foundations.PureStateMath.QState (Fin 2 × Qatlib.Foundations.PureStateMath.Reg w) :=
  fun x => Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg (w+1)) (Qatlib.Foundations.PureStateMath.Reg (w+1)) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit (w+1) gs)
    (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)) ((rotationRegisterEquiv w).symm x)

/-- A finite word legal on `w+1` wires produces a normalized `splitWordState`. -/
theorem splitWordState_normalized (w : ℕ) (gs : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode)
    (hlegal : Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal (w+1) gs = true) : Qatlib.Foundations.PureStateMath.Normalized (splitWordState w gs) := by
  have hC :=
      ((Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finite_gate_description_rejection_unitarity_and_counts (w+1) gs).2 hlegal).1
  have hn := hC.normalized_run (show (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg (w+1)) (Qatlib.Foundations.PureStateMath.Reg (w+1)) ℂ) ∈
    Matrix.unitaryGroup (Qatlib.Foundations.PureStateMath.Reg (w+1)) ℂ from by simp) (Qatlib.Foundations.PureStateMath.normalized_ket (fun _ => false))
  unfold Qatlib.Foundations.PureStateMath.Normalized splitWordState
  exact ((rotationRegisterEquiv w).symm.sum_comp (fun x =>
    ‖Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg (w+1)) (Qatlib.Foundations.PureStateMath.Reg (w+1)) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit (w+1) gs)
      (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)) x‖ ^ 2)).trans hn

/-- For a legal word, `finiteWordRun` succeeds on the zero input with the reindexed
`splitWordState`, and the decoded circuit's gate count equals the word length. -/
theorem splitWordState_actual_run (w : ℕ) (gs : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode)
    (hlegal : Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal (w+1) gs = true) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordRun (w+1) gs (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)) =
      some (fun x => splitWordState w gs (rotationRegisterEquiv w x)) ∧
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit (w+1) gs) = gs.length := by
  constructor
  · simp only [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordRun, hlegal, if_true,
      splitWordState, Equiv.symm_apply_apply]
  · exact (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts (w+1) gs).2

/-- The tensor product of the ideal signal rotation vector `rotationVector a` with an all-zero
`w`-qubit workspace. -/
def targetWordState (w : ℕ) (a : ℝ) : Qatlib.Foundations.PureStateMath.QState (Fin 2 × Qatlib.Foundations.PureStateMath.Reg w) :=
  Qatlib.Foundations.PureStateMath.TensorState (rotationVector a) (Qatlib.Foundations.PureStateMath.Ket (fun _ => false))

/-- The ideal rotation vector together with the zero workspace is normalized for every real
parameter `a`. -/
private theorem targetWordState_normalized (w : ℕ) (a : ℝ) : Qatlib.Foundations.PureStateMath.Normalized (targetWordState w a) := by
  apply Qatlib.Foundations.PureStateMath.normalized_tensorState _
      (Qatlib.Foundations.PureStateMath.normalized_ket _)
  simp [Qatlib.Foundations.PureStateMath.Normalized, rotationVector, Fin.sum_univ_two, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, direct_rotation_normalized]

/-- The sum of squared complex amplitude differences between the full circuit output
`splitWordState` and the ideal signal rotation with zero workspace. -/
def cleanWordErrorSq (w : ℕ) (gs : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode) (a : ℝ) : ℝ :=
  ∑ x : Fin 2 × Qatlib.Foundations.PureStateMath.Reg w, Complex.normSq (splitWordState w gs x - targetWordState w a x)

/-- For normalized finite pure states, squared vector distance at most `epsilon^2` with `epsilon
>= 0` implies trace norm at most `2*epsilon` between their outer-product density matrices. -/
private theorem pure_error_of_l2 {I : Type} [Fintype I] [DecidableEq I]
    (u v : Qatlib.Foundations.PureStateMath.QState I) (hu : Qatlib.Foundations.PureStateMath.Normalized u) (hv : Qatlib.Foundations.PureStateMath.Normalized v) (epsilon : ℝ) (heps : 0 ≤ epsilon)
    (hclean : (∑ x, Complex.normSq (u x - v x)) ≤ epsilon ^ 2) :
    Matrix.traceNorm (Qatlib.Foundations.PureStateMath.Reflection.outerProduct u - Qatlib.Foundations.PureStateMath.Reflection.outerProduct v) ≤ 2 * epsilon := by
  have huN : (∑ x, Complex.normSq (u x)) = 1 := by
    simpa only [Complex.normSq_eq_norm_sq, Qatlib.Foundations.PureStateMath.Normalized] using
        hu
  have hvN : (∑ x, Complex.normSq (v x)) = 1 := by
    simpa only [Complex.normSq_eq_norm_sq, Qatlib.Foundations.PureStateMath.Normalized] using
        hv
  have hcross (x : I) : (u x * (starRingEnd ℂ) (v x)).re =
      ((starRingEnd ℂ) (u x) * v x).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hm : (∑ x, Complex.normSq (u x - v x)) = 2 - 2 * (Qatlib.Foundations.PureStateMath.Inner u v).re := by
    simp only [Complex.normSq_sub]
    simp_rw [hcross]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      huN, hvN, ← Complex.re_sum, ← Qatlib.Foundations.PureStateMath.inner_apply]
    ring
  have hi : 1 - epsilon ^ 2 / 2 ≤ (Qatlib.Foundations.PureStateMath.Inner u v).re := by
    rw [hm] at hclean; linarith
  have h :=
      Qatlib.Concepts.MbqcFlow.FlowDecision.pure_traceDistance_le_of_inner u v hu hv
      (epsilon ^ 2 / 2) hi
  have hs : Real.sqrt (2 * (epsilon ^ 2 / 2)) = epsilon := by
    rw [show 2 * (epsilon ^ 2 / 2) = epsilon ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg heps]
  rw [hs] at h
  linarith

/-- The signal-qubit density operator obtained by tracing out the workspace from the outer
product of the normalized output of a legal finite word. -/
def wordPreparationState (w : ℕ) (gs : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode)
    (hlegal : Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal (w+1) gs = true) : Qatlib.Foundations.PureStateMath.DensityOperator 2 :=
  ⟨Matrix.traceRight (Qatlib.Foundations.PureStateMath.Reflection.outerProduct (splitWordState w gs)), by
    constructor
    · exact (Qatlib.Foundations.PureStateMath.BornBridge.outerProduct_posSemidef _).traceRight
    · exact (Matrix.traceRight_trace _).trans
        (Qatlib.Foundations.PureStateMath.BornBridge.outerProduct_density (splitWordState_normalized w gs hlegal)).2⟩

/-- Tracing the workspace out of the ideal full target state's outer product gives the signal
density `rotationState a`. -/
private theorem targetWordState_reduced (w : ℕ) (a : ℝ) :
    Matrix.traceRight (Qatlib.Foundations.PureStateMath.Reflection.outerProduct (targetWordState w a)) = (rotationState a).val := by
  ext i j
  change (∑ z : Qatlib.Foundations.PureStateMath.Reg w, Qatlib.Foundations.PureStateMath.Reflection.outerProduct (Qatlib.Foundations.PureStateMath.TensorState (rotationVector a) (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)))
    (i,z) (j,z)) = Qatlib.Foundations.PureStateMath.Reflection.outerProduct (rotationVector a) i j
  rw [Qatlib.Foundations.PureStateMath.BornBridge.sum_outerProduct_tensorState]
  have hn := Qatlib.Foundations.PureStateMath.normalized_ket (fun _ : Fin w => false)
  change (∑ z : Qatlib.Foundations.PureStateMath.Reg w,
      ‖Qatlib.Foundations.PureStateMath.Ket (fun _ => false) z‖ ^ 2) = 1 at hn
  rw [hn]
  simp

/-- For a legal finite word, a bound `cleanWordErrorSq <= epsilon^2` with `epsilon >= 0` implies
that its reduced signal density differs from `rotationState a` by trace norm at most
`2*epsilon`. -/
theorem wordPreparation_error (w : ℕ) (gs : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode)
    (hlegal : Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal (w+1) gs = true) (a epsilon : ℝ) (heps : 0 ≤ epsilon)
    (hclean : cleanWordErrorSq w gs a ≤ epsilon ^ 2) :
    Matrix.traceNorm ((wordPreparationState w gs hlegal).val - (rotationState a).val) ≤ 2 * epsilon := by
  rw [← targetWordState_reduced w a]
  change Matrix.traceNorm (Matrix.traceRight (Qatlib.Foundations.PureStateMath.Reflection.outerProduct (splitWordState w gs)) -
    Matrix.traceRight (Qatlib.Foundations.PureStateMath.Reflection.outerProduct (targetWordState w a))) ≤ 2 * epsilon
  rw [← Matrix.traceRight_sub]
  exact (Qatlib.Concepts.ReferenceError.DensityToRaw.traceRight_hermitian_trace_contraction
    (Qatlib.Foundations.PureStateMath.Reflection.outerProduct (splitWordState w gs) - Qatlib.Foundations.PureStateMath.Reflection.outerProduct (targetWordState w a))
    ((Qatlib.Foundations.PureStateMath.BornBridge.outerProduct_posSemidef _).isHermitian.sub (Qatlib.Foundations.PureStateMath.BornBridge.outerProduct_posSemidef _).isHermitian)).trans
      (pure_error_of_l2 _ _ (splitWordState_normalized w gs hlegal)
        (targetWordState_normalized w a) epsilon heps hclean)

/-- If a legal word has squared full-state preparation error at most `epsilon^2`, with `epsilon
>= 0`, and the index distributions differ in total variation by at most `delta`, the joint
prepared readout has half trace-norm error at most `epsilon + delta` from the ideal source
readout. -/
theorem finiteWord_source_cq_budget {L d : ℕ} (F : ReflectionFamily L d)
    (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (w : ℕ) (gs : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode)
    (hlegal : Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal (w+1) gs = true) (a epsilon delta : ℝ) (heps : 0 ≤ epsilon)
    (hclean : cleanWordErrorSq w gs a ≤ epsilon ^ 2)
    (hindex : (1/2 : ℝ) * (∑ j : Fin L, |q.prob j - p.prob j|) ≤ delta) :
    (1/2 : ℝ) * Matrix.traceNorm
      (jointPreparedReadout F q rho (wordPreparationState w gs hlegal).val -
        idealJointReadoutMatrix F p a rho) ≤ epsilon + delta :=
  native_jointReadout_budget F p q rho a (wordPreparationState w gs hlegal)
    epsilon delta (wordPreparation_error w gs hlegal a epsilon heps hclean) hindex

end Qatlib.Papers.ThermalDrift26.ThermalSampling
