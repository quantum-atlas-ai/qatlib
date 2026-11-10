/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshCopyExec.QpeConsumers.LocalControlledSwap
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.LocalCopyCleanFrame
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.LocalCopyLayout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.LocalCopyWordSemantics
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

noncomputable def localControlledCopyRawMap (n : ℕ) (ρ : Operator (2^n)) (θ : ℝ)
    (X : Matrix (Bool × Fin (2^n)) (Bool × Fin (2^n)) ℂ) :
    Matrix (Bool × Fin (2^n)) (Bool × Fin (2^n)) ℂ :=
  let F := localCopyFrame n
  let U := reflectionProgramMatrix (localControlledSwapSteps n θ)
  traceRightB (Matrix.traceRight
    (relabelGate (localCopySplit n) (U * (F * tensorCopyB ρ X * Fᴴ) * Uᴴ)))

noncomputable def localControlledCopyRawLinearMap (n : ℕ) (ρ : Operator (2^n)) (θ : ℝ) :
    MatrixMap (Bool × Fin (2^n)) (Bool × Fin (2^n)) ℂ where
  toFun := localControlledCopyRawMap n ρ θ
  map_add' X Y := by
    have ht : tensorCopyB ρ (X+Y) = tensorCopyB ρ X + tensorCopyB ρ Y := by
      ext x y
      simp [tensorCopyB, add_mul]
    simp only [localControlledCopyRawMap, ht, Matrix.mul_add, Matrix.add_mul]
    have hr : ∀ A B : Matrix (Reg (3*n+2)) (Reg (3*n+2)) ℂ,
        relabelGate (localCopySplit n) (A+B) =
          relabelGate (localCopySplit n) A + relabelGate (localCopySplit n) B := by
      intro A B; rfl
    rw [hr, Matrix.traceRight_add]
    ext x y
    simp [traceRightB, Finset.sum_add_distrib]
  map_smul' c X := by
    have ht : tensorCopyB ρ (c • X) = c • tensorCopyB ρ X := by
      ext x y
      simp [tensorCopyB, mul_assoc]
    simp only [localControlledCopyRawMap, ht, Matrix.mul_smul, Matrix.smul_mul]
    have hr : ∀ A : Matrix (Reg (3*n+2)) (Reg (3*n+2)) ℂ,
        relabelGate (localCopySplit n) (c • A) =
          c • relabelGate (localCopySplit n) A := by
      intro A; rfl
    rw [hr, Matrix.traceRight_smul]
    ext x y
    simp [traceRightB, Finset.mul_sum]

noncomputable def localControlledCopyChannelMap (n : ℕ) (ρ : Operator (2^n)) (θ : ℝ) :
    MatrixMap (Fin (2*(2^n))) (Fin (2*(2^n))) ℂ :=
  (relabelLM (controlDataEquiv (2^n))).comp
    ((localControlledCopyRawLinearMap n ρ θ).comp
      (relabelLM (controlDataEquiv (2^n)).symm))

theorem localControlledCopyChannelMap_relabel (n : ℕ) (ρ : Operator (2^n)) (θ : ℝ)
    (X : Matrix (Bool × Fin (2^n)) (Bool × Fin (2^n)) ℂ) :
    localControlledCopyChannelMap n ρ θ (relabelGate (controlDataEquiv (2^n)) X) =
      relabelGate (controlDataEquiv (2^n)) (localControlledCopyRawMap n ρ θ X) := by
  simp only [localControlledCopyChannelMap, LinearMap.comp_apply, relabelLM_apply]
  have hx : relabelGate (controlDataEquiv (2^n)).symm
      (relabelGate (controlDataEquiv (2^n)) X) = X := by
    ext i j
    simp [relabelGate]
  rw [hx]
  rfl

theorem localCopyFrame_actual_scratch_discard (n : ℕ)
    (Y : Matrix (Bool × (Fin (2^n) × Fin (2^n))) (Bool × (Fin (2^n) × Fin (2^n))) ℂ) :
    Matrix.traceRight (relabelGate (localCopySplit n) (localCopyFrame n * Y * (localCopyFrame n)ᴴ)) = Y := by
  have he : ∀ (p q : Bool × (Fin (2^n) × Fin (2^n))) (a b : Reg n × Bool),
      relabelGate (localCopySplit n) (localCopyFrame n * Y * (localCopyFrame n)ᴴ) (p,a) (q,b) =
        if a = ((fun _ => false),false) ∧ b = ((fun _ => false),false) then Y p q else 0 := by
    intro p q a b
    simp only [relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.mul_apply,
      Matrix.conjTranspose_apply,localCopyFrame,Equiv.apply_symm_apply,Prod.mk.injEq]
    by_cases ha : a = ((fun _ => false),false) <;>
      by_cases hb : b = ((fun _ => false),false) <;> simp [ha,hb]
  ext p q
  simp only [Matrix.traceRight,Matrix.of_apply,he,and_self]
  simp

theorem localControlledCopyRawMap_eq (n : ℕ) (ρ : Operator (2^n)) (θ : ℝ)
    (X : Matrix (Bool × Fin (2^n)) (Bool × Fin (2^n)) ℂ) :
    localControlledCopyRawMap n ρ θ X = controlledCopyRawMap ρ θ X := by
  have hi := local_controlled_partial_swap_clean_intertwining n θ
  have hh := congrArg Matrix.conjTranspose hi
  simp only [Matrix.conjTranspose_mul] at hh
  dsimp only [localControlledCopyRawMap,controlledCopyRawMap]
  have he : reflectionProgramMatrix (localControlledSwapSteps n θ) *
      (localCopyFrame n * tensorCopyB ρ X * (localCopyFrame n)ᴴ) *
      (reflectionProgramMatrix (localControlledSwapSteps n θ))ᴴ =
      localCopyFrame n * (controlledSwapRawGate (2^n) θ * tensorCopyB ρ X *
        (controlledSwapRawGate (2^n) θ)ᴴ) * (localCopyFrame n)ᴴ := by
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hi]
    simp only [Matrix.mul_assoc]
    rw [hh]
  rw [he,localCopyFrame_actual_scratch_discard]

theorem local_controlled_copy_actual_discard_and_reference_bridge :
    ∀ (n : ℕ) (ρ : Operator (2^n)) (θ : ℝ),
      (∀ X : Matrix (Bool × Fin (2^n)) (Bool × Fin (2^n)) ℂ,
        localControlledCopyRawMap n ρ θ X = controlledCopyRawMap ρ θ X) ∧
      localControlledCopyChannelMap n ρ θ = controlledCopyChannelMap ρ θ ∧
      (∀ (r : ℕ) (Y : Matrix (Fin (2*(2^n)) × Fin r) (Fin (2*(2^n)) × Fin r) ℂ),
        tensorLeft (R := r) (localControlledCopyChannelMap n ρ θ) Y =
          tensorLeft (R := r) (controlledCopyChannelMap ρ θ) Y) := by
  intro n ρ θ
  have hc : localControlledCopyChannelMap n ρ θ = controlledCopyChannelMap ρ θ := by
    ext X i j
    let A := relabelGate (controlDataEquiv (2^n)).symm X
    have hx : X = relabelGate (controlDataEquiv (2^n)) A := by
      ext a b
      simp [A,relabelGate]
    rw [hx,localControlledCopyChannelMap_relabel,controlledCopyChannelMap_relabel,
      localControlledCopyRawMap_eq]
  exact ⟨localControlledCopyRawMap_eq n ρ θ,hc,fun _ _ => by rw [hc]⟩

end Qatlib.Concepts.FreshCopyExec.QpeConsumers
