/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeShiftPreparation
import Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw.RationalWeightPreparation
import Qatlib.Foundations.PureStateMath.BornBridge.RelabelOperatorNorm
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.CopyEvolution.Discriminate
/-! Same-order perturbation of the actual seven generated rotations.
The comparison uses the actual rounded-axis prefixes; it is not the output
of the different rational-weight generator. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- Construction for shift Pair Gate in the native shift rotation word model. -/
def shiftPairGate (i : Fin 7) (c s : ℝ) : Matrix (Fin 8) (Fin 8) ℂ :=
  relabelGate (finSuccEquiv 7).symm (weightTwoLevel i c s)

/-- The finite construction in `NativeShiftRotationWord` satisfies `nativePair_as_shiftPair` under the displayed hypotheses. -/
theorem nativePair_as_shiftPair (i : Fin 7) (q : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.pairLogical i q=shiftPairGate i q.c q.s := by
  unfold Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.pairLogical
  change twoLevelMatrix (.pair (0 : Fin 8) i.succ (Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.rotation q))=_
  ext a b
  obtain ⟨a,rfl⟩ := (finSuccEquiv 7).symm.surjective a
  obtain ⟨b,rfl⟩ := (finSuccEquiv 7).symm.surjective b
  cases a with
  | none =>
    cases b with
    | none => simp [shiftPairGate,relabelGate,twoLevelMatrix,
        weightTwoLevel,Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.rotation]
    | some b =>
      by_cases hb : b=i
      · subst b; simp [shiftPairGate,relabelGate,twoLevelMatrix,
          weightTwoLevel,Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.rotation]
      · simp [shiftPairGate,relabelGate,twoLevelMatrix,
          weightTwoLevel,hb,Fin.succ_inj]
  | some a =>
    cases b with
    | none =>
      by_cases ha : a=i
      · subst a; simp [shiftPairGate,relabelGate,twoLevelMatrix,
          weightTwoLevel,Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.rotation]
      · simp [shiftPairGate,relabelGate,twoLevelMatrix,
          weightTwoLevel,ha,Fin.succ_inj]
    | some b =>
      by_cases ha : a=i <;> by_cases hb : b=i <;>
        simp_all [shiftPairGate,relabelGate,twoLevelMatrix,
          weightTwoLevel,Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.rotation,Fin.succ_inj,eq_comm]

/-- The actual finite word or frame satisfies `shiftPairGate_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem shiftPairGate_unitary (i : Fin 7) (c s : ℝ) (hcs : c^2+s^2=1) :
    shiftPairGate i c s ∈ unitaryGroup (Fin 8) ℂ :=
  relabelGate_mem_unitary (weightTwoLevel_unitary i c s hcs) (finSuccEquiv 7).symm

/-- The estimate `shiftPairGate_error` retains the actual parameter, input-error and normalization budgets. -/
theorem shiftPairGate_error (i : Fin 7) (c s c' s' : ℝ) :
    ‖shiftPairGate i c s-shiftPairGate i c' s'‖ ≤ |c-c'|+|s-s'| := by
  rw [shiftPairGate,shiftPairGate,Qatlib.Foundations.PureStateMath.BornBridge.l2_norm_relabelGate_sub]
  exact weightTwoLevel_error i c s c' s'

/-- Construction for shift Comparison Gate in the native shift rotation word model. -/
def shiftComparisonGate (α B x y : ℚ) (p : ℕ) (i : Fin 7) : Matrix (Fin 8) (Fin 8) ℂ :=
  shiftPairGate i (shiftIdealCircleValue α B x y p i).re
    (shiftIdealCircleValue α B x y p i).im

/-- The actual finite word or frame satisfies `shiftComparisonGate_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem shiftComparisonGate_unitary (α B x y : ℚ) (p : ℕ) (i : Fin 7) :
    shiftComparisonGate α B x y p i ∈ unitaryGroup (Fin 8) ℂ := by
  apply shiftPairGate_unitary
  dsimp [shiftIdealCircleValue]
  have hd : 1+(shiftIdealHalf α B x y p i)^2≠0 := by positivity
  field_simp [hd]
  ring

/-- The estimate `nativeShiftPair_error` retains the actual parameter, input-error and normalization budgets. -/
theorem nativeShiftPair_error (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) (i : Fin 7) :
    ‖Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.pairLogical i (nativeShiftCircles α B x y p i)-
      shiftComparisonGate α B x y p i‖ ≤ 1/(2 : ℝ)^(p+12) := by
  rw [nativePair_as_shiftPair]
  have he := nativeShiftCircles_error α B x y p hα hB hz i
  let d := gaussianRatComplex ((nativeShiftCircles α B x y p i).c,
    (nativeShiftCircles α B x y p i).s)-shiftIdealCircleValue α B x y p i
  have hr := Complex.abs_re_le_norm d
  have hi := Complex.abs_im_le_norm d
  change ‖d‖ ≤ _ at he
  have hh := shiftPairGate_error i ((nativeShiftCircles α B x y p i).c : ℝ)
    ((nativeShiftCircles α B x y p i).s : ℝ)
    (shiftIdealCircleValue α B x y p i).re (shiftIdealCircleValue α B x y p i).im
  dsimp only [d] at hr hi
  simp only [Complex.sub_re] at hr
  simp only [Complex.sub_im] at hi
  simp [gaussianRatComplex] at hr hi
  have hp : 1/(2 : ℝ)^(p+13)+1/(2 : ℝ)^(p+13)=1/(2 : ℝ)^(p+12) := by
    rw [show p+13=(p+12)+1 by omega,pow_succ]
    ring
  exact hh.trans ((add_le_add (hr.trans he) (hi.trans he)).trans_eq hp)

/-- Construction for shift Comparison Product in the native shift rotation word model. -/
def shiftComparisonProduct (α B x y : ℚ) (p : ℕ) : List (Fin 7) → Matrix (Fin 8) (Fin 8) ℂ
  | [] => 1
  | i::is => shiftComparisonProduct α B x y p is * shiftComparisonGate α B x y p i

/-- The actual finite word or frame satisfies `shiftComparisonProduct_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem shiftComparisonProduct_unitary (α B x y : ℚ) (p : ℕ) (is : List (Fin 7)) :
    shiftComparisonProduct α B x y p is ∈ unitaryGroup (Fin 8) ℂ := by
  induction is with
  | nil => exact (unitaryGroup _ ℂ).one_mem
  | cons i is ih =>
    exact (unitaryGroup _ ℂ).mul_mem ih (shiftComparisonGate_unitary α B x y p i)

/-- The estimate `nativeShiftProduct_error` retains the actual parameter, input-error and normalization budgets. -/
theorem nativeShiftProduct_error (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) (is : List (Fin 7)) :
    ‖Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.pairProduct (nativeShiftCircles α B x y p) is-
      shiftComparisonProduct α B x y p is‖ ≤ is.length/(2 : ℝ)^(p+12) := by
  induction is with
  | nil => simp [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.pairProduct,shiftComparisonProduct]
  | cons i is ih =>
    let A := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.pairProduct (nativeShiftCircles α B x y p) is
    let C := shiftComparisonProduct α B x y p is
    let g := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.pairLogical i (nativeShiftCircles α B x y p i)
    let h := shiftComparisonGate α B x y p i
    have hg : ‖g‖ ≤ 1 := Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.pairLogical_unitary _ _)
    have hC : ‖C‖ ≤ 1 := Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one (shiftComparisonProduct_unitary _ _ _ _ _ _)
    have he : ‖g-h‖ ≤ 1/(2 : ℝ)^(p+12) := nativeShiftPair_error α B x y p hα hB hz i
    change ‖A-C‖ ≤ _ at ih
    change ‖A*g-C*h‖ ≤ _
    have hid : A*g-C*h=(A-C)*g+C*(g-h) := by noncomm_ring
    rw [hid]
    calc
      _ ≤ ‖(A-C)*g‖+‖C*(g-h)‖ := norm_add_le _ _
      _ ≤ (is.length/(2 : ℝ)^(p+12))*1+1*(1/(2 : ℝ)^(p+12)) :=
        add_le_add ((norm_mul_le _ _).trans
          (mul_le_mul ih hg (norm_nonneg _) (by positivity)))
          ((norm_mul_le _ _).trans (mul_le_mul hC he (norm_nonneg _) (by norm_num)))
      _ = _ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

/-- The actual physical order is seven down to one, as in vLogical. -/
def shiftComparisonLogical (α B x y : ℚ) (p : ℕ) : Matrix (Fin 8) (Fin 8) ℂ :=
  shiftComparisonProduct α B x y p (List.finRange 7).reverse

/-- The estimate `nativeShiftLogical_error` retains the actual parameter, input-error and normalization budgets. -/
theorem nativeShiftLogical_error (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    ‖Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.vLogical (nativeShiftCircles α B x y p)-
      shiftComparisonLogical α B x y p‖ ≤ 7/(2 : ℝ)^(p+12) := by
  simpa only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.vLogical,shiftComparisonLogical,List.length_reverse,List.length_finRange,Nat.cast_ofNat]
    using nativeShiftProduct_error α B x y p hα hB hz (List.finRange 7).reverse

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
