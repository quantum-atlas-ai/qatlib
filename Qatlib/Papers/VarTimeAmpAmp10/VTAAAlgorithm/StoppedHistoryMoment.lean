/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.CoherentVariableTimeExt

/-!
# Stopped histories and paid cost moments

This module decomposes the success mass of a coherent variable-time frame into newly stopped
branches and a final running branch. It defines the paid prefix receipts and their first and
second moments, and compares these moments with the stopping-time budgets.

The variable-time amplification setting is described in [Ambainis2012].

## Main statements

* `runSuccess_stopHistory_split`: decomposition of the final success mass.
* `receiptSecondMoment_le_max_mul_mean`: second moment bounded by the full receipt times the
  mean.
* `frontier1`: combined history, receipt, and moment identities.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean

open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.CoherentVariableTimeExt

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.VarTimeAmpAmp10.Estimate
open Qatlib.Papers.VarTimeAmpAmp10.StopModel

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

noncomputable section

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.StoppedHistoryMoment

open Matrix
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA Qatlib.Papers.VarTimeAmpAmp10.Estimate
open Qatlib.Papers.VarTimeAmpAmp10.StopModel Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Qatlib.Concepts.QlsReadoutSpec.ProgramModel
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.CoherentVtFrame
open scoped Classical BigOperators
set_option warningAsError false

variable {H : Type} [Fintype H] [DecidableEq H] {m : ℕ}

/-- The state inner product is additive in its first argument. -/
private theorem inner_add_left' (ψ φ χ : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (ψ + φ) χ = Qatlib.Foundations.PureStateMath.Inner ψ χ + Qatlib.Foundations.PureStateMath.Inner φ χ := by
  rw [Qatlib.Foundations.PureStateMath.inner_apply, Qatlib.Foundations.PureStateMath.inner_apply,
    Qatlib.Foundations.PureStateMath.inner_apply]
  simp [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/-- The state inner product is additive in its second argument. -/
private theorem inner_add_right' (ψ φ χ : QState H) :
    Qatlib.Foundations.PureStateMath.Inner ψ (φ + χ) = Qatlib.Foundations.PureStateMath.Inner ψ φ + Qatlib.Foundations.PureStateMath.Inner ψ χ := by
  rw [Qatlib.Foundations.PureStateMath.inner_apply, Qatlib.Foundations.PureStateMath.inner_apply,
    Qatlib.Foundations.PureStateMath.inner_apply]
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The total measurement mass equals the real part of the state's inner product with itself. -/
private theorem measureProb_eq_re_inner (φ : QState H) :
    MeasureProb φ Finset.univ = (Qatlib.Foundations.PureStateMath.Inner φ φ).re := by
  rw [Qatlib.Foundations.PureStateMath.inner_self, Complex.re_sum]
  show (∑ x ∈ Finset.univ, ‖φ x‖ ^ 2)
    = ∑ x ∈ Finset.univ, ((‖φ x‖ ^ 2 : ℝ) : ℂ).re
  exact Finset.sum_congr rfl fun x _ => (Complex.ofReal_re _).symm

/-- The total measurement mass of two mutually orthogonal states is the sum of their individual
masses. -/
private theorem measureProb_add_of_inner (x y : QState H)
    (hxy : Qatlib.Foundations.PureStateMath.Inner x y = 0) (hyx : Qatlib.Foundations.PureStateMath.Inner y x = 0) :
    MeasureProb (x + y) Finset.univ
      = MeasureProb x Finset.univ + MeasureProb y Finset.univ := by
  have hexp : Qatlib.Foundations.PureStateMath.Inner (x + y) (x + y)
      = Qatlib.Foundations.PureStateMath.Inner x x + Qatlib.Foundations.PureStateMath.Inner y y := by
    rw [inner_add_left', inner_add_right', inner_add_right', hxy, hyx]
    ring
  rw [measureProb_eq_re_inner (x + y), hexp, Complex.add_re,
    measureProb_eq_re_inner x, measureProb_eq_re_inner y]

/-- The complement of an orthogonal projector is an orthogonal projector. -/
private theorem one_sub_proj_orth (P : Matrix H H ℂ) (hP : IsOrthogonalProjector P) :
    IsOrthogonalProjector (1 - P) := by
  have hstarP : Pᴴ = P := by simpa only [Matrix.star_eq_conjTranspose] using! hP.2
  constructor
  · show (1 - P) * (1 - P) = 1 - P
    calc (1 - P) * (1 - P) = 1 * (1 - P) - P * (1 - P) := Matrix.sub_mul _ _ _
      _ = (1 - P) - P * (1 - P) := by rw [Matrix.one_mul]
      _ = (1 - P) - (P - P * P) := by rw [Matrix.mul_sub, Matrix.mul_one]
      _ = (1 - P) - (P - P) := by rw [hP.1]
      _ = 1 - P := by rw [sub_self, sub_zero]
  · show (1 - P)ᴴ = 1 - P
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hstarP]

/-- Applying a target projector that commutes with two orthogonal branch projectors preserves
orthogonality between the branches. -/
private theorem inner_target_orth_branches (T P Q : Matrix H H ℂ)
    (hT : IsOrthogonalProjector T) (hP : IsOrthogonalProjector P)
    (hQ : IsOrthogonalProjector Q) (hPQ : P * Q = 0)
    (hTP : T * P = P * T) (hTQ : T * Q = Q * T) (w z : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (ApplyGate (T * P) w) (ApplyGate (T * Q) z) = 0 := by
  have hAB : (T * P)ᴴ * (T * Q) = 0 := by
    have hstarP : Pᴴ = P := by simpa only [Matrix.star_eq_conjTranspose] using! hP.2
    have hstarT : Tᴴ = T := by simpa only [Matrix.star_eq_conjTranspose] using! hT.2
    rw [Matrix.conjTranspose_mul, hstarP, hstarT]
    have hstep : (P * T) * (T * Q) = P * (T * T) * Q := by
      rw [Matrix.mul_assoc P T (T * Q), ← Matrix.mul_assoc T T Q,
        ← Matrix.mul_assoc P (T * T) Q]
    rw [hstep, hT.1, ← hTP, Matrix.mul_assoc, hPQ, Matrix.mul_zero]
  simp only [Qatlib.Foundations.PureStateMath.Inner, ApplyGate]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hAB]
  simp

/-- A newly stopped branch is contained in every strictly later stopping projector. -/
private theorem freshStop_mul_stopAt_ge (f : CoherentVtFrame H m) {j n : ℕ}
    (hj : j < m) (hn : n < m) (hjn : j < n) :
    f.freshStop ⟨j, hj⟩ * f.stopAt ⟨n, hn⟩ = f.freshStop ⟨j, hj⟩ := by
  have h1 : f.stop ⟨n, Nat.lt_succ_of_lt hn⟩ * f.stop ⟨j + 1, Nat.succ_lt_succ hj⟩
      = f.stop ⟨j + 1, Nat.succ_lt_succ hj⟩ :=
    nestedStopFamily_mul_rev f.stopNested (by simp only [Fin.le_def]; omega)
  have h2 : f.stop ⟨n, Nat.lt_succ_of_lt hn⟩ * f.stop ⟨j, Nat.lt_succ_of_lt hj⟩
      = f.stop ⟨j, Nat.lt_succ_of_lt hj⟩ :=
    nestedStopFamily_mul_rev f.stopNested (by simp only [Fin.le_def]; omega)
  have h3 : f.stop ⟨n, Nat.lt_succ_of_lt hn⟩ * f.freshStop ⟨j, hj⟩
      = f.freshStop ⟨j, hj⟩ := by
    show f.stop ⟨n, Nat.lt_succ_of_lt hn⟩
        * (f.stop ⟨j + 1, Nat.succ_lt_succ hj⟩ - f.stop ⟨j, Nat.lt_succ_of_lt hj⟩) = _
    rw [Matrix.mul_sub, h1, h2]
    rfl
  have hstar := congrArg Matrix.conjTranspose h3
  have hfresh : (f.freshStop ⟨j, hj⟩)ᴴ = f.freshStop ⟨j, hj⟩ := by
    simpa only [Matrix.star_eq_conjTranspose] using! (f.freshStop_orth ⟨j, hj⟩).2
  have hstopn : (f.stop ⟨n, Nat.lt_succ_of_lt hn⟩)ᴴ
      = f.stop ⟨n, Nat.lt_succ_of_lt hn⟩ := by
    simpa only [Matrix.star_eq_conjTranspose] using!
      (f.stopNested.1 ⟨n, Nat.lt_succ_of_lt hn⟩).2
  rw [Matrix.conjTranspose_mul, hfresh, hstopn] at hstar
  exact hstar

/-- Projecting the current stage operation onto its newly stopped branch agrees with projecting
the current round. -/
private theorem freshStop_mul_stageOp (f : CoherentVtFrame H m) (j : Fin m) :
    f.freshStop j * f.stageOp j = f.freshStop j * f.round j := by
  have h0 : f.freshStop j * f.stopAt j = 0 := (f.freshStop_orthogonal j).2
  have h1 : f.freshStop j * (1 - f.stopAt j) = f.freshStop j := by
    rw [Matrix.mul_sub, Matrix.mul_one, h0, sub_zero]
  show f.freshStop j * (f.stopAt j + (1 - f.stopAt j) * f.round j)
      = f.freshStop j * f.round j
  rw [Matrix.mul_add, h0, zero_add, ← Matrix.mul_assoc, h1]

/-- A later stage operation acts as the identity after projection onto an earlier newly stopped
branch. -/
private theorem freshStop_mul_stageOp_later (f : CoherentVtFrame H m) {j n : ℕ}
    (hj : j < m) (hn : n < m) (hjn : j < n) :
    f.freshStop ⟨j, hj⟩ * f.stageOp ⟨n, hn⟩ = f.freshStop ⟨j, hj⟩ := by
  have hnest := freshStop_mul_stopAt_ge f hj hn hjn
  have h0 : f.freshStop ⟨j, hj⟩ * (1 - f.stopAt ⟨n, hn⟩) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hnest, sub_self]
  show f.freshStop ⟨j, hj⟩ * (f.stopAt ⟨n, hn⟩ + (1 - f.stopAt ⟨n, hn⟩) * f.round ⟨n, hn⟩)
      = f.freshStop ⟨j, hj⟩
  rw [Matrix.mul_add, hnest, ← Matrix.mul_assoc, h0, zero_mul, add_zero]

/-- For finite stage indices in increasing order, the earlier newly stopped projector absorbs
the later stage operation. -/
private theorem freshStop_mul_stageOp_later' (f : CoherentVtFrame H m) (j k : Fin m)
    (hjk : j.val < k.val) :
    f.freshStop j * f.stageOp k = f.freshStop j := by
  have hnest := freshStop_mul_stopAt_ge f j.isLt k.isLt hjk
  have h0 : f.freshStop j * (1 - f.stopAt k) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hnest, sub_self]
  show f.freshStop j * (f.stopAt k + (1 - f.stopAt k) * f.round k) = f.freshStop j
  rw [Matrix.mul_add, hnest, ← Matrix.mul_assoc, h0, zero_mul, add_zero]

/-- The component newly stopped at stage `j` remains equal to its value immediately after that
round throughout all later stages. -/
theorem freshStop_stageState_frozen (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    ∀ (n : ℕ) (hjn : j.val < n) (hn : n ≤ m),
      ApplyGate (f.freshStop j) (f.stageState ψ n hn)
        = ApplyGate (f.freshStop j)
            (ApplyGate (f.round j)
              (f.stageState ψ j.val (Nat.le_of_lt j.isLt))) := by
  intro n hjn hn
  refine Nat.le_induction (m := j.val + 1)
    (P := fun k _ => ∀ hb : k ≤ m,
      ApplyGate (f.freshStop j) (f.stageState ψ k hb)
        = ApplyGate (f.freshStop j)
            (ApplyGate (f.round j)
              (f.stageState ψ j.val (Nat.le_of_lt j.isLt))))
    (fun hb => ?_) (fun k hk ih hb => ?_) n (by omega) hn
  · have hstep : f.stageState ψ (j.val + 1) hb
        = ApplyGate (f.stageOp j) (f.stageState ψ j.val (Nat.le_of_lt j.isLt)) := by
      have h := f.stageState_succ ψ j.val hb
      rw [show (⟨j.val, Nat.lt_of_succ_le hb⟩ : Fin m) = j from Fin.ext rfl] at h
      exact h
    rw [hstep, ← applyGate_mul, freshStop_mul_stageOp, applyGate_mul]
  · rw [f.stageState_succ ψ k hb, ← applyGate_mul,
      freshStop_mul_stageOp_later' f j ⟨k, Nat.lt_of_succ_le hb⟩ (by show ↑j < k; omega)]
    exact ih (by omega)

/-- The target measurement mass in the branch newly stopped at stage `j`, evaluated immediately
after its round. -/
def freshStopSuccess (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) : ℝ :=
  MeasureProb (ApplyGate (f.target * f.freshStop j)
    (ApplyGate (f.round j) (f.stageState ψ j.val (by omega)))) Finset.univ

/-- The target measurement mass in the branch still running after all stages. -/
def runningStopSuccess (f : CoherentVtFrame H m) (ψ : QState H) : ℝ :=
  MeasureProb (ApplyGate (f.target * (1 - f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩))
    (f.stageState ψ m (by omega))) Finset.univ

/-- The newly stopped success mass at a natural-number stage index, extended by zero outside the
stage range. -/
def freshStopSuccessAt (f : CoherentVtFrame H m) (ψ : QState H) (j : ℕ) : ℝ :=
  if hj : j < m then freshStopSuccess f ψ ⟨j, hj⟩ else 0

/-- At a valid stage index, the zero-extended success mass equals `freshStopSuccess`. -/
theorem freshStopSuccessAt_of_lt (f : CoherentVtFrame H m) (ψ : QState H) {j : ℕ}
    (hj : j < m) :
    freshStopSuccessAt f ψ j = freshStopSuccess f ψ ⟨j, hj⟩ := by
  simp [freshStopSuccessAt, hj]

/-- At any valid prefix length, the stopped target mass is the sum of the newly stopped success
masses in that prefix. -/
private theorem stoppedSuccess_sum (f : CoherentVtFrame H m) (ψ : QState H) :
    ∀ (n : ℕ) (hn : n ≤ m),
      MeasureProb (ApplyGate (f.target * f.stop ⟨n, Nat.lt_succ_of_le hn⟩)
        (f.stageState ψ n hn)) Finset.univ
          = ∑ i ∈ Finset.range n, freshStopSuccessAt f ψ i := by
  intro n hn
  induction n with
  | zero =>
    have h0 : f.target * f.stop ⟨0, Nat.lt_succ_of_le hn⟩ = 0 := by
      show f.target * f.stop 0 = 0
      rw [f.stopZero, Matrix.mul_zero]
    rw [h0, Finset.sum_range_zero]
    simp [MeasureProb, BornProb, ApplyGate, Matrix.zero_mulVec]
  | succ n ih =>
    have hn' : n ≤ m := by omega
    have hTP : f.target * f.stopAt ⟨n, by omega⟩
        = f.stopAt ⟨n, by omega⟩ * f.target := f.targetCommutes ⟨n, by omega⟩
    have hTQ : f.target * f.freshStop ⟨n, by omega⟩
        = f.freshStop ⟨n, by omega⟩ * f.target := by
      have h1 := f.targetCommutes ⟨n, by omega⟩
      have h2 := f.targetCommutes ⟨n + 1, by omega⟩
      show f.target * (f.stop ⟨n + 1, by omega⟩ - f.stop ⟨n, by omega⟩)
          = (f.stop ⟨n + 1, by omega⟩ - f.stop ⟨n, by omega⟩) * f.target
      rw [Matrix.mul_sub, Matrix.sub_mul, h2, h1]
    have hsplit : f.stop ⟨n + 1, Nat.lt_succ_of_le (by omega)⟩
        = f.stopAt ⟨n, by omega⟩ + f.freshStop ⟨n, by omega⟩ :=
      stopHistory_split f ⟨n, by omega⟩
    have horth1 : Qatlib.Foundations.PureStateMath.Inner
        (ApplyGate (f.target * f.stopAt ⟨n, by omega⟩) (f.stageState ψ (n + 1) (by omega)))
        (ApplyGate (f.target * f.freshStop ⟨n, by omega⟩)
          (f.stageState ψ (n + 1) (by omega))) = 0 :=
      inner_target_orth_branches f.target (f.stopAt ⟨n, by omega⟩)
        (f.freshStop ⟨n, by omega⟩) f.targetOrth
        (f.stopNested.1 ⟨n, by omega⟩) (f.freshStop_orth ⟨n, by omega⟩)
        (f.freshStop_orthogonal ⟨n, by omega⟩).1 hTP hTQ _ _
    have horth2 : Qatlib.Foundations.PureStateMath.Inner
        (ApplyGate (f.target * f.freshStop ⟨n, by omega⟩)
          (f.stageState ψ (n + 1) (by omega)))
        (ApplyGate (f.target * f.stopAt ⟨n, by omega⟩)
          (f.stageState ψ (n + 1) (by omega))) = 0 :=
      inner_target_orth_branches f.target (f.freshStop ⟨n, by omega⟩)
        (f.stopAt ⟨n, by omega⟩) f.targetOrth
        (f.freshStop_orth ⟨n, by omega⟩) (f.stopNested.1 ⟨n, by omega⟩)
        (f.freshStop_orthogonal ⟨n, by omega⟩).2 hTQ hTP _ _
    have hstep : f.stageState ψ (n + 1) (by omega)
        = ApplyGate (f.stageOp ⟨n, by omega⟩) (f.stageState ψ n hn') :=
      f.stageState_succ ψ n (by omega)
    have hmat1 : (f.target * f.stopAt ⟨n, by omega⟩) * f.stageOp ⟨n, by omega⟩
        = f.target * f.stopAt ⟨n, by omega⟩ := by
      rw [Matrix.mul_assoc, stop_mul_stageOp]
    have hpiece1 : ApplyGate (f.target * f.stopAt ⟨n, by omega⟩)
          (f.stageState ψ (n + 1) (by omega))
        = ApplyGate (f.target * f.stopAt ⟨n, by omega⟩) (f.stageState ψ n hn') := by
      rw [hstep, ← applyGate_mul, hmat1]
    have hmat2 : (f.target * f.freshStop ⟨n, by omega⟩) * f.stageOp ⟨n, by omega⟩
        = (f.target * f.freshStop ⟨n, by omega⟩) * f.round ⟨n, by omega⟩ := by
      rw [Matrix.mul_assoc, freshStop_mul_stageOp, ← Matrix.mul_assoc]
    have hpiece2 : ApplyGate (f.target * f.freshStop ⟨n, by omega⟩)
          (f.stageState ψ (n + 1) (by omega))
        = ApplyGate (f.target * f.freshStop ⟨n, by omega⟩)
            (ApplyGate (f.round ⟨n, by omega⟩) (f.stageState ψ n hn')) := by
      rw [hstep, ← applyGate_mul, hmat2, applyGate_mul]
    have hvec : ApplyGate (f.target * f.stop ⟨n + 1, Nat.lt_succ_of_le (by omega)⟩)
        (f.stageState ψ (n + 1) (by omega))
        = ApplyGate (f.target * f.stopAt ⟨n, by omega⟩) (f.stageState ψ (n + 1) (by omega))
          + ApplyGate (f.target * f.freshStop ⟨n, by omega⟩)
              (f.stageState ψ (n + 1) (by omega)) := by
      rw [hsplit, Matrix.mul_add]
      simp only [ApplyGate, Matrix.add_mulVec]
    have ih' : MeasureProb (ApplyGate (f.target * f.stopAt ⟨n, by omega⟩)
        (f.stageState ψ n hn')) Finset.univ
        = ∑ i ∈ Finset.range n, freshStopSuccessAt f ψ i := ih hn'
    rw [hvec]
    rw [measureProb_add_of_inner
      (ApplyGate (f.target * f.stopAt ⟨n, by omega⟩) (f.stageState ψ (n + 1) (by omega)))
      (ApplyGate (f.target * f.freshStop ⟨n, by omega⟩) (f.stageState ψ (n + 1) (by omega)))
      horth1 horth2]
    rw [hpiece1, hpiece2]
    rw [ih']
    rw [Finset.sum_range_succ, freshStopSuccessAt_of_lt f ψ (by omega)]
    have hM2 : MeasureProb (ApplyGate (f.target * f.freshStop ⟨n, by omega⟩)
        (ApplyGate (f.round ⟨n, by omega⟩) (f.stageState ψ n hn'))) Finset.univ
        = freshStopSuccess f ψ ⟨n, by omega⟩ := rfl
    rw [hM2]

/-- The final success mass splits into the sum of newly stopped success masses and the final
running success mass. -/
theorem runSuccess_stopHistory_split (f : CoherentVtFrame H m) (ψ : QState H) :
    f.runSuccess ψ = (∑ j : Fin m, freshStopSuccess f ψ j) + runningStopSuccess f ψ := by
  have hTP : f.target * f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩
      = f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩ * f.target :=
    f.targetCommutes ⟨m, Nat.lt_succ_of_le (le_refl m)⟩
  have hTQ : f.target * (1 - f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩)
      = (1 - f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩) * f.target := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, hTP]
  have hPQ : f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩
      * (1 - f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one,
      (f.stopNested.1 ⟨m, Nat.lt_succ_of_le (le_refl m)⟩).1, sub_self]
  have hQP : (1 - f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩)
      * f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩ = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul,
      (f.stopNested.1 ⟨m, Nat.lt_succ_of_le (le_refl m)⟩).1, sub_self]
  have hvec : ApplyGate f.target (f.stageState ψ m (by omega))
      = ApplyGate (f.target * f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩)
          (f.stageState ψ m (by omega))
        + ApplyGate (f.target * (1 - f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩))
          (f.stageState ψ m (by omega)) := by
    have hsplit : f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩
        + (1 - f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩) = 1 := by abel
    calc ApplyGate f.target (f.stageState ψ m (by omega))
        = ApplyGate (f.target * 1) (f.stageState ψ m (by omega)) := by rw [Matrix.mul_one]
      _ = ApplyGate (f.target * (f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩
            + (1 - f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩)))
            (f.stageState ψ m (by omega)) := by rw [hsplit]
      _ = _ := by
          rw [Matrix.mul_add]
          simp only [ApplyGate, Matrix.add_mulVec]
  have horth1 : Qatlib.Foundations.PureStateMath.Inner
      (ApplyGate (f.target * f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩)
        (f.stageState ψ m (by omega)))
      (ApplyGate (f.target * (1 - f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩))
        (f.stageState ψ m (by omega))) = 0 :=
    inner_target_orth_branches f.target
      (f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩)
      (1 - f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩) f.targetOrth
      (f.stopNested.1 ⟨m, Nat.lt_succ_of_le (le_refl m)⟩)
      (one_sub_proj_orth _ (f.stopNested.1 ⟨m, Nat.lt_succ_of_le (le_refl m)⟩))
      hPQ hTP hTQ _ _
  have horth2 : Qatlib.Foundations.PureStateMath.Inner
      (ApplyGate (f.target * (1 - f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩))
        (f.stageState ψ m (by omega)))
      (ApplyGate (f.target * f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩)
        (f.stageState ψ m (by omega))) = 0 :=
    inner_target_orth_branches f.target
      (1 - f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩)
      (f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩) f.targetOrth
      (one_sub_proj_orth _ (f.stopNested.1 ⟨m, Nat.lt_succ_of_le (le_refl m)⟩))
      (f.stopNested.1 ⟨m, Nat.lt_succ_of_le (le_refl m)⟩)
      hQP hTQ hTP _ _
  have hconv : ∑ i ∈ Finset.range m, freshStopSuccessAt f ψ i
      = ∑ j : Fin m, freshStopSuccess f ψ j := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => freshStopSuccessAt_of_lt f ψ j.isLt
  show MeasureProb (ApplyGate f.target (f.stageState ψ m (by omega))) Finset.univ = _
  rw [hvec]
  rw [measureProb_add_of_inner
    (ApplyGate (f.target * f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩)
      (f.stageState ψ m (by omega)))
    (ApplyGate (f.target * (1 - f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩))
      (f.stageState ψ m (by omega)))
    horth1 horth2]
  rw [stoppedSuccess_sum f ψ m (le_refl m), hconv]
  rfl

/-- The weighted oracle cost of the paid prefix ending immediately after stage `j`, with stage
weights `2 ^ i`. -/
def paidStopReceipt (f : CoherentVtFrame H m) (j : Fin m) : ℕ :=
  Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost (fun i => 2 ^ i) (paidPrefix f (j.val + 1) (by omega))

/-- The paid receipt through stage `j` equals `2 ^ (j.val + 1) - 1`. -/
theorem paidStopReceipt_eq (f : CoherentVtFrame H m) (j : Fin m) :
    paidStopReceipt f j = 2 ^ (j.val + 1) - 1 := by
  have h := paidPrefix_accessPrice f (j.val + 1) (by omega)
  unfold paidStopReceipt at *
  omega

/-- The weighted oracle cost of the full paid prefix, with stage weights `2 ^ i`. -/
def paidFullReceipt (f : CoherentVtFrame H m) : ℕ :=
  Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost (fun i => 2 ^ i) (paidPrefix f m (by omega))

/-- The full paid receipt equals `2 ^ m - 1`. -/
theorem paidFullReceipt_eq (f : CoherentVtFrame H m) :
    paidFullReceipt f = 2 ^ m - 1 := by
  have h := paidPrefix_accessPrice f m (by omega)
  unfold paidFullReceipt at *
  omega

/-- Every stage's paid receipt is at most the full paid receipt. -/
theorem paidStopReceipt_le_full (f : CoherentVtFrame H m) (j : Fin m) :
    paidStopReceipt f j ≤ paidFullReceipt f := by
  rw [paidStopReceipt_eq, paidFullReceipt_eq]
  have hpow : (2 : ℕ) ^ (j.val + 1) ≤ 2 ^ m :=
    pow_le_pow_right' (a := (2 : ℕ)) (by norm_num) (by omega)
  omega

/-- The paid receipt through a stage is bounded by that stage's stopping time. -/
theorem paidReceipt_le_stopTime (f : CoherentVtFrame H m) (j : Fin m) :
    (paidStopReceipt f j : ℝ) ≤ stopTime j.val := by
  have h1 : (1 : ℕ) ≤ 2 ^ (j.val + 1) := Nat.one_le_two_pow
  have h2 : ((2 ^ (j.val + 1) - 1 : ℕ) : ℝ) = (2 : ℝ) ^ (j.val + 1) - 1 := by
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (j.val + 1) := by exact_mod_cast Nat.one_le_two_pow
  rw [paidStopReceipt_eq, h2]
  unfold stopTime
  linarith

/-- The full paid receipt is bounded by the maximum stopping time. -/
theorem paidFullReceipt_le_maxStopTime (f : CoherentVtFrame H m) :
    (paidFullReceipt f : ℝ) ≤ maxStopTime m := by
  have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
  have h2 : ((2 ^ m - 1 : ℕ) : ℝ) = (2 : ℝ) ^ m - 1 := by
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast Nat.one_le_two_pow
  rw [paidFullReceipt_eq, h2]
  unfold maxStopTime
  linarith

/-- The full paid receipt equals the maximum stopping time minus one. -/
theorem paidFullReceipt_eq_maxStopTime_sub_one (f : CoherentVtFrame H m) :
    (paidFullReceipt f : ℝ) = maxStopTime m - 1 := by
  have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
  rw [paidFullReceipt_eq, maxStopTime, Nat.cast_sub h1]
  push_cast
  ring

/-- The paid prefix recovers the newly stopped mass with weighted cost `2 ^ (j.val + 1) - 1` and
gate count `4 * (j.val + 1)`. It is legal and makes exactly one forward call to each
included slot and no other directed calls. -/
theorem paid_fresh_receipt (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    MeasureProb (ApplyGate (f.freshStop j) (payload (Qatlib.Concepts.QlsReadoutSpec.Amplification.run (by decide : 0 < 2)
        (baseOracles f) (paidPrefix f (j.val + 1) (by omega)) ψ))) Finset.univ
      = f.freshStopMass ψ j ∧
    Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost (fun i => 2 ^ i) (paidPrefix f (j.val + 1) (by omega))
      = 2 ^ (j.val + 1) - 1 ∧
    Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (paidPrefix f (j.val + 1) (by omega)) = 4 * (j.val + 1) ∧
    Qatlib.Concepts.QlsReadoutSpec.Amplification.legal m (paidPrefix f (j.val + 1) (by omega)) ∧
    ∀ slot adj, directedCalls (paidPrefix f (j.val + 1) (by omega)) slot adj
      = if slot < j.val + 1 ∧ adj = false then 1 else 0 := by
  refine ⟨paid_fresh_mass f ψ j, ?_, paidPrefix_knownCount f (j.val + 1) (by omega),
    paidPrefix_legal f (j.val + 1) (by omega),
    fun slot adj => paidPrefix_directedCalls f (j.val + 1) (by omega) slot adj⟩
  have h := paidPrefix_accessPrice f (j.val + 1) (by omega)
  omega

/-- The total measurement mass in the branch still running at the end of the coherent execution. -/
def runningStopMass (f : CoherentVtFrame H m) (ψ : QState H) : ℝ :=
  MeasureProb (ApplyGate (1 - f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩)
    (f.stageState ψ m (by omega))) Finset.univ

/-- The final running mass is nonnegative. -/
theorem runningStopMass_nonneg (f : CoherentVtFrame H m) (ψ : QState H) :
    0 ≤ runningStopMass f ψ := measureProb_nonneg _ _

/-- The final running mass equals the input's total mass minus the sum of newly stopped masses. -/
theorem runningStopMass_eq (f : CoherentVtFrame H m) (ψ : QState H) :
    runningStopMass f ψ = MeasureProb ψ Finset.univ - ∑ j : Fin m, f.freshStopMass ψ j :=
  f.runningMass_eq_one_sub_sum ψ

/-- A complete final stopping projector leaves zero running mass for a normalized input. -/
theorem runningStopMass_zero (f : CoherentVtFrame H m) (ψ : QState H)
    (hcomplete : f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩ = 1) (hnorm : Normalized ψ) :
    runningStopMass f ψ = 0 := by
  rw [runningStopMass_eq, f.freshStopMass_total_eq_one ψ hcomplete hnorm,
    measureProb_univ hnorm]
  ring

/-- The sum of each stopping receipt weighted by its newly stopped mass, including the full
receipt weighted by the final running mass. -/
def receiptStopMean (f : CoherentVtFrame H m) (ψ : QState H) : ℝ :=
  ∑ j : Fin m, (paidStopReceipt f j : ℝ) * f.freshStopMass ψ j
    + (paidFullReceipt f : ℝ) * runningStopMass f ψ

/-- The sum of squared stopping receipts weighted by their branch masses, including the squared
full receipt for the final running branch. -/
def receiptSecondMoment (f : CoherentVtFrame H m) (ψ : QState H) : ℝ :=
  ∑ j : Fin m, ((paidStopReceipt f j : ℝ)) ^ 2 * f.freshStopMass ψ j
    + ((paidFullReceipt f : ℝ)) ^ 2 * runningStopMass f ψ

/-- The first paid receipt moment is nonnegative. -/
theorem receiptStopMean_nonneg (f : CoherentVtFrame H m) (ψ : QState H) :
    0 ≤ receiptStopMean f ψ := by
  refine add_nonneg (Finset.sum_nonneg fun j _ => ?_) ?_
  · exact mul_nonneg (Nat.cast_nonneg _) (f.freshStopMass_nonneg ψ j)
  · exact mul_nonneg (Nat.cast_nonneg _) (runningStopMass_nonneg f ψ)

/-- The second paid receipt moment is nonnegative. -/
theorem receiptSecondMoment_nonneg (f : CoherentVtFrame H m) (ψ : QState H) :
    0 ≤ receiptSecondMoment f ψ := by
  refine add_nonneg (Finset.sum_nonneg fun j _ => ?_) ?_
  · exact mul_nonneg (sq_nonneg _) (f.freshStopMass_nonneg ψ j)
  · exact mul_nonneg (sq_nonneg _) (runningStopMass_nonneg f ψ)

/-- For complete stopping and normalized input, the receipt mean is the sum over newly stopped
branches alone. -/
theorem receiptStopMean_complete (f : CoherentVtFrame H m) (ψ : QState H)
    (hcomplete : f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩ = 1) (hnorm : Normalized ψ) :
    receiptStopMean f ψ = ∑ j : Fin m, (paidStopReceipt f j : ℝ) * f.freshStopMass ψ j := by
  rw [receiptStopMean, runningStopMass_zero f ψ hcomplete hnorm, mul_zero, add_zero]

/-- For complete stopping and normalized input, the second receipt moment is the sum over newly
stopped branches alone. -/
theorem receiptSecondMoment_complete (f : CoherentVtFrame H m) (ψ : QState H)
    (hcomplete : f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩ = 1) (hnorm : Normalized ψ) :
    receiptSecondMoment f ψ
      = ∑ j : Fin m, ((paidStopReceipt f j : ℝ)) ^ 2 * f.freshStopMass ψ j := by
  rw [receiptSecondMoment, runningStopMass_zero f ψ hcomplete hnorm, mul_zero, add_zero]

/-- The second receipt moment is at most the full paid receipt times the first receipt moment. -/
theorem receiptSecondMoment_le_max_mul_mean (f : CoherentVtFrame H m) (ψ : QState H) :
    receiptSecondMoment f ψ ≤ (paidFullReceipt f : ℝ) * receiptStopMean f ψ := by
  have hq : ∀ j : Fin m, 0 ≤ f.freshStopMass ψ j := fun j => f.freshStopMass_nonneg ψ j
  have hrun : 0 ≤ runningStopMass f ψ := runningStopMass_nonneg f ψ
  have hle : ∀ j : Fin m, (paidStopReceipt f j : ℝ) ≤ (paidFullReceipt f : ℝ) :=
    fun j => by exact_mod_cast paidStopReceipt_le_full f j
  have hsum : ∑ j : Fin m, ((paidStopReceipt f j : ℝ)) ^ 2 * f.freshStopMass ψ j
      ≤ (paidFullReceipt f : ℝ) * ∑ j : Fin m, (paidStopReceipt f j : ℝ) * f.freshStopMass ψ j := by
    have hterm : ∀ j : Fin m, ((paidStopReceipt f j : ℝ)) ^ 2 * f.freshStopMass ψ j
        ≤ (paidFullReceipt f : ℝ) * ((paidStopReceipt f j : ℝ) * f.freshStopMass ψ j) := by
      intro j
      have hc : (0 : ℝ) ≤ (paidStopReceipt f j : ℝ) := Nat.cast_nonneg _
      have e1 : (paidStopReceipt f j : ℝ) * (paidStopReceipt f j : ℝ)
          ≤ (paidFullReceipt f : ℝ) * (paidStopReceipt f j : ℝ) :=
        mul_le_mul_of_nonneg_right (hle j) hc
      calc ((paidStopReceipt f j : ℝ)) ^ 2 * f.freshStopMass ψ j
          = (paidStopReceipt f j : ℝ) * (paidStopReceipt f j : ℝ) * f.freshStopMass ψ j := by
            ring
        _ ≤ ((paidFullReceipt f : ℝ) * (paidStopReceipt f j : ℝ)) * f.freshStopMass ψ j :=
            mul_le_mul_of_nonneg_right e1 (hq j)
        _ = (paidFullReceipt f : ℝ)
            * ((paidStopReceipt f j : ℝ) * f.freshStopMass ψ j) := by ring
    calc ∑ j : Fin m, ((paidStopReceipt f j : ℝ)) ^ 2 * f.freshStopMass ψ j
        ≤ ∑ j : Fin m, (paidFullReceipt f : ℝ)
            * ((paidStopReceipt f j : ℝ) * f.freshStopMass ψ j) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = (paidFullReceipt f : ℝ)
            * ∑ j : Fin m, (paidStopReceipt f j : ℝ) * f.freshStopMass ψ j :=
          (Finset.mul_sum Finset.univ
            (fun j => (paidStopReceipt f j : ℝ) * f.freshStopMass ψ j)
            (paidFullReceipt f : ℝ)).symm
  have hrun2 : ((paidFullReceipt f : ℝ)) ^ 2 * runningStopMass f ψ
      ≤ (paidFullReceipt f : ℝ) * ((paidFullReceipt f : ℝ) * runningStopMass f ψ) :=
    le_of_eq (by ring)
  simp only [receiptSecondMoment, receiptStopMean]
  nlinarith [hsum, hrun2]

/-- For complete stopping and normalized input, the second receipt moment is bounded by the
stopping-time second moment. -/
theorem receiptSecondMoment_le_stopSecondMoment (f : CoherentVtFrame H m)
    (ψ : QState H)
    (hcomplete : f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩ = 1) (hnorm : Normalized ψ) :
    receiptSecondMoment f ψ ≤ stopSecondMoment m (fun j => f.freshStopMass ψ j) := by
  rw [receiptSecondMoment_complete f ψ hcomplete hnorm]
  have hle : ∀ j : Fin m, ((paidStopReceipt f j : ℝ)) ^ 2 * f.freshStopMass ψ j
      ≤ f.freshStopMass ψ j * (stopTime j.val) ^ 2 := by
    intro j
    have h1 : (paidStopReceipt f j : ℝ) ≤ stopTime j.val := paidReceipt_le_stopTime f j
    have h2 : 0 ≤ stopTime j.val := by unfold stopTime; positivity
    have hq := f.freshStopMass_nonneg ψ j
    have hsq : ((paidStopReceipt f j : ℝ)) ^ 2 ≤ (stopTime j.val) ^ 2 := by
      have e1 : (paidStopReceipt f j : ℝ) * (paidStopReceipt f j : ℝ)
          ≤ stopTime j.val * (paidStopReceipt f j : ℝ) :=
        mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
      have e2 : stopTime j.val * (paidStopReceipt f j : ℝ)
          ≤ stopTime j.val * stopTime j.val :=
        mul_le_mul_of_nonneg_left h1 h2
      nlinarith [e1, e2]
    nlinarith [hsq, hq]
  calc ∑ j : Fin m, ((paidStopReceipt f j : ℝ)) ^ 2 * f.freshStopMass ψ j
      ≤ ∑ j : Fin m, f.freshStopMass ψ j * (stopTime j.val) ^ 2 :=
        Finset.sum_le_sum fun j _ => hle j
    _ = stopSecondMoment m (fun j => f.freshStopMass ψ j) := rfl

/-- For complete stopping and normalized input, the second receipt moment is at most the maximum
stopping time times the average stopping time. -/
theorem receiptSecondMoment_le_max_mul_average (f : CoherentVtFrame H m) (ψ : QState H)
    (hcomplete : f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩ = 1) (hnorm : Normalized ψ) :
    receiptSecondMoment f ψ
      ≤ maxStopTime m * averageStopTime m (fun j => f.freshStopMass ψ j) :=
  le_trans (receiptSecondMoment_le_stopSecondMoment f ψ hcomplete hnorm)
    (stopSecondMoment_le_max_mul_average (fun j => f.freshStopMass ψ j)
      (fun j => f.freshStopMass_nonneg ψ j)
      (le_of_eq (f.freshStopMass_total_eq_one ψ hcomplete hnorm)))

/-- For complete stopping and normalized input, dividing the second receipt moment by a positive
success parameter is bounded by `meanSquareBound`. -/
theorem nonadaptive_receipt_budget (f : CoherentVtFrame H m) (ψ : QState H)
    (hcomplete : f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩ = 1) (hnorm : Normalized ψ)
    (p : ℝ) (hp : 0 < p) :
    receiptSecondMoment f ψ / p
      ≤ meanSquareBound m (averageStopTime m (fun j => f.freshStopMass ψ j)) p := by
  have h1 := receiptSecondMoment_le_stopSecondMoment f ψ hcomplete hnorm
  have h2 := amplified_stopSecondMoment_le (fun j => f.freshStopMass ψ j)
    (fun j => f.freshStopMass_nonneg ψ j)
    (le_of_eq (f.freshStopMass_total_eq_one ψ hcomplete hnorm)) p hp
  exact (div_le_div_of_nonneg_right h1 (le_of_lt hp)).trans h2

/-- Under the stated complete-stopping, normalization, accuracy, and maximum-time assumptions,
the scaled second receipt moment is bounded by `adaptiveMeanSquareBound`. -/
theorem adaptive_receipt_budget (f : CoherentVtFrame H m) (ψ : QState H)
    (hcomplete : f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩ = 1) (hnorm : Normalized ψ)
    (p : ℝ) (hp : 0 < p) (c qhat : ℝ) (hacc : estimateAccurate c p qhat)
    (B : ℝ) (hB : maxStopTime m ≤ B) :
    receiptSecondMoment f ψ / p
      ≤ adaptiveMeanSquareBound B (averageStopTime m (fun j => f.freshStopMass ψ j)) p := by
  have h1 := receiptSecondMoment_le_stopSecondMoment f ψ hcomplete hnorm
  have h2 := adaptive_stopSecondMoment_le (fun j => f.freshStopMass ψ j)
    (fun j => f.freshStopMass_nonneg ψ j)
    (le_of_eq (f.freshStopMass_total_eq_one ψ hcomplete hnorm)) p hp c qhat hacc B hB
  exact (div_le_div_of_nonneg_right h1 (le_of_lt hp)).trans h2

/-- Combines the success-history decomposition, legal paid prefix receipts, the second-moment
inequality, and the exact full receipt formulas. -/
theorem frontier1 (f : CoherentVtFrame H m) (ψ : QState H) :
    f.runSuccess ψ = (∑ j : Fin m, freshStopSuccess f ψ j) + runningStopSuccess f ψ ∧
    (∀ j : Fin m,
      MeasureProb (ApplyGate (f.freshStop j) (payload (Qatlib.Concepts.QlsReadoutSpec.Amplification.run (by decide : 0 < 2)
        (baseOracles f) (paidPrefix f (j.val + 1) (by omega)) ψ))) Finset.univ
        = f.freshStopMass ψ j ∧
      paidStopReceipt f j = 2 ^ (j.val + 1) - 1 ∧
      Qatlib.Concepts.QlsReadoutSpec.Amplification.legal m (paidPrefix f (j.val + 1) (by omega))) ∧
    receiptSecondMoment f ψ ≤ (paidFullReceipt f : ℝ) * receiptStopMean f ψ ∧
    paidFullReceipt f = 2 ^ m - 1 ∧
    (paidFullReceipt f : ℝ) = maxStopTime m - 1 := by
  refine ⟨runSuccess_stopHistory_split f ψ, fun j => ?_,
    receiptSecondMoment_le_max_mul_mean f ψ, paidFullReceipt_eq f,
    paidFullReceipt_eq_maxStopTime_sub_one f⟩
  exact ⟨(paid_fresh_receipt f ψ j).1, paidStopReceipt_eq f j,
    (paid_fresh_receipt f ψ j).2.2.2.1⟩

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.StoppedHistoryMoment
end
