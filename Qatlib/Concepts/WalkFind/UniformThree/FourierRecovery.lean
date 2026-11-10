/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniformThree.HiddenSubgroupOracle
import Qatlib.Concepts.SpectralFilter.PhaseReadout.FourierRecoveryDefs
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.IntWordFraming.WordFraming
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.HspRecovery.ReductionCore.CompactPresentation
open Qatlib.Concepts.HspRecovery.ReductionCore.Guarded
open Qatlib.Concepts.HspRecovery.ReductionCore.InPlace
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.PhaseReadout.ArithState

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.WalkFind.UniformThree

open Qatlib
open Qatlib.Foundations.PureStateMath
open Matrix
open scoped Classical BigOperators
set_option warningAsError false

theorem arithState_ext {N : ℕ} {s t : ArithState N}
    (hdata : s.1.1 = t.1.1) (haddend : s.1.2 = t.1.2)
    (hcarry : s.2.1 = t.2.1) (hctrl : s.2.2 = t.2.2) : s = t := by
  have h1 : s.1 = t.1 := Prod.ext hdata haddend
  have h2 : s.2 = t.2 := Prod.ext hcarry hctrl
  exact Prod.ext h1 h2

theorem arithGateFn_add_value {N : ℕ} (s : ArithState N) :
    (arithGateFn (.add) s).data = s.data + s.addend ∧
      (arithGateFn (.add) s).addend = s.addend ∧
      (arithGateFn (.add) s).carry = s.carry := by
  simp [arithGateFn, ArithState.data, ArithState.addend, ArithState.carry, ArithState.ctrl]

theorem arithGateFn_sub_value {N : ℕ} (s : ArithState N) :
    (arithGateFn (.sub) s).data = s.data - s.addend ∧
      (arithGateFn (.sub) s).addend = s.addend ∧
      (arithGateFn (.sub) s).carry = s.carry := by
  simp [arithGateFn, ArithState.data, ArithState.addend, ArithState.carry, ArithState.ctrl]

theorem arithGateFn_cadd_value {N : ℕ} (i : Fin N) (s : ArithState N) :
    (arithGateFn (.cadd i) s).data =
      (if s.ctrl i then s.data + s.addend else s.data) ∧
      (arithGateFn (.cadd i) s).addend = s.addend := by
  by_cases h : s.2.2 i
  · simp [arithGateFn, h, ArithState.data, ArithState.addend, ArithState.ctrl]
  · simp [arithGateFn, h, ArithState.data, ArithState.addend, ArithState.ctrl]

theorem arithGateFn_csub_value {N : ℕ} (i : Fin N) (s : ArithState N) :
    (arithGateFn (.csub i) s).data =
      (if s.ctrl i then s.data - s.addend else s.data) ∧
      (arithGateFn (.csub i) s).addend = s.addend := by
  by_cases h : s.2.2 i
  · simp [arithGateFn, h, ArithState.data, ArithState.addend, ArithState.ctrl]
  · simp [arithGateFn, h, ArithState.data, ArithState.addend, ArithState.ctrl]

theorem arithGateFn_mulConst_value {N : ℕ} (k : ZMod N) (s : ArithState N) :
    (arithGateFn (.mulConst k) s).data = k * s.data ∧
      (arithGateFn (.mulConst k) s).addend = s.addend := by
  simp [arithGateFn, ArithState.data, ArithState.addend, ArithState.carry, ArithState.ctrl]

theorem arithGateFn_cmulConst_value {N : ℕ} (i : Fin N) (k : ZMod N) (s : ArithState N) :
    (arithGateFn (.cmulConst i k) s).data =
      (if s.ctrl i then k * s.data else s.data) ∧
      (arithGateFn (.cmulConst i k) s).addend = s.addend := by
  by_cases h : s.2.2 i
  · simp [arithGateFn, h, ArithState.data, ArithState.addend, ArithState.ctrl]
  · simp [arithGateFn, h, ArithState.data, ArithState.addend, ArithState.ctrl]

theorem carryOut_iff {N : ℕ} (d a : ZMod N) :
    carryOut d a = true ↔ N ≤ d.val + a.val := by
  simp [carryOut]

theorem arithGateFn_carry_value {N : ℕ} (s : ArithState N) :
    (arithGateFn (.carry) s).data = s.data ∧
      (arithGateFn (.carry) s).addend = s.addend ∧
      (arithGateFn (.carry) s).carry = Bool.xor s.carry (carryOut s.data s.addend) := by
  simp [arithGateFn, ArithState.data, ArithState.addend, ArithState.carry]

private theorem cadd_ctrl_eq {N : ℕ} (i : Fin N) {s t : ArithState N}
    (h : arithGateFn (.cadd i) s = arithGateFn (.cadd i) t) : s.2.2 = t.2.2 := by
  have h2 : (arithGateFn (.cadd i) s).2.2 = (arithGateFn (.cadd i) t).2.2 :=
    congrArg (fun p => p.2.2) h
  have hleft : (arithGateFn (.cadd i) s).2.2 = s.2.2 := by
    by_cases hs : s.2.2 i
    · simp [arithGateFn, hs]
    · simp [arithGateFn, hs]
  have hright : (arithGateFn (.cadd i) t).2.2 = t.2.2 := by
    by_cases ht : t.2.2 i
    · simp [arithGateFn, ht]
    · simp [arithGateFn, ht]
  rw [hleft, hright] at h2
  exact h2

private theorem csub_ctrl_eq {N : ℕ} (i : Fin N) {s t : ArithState N}
    (h : arithGateFn (.csub i) s = arithGateFn (.csub i) t) : s.2.2 = t.2.2 := by
  have h2 : (arithGateFn (.csub i) s).2.2 = (arithGateFn (.csub i) t).2.2 :=
    congrArg (fun p => p.2.2) h
  have hleft : (arithGateFn (.csub i) s).2.2 = s.2.2 := by
    by_cases hs : s.2.2 i
    · simp [arithGateFn, hs]
    · simp [arithGateFn, hs]
  have hright : (arithGateFn (.csub i) t).2.2 = t.2.2 := by
    by_cases ht : t.2.2 i
    · simp [arithGateFn, ht]
    · simp [arithGateFn, ht]
  rw [hleft, hright] at h2
  exact h2

private theorem cmulConst_ctrl_eq {N : ℕ} (i : Fin N) {k : ZMod N} {s t : ArithState N}
    (h : arithGateFn (.cmulConst i k) s = arithGateFn (.cmulConst i k) t) :
    s.2.2 = t.2.2 := by
  have h2 : (arithGateFn (.cmulConst i k) s).2.2 = (arithGateFn (.cmulConst i k) t).2.2 :=
    congrArg (fun p => p.2.2) h
  have hleft : (arithGateFn (.cmulConst i k) s).2.2 = s.2.2 := by
    by_cases hs : s.2.2 i
    · simp [arithGateFn, hs]
    · simp [arithGateFn, hs]
  have hright : (arithGateFn (.cmulConst i k) t).2.2 = t.2.2 := by
    by_cases ht : t.2.2 i
    · simp [arithGateFn, ht]
    · simp [arithGateFn, ht]
  rw [hleft, hright] at h2
  exact h2

theorem arithGateFn_add_injective {N : ℕ} :
    Function.Injective (arithGateFn (.add : ArithGate N)) := by
  intro s t h
  have hadd : s.1.2 = t.1.2 := by
    have h2 := congrArg (fun p => p.1.2) h
    simp only [arithGateFn] at h2
    exact h2
  have hdata : s.1.1 = t.1.1 := by
    have h2 := congrArg (fun p => p.1.1) h
    simp only [arithGateFn] at h2
    rw [← hadd] at h2
    exact add_right_cancel h2
  have hcarry : s.2.1 = t.2.1 := by
    have h2 := congrArg (fun p => p.2.1) h
    simp only [arithGateFn] at h2
    exact h2
  have hctrl : s.2.2 = t.2.2 := by
    have h2 := congrArg (fun p => p.2.2) h
    simp only [arithGateFn] at h2
    exact h2
  exact arithState_ext hdata hadd hcarry hctrl

theorem arithGateFn_sub_injective {N : ℕ} :
    Function.Injective (arithGateFn (.sub : ArithGate N)) := by
  intro s t h
  have hadd : s.1.2 = t.1.2 := by
    have h2 := congrArg (fun p => p.1.2) h
    simp only [arithGateFn] at h2
    exact h2
  have hdata : s.1.1 = t.1.1 := by
    have h2 := congrArg (fun p => p.1.1) h
    simp only [arithGateFn] at h2
    rw [← hadd] at h2
    have h3 : s.1.1 + (-s.1.2) = t.1.1 + (-s.1.2) := by simpa using! h2
    exact add_right_cancel h3
  have hcarry : s.2.1 = t.2.1 := by
    have h2 := congrArg (fun p => p.2.1) h
    simp only [arithGateFn] at h2
    exact h2
  have hctrl : s.2.2 = t.2.2 := by
    have h2 := congrArg (fun p => p.2.2) h
    simp only [arithGateFn] at h2
    exact h2
  exact arithState_ext hdata hadd hcarry hctrl

theorem arithGateFn_carry_injective {N : ℕ} :
    Function.Injective (arithGateFn (.carry : ArithGate N)) := by
  intro s t h
  have hdata : s.1.1 = t.1.1 := by
    have h2 := congrArg (fun p => p.1.1) h
    simp only [arithGateFn] at h2
    exact h2
  have hadd : s.1.2 = t.1.2 := by
    have h2 := congrArg (fun p => p.1.2) h
    simp only [arithGateFn] at h2
    exact h2
  have hcarry : s.2.1 = t.2.1 := by
    have h2 := congrArg (fun p => p.2.1) h
    simp only [arithGateFn] at h2
    rw [hdata, hadd] at h2
    cases hs : s.2.1 <;> cases ht : t.2.1 <;> simp_all
  have hctrl : s.2.2 = t.2.2 := by
    have h2 := congrArg (fun p => p.2.2) h
    simp only [arithGateFn] at h2
    exact h2
  exact arithState_ext hdata hadd hcarry hctrl

theorem arithGateFn_mulConst_injective {N : ℕ} {k : ZMod N} (hk : IsUnit k) :
    Function.Injective (arithGateFn (.mulConst k : ArithGate N)) := by
  intro s t h
  have hdata : s.1.1 = t.1.1 := by
    have h2 := congrArg (fun p => p.1.1) h
    simp only [arithGateFn] at h2
    exact hk.mul_left_cancel h2
  have hadd : s.1.2 = t.1.2 := by
    have h2 := congrArg (fun p => p.1.2) h
    simp only [arithGateFn] at h2
    exact h2
  have hcarry : s.2.1 = t.2.1 := by
    have h2 := congrArg (fun p => p.2.1) h
    simp only [arithGateFn] at h2
    exact h2
  have hctrl : s.2.2 = t.2.2 := by
    have h2 := congrArg (fun p => p.2.2) h
    simp only [arithGateFn] at h2
    exact h2
  exact arithState_ext hdata hadd hcarry hctrl

theorem arithGateFn_cadd_injective {N : ℕ} (i : Fin N) :
    Function.Injective (arithGateFn (.cadd i : ArithGate N)) := by
  intro s t h
  have hctrl : s.2.2 = t.2.2 := cadd_ctrl_eq i h
  by_cases hs : s.2.2 i
  · have ht : t.2.2 i := by rw [← hctrl]; exact hs
    have hadd : s.1.2 = t.1.2 := by
      have h2 := congrArg (fun p => p.1.2) h
      simp only [arithGateFn, hs, ht, if_true] at h2
      exact h2
    have hdata : s.1.1 = t.1.1 := by
      have h2 := congrArg (fun p => p.1.1) h
      simp only [arithGateFn, hs, ht, if_true] at h2
      rw [← hadd] at h2
      exact add_right_cancel h2
    have hcarry : s.2.1 = t.2.1 := by
      have h2 := congrArg (fun p => p.2.1) h
      simp only [arithGateFn, hs, ht, if_true] at h2
      exact h2
    exact arithState_ext hdata hadd hcarry hctrl
  · have ht : ¬ t.2.2 i := by rw [← hctrl]; exact hs
    simp only [arithGateFn, hs, ht, if_false] at h
    exact h

theorem arithGateFn_csub_injective {N : ℕ} (i : Fin N) :
    Function.Injective (arithGateFn (.csub i : ArithGate N)) := by
  intro s t h
  have hctrl : s.2.2 = t.2.2 := csub_ctrl_eq i h
  by_cases hs : s.2.2 i
  · have ht : t.2.2 i := by rw [← hctrl]; exact hs
    have hadd : s.1.2 = t.1.2 := by
      have h2 := congrArg (fun p => p.1.2) h
      simp only [arithGateFn, hs, ht, if_true] at h2
      exact h2
    have hdata : s.1.1 = t.1.1 := by
      have h2 := congrArg (fun p => p.1.1) h
      simp only [arithGateFn, hs, ht, if_true] at h2
      rw [← hadd] at h2
      have h3 : s.1.1 + (-s.1.2) = t.1.1 + (-s.1.2) := by simpa using! h2
      exact add_right_cancel h3
    have hcarry : s.2.1 = t.2.1 := by
      have h2 := congrArg (fun p => p.2.1) h
      simp only [arithGateFn, hs, ht, if_true] at h2
      exact h2
    exact arithState_ext hdata hadd hcarry hctrl
  · have ht : ¬ t.2.2 i := by rw [← hctrl]; exact hs
    simp only [arithGateFn, hs, ht, if_false] at h
    exact h

theorem arithGateFn_cmulConst_injective {N : ℕ} (i : Fin N) {k : ZMod N} (hk : IsUnit k) :
    Function.Injective (arithGateFn (.cmulConst i k : ArithGate N)) := by
  intro s t h
  have hctrl : s.2.2 = t.2.2 := cmulConst_ctrl_eq i h
  by_cases hs : s.2.2 i
  · have ht : t.2.2 i := by rw [← hctrl]; exact hs
    have hdata : s.1.1 = t.1.1 := by
      have h2 := congrArg (fun p => p.1.1) h
      simp only [arithGateFn, hs, ht, if_true] at h2
      exact hk.mul_left_cancel h2
    have hadd : s.1.2 = t.1.2 := by
      have h2 := congrArg (fun p => p.1.2) h
      simp only [arithGateFn, hs, ht, if_true] at h2
      exact h2
    have hcarry : s.2.1 = t.2.1 := by
      have h2 := congrArg (fun p => p.2.1) h
      simp only [arithGateFn, hs, ht, if_true] at h2
      exact h2
    exact arithState_ext hdata hadd hcarry hctrl
  · have ht : ¬ t.2.2 i := by rw [← hctrl]; exact hs
    simp only [arithGateFn, hs, ht, if_false] at h
    exact h

noncomputable def arithGateMatrix {N : ℕ} [NeZero N] :
    ArithGate N → Matrix (ArithState N) (ArithState N) ℂ
  | .rot a t =>
      Matrix.diagonal fun s => Complex.exp (rotAngle (a * (s.1.1.val : ℤ)) t * Complex.I)
  | g => permMatrix (arithGateFn g)

private theorem ofReal_neg (θ : ℝ) : ((-θ : ℝ) : ℂ) = -((θ : ℝ) : ℂ) := by simp

private theorem rotAngle_neg (num : ℤ) (t : ℕ) :
    rotAngle (-num) t = -rotAngle num t := by
  simp only [rotAngle, Int.cast_neg]
  ring

private theorem arithGateMatrix_rot_star {N : ℕ} [NeZero N] (a : ℤ) (t : ℕ) :
    (arithGateMatrix (.rot a t : ArithGate N))ᴴ = arithGateMatrix (.rot (-a) t : ArithGate N) := by
  have hpoint : ∀ s : ArithState N,
      (starRingEnd ℂ) (Complex.exp (rotAngle (a * (s.1.1.val : ℤ)) t * Complex.I))
        = Complex.exp (rotAngle ((-a) * (s.1.1.val : ℤ)) t * Complex.I) := by
    intro s
    have hnum : (-a) * (s.1.1.val : ℤ) = -(a * (s.1.1.val : ℤ)) := by push_cast; ring
    have hang : rotAngle ((-a) * (s.1.1.val : ℤ)) t
        = -rotAngle (a * (s.1.1.val : ℤ)) t := by
      rw [hnum, rotAngle_neg]
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [hang, ofReal_neg]
    apply congrArg Complex.exp
    ring
  unfold arithGateMatrix
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  exact funext hpoint

theorem arithGateMatrix_rot_unitary {N : ℕ} [NeZero N] (a : ℤ) (t : ℕ) :
    arithGateMatrix (.rot a t : ArithGate N) ∈ Matrix.unitaryGroup (ArithState N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, arithGateMatrix_rot_star]
  simp only [arithGateMatrix]
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext s
  have hang : rotAngle ((-a) * (s.1.1.val : ℤ)) t
      = -rotAngle (a * (s.1.1.val : ℤ)) t := by
    have hnum : (-a) * (s.1.1.val : ℤ) = -(a * (s.1.1.val : ℤ)) := by push_cast; ring
    rw [hnum, rotAngle_neg]
  have hzero : rotAngle ((-a) * (s.1.1.val : ℤ)) t * Complex.I
      + rotAngle (a * (s.1.1.val : ℤ)) t * Complex.I = 0 := by
    rw [hang]
    have hneg : ((-rotAngle (a * (s.1.1.val : ℤ)) t : ℝ) : ℂ)
        = -((rotAngle (a * (s.1.1.val : ℤ)) t : ℝ) : ℂ) := by
      simp
    rw [hneg]
    ring
  rw [← Complex.exp_add, hzero, Complex.exp_zero]

theorem arithGateMatrix_unitary {N : ℕ} [NeZero N] (g : ArithGate N)
    (hg : match g with
      | .mulConst k => IsUnit k
      | .cmulConst _ k => IsUnit k
      | _ => True) :
    arithGateMatrix g ∈ Matrix.unitaryGroup (ArithState N) ℂ := by
  cases g with
  | rot a t => exact arithGateMatrix_rot_unitary a t
  | add =>
      rw [show arithGateMatrix (.add : ArithGate N) = permMatrix (arithGateFn (.add)) from rfl]
      exact permMatrix_unitary_of_injective (arithGateFn_add_injective)
  | sub =>
      rw [show arithGateMatrix (.sub : ArithGate N) = permMatrix (arithGateFn (.sub)) from rfl]
      exact permMatrix_unitary_of_injective (arithGateFn_sub_injective)
  | carry =>
      rw [show arithGateMatrix (.carry : ArithGate N) = permMatrix (arithGateFn (.carry)) from rfl]
      exact permMatrix_unitary_of_injective (arithGateFn_carry_injective)
  | mulConst k =>
      rw [show arithGateMatrix (.mulConst k : ArithGate N)
        = permMatrix (arithGateFn (.mulConst k)) from rfl]
      exact permMatrix_unitary_of_injective (arithGateFn_mulConst_injective hg)
  | cadd i =>
      rw [show arithGateMatrix (.cadd i : ArithGate N)
        = permMatrix (arithGateFn (.cadd i)) from rfl]
      exact permMatrix_unitary_of_injective (arithGateFn_cadd_injective i)
  | csub i =>
      rw [show arithGateMatrix (.csub i : ArithGate N)
        = permMatrix (arithGateFn (.csub i)) from rfl]
      exact permMatrix_unitary_of_injective (arithGateFn_csub_injective i)
  | cmulConst i k =>
      rw [show arithGateMatrix (.cmulConst i k : ArithGate N)
        = permMatrix (arithGateFn (.cmulConst i k)) from rfl]
      exact permMatrix_unitary_of_injective (arithGateFn_cmulConst_injective i hg)

noncomputable def arithProgramMatrix {N : ℕ} [NeZero N] :
    List (ArithGate N) → Matrix (ArithState N) (ArithState N) ℂ
  | [] => 1
  | g :: gs => arithProgramMatrix gs * arithGateMatrix g

theorem arithProgramMatrix_nil (N : ℕ) [NeZero N] :
    arithProgramMatrix ([] : List (ArithGate N)) = 1 := rfl

theorem arithProgramMatrix_cons {N : ℕ} [NeZero N] (g : ArithGate N) (gs : List (ArithGate N)) :
    arithProgramMatrix (g :: gs) = arithProgramMatrix gs * arithGateMatrix g := rfl

theorem arithProgramMatrix_eq_reverse_prod {N : ℕ} [NeZero N] (gs : List (ArithGate N)) :
    arithProgramMatrix gs = (gs.reverse.map arithGateMatrix).prod := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [arithProgramMatrix_cons, ih, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one]

noncomputable def arithProgramCircuit {N : ℕ} [NeZero N] (gs : List (ArithGate N)) :
    Circuit (ArithState N) :=
  gs.map (fun g => Step.gate (arithGateMatrix g))

theorem arithProgramCircuit_resources {N : ℕ} [NeZero N] (gs : List (ArithGate N)) :
    QueryCount (arithProgramCircuit gs) = 0 ∧
      GateCount (arithProgramCircuit gs) = gs.length := by
  constructor
  · induction gs with
    | nil => rfl
    | cons g gs ih =>
      show QueryCount (Step.gate (arithGateMatrix g) :: arithProgramCircuit gs) = 0
      simp [QueryCount, ih]
  · induction gs with
    | nil => rfl
    | cons g gs ih =>
      show GateCount (Step.gate (arithGateMatrix g) :: arithProgramCircuit gs) = (g :: gs).length
      simp [GateCount, ih, List.length_cons]

theorem arithProgramMatrix_unitary {N : ℕ} [NeZero N] (gs : List (ArithGate N))
    (hg : ∀ g ∈ gs, match g with
      | .mulConst k => IsUnit k
      | .cmulConst _ k => IsUnit k
      | _ => True) :
    arithProgramMatrix gs ∈ Matrix.unitaryGroup (ArithState N) ℂ := by
  induction gs with
  | nil => exact (Matrix.unitaryGroup (ArithState N) ℂ).one_mem
  | cons g gs ih =>
    rw [arithProgramMatrix_cons]
    exact Submonoid.mul_mem (Matrix.unitaryGroup (ArithState N) ℂ)
      (ih (fun h hh => hg h (List.mem_cons_of_mem _ hh)))
      (arithGateMatrix_unitary g (hg g List.mem_cons_self))

theorem arithGateFn_add_sub_roundtrip {N : ℕ} (s : ArithState N) :
    (arithGateFn (.sub) (arithGateFn (.add) s)).data = s.data ∧
      (arithGateFn (.sub) (arithGateFn (.add) s)).addend = s.addend ∧
      (arithGateFn (.sub) (arithGateFn (.add) s)).carry = s.carry := by
  simp [arithGateFn, ArithState.data, ArithState.addend, ArithState.carry]

theorem arithGateFn_cadd_csub_roundtrip {N : ℕ} (i : Fin N) (s : ArithState N) :
    (arithGateFn (.csub i) (arithGateFn (.cadd i) s)).data = s.data ∧
      (arithGateFn (.csub i) (arithGateFn (.cadd i) s)).addend = s.addend ∧
      (arithGateFn (.csub i) (arithGateFn (.cadd i) s)).carry = s.carry := by
  by_cases hs : s.2.2 i
  · simp [arithGateFn, hs, ArithState.data, ArithState.addend, ArithState.carry]
  · simp [arithGateFn, hs, ArithState.data, ArithState.addend, ArithState.carry]

theorem arithGateFn_mulConst_roundtrip {N : ℕ} {k : ZMod N} (hk : IsUnit k) (s : ArithState N) :
    (arithGateFn (.mulConst (↑(hk.unit⁻¹) : ZMod N)) (arithGateFn (.mulConst k) s)).data
      = s.data := by
  have hk' : (↑(hk.unit⁻¹) : ZMod N) * k = 1 := by
    calc (↑(hk.unit⁻¹) : ZMod N) * k
        = (↑(hk.unit⁻¹) : ZMod N) * (↑hk.unit : ZMod N) := by rw [hk.unit_spec]
      _ = 1 := by simpa using! Units.mul_inv hk.unit⁻¹
  simp only [arithGateFn, ArithState.data]
  rw [← mul_assoc, hk', one_mul]

theorem arithGateFn_cmulConst_roundtrip {N : ℕ} (i : Fin N) {k : ZMod N} (hk : IsUnit k)
    (s : ArithState N) :
    (arithGateFn (.cmulConst i (↑(hk.unit⁻¹) : ZMod N)) (arithGateFn (.cmulConst i k) s)).data
      = s.data := by
  have hk' : (↑(hk.unit⁻¹) : ZMod N) * k = 1 := by
    calc (↑(hk.unit⁻¹) : ZMod N) * k
        = (↑(hk.unit⁻¹) : ZMod N) * (↑hk.unit : ZMod N) := by rw [hk.unit_spec]
      _ = 1 := by simpa using! Units.mul_inv hk.unit⁻¹
  by_cases hs : s.2.2 i = true
  · simp [arithGateFn, hs, ArithState.data]
    rw [← mul_assoc, hk', one_mul]
  · have hs' : s.2.2 i = false := by
      cases h : s.2.2 i
      · rfl
      · exact absurd h hs
    simp [arithGateFn, hs', ArithState.data]

theorem rotAngle_is_dyadic (num : ℤ) (t : ℕ) :
    ∃ q : ℝ, rotAngle num t = 2 * Real.pi * q ∧ q * (2 ^ t : ℝ) = (num : ℝ) := by
  refine ⟨(num : ℝ) / (2 ^ t : ℝ), ?_, ?_⟩
  · simp only [rotAngle]
    field_simp
  · field_simp

theorem rotAngle_sub_eq_turns {num num' : ℤ} {t : ℕ} (h : (2 ^ t : ℤ) ∣ num - num') :
    ∃ k : ℤ, rotAngle num t - rotAngle num' t = (k : ℝ) * (2 * Real.pi) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have hnum : (num : ℝ) = (num' : ℝ) + (2 ^ t : ℝ) * (k : ℝ) := by
    have hk' : num = num' + (2 ^ t : ℤ) * k := by omega
    rw [hk']
    push_cast
    ring
  simp only [rotAngle]
  rw [hnum]
  have h2t : (2 ^ t : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem rotPhase_eq_of_mod {num num' : ℤ} {t : ℕ} (h : (2 ^ t : ℤ) ∣ num - num') :
    Complex.exp (rotAngle num t * Complex.I) = Complex.exp (rotAngle num' t * Complex.I) := by
  obtain ⟨k, hk⟩ := rotAngle_sub_eq_turns h
  have hsplit : (rotAngle num t : ℝ) = (rotAngle num' t : ℝ) + (k : ℝ) * (2 * Real.pi) := by
    linarith
  have hc : ((rotAngle num t : ℝ) : ℂ) * Complex.I
      = ((rotAngle num' t : ℝ) : ℂ) * Complex.I
        + (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    rw [hsplit, Complex.ofReal_add, Complex.ofReal_mul]
    ring
  have hturn : Complex.exp (((k : ℝ) * (2 * Real.pi) : ℝ) * Complex.I) = 1 := by
    convert! Complex.exp_int_mul_two_pi_mul_I (k : ℤ) using 1 <;> push_cast <;> ring
  rw [hc, Complex.exp_add, hturn, mul_one]

theorem prod_pow_eq_pow_sum {N : ℕ} [NeZero N] (a : ZMod N) :
    ∀ L : List ℕ, (L.map (fun i => a ^ (2 ^ i))).prod = a ^ (L.map (fun i => 2 ^ i)).sum := by
  intro L
  induction L with
  | nil => simp
  | cons i L ih =>
    rw [List.map_cons, List.prod_cons, ih]
    simp only [List.map_cons, List.sum_cons]
    exact (pow_add a (2 ^ i) (List.map (fun i => 2 ^ i) L).sum).symm

theorem bitIndexFin_val {N : ℕ} (hN : 0 < N) {i : ℕ} (hi : i < N) :
    (bitIndexFin hN i).val = i := by
  simp [bitIndexFin, Nat.mod_eq_of_lt hi]

theorem bitIndexFin_eq {N : ℕ} (hN : 0 < N) {i : ℕ} (hi : i < N) :
    bitIndexFin hN i = ⟨i, hi⟩ := by
  apply Fin.ext
  simp [bitIndexFin, Nat.mod_eq_of_lt hi]

private theorem map_map_snd {N : ℕ} (L : List ℕ) (f : ℕ → Fin N) (c : ℕ → ZMod N) :
    (L.map (fun i => (f i, c i))).map (fun p => p.2) = L.map c := by
  rw [List.map_map]
  rfl

theorem modexpFactors_prod {N : ℕ} [NeZero N] (hN : 0 < N) (a : ZMod N) (e : ℕ)
    (h : e < 2 ^ N) :
    ((modexpFactors hN a e h).map (fun p => p.2)).prod = a ^ e := by
  rw [show modexpFactors hN a e h
      = (e.bitIndices).map fun i => (bitIndexFin hN i, a ^ (2 ^ i)) from rfl,
    map_map_snd, prod_pow_eq_pow_sum, Nat.sum_map_two_pow_bitIndices]

theorem arithProgramFn_cmulList {N : ℕ} (ps : List (Fin N × ZMod N)) (s : ArithState N) :
    (arithProgramFn (ps.map (fun p => ArithGate.cmulConst p.1 p.2)) s).data
      = ((ps.filter (fun p => s.ctrl p.1)).map (fun p => p.2)).prod * s.data := by
  induction ps generalizing s with
  | nil => simp [arithProgramFn]
  | cons p ps ih =>
    by_cases h : s.2.2 p.1 = true
    · have hctrl : (arithGateFn (.cmulConst p.1 p.2) s).2.2 = s.2.2 := by
        simp [arithGateFn, h]
      have hctrl' : (arithGateFn (.cmulConst p.1 p.2) s).ctrl = s.ctrl := by
        simpa [ArithState.ctrl] using! hctrl
      have hdata : (arithGateFn (.cmulConst p.1 p.2) s).data = p.2 * s.data := by
        simp [arithGateFn, h, ArithState.data]
      have hfilter : (p :: ps).filter (fun q => s.ctrl q.1)
          = p :: ps.filter (fun q => s.ctrl q.1) := by
        rw [List.filter_cons]
        simp only [ArithState.ctrl]
        rw [if_pos h]
      rw [List.map_cons, arithProgramFn, ih, hctrl', hdata]
      rw [hfilter, List.map_cons, List.prod_cons]
      ring
    · have hfalse : s.2.2 p.1 = false := by
        cases hx : s.2.2 p.1
        · rfl
        · exact absurd hx h
      have hctrl : (arithGateFn (.cmulConst p.1 p.2) s).2.2 = s.2.2 := by
        simp [arithGateFn, hfalse]
      have hctrl' : (arithGateFn (.cmulConst p.1 p.2) s).ctrl = s.ctrl := by
        simpa [ArithState.ctrl] using! hctrl
      have hdata : (arithGateFn (.cmulConst p.1 p.2) s).data = s.data := by
        simp [arithGateFn, hfalse, ArithState.data]
      have hfilter : (p :: ps).filter (fun q => s.ctrl q.1)
          = ps.filter (fun q => s.ctrl q.1) := by
        rw [List.filter_cons]
        simp only [ArithState.ctrl]
        rw [if_neg (by simpa only [ArithState.ctrl] using! h)]
      rw [List.map_cons, arithProgramFn, ih, hctrl', hdata]
      rw [hfilter]

private theorem filter_map_comm {α β : Type*} (f : α → β) (p : β → Bool) :
    ∀ L : List α, (L.map f).filter p = (L.filter (fun a => p (f a))).map f := by
  intro L
  induction L with
  | nil => rfl
  | cons a L ih =>
    by_cases h : p (f a)
    · simp [List.map_cons, List.filter_cons, h, ih]
    · simp [List.map_cons, List.filter_cons, h, ih]

private theorem filter_eq_self_of_all {α : Type*} {p : α → Bool} :
    ∀ (L : List α), (∀ a ∈ L, p a = true) → L.filter p = L := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons a L ih =>
    intro h
    have ha : p a = true := h a List.mem_cons_self
    have hL : ∀ b ∈ L, p b = true := by
      intro b hb
      exact h b (List.mem_cons_of_mem _ hb)
    simp [List.filter_cons, ha, ih hL]

theorem modexpWord_data {N : ℕ} [NeZero N] (hN : 0 < N) (a : ZMod N) (e : ℕ) (h : e < 2 ^ N)
    (s : ArithState N) (hs : ∀ i : ℕ, i < N → s.ctrl (bitIndexFin hN i) = e.testBit i) :
    (arithProgramFn (modexpWord hN a e h) s).data = a ^ e * s.data := by
  rw [modexpWord, arithProgramFn_cmulList]
  have hcomm : (modexpFactors hN a e h).filter (fun p => s.ctrl p.1)
      = ((e.bitIndices).filter (fun i => s.ctrl (bitIndexFin hN i))).map
          (fun i => (bitIndexFin hN i, a ^ (2 ^ i))) := by
    rw [show modexpFactors hN a e h
        = (e.bitIndices).map fun i => (bitIndexFin hN i, a ^ (2 ^ i)) from rfl,
      filter_map_comm]
  rw [hcomm, map_map_snd]
  have hall : ∀ i ∈ e.bitIndices, s.ctrl (bitIndexFin hN i) = true := by
    intro i hi
    have hil : i < N := bitIndex_lt h hi
    have htb : e.testBit i = true := (Nat.mem_bitIndices (i := i) (n := e)).mp hi
    have hval : bitIndexFin hN i = ⟨i, hil⟩ := bitIndexFin_eq hN hil
    have hstep := hs i hil
    rw [hval] at hstep
    have hsame : s.ctrl (bitIndexFin hN i) = e.testBit i := by
      rw [hval]
      exact hstep
    rw [hsame, htb]
  rw [filter_eq_self_of_all (p := fun i => s.ctrl (bitIndexFin hN i)) e.bitIndices hall,
    prod_pow_eq_pow_sum, Nat.sum_map_two_pow_bitIndices]

private theorem countKind_foldl {N : ℕ} (acc : ℕ) (gs : List (ArithGate N))
    (kind : ArithGate N → Bool) (h : ∀ g ∈ gs, kind g = true) :
    gs.foldl (fun c g => if kind g then c + 1 else c) acc = acc + gs.length := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hg : kind g = true := h g List.mem_cons_self
    have hgs : ∀ g' ∈ gs, kind g' = true := by
      intro g' hg'
      exact h g' (List.mem_cons_of_mem _ hg')
    rw [List.foldl_cons, if_pos hg, ih (acc + 1) hgs, List.length_cons]
    ring

private theorem countKind_all {N : ℕ} (gs : List (ArithGate N)) (kind : ArithGate N → Bool)
    (h : ∀ g ∈ gs, kind g = true) : countKind gs kind = gs.length := by
  show gs.foldl (fun c g => if kind g then c + 1 else c) 0 = gs.length
  rw [countKind_foldl 0 gs kind h]
  ring

private theorem countKind_none {N : ℕ} (gs : List (ArithGate N)) (kind : ArithGate N → Bool)
    (h : ∀ g ∈ gs, kind g = false) : countKind gs kind = 0 := by
  have : gs.foldl (fun c g => if kind g then c + 1 else c) 0 = 0 := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      have hg : kind g = false := h g List.mem_cons_self
      have hgs : ∀ g' ∈ gs, kind g' = false := by
        intro g' hg'
        exact h g' (List.mem_cons_of_mem _ hg')
      rw [List.foldl_cons, if_neg (by simpa using! hg), ih hgs]
  exact this

theorem modexpWord_length {N : ℕ} [NeZero N] (hN : 0 < N) (a : ZMod N) (e : ℕ) (h : e < 2 ^ N) :
    (modexpWord hN a e h).length = e.bitIndices.length := by
  simp [modexpWord, show modexpFactors hN a e h
    = (e.bitIndices).map fun i => (bitIndexFin hN i, a ^ (2 ^ i)) from rfl]

theorem modexpWord_ledger {N : ℕ} [NeZero N] (hN : 0 < N) (a : ZMod N) (e : ℕ) (h : e < 2 ^ N) :
    (arithLedger (modexpWord hN a e h) 0).cmulConsts = e.bitIndices.length ∧
      (arithLedger (modexpWord hN a e h) 0).gates = e.bitIndices.length ∧
      (arithLedger (modexpWord hN a e h) 0).adds = 0 ∧
      (arithLedger (modexpWord hN a e h) 0).rots = 0 := by
  have hmem : ∀ g ∈ modexpWord hN a e h, isCmulConst g = true := by
    intro g hg
    simp only [modexpWord, List.mem_map] at hg
    obtain ⟨p, hp, rfl⟩ := hg
    rfl
  have hnone : ∀ g ∈ modexpWord hN a e h, isAdd g = false := by
    intro g hg
    simp only [modexpWord, List.mem_map] at hg
    obtain ⟨p, hp, rfl⟩ := hg
    rfl
  have hnorot : ∀ g ∈ modexpWord hN a e h, isRot g = false := by
    intro g hg
    simp only [modexpWord, List.mem_map] at hg
    obtain ⟨p, hp, rfl⟩ := hg
    rfl
  have hlen : (modexpWord hN a e h).length = e.bitIndices.length := modexpWord_length hN a e h
  refine ⟨?_, hlen, ?_, ?_⟩
  · simp only [arithLedger]
    exact (countKind_all (modexpWord hN a e h) isCmulConst hmem).trans hlen
  · simp only [arithLedger]
    exact countKind_none (modexpWord hN a e h) isAdd hnone
  · simp only [arithLedger]
    exact countKind_none (modexpWord hN a e h) isRot hnorot

theorem clause2_endpoint {N : ℕ} [NeZero N] (hN : 0 < N) (a : ZMod N) (e : ℕ) (h : e < 2 ^ N)
    (s : ArithState N) (hs : ∀ i : ℕ, i < N → s.ctrl (bitIndexFin hN i) = e.testBit i) :
    (arithProgramFn (modexpWord hN a e h) s).data = a ^ e * s.data ∧
      QueryCount (arithProgramCircuit (modexpWord hN a e h)) = 0 ∧
      GateCount (arithProgramCircuit (modexpWord hN a e h)) = e.bitIndices.length ∧
      (arithLedger (modexpWord hN a e h) 0).cmulConsts = e.bitIndices.length ∧
      (∀ num num' : ℤ, (2 ^ 3 : ℤ) ∣ num - num' →
        Complex.exp (rotAngle num 3 * Complex.I) = Complex.exp (rotAngle num' 3 * Complex.I)) := by
  refine ⟨modexpWord_data hN a e h s hs, ?_, ?_, ?_, ?_⟩
  · exact (arithProgramCircuit_resources (modexpWord hN a e h)).1
  · exact (arithProgramCircuit_resources (modexpWord hN a e h)).2.trans
      (modexpWord_length hN a e h)
  · exact (modexpWord_ledger hN a e h).1
  · intro num num' hmod
    exact rotPhase_eq_of_mod hmod

private theorem gcdList_swap (d c : ℕ) : ∀ L : List ℕ,
    gcdList (Nat.gcd d c) L = Nat.gcd (gcdList d L) c := by
  intro L
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [gcdList, gcdList, ih]
    exact (Nat.gcd_assoc _ _ _).trans (by rw [Nat.gcd_comm c x, ← Nat.gcd_assoc])

private theorem gcdList_cons (d c : ℕ) (cs : List ℕ) :
    gcdList d (c :: cs) = Nat.gcd (gcdList d cs) c := by
  rw [gcdList.eq_def]

private theorem gcd_swap_two (a b c : ℕ) :
    Nat.gcd (Nat.gcd a b) c = Nat.gcd (Nat.gcd a c) b := by
  apply Nat.dvd_antisymm
  · have hXa : Nat.gcd (Nat.gcd a b) c ∣ a := by
      exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
    have hXb : Nat.gcd (Nat.gcd a b) c ∣ b := by
      exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    have hXc : Nat.gcd (Nat.gcd a b) c ∣ c := Nat.gcd_dvd_right _ _
    exact Nat.dvd_gcd_iff.mpr ⟨Nat.dvd_gcd_iff.mpr ⟨hXa, hXc⟩, hXb⟩
  · have hYa : Nat.gcd (Nat.gcd a c) b ∣ a := by
      exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
    have hYb : Nat.gcd (Nat.gcd a c) b ∣ b := Nat.gcd_dvd_right _ _
    have hYc : Nat.gcd (Nat.gcd a c) b ∣ c := by
      exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    exact Nat.dvd_gcd_iff.mpr ⟨Nat.dvd_gcd_iff.mpr ⟨hYa, hYb⟩, hYc⟩

private theorem gcdList_swap3 (d a b : ℕ) (cs : List ℕ) :
    gcdList d (a :: b :: cs) = gcdList d (b :: a :: cs) := by
  have e1 := gcdList_cons d a (b :: cs)
  have e2 := gcdList_cons d b (a :: cs)
  calc gcdList d (a :: b :: cs)
      = Nat.gcd (gcdList d (b :: cs)) a := e1
    _ = Nat.gcd (Nat.gcd (gcdList d cs) b) a := by rw [gcdList_cons d b cs]
    _ = Nat.gcd (Nat.gcd (gcdList d cs) a) b := gcd_swap_two (gcdList d cs) b a
    _ = Nat.gcd (gcdList d (a :: cs)) b := by rw [gcdList_cons d a cs]
    _ = gcdList d (b :: a :: cs) := e2.symm

private theorem foldl_gcd {m : ℕ} (acc : ℕ) (L : List (Fin m → ℕ)) (r : Fin m) :
    L.foldl (fun g l => Nat.gcd g (l r)) acc = gcdList acc (L.map (fun l => l r)) := by
  induction L generalizing acc with
  | nil => rfl
  | cons l L ih =>
    rw [List.foldl_cons, ih (Nat.gcd acc (l r)), gcdList_swap, List.map_cons, gcdList_cons]

theorem independentLabelGcd_eq_gcdList {m : ℕ} (d : ℕ) (L : List (Fin m → ℕ)) (r : Fin m) :
    independentLabelGcd d L r = gcdList d (L.map (fun l => l r)) := by
  show L.foldl (fun g l => Nat.gcd g (l r)) d = gcdList d (L.map (fun l => l r))
  exact foldl_gcd d L r

theorem independentDecode_eq_compactDecode {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) :
    independentDecode p L = compactDecode p L := by
  funext r
  simp only [independentDecode, compactDecode, annGenerator]
  rw [independentLabelGcd_eq_gcdList, labelGcd_eq_gcdList]

private theorem foldl_gcd_zero {m : ℕ} (acc : ℕ) (r : Fin m) :
    ∀ L : List (Fin m → ℕ), (∀ l ∈ L, l r = 0) ->
      L.foldl (fun g l => Nat.gcd g (l r)) acc = acc := by
  intro L
  induction L generalizing acc with
  | nil => intro _; rfl
  | cons l L ih =>
    intro h
    have hx : l r = 0 := h l List.mem_cons_self
    have hL : ∀ l' ∈ L, l' r = 0 := by
      intro l' hy
      exact h l' (List.mem_cons_of_mem _ hy)
    rw [List.foldl_cons, hx]
    have hgcd : Nat.gcd acc 0 = acc := Nat.gcd_zero_right acc
    rw [hgcd]
    exact ih acc hL

theorem independentDecode_zero_record {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) (hl : ∀ l ∈ L, ∀ r : Fin m, l r = 0)
    (hf : ∀ r : Fin m, 0 < p.coeff r) (r : Fin m) :
    independentDecode p L r = 1 := by
  have hg : independentLabelGcd (p.coeff r) L r = p.coeff r := by
    show L.foldl (fun g l => Nat.gcd g (l r)) (p.coeff r) = p.coeff r
    exact foldl_gcd_zero (p.coeff r) r L (by intro x hx; exact hl x hx r)
  rw [independentDecode, hg]
  exact Nat.div_self (hf r)

theorem independentDecode_swap {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) (l l' : FactorLabel p) (r : Fin m) :
    independentDecode p (l :: l' :: L) r = independentDecode p (l' :: l :: L) r := by
  show p.coeff r / independentLabelGcd (p.coeff r) (l :: l' :: L) r
      = p.coeff r / independentLabelGcd (p.coeff r) (l' :: l :: L) r
  have h1 : independentLabelGcd (p.coeff r) (l :: l' :: L) r
      = gcdList (p.coeff r) ((l :: l' :: L).map (fun x => x r)) :=
    independentLabelGcd_eq_gcdList _ _ _
  have h2 : independentLabelGcd (p.coeff r) (l' :: l :: L) r
      = gcdList (p.coeff r) ((l' :: l :: L).map (fun x => x r)) :=
    independentLabelGcd_eq_gcdList _ _ _
  simp only [List.map_cons] at h1 h2
  have hg : gcdList (p.coeff r) (l r :: l' r :: (L.map (fun x => x r)))
      = gcdList (p.coeff r) (l' r :: l r :: (L.map (fun x => x r))) := by
    exact gcdList_swap3 (p.coeff r) (l r) (l' r) (L.map (fun x => x r))
  rw [h1, h2, hg]

theorem independentDecode_annihilates {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) (hf : ∀ r : Fin m, 0 < p.coeff r) :
    ∀ l ∈ L, ∀ r : Fin m, p.coeff r ∣ l r * independentDecode p L r := by
  intro l hl r
  rw [independentDecode_eq_compactDecode]
  exact compactDecode_annihilates p L hf l hl r

theorem recoveryAttempt_verdict {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) :
    (recoveryAttempt p L).verdict =
      (if ∀ r : Fin m, 1 < independentDecode p L r then
        RecoveryVerdict.accepted (independentDecode p L)
      else RecoveryVerdict.rejected) := rfl

theorem recoveryAttempt_ledger {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) :
    (recoveryAttempt p L).labelReads = m * L.length ∧
      (recoveryAttempt p L).gcdReductions = m * L.length ∧
      (recoveryAttempt p L).verificationChecks = L.length * m ∧
      (recoveryAttempt p L).groupEnumeration = 0 := by
  simp [recoveryAttempt]

theorem recoveryAttempt_accepted_generators {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) (h : ∀ r : Fin m, 1 < independentDecode p L r) :
    (recoveryAttempt p L).verdict = RecoveryVerdict.accepted (independentDecode p L) := by
  simp [recoveryAttempt, h]

theorem clause1_endpoint {m n : ℕ} (p : CompactPresentation) (hp : p.isFinite = true)
    (L : List (FactorLabel p.smith)) :
    p.factors.length = p.generatorWords.length ∧
      (∀ v : Fin p.generators → ℤ,
        (Submodule.Quotient.mk (normalizedDecode p.smith (normalizedEncode p.smith v)) :
          PresentationModule (p.relationMatrix)) = Submodule.Quotient.mk v) ∧
      (∀ r : Fin p.generators, independentDecode p.smith L r = compactDecode p.smith L r) ∧
      (∀ l ∈ L, ∀ r : Fin p.generators,
        p.smith.coeff r ∣ l r * independentDecode p.smith L r) ∧
      (∀ l l' : FactorLabel p.smith, ∀ r : Fin p.generators,
        independentDecode p.smith (l :: l' :: L) r
          = independentDecode p.smith (l' :: l :: L) r) ∧
      (recoveryAttempt p.smith L).groupEnumeration = 0 ∧
      (recoveryAttempt p.smith L).labelReads = p.generators * L.length := by
  have hf : ∀ r : Fin p.generators, 0 < p.smith.coeff r := coeff_pos_of_finite p.smith hp
  refine ⟨(compactPresentation_output_size p).symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact compactPresentation_reconstruct p v
  · intro r
    exact congrFun (independentDecode_eq_compactDecode p.smith L) r
  · intro l hl r
    exact independentDecode_annihilates p.smith L hf l hl r
  · intro l l' r
    exact independentDecode_swap p.smith L l l' r
  · exact (recoveryAttempt_ledger p.smith L).2.2.2
  · exact (recoveryAttempt_ledger p.smith L).1

theorem clause3_near_uniform {N : ℕ} [NeZero N]
    {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : ZMod N → R) (e : ZMod N ≃ AddChar (ZMod N) ℂ) (H : AddSubgroup (ZMod N))
    (hf : HidesSubgroup f H) (m : ℕ) (he : ∀ a y : ZMod N, e a y = 1 ↔ a * y = 0) :
    1 - (Fintype.card (ZMod N) : ℝ) * ((2 : ℝ)⁻¹)^m ≤
      (tableGroupRecordDist f e).probEvent (fun xs : Fin m → ZMod N =>
        (cyclicDecodedSet (Nat.pos_of_ne_zero (NeZero.ne N)) (List.ofFn xs) : Set (ZMod N))
          = (H : Set (ZMod N))) := by
  exact compact_cyclic_recovery_probability f e H hf m he

theorem clause3_rejection_budget {N : ℕ} [NeZero N]
    {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : ZMod N → R) (e : ZMod N ≃ AddChar (ZMod N) ℂ) (H : AddSubgroup (ZMod N))
    (hf : HidesSubgroup f H) (m : ℕ) (he : ∀ a y : ZMod N, e a y = 1 ↔ a * y = 0) :
    (Fintype.card (ZMod N) : ℝ) * ((2 : ℝ)⁻¹)^m ≥
      1 - (tableGroupRecordDist f e).probEvent (fun xs : Fin m → ZMod N =>
        (cyclicDecodedSet (Nat.pos_of_ne_zero (NeZero.ne N)) (List.ofFn xs) : Set (ZMod N))
          = (H : Set (ZMod N))) := by
  have h := clause3_near_uniform f e H hf m he
  linarith

theorem clause3_zero_sample {N : ℕ} [NeZero N] :
    cyclicAnnGenerator ([] : List (ZMod N)) = 1 ∧
      (cyclicDecodedSet (Nat.pos_of_ne_zero (NeZero.ne N)) [] : Set (ZMod N)) = Set.univ := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hgen : cyclicAnnGenerator ([] : List (ZMod N)) = 1 := by
    show N / gcdList N [] = 1
    rw [gcdList.eq_def, Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne N))]
  refine ⟨hgen, ?_⟩
  have hfin : cyclicDecodedSet hN [] = Finset.univ := by
    ext x
    simp [cyclicDecodedSet, hgen]
  rw [hfin]
  simp

theorem clause3_same_run {N : ℕ} [NeZero N] (xs : List (ZMod N)) (H : AddSubgroup (ZMod N))
    (hgood : cyclicGoodSample (Nat.pos_of_ne_zero (NeZero.ne N)) xs H) :
    (∀ x : ZMod N, (x ∈ H) ↔ cyclicAnnGenerator xs ∣ x.val) := by
  intro x
  have hmem : x ∈ H ↔ x ∈ (cyclicDecodedSet (Nat.pos_of_ne_zero (NeZero.ne N)) xs : Set (ZMod N)) :=
    by
      rw [hgood]
      rfl
  rw [hmem]
  simp [cyclicDecodedSet]

theorem clause3_endpoint {N : ℕ} [NeZero N]
    {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : ZMod N → R) (e : ZMod N ≃ AddChar (ZMod N) ℂ) (H : AddSubgroup (ZMod N))
    (hf : HidesSubgroup f H) (m : ℕ) (he : ∀ a y : ZMod N, e a y = 1 ↔ a * y = 0)
    (xs : List (ZMod N)) (hgood : cyclicGoodSample (Nat.pos_of_ne_zero (NeZero.ne N)) xs H) :
    1 - (Fintype.card (ZMod N) : ℝ) * ((2 : ℝ)⁻¹)^m ≤
        (tableGroupRecordDist f e).probEvent (fun ys : Fin m → ZMod N =>
          (cyclicDecodedSet (Nat.pos_of_ne_zero (NeZero.ne N)) (List.ofFn ys) : Set (ZMod N))
            = (H : Set (ZMod N))) ∧
      (Fintype.card (ZMod N) : ℝ) * ((2 : ℝ)⁻¹)^m ≥
        1 - (tableGroupRecordDist f e).probEvent (fun ys : Fin m → ZMod N =>
          (cyclicDecodedSet (Nat.pos_of_ne_zero (NeZero.ne N)) (List.ofFn ys) : Set (ZMod N))
            = (H : Set (ZMod N))) ∧
      (∀ x : ZMod N, (x ∈ H) ↔ cyclicAnnGenerator xs ∣ x.val) ∧
      cyclicAnnGenerator ([] : List (ZMod N)) = 1 := by
  refine ⟨clause3_near_uniform f e H hf m he, clause3_rejection_budget f e H hf m he, ?_, ?_⟩
  · exact clause3_same_run xs H hgood
  · exact clause3_zero_sample (N := N).1

end Qatlib.Concepts.WalkFind.UniformThree
