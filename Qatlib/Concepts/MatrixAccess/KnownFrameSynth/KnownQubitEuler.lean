/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.QspSimulation.WordModel.SignalProcessing
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs

namespace Qatlib.Concepts.MatrixAccess.KnownFrameSynth

open Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

structure KnownQubitAngles where

  delta : ℝ

  alpha : ℝ

  theta : ℝ

  beta : ℝ

noncomputable def qubitEulerPhase (a : ℝ) : Matrix Bool Bool ℂ :=
  relabelGate boolEquivFin2.symm (PhaseRotation (a / 2))

noncomputable def qubitEulerRotation (θ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of fun i j =>
    if i = j then (Real.cos (θ / 2) : ℂ)
    else if i then -(Real.sin (θ / 2) : ℂ) else (Real.sin (θ / 2) : ℂ)

noncomputable def knownQubitUnitary (p : KnownQubitAngles) : Matrix Bool Bool ℂ :=
  Complex.exp ((p.delta : ℂ) * Complex.I) •
    (qubitEulerPhase p.alpha * qubitEulerRotation p.theta * qubitEulerPhase p.beta)

def knownQubitAngleAdjoint (p : KnownQubitAngles) : KnownQubitAngles :=
  ⟨-p.delta, -p.beta, -p.theta, -p.alpha⟩

noncomputable def knownQubitNormalize (U : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ :=
  Complex.exp (((-(Complex.arg (Matrix.det U) / 2 : ℝ)) : ℂ) * Complex.I) • U

noncomputable def knownQubitAnglesOfUnitary (U : Matrix Bool Bool ℂ) : KnownQubitAngles :=
  ⟨Complex.arg (Matrix.det U) / 2,
   Complex.arg (knownQubitNormalize U false false)
     + Complex.arg (knownQubitNormalize U false true),
   2 * Real.arccos ‖knownQubitNormalize U false false‖,
   Complex.arg (knownQubitNormalize U false false)
     - Complex.arg (knownQubitNormalize U false true)⟩

theorem boolEquivFin2_false : boolEquivFin2 false = 0 := rfl

theorem boolEquivFin2_true : boolEquivFin2 true = 1 := rfl

theorem boolEquivFin2_symm_zero : boolEquivFin2.symm 0 = false := rfl

theorem boolEquivFin2_symm_one : boolEquivFin2.symm 1 = true := rfl

@[simp] theorem qubitEulerRotation_apply (t : ℝ) (i j : Bool) :
    qubitEulerRotation t i j =
      if i = j then (Real.cos (t / 2) : ℂ)
      else if i then -(Real.sin (t / 2) : ℂ) else (Real.sin (t / 2) : ℂ) := rfl

theorem qubitEulerPhase_ff (t : ℝ) :
    qubitEulerPhase t false false = Complex.exp (((t / 2 : ℝ) : ℂ) * Complex.I) := by
  simp [qubitEulerPhase, relabelGate, Matrix.reindex_apply, PhaseRotation,
    boolEquivFin2_false]

theorem qubitEulerPhase_ft (t : ℝ) :
    qubitEulerPhase t false true = 0 := by
  simp [qubitEulerPhase, relabelGate, Matrix.reindex_apply, PhaseRotation,
    boolEquivFin2_false, boolEquivFin2_true]

theorem qubitEulerPhase_tf (t : ℝ) :
    qubitEulerPhase t true false = 0 := by
  simp [qubitEulerPhase, relabelGate, Matrix.reindex_apply, PhaseRotation,
    boolEquivFin2_false, boolEquivFin2_true]

theorem qubitEulerPhase_tt (t : ℝ) :
    qubitEulerPhase t true true = Complex.exp (((-(t / 2 : ℝ)) : ℂ) * Complex.I) := by
  simp [qubitEulerPhase, relabelGate, Matrix.reindex_apply, PhaseRotation,
    boolEquivFin2_true]

theorem qubitEulerPhase_apply (t : ℝ) (i j : Bool) :
    qubitEulerPhase t i j =
      if i = j then
        (if i then Complex.exp (((-(t / 2 : ℝ)) : ℂ) * Complex.I)
          else Complex.exp (((t / 2 : ℝ) : ℂ) * Complex.I))
      else 0 := by
  rcases i <;> rcases j <;>
    simp [qubitEulerPhase_ff, qubitEulerPhase_ft, qubitEulerPhase_tf, qubitEulerPhase_tt]

theorem qubitEulerRotation_ff (t : ℝ) :
    qubitEulerRotation t false false = (Real.cos (t / 2) : ℂ) := rfl

theorem qubitEulerRotation_ft (t : ℝ) :
    qubitEulerRotation t false true = (Real.sin (t / 2) : ℂ) := rfl

theorem qubitEulerRotation_tf (t : ℝ) :
    qubitEulerRotation t true false = -(Real.sin (t / 2) : ℂ) := rfl

theorem qubitEulerRotation_tt (t : ℝ) :
    qubitEulerRotation t true true = (Real.cos (t / 2) : ℂ) := rfl

theorem qubitEulerRotation_zero : qubitEulerRotation 0 = 1 := by
  ext i j
  rcases i <;> rcases j <;>
    simp [qubitEulerRotation_apply, Real.cos_zero]

theorem qubitEulerPhase_zero : qubitEulerPhase 0 = 1 := by
  ext i j
  rcases i <;> rcases j <;>
    simp [qubitEulerPhase_apply, zero_div, Complex.exp_zero]

theorem qubitEulerRotation_mul (s t : ℝ) :
    qubitEulerRotation s * qubitEulerRotation t = qubitEulerRotation (s + t) := by
  ext i j
  rcases i <;> rcases j <;>
    simp [Matrix.mul_apply, qubitEulerRotation_apply,
      show (s + t : ℝ) / 2 = s / 2 + t / 2 from by ring, Real.cos_add, Real.sin_add] <;>
    ring

theorem qubitEulerPhase_mul (s t : ℝ) :
    qubitEulerPhase s * qubitEulerPhase t = qubitEulerPhase (s + t) := by
  ext i j
  rcases i <;> rcases j <;>
    simp [Matrix.mul_apply, qubitEulerPhase_apply, ← Complex.exp_add] <;>
    congr 1 <;> ring

theorem pauliX_mul_qubitEulerRotation (t : ℝ) :
    PauliX * qubitEulerRotation t * PauliX = qubitEulerRotation (-t) := by
  ext i j
  rcases i <;> rcases j <;>
    simp [Matrix.mul_apply, qubitEulerRotation_apply, PauliX, permMatrix,
      show ((Real.cos (-t / 2) : ℂ)) = ((Real.cos (t / 2) : ℂ)) from by
        rw [show -t / 2 = -(t / 2) from by ring, Real.cos_neg],
      show ((Real.sin (-t / 2) : ℂ)) = -((Real.sin (t / 2) : ℂ)) from by
        rw [show -t / 2 = -(t / 2) from by ring, Real.sin_neg, Complex.ofReal_neg]]

theorem pauliX_mul_qubitEulerPhase (t : ℝ) :
    PauliX * qubitEulerPhase t * PauliX = qubitEulerPhase (-t) := by
  ext i j
  rcases i <;> rcases j <;>
    simp [Matrix.mul_apply, qubitEulerPhase_apply, PauliX, permMatrix] <;>
    congr 1 <;> ring

theorem conj_mul₂ (a b : ℂ) :
    (starRingEnd ℂ) (a * b) = (starRingEnd ℂ) a * (starRingEnd ℂ) b := map_mul _ _ _

theorem conj_zero : (starRingEnd ℂ) 0 = 0 := map_zero _

theorem conjTranspose_apply' (M : Matrix Bool Bool ℂ) (i j : Bool) :
    Mᴴ i j = (starRingEnd ℂ) (M j i) := rfl

theorem star_eq_norm_mul_exp (x : ℂ) :
    (starRingEnd ℂ) x = ((‖x‖ : ℂ)) * Complex.exp ((-(Complex.arg x : ℂ)) * Complex.I) := by
  have harg : Complex.exp (((Complex.arg x : ℂ) * (-Complex.I)))
      = Complex.exp ((-((Complex.arg x : ℂ))) * Complex.I) := by
    congr 1
    ring
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I x]
  rw [conj_mul₂, Complex.conj_ofReal, ← Complex.exp_conj, conj_mul₂, Complex.conj_ofReal,
    Complex.conj_I, harg]

theorem smul_mem_unitaryGroup {I : Type*} [Fintype I] [DecidableEq I] {c : ℂ} (hc : ‖c‖ = 1)
    {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    c • U ∈ Matrix.unitaryGroup I ℂ := by
  have hnormSq : Complex.normSq c = 1 := by
    rw [Complex.normSq_eq_norm_sq, hc, one_pow]
  have hcc : star c * c = 1 := by
    calc star c * c = (Complex.normSq c : ℂ) :=
          (Complex.normSq_eq_conj_mul_self (z := c)).symm
      _ = 1 := by rw [hnormSq]; simp
  have h1 : Uᴴ * U = 1 := by
    have hh := (Matrix.mem_unitaryGroup_iff').mp hU
    rwa [Matrix.star_eq_conjTranspose] at hh
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
    smul_mul_smul, h1, hcc, one_smul]

theorem mul_mem_unitaryGroup {I : Type*} [Fintype I] [DecidableEq I] {U V : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ) :
    U * V ∈ Matrix.unitaryGroup I ℂ := by
  have h1 : Uᴴ * U = 1 := by
    have hh := (Matrix.mem_unitaryGroup_iff').mp hU
    rwa [Matrix.star_eq_conjTranspose] at hh
  have h2 : Vᴴ * V = 1 := by
    have hh := (Matrix.mem_unitaryGroup_iff').mp hV
    rwa [Matrix.star_eq_conjTranspose] at hh
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U V, h1, Matrix.one_mul, h2]

theorem qubitEulerRotation_conjTranspose (t : ℝ) :
    (qubitEulerRotation t)ᴴ = qubitEulerRotation (-t) := by
  ext i j
  rcases i <;> rcases j <;>
    simp only [conjTranspose_apply', qubitEulerRotation_ff, qubitEulerRotation_ft,
      qubitEulerRotation_tf, qubitEulerRotation_tt, Complex.conj_ofReal, map_neg, neg_neg,
      show ((Real.cos ((-t) / 2) : ℂ)) = ((Real.cos (t / 2) : ℂ)) from by
        rw [show (-t : ℝ) / 2 = -(t / 2) from by ring, Real.cos_neg],
      show ((Real.sin ((-t) / 2) : ℂ)) = -((Real.sin (t / 2) : ℂ)) from by
        rw [show (-t : ℝ) / 2 = -(t / 2) from by ring, Real.sin_neg, Complex.ofReal_neg]]

theorem qubitEulerPhase_conjTranspose (t : ℝ) :
    (qubitEulerPhase t)ᴴ = qubitEulerPhase (-t) := by
  ext i j
  rcases i <;> rcases j <;>
    simp only [conjTranspose_apply', qubitEulerPhase_ff, qubitEulerPhase_ft,
      qubitEulerPhase_tf, qubitEulerPhase_tt, conj_zero, ← Complex.exp_conj, conj_mul₂,
      map_neg, Complex.conj_ofReal, Complex.conj_I] <;>
    congr 1 <;> push_cast <;> ring

theorem qubitEulerRotation_unitary (t : ℝ) :
    qubitEulerRotation t ∈ Matrix.unitaryGroup Bool ℂ := by
  have hmul : qubitEulerRotation (-t) * qubitEulerRotation t = 1 := by
    rw [qubitEulerRotation_mul, neg_add_cancel, qubitEulerRotation_zero]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, qubitEulerRotation_conjTranspose,
    hmul]

theorem qubitEulerPhase_unitary (t : ℝ) :
    qubitEulerPhase t ∈ Matrix.unitaryGroup Bool ℂ := by
  have hmul : qubitEulerPhase (-t) * qubitEulerPhase t = 1 := by
    rw [qubitEulerPhase_mul, neg_add_cancel, qubitEulerPhase_zero]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, qubitEulerPhase_conjTranspose,
    hmul]

theorem knownQubitUnitary_unitary (p : KnownQubitAngles) :
    knownQubitUnitary p ∈ Matrix.unitaryGroup Bool ℂ := by
  unfold knownQubitUnitary
  exact smul_mem_unitaryGroup (Complex.norm_exp_ofReal_mul_I p.delta)
    (mul_mem_unitaryGroup (mul_mem_unitaryGroup (qubitEulerPhase_unitary p.alpha)
      (qubitEulerRotation_unitary p.theta)) (qubitEulerPhase_unitary p.beta))

theorem knownQubitUnitary_adjoint (p : KnownQubitAngles) :
    knownQubitUnitary (knownQubitAngleAdjoint p) = (knownQubitUnitary p)ᴴ := by
  have hexp : star (Complex.exp ((p.delta : ℂ) * Complex.I))
      = Complex.exp ((-p.delta : ℂ) * Complex.I) := by
    rw [show star (Complex.exp ((p.delta : ℂ) * Complex.I))
        = (starRingEnd ℂ) (Complex.exp ((p.delta : ℂ) * Complex.I)) from rfl,
      ← Complex.exp_conj, conj_mul₂, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  simp only [knownQubitUnitary, knownQubitAngleAdjoint, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, qubitEulerPhase_conjTranspose, qubitEulerRotation_conjTranspose,
    hexp, Matrix.mul_assoc, Complex.ofReal_neg]

theorem knownQubitEuler_primitives_and_algebra :
    (∀ (t : ℝ),
      qubitEulerPhase t = relabelGate boolEquivFin2.symm (PhaseRotation (t / 2)) ∧
      qubitEulerRotation t ∈ Matrix.unitaryGroup Bool ℂ ∧
      qubitEulerPhase t ∈ Matrix.unitaryGroup Bool ℂ ∧
      (∀ a b : Bool, qubitEulerRotation t a b =
        if a = b then (Real.cos (t / 2) : ℂ) else
          if a then -(Real.sin (t / 2) : ℂ) else (Real.sin (t / 2) : ℂ)) ∧
      PauliX * qubitEulerRotation t * PauliX = qubitEulerRotation (-t) ∧
      PauliX * qubitEulerPhase t * PauliX = qubitEulerPhase (-t)) ∧
    (∀ s t : ℝ, qubitEulerRotation s * qubitEulerRotation t = qubitEulerRotation (s + t) ∧
      qubitEulerPhase s * qubitEulerPhase t = qubitEulerPhase (s + t)) ∧
    (∀ p : KnownQubitAngles, knownQubitUnitary p = Complex.exp ((p.delta : ℂ) * Complex.I) •
      (qubitEulerPhase p.alpha * qubitEulerRotation p.theta * qubitEulerPhase p.beta) ∧
      knownQubitUnitary p ∈ Matrix.unitaryGroup Bool ℂ ∧
      knownQubitUnitary (knownQubitAngleAdjoint p) = (knownQubitUnitary p)ᴴ) := by
  refine ⟨fun t => ⟨rfl, qubitEulerRotation_unitary t, qubitEulerPhase_unitary t,
    fun a b => qubitEulerRotation_apply t a b, pauliX_mul_qubitEulerRotation t,
    pauliX_mul_qubitEulerPhase t⟩,
    fun s t => ⟨qubitEulerRotation_mul s t, qubitEulerPhase_mul s t⟩,
    fun p => ⟨rfl, knownQubitUnitary_unitary p, knownQubitUnitary_adjoint p⟩⟩

theorem det_apply_bool (W : Matrix Bool Bool ℂ) :
    W.det = W false false * W true true - W false true * W true false := by
  rw [← Matrix.det_reindex_self boolEquivFin2 W, Matrix.det_fin_two]
  simp [Matrix.reindex_apply, boolEquivFin2_symm_zero, boolEquivFin2_symm_one]

def boolAdj (W : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ :=
  Matrix.of fun i j =>
    match i, j with
    | false, false => W true true
    | false, true => -W false true
    | true, false => -W true false
    | true, true => W false false

theorem mul_boolAdj (W : Matrix Bool Bool ℂ) :
    W * boolAdj W = W.det • (1 : Matrix Bool Bool ℂ) := by
  ext i j
  rcases i <;> rcases j <;>
    simp [Matrix.mul_apply, boolAdj, det_apply_bool, Matrix.smul_apply] <;>
    ring

theorem bool_unitary_det_one {W : Matrix Bool Bool ℂ} (hW : W ∈ Matrix.unitaryGroup Bool ℂ)
    (hdet : W.det = 1) :
    W true true = (starRingEnd ℂ) (W false false) ∧
    W true false = -((starRingEnd ℂ) (W false true)) := by
  have hL : Wᴴ * W = 1 := by
    have hh := (Matrix.mem_unitaryGroup_iff').mp hW
    rwa [Matrix.star_eq_conjTranspose] at hh
  have hR : W * Wᴴ = 1 := by
    have hh := (Matrix.mem_unitaryGroup_iff).mp hW
    rwa [Matrix.star_eq_conjTranspose] at hh
  have hsmul : W.det • (1 : Matrix Bool Bool ℂ) = 1 := by
    rw [hdet]; simp
  have hadj : boolAdj W = Wᴴ := by
    calc boolAdj W = (Wᴴ * W) * boolAdj W := by rw [hL, Matrix.one_mul]
      _ = Wᴴ * (W * boolAdj W) := by rw [Matrix.mul_assoc]
      _ = Wᴴ * (W * Wᴴ) := by rw [mul_boolAdj, hsmul, hR, Matrix.mul_one]
      _ = (Wᴴ * W) * Wᴴ := by rw [← Matrix.mul_assoc]
      _ = Wᴴ := by rw [hL, Matrix.one_mul]
  refine ⟨?_, ?_⟩
  · have e := congrArg (fun M : Matrix Bool Bool ℂ => M false false) hadj
    simpa [boolAdj, Matrix.conjTranspose_apply] using! e
  · have e := congrArg (fun M : Matrix Bool Bool ℂ => M true false) hadj
    have e' : -W true false = (starRingEnd ℂ) (W false true) := by
      simpa [boolAdj, conjTranspose_apply'] using! e
    rw [← e', neg_neg]

theorem eulerPRP_ff (α θ β : ℝ) :
    (qubitEulerPhase α * qubitEulerRotation θ * qubitEulerPhase β) false false
      = Complex.exp (((α / 2 : ℝ) : ℂ) * Complex.I) * ((Real.cos (θ / 2) : ℂ))
        * Complex.exp (((β / 2 : ℝ) : ℂ) * Complex.I) := by
  simp [Matrix.mul_apply, qubitEulerPhase_ff, qubitEulerPhase_ft, qubitEulerPhase_tf,
    qubitEulerPhase_tt, qubitEulerRotation_ff, qubitEulerRotation_ft, qubitEulerRotation_tf,
    qubitEulerRotation_tt]

theorem eulerPRP_ft (α θ β : ℝ) :
    (qubitEulerPhase α * qubitEulerRotation θ * qubitEulerPhase β) false true
      = Complex.exp (((α / 2 : ℝ) : ℂ) * Complex.I) * ((Real.sin (θ / 2) : ℂ))
        * Complex.exp (((-(β / 2 : ℝ)) : ℂ) * Complex.I) := by
  simp [Matrix.mul_apply, qubitEulerPhase_ff, qubitEulerPhase_ft, qubitEulerPhase_tf,
    qubitEulerPhase_tt, qubitEulerRotation_ff, qubitEulerRotation_ft, qubitEulerRotation_tf,
    qubitEulerRotation_tt]

theorem eulerPRP_tf (α θ β : ℝ) :
    (qubitEulerPhase α * qubitEulerRotation θ * qubitEulerPhase β) true false
      = Complex.exp (((-(α / 2 : ℝ)) : ℂ) * Complex.I) * (-((Real.sin (θ / 2) : ℂ)))
        * Complex.exp (((β / 2 : ℝ) : ℂ) * Complex.I) := by
  simp [Matrix.mul_apply, qubitEulerPhase_ff, qubitEulerPhase_ft, qubitEulerPhase_tf,
    qubitEulerPhase_tt, qubitEulerRotation_ff, qubitEulerRotation_ft, qubitEulerRotation_tf,
    qubitEulerRotation_tt]

theorem eulerPRP_tt (α θ β : ℝ) :
    (qubitEulerPhase α * qubitEulerRotation θ * qubitEulerPhase β) true true
      = Complex.exp (((-(α / 2 : ℝ)) : ℂ) * Complex.I) * ((Real.cos (θ / 2) : ℂ))
        * Complex.exp (((-(β / 2 : ℝ)) : ℂ) * Complex.I) := by
  simp [Matrix.mul_apply, qubitEulerPhase_ff, qubitEulerPhase_ft, qubitEulerPhase_tf,
    qubitEulerPhase_tt, qubitEulerRotation_ff, qubitEulerRotation_ft, qubitEulerRotation_tf,
    qubitEulerRotation_tt]

theorem euler_angles_reconstruct (a b : ℂ) (hab : Complex.normSq a + Complex.normSq b = 1) :
    qubitEulerPhase (Complex.arg a + Complex.arg b) * qubitEulerRotation (2 * Real.arccos ‖a‖) *
      qubitEulerPhase (Complex.arg a - Complex.arg b)
      = Matrix.of fun i j =>
        match i, j with
        | false, false => a
        | false, true => b
        | true, false => -((starRingEnd ℂ) b)
        | true, true => (starRingEnd ℂ) a := by
  have h0 : 0 ≤ ‖a‖ := norm_nonneg a
  have hnb0 : 0 ≤ ‖b‖ := norm_nonneg b
  have hb2 : ‖b‖ ^ 2 = 1 - ‖a‖ ^ 2 := by
    have e1 : ∀ z : ℂ, Complex.normSq z = ‖z‖ ^ 2 := fun z => Complex.normSq_eq_norm_sq z
    rw [e1 a, e1 b] at hab
    linarith
  have h1 : ‖a‖ ≤ 1 := by nlinarith [hnb0, sq_nonneg ‖a‖]
  have hca : ((‖a‖ : ℂ)) * Complex.exp ((Complex.arg a : ℂ) * Complex.I) = a :=
    Complex.norm_mul_exp_arg_mul_I a
  have hcb : ((‖b‖ : ℂ)) * Complex.exp ((Complex.arg b : ℂ) * Complex.I) = b :=
    Complex.norm_mul_exp_arg_mul_I b
  have hconjb : Complex.exp ((-(Complex.arg b : ℂ)) * Complex.I) * ((‖b‖ : ℂ))
      = (starRingEnd ℂ) b := by
    rw [mul_comm]
    exact (star_eq_norm_mul_exp b).symm
  have hconja : Complex.exp ((-(Complex.arg a : ℂ)) * Complex.I) * ((‖a‖ : ℂ))
      = (starRingEnd ℂ) a := by
    rw [mul_comm]
    exact (star_eq_norm_mul_exp a).symm
  have hθhalf : (2 * Real.arccos ‖a‖) / 2 = Real.arccos ‖a‖ := by ring
  have hcos' : ((Real.cos ((2 * Real.arccos ‖a‖) / 2) : ℂ)) = ((‖a‖ : ℂ)) := by
    rw [hθhalf, Real.cos_arccos (by linarith) h1]
  have hsin' : ((Real.sin ((2 * Real.arccos ‖a‖) / 2) : ℂ)) = ((‖b‖ : ℂ)) := by
    have ha2 : ‖a‖ ^ 2 ≤ 1 := by nlinarith [h0, h1, sq_nonneg (1 - ‖a‖)]
    rw [hθhalf, Real.sin_arccos ‖a‖, Complex.ofReal_inj,
      Real.sqrt_eq_iff_mul_self_eq (by linarith) hnb0, ← pow_two]
    linarith
  ext i j
  rcases i <;> rcases j
  · simp only [eulerPRP_ff, hcos', Matrix.of_apply]
    rw [mul_right_comm, ← Complex.exp_add,
      show (((Complex.arg a + Complex.arg b : ℝ) / 2 : ℝ) : ℂ) * Complex.I
          + (((Complex.arg a - Complex.arg b : ℝ) / 2 : ℝ) : ℂ) * Complex.I
          = ((Complex.arg a : ℂ)) * Complex.I from by
        push_cast
        ring,
      mul_comm]
    exact hca
  · simp only [eulerPRP_ft, hsin', Matrix.of_apply]
    rw [mul_right_comm, ← Complex.exp_add,
      show (((Complex.arg a + Complex.arg b : ℝ) / 2 : ℝ) : ℂ) * Complex.I
          + (-(((Complex.arg a - Complex.arg b : ℝ) / 2 : ℝ) : ℂ)) * Complex.I
          = ((Complex.arg b : ℂ)) * Complex.I from by
        push_cast
        ring,
      mul_comm]
    exact hcb
  · simp only [eulerPRP_tf, hsin', Matrix.of_apply]
    rw [mul_right_comm, ← Complex.exp_add,
      show (-(((Complex.arg a + Complex.arg b : ℝ) / 2 : ℝ) : ℂ)) * Complex.I
          + (((Complex.arg a - Complex.arg b : ℝ) / 2 : ℝ) : ℂ) * Complex.I
          = -((Complex.arg b : ℂ)) * Complex.I from by
        push_cast
        ring,
      mul_neg, hconjb]
  · simp only [eulerPRP_tt, hcos', Matrix.of_apply]
    rw [mul_right_comm, ← Complex.exp_add,
      show (-(((Complex.arg a + Complex.arg b : ℝ) / 2 : ℝ) : ℂ)) * Complex.I
          + (-(((Complex.arg a - Complex.arg b : ℝ) / 2 : ℝ) : ℂ)) * Complex.I
          = -((Complex.arg a : ℂ)) * Complex.I from by
        push_cast
        ring]
    exact hconja

theorem exp_neg_arg_mul_self (x : ℂ) (hx : ‖x‖ = 1) :
    Complex.exp (-((Complex.arg x : ℂ)) * Complex.I) * x = 1 := by
  have hn := Complex.norm_mul_exp_arg_mul_I x
  calc Complex.exp (-((Complex.arg x : ℂ)) * Complex.I) * x
      = Complex.exp (-((Complex.arg x : ℂ)) * Complex.I)
          * (((‖x‖ : ℂ)) * Complex.exp ((Complex.arg x : ℂ) * Complex.I)) := by rw [hn]
    _ = ((‖x‖ : ℂ)) * (Complex.exp (-((Complex.arg x : ℂ)) * Complex.I)
          * Complex.exp ((Complex.arg x : ℂ) * Complex.I)) := by ring
    _ = ((‖x‖ : ℂ)) * Complex.exp
          (-((Complex.arg x : ℂ)) * Complex.I + (Complex.arg x : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]
    _ = 1 := by
        rw [show -((Complex.arg x : ℂ)) * Complex.I + (Complex.arg x : ℂ) * Complex.I = 0
            from by ring, Complex.exp_zero, mul_one, hx]
        norm_num

theorem knownQubitEuler_explicit_angles_cover_unitaries :
    ∀ (U : Matrix Bool Bool ℂ), U ∈ Matrix.unitaryGroup Bool ℂ →
      knownQubitUnitary (knownQubitAnglesOfUnitary U) = U ∧
      0 ≤ (knownQubitAnglesOfUnitary U).theta ∧ (knownQubitAnglesOfUnitary U).theta ≤ Real.pi := by
  intro U hU
  have hdetU : (starRingEnd ℂ) (Matrix.det U) * Matrix.det U = 1 :=
    Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary hU)
  have hnormSq : Complex.normSq (Matrix.det U) = 1 := by
    have h := Complex.normSq_eq_conj_mul_self (z := Matrix.det U)
    rw [hdetU] at h
    exact Complex.ofReal_inj.mp h
  have hnormdet : ‖Matrix.det U‖ = 1 := by
    rw [Complex.norm_def, hnormSq, Real.sqrt_one]
  have hcN : ‖Complex.exp (((-(Complex.arg (Matrix.det U) / 2 : ℝ)) : ℂ) * Complex.I)‖ = 1 := by
    have h := Complex.norm_exp_ofReal_mul_I (-(Complex.arg (Matrix.det U) / 2 : ℝ))
    rw [Complex.ofReal_neg] at h
    exact h
  have hWU : knownQubitNormalize U ∈ Matrix.unitaryGroup Bool ℂ :=
    smul_mem_unitaryGroup hcN hU
  have hdetW : (knownQubitNormalize U).det = 1 := by
    unfold knownQubitNormalize
    rw [Matrix.det_smul, Fintype.card_bool, pow_two, ← Complex.exp_add]
    have harg : ((-(Complex.arg (Matrix.det U) / 2 : ℝ)) : ℂ) * Complex.I
        + ((-(Complex.arg (Matrix.det U) / 2 : ℝ)) : ℂ) * Complex.I
        = -((Complex.arg (Matrix.det U) : ℂ)) * Complex.I := by
      push_cast
      ring
    rw [harg]
    exact exp_neg_arg_mul_self (Matrix.det U) hnormdet
  obtain ⟨hd1, hd2⟩ := bool_unitary_det_one hWU hdetW
  have hnorm : Complex.normSq (knownQubitNormalize U false false)
      + Complex.normSq (knownQubitNormalize U false true) = 1 := by
    have hR : knownQubitNormalize U * (knownQubitNormalize U)ᴴ = 1 := by
      have hh := (Matrix.mem_unitaryGroup_iff).mp hWU
      rwa [Matrix.star_eq_conjTranspose] at hh
    have h1 : (knownQubitNormalize U * (knownQubitNormalize U)ᴴ) false false = 1 := by
      rw [hR]
      simp [Matrix.one_apply]
    have e2 : ∀ z : ℂ, z * (starRingEnd ℂ) z = (Complex.normSq z : ℂ) := by
      intro z
      rw [mul_comm]
      exact (Complex.normSq_eq_conj_mul_self (z := z)).symm
    simp only [Matrix.mul_apply, Fintype.sum_bool, conjTranspose_apply', e2] at h1
    rw [add_comm]
    exact_mod_cast h1
  have hre := euler_angles_reconstruct (knownQubitNormalize U false false)
    (knownQubitNormalize U false true) hnorm
  have hWmat : (Matrix.of fun i j =>
      match i, j with
      | false, false => knownQubitNormalize U false false
      | false, true => knownQubitNormalize U false true
      | true, false => -((starRingEnd ℂ) (knownQubitNormalize U false true))
      | true, true => (starRingEnd ℂ) (knownQubitNormalize U false false))
      = knownQubitNormalize U := by
    ext i j
    rcases i <;> rcases j <;> simp [Matrix.of_apply, hd1, hd2]
  have h0 : 0 ≤ ‖knownQubitNormalize U false false‖ :=
    norm_nonneg _
  have h1 : ‖knownQubitNormalize U false false‖ ≤ 1 := by
    have e1 : ∀ z : ℂ, Complex.normSq z = ‖z‖ ^ 2 := fun z => Complex.normSq_eq_norm_sq z
    rw [e1 _, e1 _] at hnorm
    have hnb : 0 ≤ ‖knownQubitNormalize U false true‖ := norm_nonneg _
    nlinarith [hnb, sq_nonneg ‖knownQubitNormalize U false false‖]
  refine ⟨?_, ?_, ?_⟩
  · simp only [knownQubitAnglesOfUnitary, knownQubitUnitary]
    rw [hre, hWmat]
    unfold knownQubitNormalize
    rw [smul_smul,
      show Complex.exp (((Complex.arg (Matrix.det U) / 2 : ℝ) : ℂ) * Complex.I)
          * Complex.exp (((-(Complex.arg (Matrix.det U) / 2 : ℝ)) : ℂ) * Complex.I) = 1 from by
        rw [← Complex.exp_add,
          show ((Complex.arg (Matrix.det U) / 2 : ℝ) : ℂ) * Complex.I
              + ((-(Complex.arg (Matrix.det U) / 2 : ℝ)) : ℂ) * Complex.I = 0 from by
            push_cast
            ring,
          Complex.exp_zero],
      one_smul]
  · show 0 ≤ 2 * Real.arccos ‖knownQubitNormalize U false false‖
    exact mul_nonneg two_pos.le (Real.arccos_nonneg _)
  · show 2 * Real.arccos ‖knownQubitNormalize U false false‖ ≤ Real.pi
    have harc : Real.arccos ‖knownQubitNormalize U false false‖ ≤ Real.pi / 2 := by
      rw [← Real.arccos_zero]
      exact Real.arccos_le_arccos h0
    nlinarith

end Qatlib.Concepts.MatrixAccess.KnownFrameSynth
