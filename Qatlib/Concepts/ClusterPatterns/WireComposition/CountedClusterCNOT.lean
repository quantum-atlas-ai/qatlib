/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterCZ
import Mathlib.Algebra.Ring.BooleanRing
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false


open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.ClusterPatterns.WireComposition
open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder

set_option maxHeartbeats 4000000

def clusterCNOTFlip : Bool × Bool → Bool × Bool := fun p => (p.1 ^^ p.2, p.2)

noncomputable def clusterCNOTb : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  permMatrix clusterCNOTFlip

noncomputable def clusterCNOTMat : Operator 4 :=
  relabelGate teleportOutcomeEquiv clusterCNOTb

noncomputable def clusterCNOTEdge12B :
    Matrix ((Bool × Bool) × (Bool × Bool)) ((Bool × Bool) × (Bool × Bool)) ℂ :=
  TensorGate clusterCZb (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)

noncomputable def clusterCNOTEdge23B :
    Matrix ((Bool × Bool) × (Bool × Bool)) ((Bool × Bool) × (Bool × Bool)) ℂ :=
  Matrix.diagonal fun p => if p.1.2 && p.2.1 then (-1 : ℂ) else 1

noncomputable def clusterCNOTEdge12Gate : Operator 16 :=
  relabelGate clusterCZRegisterEquiv clusterCNOTEdge12B

noncomputable def clusterCNOTEdge23Gate : Operator 16 :=
  relabelGate clusterCZRegisterEquiv clusterCNOTEdge23B

def clusterCNOTInitialFrame : Matrix (Fin 16) (Fin 4) ℂ :=
  Matrix.of fun r i =>
    if r = clusterCZRegisterEquiv
        (((teleportOutcomeEquiv.symm i).1, false), (false, (teleportOutcomeEquiv.symm i).2))
      then 1 else 0

noncomputable def clusterCNOTRawProgram : ObservedCircuit (Fin 16) :=
  .step (.gate clusterCZHdGate)
    (.step (.gate clusterCZHbGate)
      (.step (.gate clusterCNOTEdge12Gate)
        (.step (.gate clusterCNOTEdge23Gate)
          (.step (.gate clusterCZEdgeDcGate)
            (.step (.gate clusterCZHaGate)
              (.step (.gate clusterCZHdGate)
                (.measure 2 clusterCZLabelA (fun _ka =>
                  .measure 2 clusterCZLabelD (fun _kd => .halt true)))))))))

noncomputable def clusterCNOTProgram : ObservedCircuit (Fin 16) :=
  .step (.gate clusterCZHdGate)
    (.step (.gate clusterCZHbGate)
      (.step (.gate clusterCNOTEdge12Gate)
        (.step (.gate clusterCNOTEdge23Gate)
          (.step (.gate clusterCZEdgeDcGate)
            (.step (.gate clusterCZHaGate)
              (.step (.gate clusterCZHdGate)
                (.measure 2 clusterCZLabelA (fun ka =>
                  .measure 2 clusterCZLabelD (fun kd =>
                    .step (.gate (clusterCZXbGate kd))
                      (.step (.gate (clusterCZZbGate ka))
                        (.step (.gate (clusterCZZcGate ka))
                          (.halt true))))))))))))

noncomputable def clusterCNOTRawLeaf (a b : Bool) :
    Fin (observedLeafCount clusterCNOTRawProgram) :=
  Fin.cast (by rfl) (teleportOutcomeEquiv (a, b))

noncomputable def clusterCNOTLeaf (a b : Bool) :
    Fin (observedLeafCount clusterCNOTProgram) :=
  Fin.cast (by rfl) (teleportOutcomeEquiv (a, b))

def clusterCNOTMessage (a b : Bool) : List Bool := [a, b]

noncomputable def clusterCNOTActualBranchCore (a b : Bool) (ρ : Operator 4) : Operator 4 :=
  relabelGate teleportOutcomeEquiv (Matrix.traceLeft
    (relabelGate clusterCZRegisterEquiv.symm
      ((observedLeaf 1 clusterCNOTProgram (clusterCNOTLeaf a b)).operator
        * (clusterCNOTInitialFrame * ρ * clusterCNOTInitialFrame.conjTranspose)
        * (observedLeaf 1 clusterCNOTProgram (clusterCNOTLeaf a b)).operator.conjTranspose)))

noncomputable def clusterCNOTActualBranchMap (a b : Bool) : Operator 4 →ₗ[ℂ] Operator 4 where
  toFun := clusterCNOTActualBranchCore a b
  map_add' := by
    intro ρ σ
    unfold clusterCNOTActualBranchCore
    simp only [Matrix.mul_add, Matrix.add_mul, relabelGate_add', traceLeft_add4]
  map_smul' := by
    intro r ρ
    unfold clusterCNOTActualBranchCore
    simp only [Matrix.mul_smul, Matrix.smul_mul, relabelGate_smul', traceLeft_smul4,
      RingHom.id_apply]

theorem clusterCNOTInitialFrame_column (i : Fin 4) (r : Fin 16) :
    clusterCNOTInitialFrame r i
      = relabelState clusterCZRegisterEquiv
          (Qatlib.Foundations.PureStateMath.Ket (((teleportOutcomeEquiv.symm i).1, false), (false, (teleportOutcomeEquiv.symm i).2))) r := by
  by_cases h : r = clusterCZRegisterEquiv (((teleportOutcomeEquiv.symm i).1, false), (false, (teleportOutcomeEquiv.symm i).2))
  · subst h
    simp [clusterCNOTInitialFrame, relabelState, Qatlib.Foundations.PureStateMath.Ket,
        Equiv.symm_apply_apply]
  · have h2 : clusterCZRegisterEquiv.symm r ≠ (((teleportOutcomeEquiv.symm i).1, false), (false, (teleportOutcomeEquiv.symm i).2)) := by
      intro hc
      apply h
      have h3 := congrArg clusterCZRegisterEquiv hc
      rwa [Equiv.apply_symm_apply] at h3
    simp [clusterCNOTInitialFrame, relabelState, Qatlib.Foundations.PureStateMath.Ket, h, h2]

theorem clusterCNOTInitialFrame_isometry : IsIsometry clusterCNOTInitialFrame := by
  have hInj : ∀ i j : Fin 4,
      clusterCZRegisterEquiv (((teleportOutcomeEquiv.symm i).1, false), (false, (teleportOutcomeEquiv.symm i).2))
        = clusterCZRegisterEquiv (((teleportOutcomeEquiv.symm j).1, false), (false, (teleportOutcomeEquiv.symm j).2)) → i = j := by
    intro i j hij
    have h2 := clusterCZRegisterEquiv.injective hij
    exact teleportOutcomeEquiv.symm.injective
      (Prod.ext (congrArg (fun q => q.1.1) h2) (congrArg (fun q => q.2.2) h2))
  have h : clusterCNOTInitialFrameᴴ * clusterCNOTInitialFrame = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have hval : ∀ r : Fin 16, clusterCNOTInitialFrameᴴ i r * clusterCNOTInitialFrame r i
          = if r = clusterCZRegisterEquiv (((teleportOutcomeEquiv.symm i).1, false), (false, (teleportOutcomeEquiv.symm i).2))
              then (1 : ℂ) else 0 := by
        intro r
        rw [conjTranspose_apply]
        unfold clusterCNOTInitialFrame
        simp only [Matrix.of_apply]
        by_cases hr : r = clusterCZRegisterEquiv (((teleportOutcomeEquiv.symm i).1, false), (false, (teleportOutcomeEquiv.symm i).2))
        · rw [if_pos hr]; simp
        · rw [if_neg hr]; simp
      rw [Matrix.mul_apply,
        Finset.sum_congr rfl (fun r _ => hval r),
        Finset.sum_ite_eq' Finset.univ
          (clusterCZRegisterEquiv (((teleportOutcomeEquiv.symm i).1, false), (false, (teleportOutcomeEquiv.symm i).2)))
          (fun _ => (1 : ℂ)),
        if_pos (Finset.mem_univ _)]
      simp
    · have hzero : ∀ r : Fin 16,
          clusterCNOTInitialFrameᴴ i r * clusterCNOTInitialFrame r j = 0 := by
        intro r
        rw [conjTranspose_apply]
        unfold clusterCNOTInitialFrame
        simp only [Matrix.of_apply]
        by_cases hr : r = clusterCZRegisterEquiv (((teleportOutcomeEquiv.symm i).1, false), (false, (teleportOutcomeEquiv.symm i).2))
        · rw [if_pos hr, if_neg (fun hc => hij (hInj i j (hr.symm.trans hc))), mul_zero]
        · rw [if_neg hr, star_zero, zero_mul]
      rw [Matrix.mul_apply, Finset.sum_congr rfl (fun r _ => hzero r),
        Finset.sum_const_zero]
      simp [hij]
  exact h

theorem clusterCNOTFlip_involutive : Function.Involutive clusterCNOTFlip := by
  intro ⟨t,c⟩
  change ((t ^^ c) ^^ c,c) = (t,c)
  rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

theorem clusterCNOTMat_unitary : clusterCNOTMat ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  teleportRelabelGate_mem_unitaryGroup (permMatrix_unitary clusterCNOTFlip_involutive) _

private theorem clusterCNOTEdge12Gate_unitary :
    clusterCNOTEdge12Gate ∈ Matrix.unitaryGroup (Fin 16) ℂ := by
  have h : clusterCZb ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
    refine diagonal_mem_unitaryGroup _ fun ⟨a,b⟩ => ?_
    cases a <;> cases b <;> simp
  exact teleportRelabelGate_mem_unitaryGroup
    (tensorGate_unitary h (Submonoid.one_mem _)) _

private theorem clusterCNOTEdge23Gate_unitary :
    clusterCNOTEdge23Gate ∈ Matrix.unitaryGroup (Fin 16) ℂ := by
  have h : clusterCNOTEdge23B ∈ Matrix.unitaryGroup ((Bool × Bool) × (Bool × Bool)) ℂ := by
    refine diagonal_mem_unitaryGroup _ fun ⟨⟨a,b⟩,⟨c,d⟩⟩ => ?_
    cases b <;> cases c <;> simp
  exact teleportRelabelGate_mem_unitaryGroup h _

theorem cluster_cnot_resource_preparation :
  IsIsometry clusterCNOTInitialFrame ∧
    observedWellFormed clusterCNOTRawProgram ∧ observedWellFormed clusterCNOTProgram := by
  refine ⟨clusterCNOTInitialFrame_isometry, ?_, ?_⟩
  · simp only [clusterCNOTRawProgram, observedWellFormed]
    exact ⟨clusterCZHdGate_unitary, clusterCZHbGate_unitary, clusterCNOTEdge12Gate_unitary,
      clusterCNOTEdge23Gate_unitary, clusterCZEdgeDcGate_unitary, clusterCZHaGate_unitary,
      clusterCZHdGate_unitary, fun _ _ => trivial⟩
  · simp only [clusterCNOTProgram, observedWellFormed]
    exact ⟨clusterCZHdGate_unitary, clusterCZHbGate_unitary, clusterCNOTEdge12Gate_unitary,
      clusterCNOTEdge23Gate_unitary, clusterCZEdgeDcGate_unitary, clusterCZHaGate_unitary,
      clusterCZHdGate_unitary, fun a b =>
        ⟨clusterCZXbGate_unitary b, clusterCZZbGate_unitary a, clusterCZZcGate_unitary a, trivial⟩⟩

private theorem clusterCNOTEdge12B_apply (ψ : QState ((Bool × Bool) × (Bool × Bool))) :
    ApplyGate clusterCNOTEdge12B ψ =
      fun p => (if p.1.1 && p.1.2 then (-1 : ℂ) else 1) * ψ p := by
  rw [clusterCNOTEdge12B, applyGate_firstFactor]
  funext p
  rw [show clusterCZb = Matrix.diagonal (fun q : Bool × Bool =>
    if q.1 && q.2 then (-1 : ℂ) else 1) from rfl, applyGate_diagonal]

private theorem clusterCNOTEdge23B_apply (ψ : QState ((Bool × Bool) × (Bool × Bool))) :
    ApplyGate clusterCNOTEdge23B ψ =
      fun p => (if p.1.2 && p.2.1 then (-1 : ℂ) else 1) * ψ p := by
  rw [clusterCNOTEdge23B, applyGate_diagonal]

theorem clusterCNOTDecoded (t c : Bool) :
    ApplyGate (clusterCZHdB * (clusterCZHaB * (clusterCZEdgeDcB *
      (clusterCNOTEdge23B * (clusterCNOTEdge12B * (clusterCZHbB * clusterCZHdB))))))
      (Qatlib.Foundations.PureStateMath.Ket ((t,false),(false,c))) =
      fun p : (Bool × Bool) × (Bool × Bool) =>
        if p.2.2 = c ∧ p.2.1 = (t ^^ c ^^ p.1.2)
          then (if p.1.1 && t then (-1 : ℂ) else 1) / 2 else 0 := by
  rw [applyGate_mul, applyGate_mul, applyGate_mul, applyGate_mul, applyGate_mul,
    applyGate_mul, clusterCZHdB_apply, clusterCZHaB_apply, clusterCZEdgeDcB_apply,
    clusterCNOTEdge23B_apply, clusterCNOTEdge12B_apply, clusterCZHbB_apply, clusterCZHdB_apply]
  funext ⟨⟨a,b⟩,⟨x,y⟩⟩
  cases t <;> cases c <;> cases a <;> cases b <;> cases x <;> cases y <;>
    simp [Qatlib.Foundations.PureStateMath.Ket, sqrt2_inv_sq, mul_comm] <;> ring_nf <;>
      try (rw [pow_two, sqrt2_inv_sq]) <;> ring_nf

theorem clusterCNOTRawLeafOperator_eq (a b : Bool) :
    (observedLeaf 1 clusterCNOTRawProgram (clusterCNOTRawLeaf a b)).operator =
      (1 : Operator 16) *
      Projector (Finset.univ.filter (fun i => clusterCZLabelD i = boolEquivFin2 b)) *
      Projector (Finset.univ.filter (fun i => clusterCZLabelA i = boolEquivFin2 a)) *
      clusterCZHdGate * clusterCZHaGate * clusterCZEdgeDcGate * clusterCNOTEdge23Gate *
      clusterCNOTEdge12Gate * clusterCZHbGate * clusterCZHdGate := by
  cases a <;> cases b <;> rfl

theorem clusterCNOTLeafOperator_eq (a b : Bool) :
    (observedLeaf 1 clusterCNOTProgram (clusterCNOTLeaf a b)).operator =
      clusterCZZcGate a * (clusterCZZbGate a * (clusterCZXbGate b *
        (observedLeaf 1 clusterCNOTRawProgram (clusterCNOTRawLeaf a b)).operator)) := by
  have hc : (observedLeaf 1 clusterCNOTProgram (clusterCNOTLeaf a b)).operator =
      (1 : Operator 16) * clusterCZZcGate a * clusterCZZbGate a * clusterCZXbGate b *
      Projector (Finset.univ.filter (fun i => clusterCZLabelD i = boolEquivFin2 b)) *
      Projector (Finset.univ.filter (fun i => clusterCZLabelA i = boolEquivFin2 a)) *
      clusterCZHdGate * clusterCZHaGate * clusterCZEdgeDcGate * clusterCNOTEdge23Gate *
      clusterCNOTEdge12Gate * clusterCZHbGate * clusterCZHdGate := by
    cases a <;> cases b <;> rfl
  rw [hc, clusterCNOTRawLeafOperator_eq]
  simp only [Matrix.mul_assoc, Matrix.one_mul]

theorem clusterCNOTRawLeafColumn (a b t c : Bool) :
    ApplyGate (observedLeaf 1 clusterCNOTRawProgram (clusterCNOTRawLeaf a b)).operator
      (relabelState clusterCZRegisterEquiv (Qatlib.Foundations.PureStateMath.Ket ((t,false),(false,c)))) =
      relabelState clusterCZRegisterEquiv
        (fun q : (Bool × Bool) × (Bool × Bool) =>
          if q.1 = (a,b) then ((if a && t then (-1 : ℂ) else 1) / 2) *
            Qatlib.Foundations.PureStateMath.Ket (t ^^ c ^^ b,c) q.2 else 0) := by
  have hG : clusterCZHdGate * (clusterCZHaGate * (clusterCZEdgeDcGate *
      (clusterCNOTEdge23Gate * (clusterCNOTEdge12Gate * (clusterCZHbGate * clusterCZHdGate))))) =
      relabelGate clusterCZRegisterEquiv (clusterCZHdB * (clusterCZHaB *
        (clusterCZEdgeDcB * (clusterCNOTEdge23B *
          (clusterCNOTEdge12B * (clusterCZHbB * clusterCZHdB)))))) := by
    simp only [clusterCZHdGate, clusterCZHaGate, clusterCZEdgeDcGate, clusterCNOTEdge23Gate,
      clusterCNOTEdge12Gate, clusterCZHbGate, ← teleportRelabelGate_mul]
  have hPA : Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelA r = boolEquivFin2 a)) =
      relabelGate clusterCZRegisterEquiv (relabelGate clusterCZRegisterEquiv.symm
        (Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelA r = boolEquivFin2 a)))) :=
    (relabelGate_relabelGate _ _).symm
  have hPD : Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelD r = boolEquivFin2 b)) =
      relabelGate clusterCZRegisterEquiv (relabelGate clusterCZRegisterEquiv.symm
        (Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelD r = boolEquivFin2 b)))) :=
    (relabelGate_relabelGate _ _).symm
  have hPlabA : relabelGate clusterCZRegisterEquiv.symm
        (Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelA r = boolEquivFin2 a))) =
      relabelGate clusterCZRegisterEquiv.symm
        (Projector (Finset.univ.filter (fun r : Fin 16 =>
          (boolEquivFin2 ∘ (fun q : (Bool × Bool) × (Bool × Bool) => q.1.1)
            ∘ clusterCZRegisterEquiv.symm) r = boolEquivFin2 a))) := rfl
  have hPlabD : relabelGate clusterCZRegisterEquiv.symm
        (Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelD r = boolEquivFin2 b))) =
      relabelGate clusterCZRegisterEquiv.symm
        (Projector (Finset.univ.filter (fun r : Fin 16 =>
          (boolEquivFin2 ∘ (fun q : (Bool × Bool) × (Bool × Bool) => q.1.2)
            ∘ clusterCZRegisterEquiv.symm) r = boolEquivFin2 b))) := rfl
  rw [clusterCNOTRawLeafOperator_eq]
  simp only [Matrix.mul_assoc, Matrix.one_mul]
  rw [hG, applyGate_mul, applyGate_mul, applyGate_relabelGate, clusterCNOTDecoded,
    hPA, hPlabA, applyGate_relabelGate,
    applyGate_relabelBoolProjector (comp := fun q : (Bool × Bool) × (Bool × Bool) => q.1.1),
    hPD, hPlabD, applyGate_relabelGate,
    applyGate_relabelBoolProjector (comp := fun q : (Bool × Bool) × (Bool × Bool) => q.1.2)]
  funext r
  obtain ⟨⟨⟨a',b'⟩,⟨x,y⟩⟩, hr⟩ : ∃ q : (Bool × Bool) × (Bool × Bool),
      r = clusterCZRegisterEquiv q := ⟨_,(Equiv.apply_symm_apply _ _).symm⟩
  subst hr
  simp only [relabelState, Function.comp_apply, Equiv.symm_apply_apply]
  cases a <;> cases b <;> cases t <;> cases c <;>
    cases a' <;> cases b' <;> cases x <;> cases y <;> simp
        [Qatlib.Foundations.PureStateMath.Ket]

theorem clusterCNOTMat_tele_entry (x y t c : Bool) :
    clusterCNOTMat (teleportOutcomeEquiv (x,y)) (teleportOutcomeEquiv (t,c)) =
      if (x,y) = (t ^^ c,c) then (1 : ℂ) else 0 := by
  cases x <;> cases y <;> cases t <;> cases c <;>
    simp [clusterCNOTMat, relabelGate, clusterCNOTb, permMatrix, clusterCNOTFlip]

theorem clusterCNOTLeafColumn (a b t c : Bool) :
    ApplyGate (observedLeaf 1 clusterCNOTProgram (clusterCNOTLeaf a b)).operator
      (relabelState clusterCZRegisterEquiv (Qatlib.Foundations.PureStateMath.Ket ((t,false),(false,c)))) =
      relabelState clusterCZRegisterEquiv
        (fun q : (Bool × Bool) × (Bool × Bool) =>
          if q.1 = (a,b) then (1/2 : ℂ) *
            clusterCNOTMat (teleportOutcomeEquiv q.2) (teleportOutcomeEquiv (t,c)) else 0) := by
  rw [clusterCNOTLeafOperator_eq, applyGate_mul, applyGate_mul, applyGate_mul,
    clusterCNOTRawLeafColumn,
    show clusterCZXbGate b = relabelGate clusterCZRegisterEquiv (clusterCZXbB b) from rfl,
    applyGate_relabelGate, clusterCZXbB_apply,
    show clusterCZZbGate a = relabelGate clusterCZRegisterEquiv (clusterCZZbB a) from rfl,
    applyGate_relabelGate, clusterCZZbB_apply,
    show clusterCZZcGate a = relabelGate clusterCZRegisterEquiv (clusterCZZcB a) from rfl,
    applyGate_relabelGate, clusterCZZcB_apply]
  funext r
  obtain ⟨⟨⟨a',b'⟩,⟨x,y⟩⟩, hr⟩ : ∃ q : (Bool × Bool) × (Bool × Bool),
      r = clusterCZRegisterEquiv q := ⟨_,(Equiv.apply_symm_apply _ _).symm⟩
  subst hr
  simp only [relabelState, Function.comp_apply, Equiv.symm_apply_apply]
  rw [clusterCNOTMat_tele_entry]
  cases a <;> cases b <;> cases t <;> cases c <;>
    cases a' <;> cases b' <;> cases x <;> cases y <;> simp
        [Qatlib.Foundations.PureStateMath.Ket] <;> norm_num

theorem cluster_cnot_raw_leaf_display_frame :
  ∀ (a b : Bool) (i : Fin 4) (r : Fin 16),
    ((observedLeaf 1 clusterCNOTRawProgram (clusterCNOTRawLeaf a b)).operator
        * clusterCNOTInitialFrame) r i
      = if r = clusterCZRegisterEquiv
            ((a, b),
              ((teleportOutcomeEquiv.symm i).1 ^^ (teleportOutcomeEquiv.symm i).2 ^^ b,
                (teleportOutcomeEquiv.symm i).2))
        then ((if a && (teleportOutcomeEquiv.symm i).1 then (-1 : ℂ) else 1) / 2) else 0 := by
  intro a b i r
  obtain ⟨⟨t,c⟩, rfl⟩ : ∃ q : Bool × Bool, i = teleportOutcomeEquiv q :=
    ⟨_,(Equiv.apply_symm_apply _ _).symm⟩
  have hc : (fun r => clusterCNOTInitialFrame r (teleportOutcomeEquiv (t,c))) =
      relabelState clusterCZRegisterEquiv (Qatlib.Foundations.PureStateMath.Ket ((t,false),(false,c))) := by
    funext r
    rw [clusterCNOTInitialFrame_column, Equiv.symm_apply_apply]
  rw [matrix_mul_column, hc, clusterCNOTRawLeafColumn]
  obtain ⟨⟨⟨a',b'⟩,⟨x,y⟩⟩, hr⟩ : ∃ q : (Bool × Bool) × (Bool × Bool),
      r = clusterCZRegisterEquiv q := ⟨_,(Equiv.apply_symm_apply _ _).symm⟩
  subst hr
  simp only [relabelState, Function.comp_apply, Equiv.symm_apply_apply]
  cases a <;> cases b <;> cases t <;> cases c <;>
    cases a' <;> cases b' <;> cases x <;> cases y <;> simp
        [Qatlib.Foundations.PureStateMath.Ket]

theorem cluster_cnot_actual_leaf_frame :
  ∀ (a b : Bool) (i : Fin 4) (r : Fin 16),
    ((observedLeaf 1 clusterCNOTProgram (clusterCNOTLeaf a b)).operator
        * clusterCNOTInitialFrame) r i
      = if r = clusterCZRegisterEquiv
            ((a, b),
              ((teleportOutcomeEquiv.symm i).1 ^^ (teleportOutcomeEquiv.symm i).2,
                (teleportOutcomeEquiv.symm i).2))
        then (1 / 2 : ℂ) else 0 := by
  intro a b i r
  obtain ⟨⟨t,c⟩, rfl⟩ : ∃ q : Bool × Bool, i = teleportOutcomeEquiv q :=
    ⟨_,(Equiv.apply_symm_apply _ _).symm⟩
  have hc : (fun r => clusterCNOTInitialFrame r (teleportOutcomeEquiv (t,c))) =
      relabelState clusterCZRegisterEquiv (Qatlib.Foundations.PureStateMath.Ket ((t,false),(false,c))) := by
    funext r
    rw [clusterCNOTInitialFrame_column, Equiv.symm_apply_apply]
  rw [matrix_mul_column, hc, clusterCNOTLeafColumn]
  obtain ⟨⟨⟨a',b'⟩,⟨x,y⟩⟩, hr⟩ : ∃ q : (Bool × Bool) × (Bool × Bool),
      r = clusterCZRegisterEquiv q := ⟨_,(Equiv.apply_symm_apply _ _).symm⟩
  subst hr
  simp only [relabelState, Function.comp_apply, Equiv.symm_apply_apply]
  rw [clusterCNOTMat_tele_entry]
  cases a <;> cases b <;> cases t <;> cases c <;>
    cases a' <;> cases b' <;> cases x <;> cases y <;> simp

theorem clusterCNOTFrame_matUnit (i j : Fin 4) :
    clusterCNOTInitialFrame * clusterCZMatUnit i j * clusterCNOTInitialFrame.conjTranspose
      = matOuter (fun r => clusterCNOTInitialFrame r i)
          (fun r => clusterCNOTInitialFrame r j) := by
  ext r r'
  have hinner : ∀ k : Fin 4,
      (∑ b : Fin 4, clusterCNOTInitialFrame r b * (if b = i ∧ k = j then (1 : ℂ) else 0))
      = if k = j then clusterCNOTInitialFrame r i else 0 := by
    intro k
    rw [Fintype.sum_eq_single i]
    · by_cases haj : k = j
      · rw [if_pos ⟨rfl, haj⟩, mul_one, if_pos haj]
      · rw [if_neg (fun hc => haj hc.2), mul_zero, if_neg haj]
    · intro b hb
      rw [if_neg (fun hc => hb hc.1), mul_zero]
  have houter : ∀ k : Fin 4,
      ((∑ b : Fin 4, clusterCNOTInitialFrame r b * (if b = i ∧ k = j then (1 : ℂ) else 0))
          * (starRingEnd ℂ) (clusterCNOTInitialFrame r' k))
      = (if k = j then clusterCNOTInitialFrame r i else 0)
          * (starRingEnd ℂ) (clusterCNOTInitialFrame r' k) :=
    fun k => congrArg (· * (starRingEnd ℂ) (clusterCNOTInitialFrame r' k)) (hinner k)
  simp only [Matrix.mul_apply, conjTranspose_apply, clusterCZMatUnit, Matrix.of_apply,
    matOuter, RCLike.star_def]
  rw [Finset.sum_congr rfl fun k _ => houter k, Fintype.sum_eq_single j]
  · rw [if_pos rfl]
  · intro k hk
    rw [if_neg hk, zero_mul]

theorem clusterCNOTActualBranchCore_matUnit (a d : Bool) (i j : Fin 4) :
    clusterCNOTActualBranchCore a d (clusterCZMatUnit i j)
      = (1 / 4 : ℂ) • (clusterCNOTMat * clusterCZMatUnit i j * clusterCNOTMat.conjTranspose) := by
  obtain ⟨⟨x, y⟩, rfl⟩ : ∃ q : Bool × Bool, i = teleportOutcomeEquiv q :=
    ⟨_, (Equiv.apply_symm_apply _ _).symm⟩
  obtain ⟨⟨x', y'⟩, rfl⟩ : ∃ q : Bool × Bool, j = teleportOutcomeEquiv q :=
    ⟨_, (Equiv.apply_symm_apply _ _).symm⟩
  have hcolI : (fun r : Fin 16 => clusterCNOTInitialFrame r (teleportOutcomeEquiv (x, y)))
      = relabelState clusterCZRegisterEquiv (Qatlib.Foundations.PureStateMath.Ket ((x, false), (false, y))) := by
    funext r
    rw [clusterCNOTInitialFrame_column, Equiv.symm_apply_apply]
  have hcolJ : (fun r : Fin 16 => clusterCNOTInitialFrame r (teleportOutcomeEquiv (x', y')))
      = relabelState clusterCZRegisterEquiv (Qatlib.Foundations.PureStateMath.Ket ((x', false), (false, y'))) := by
    funext r
    rw [clusterCNOTInitialFrame_column, Equiv.symm_apply_apply]
  have hεreal : (starRingEnd ℂ) (1 / 2 : ℂ)
      = (1 / 2 : ℂ) := by
    norm_num [map_ofNat]
  have hεsq : (1 / 2 : ℂ) * (1 / 2 : ℂ)
      = 1 / 4 := by
    norm_num
  have htr := traceLeft_matOuter_supported (I := Bool × Bool) (J := Bool × Bool) (a, d)
    (fun q : Bool × Bool => (1 / 2 : ℂ) *
      clusterCNOTMat (teleportOutcomeEquiv q) (teleportOutcomeEquiv (x, y)))
    (fun q : Bool × Bool => (1 / 2 : ℂ) *
      clusterCNOTMat (teleportOutcomeEquiv q) (teleportOutcomeEquiv (x', y')))
  have hsymm : ∀ X : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      relabelGate teleportOutcomeEquiv X
        = relabelGate teleportOutcomeEquiv.symm.symm X := fun X =>
    (congrArg (fun e => relabelGate e X) (Equiv.symm_symm teleportOutcomeEquiv)).symm
  have hcol : ∀ m : Bool × Bool,
      (fun q : Bool × Bool => (1 / 2 : ℂ) *
          clusterCNOTMat (teleportOutcomeEquiv q) (teleportOutcomeEquiv m))
        = relabelState teleportOutcomeEquiv.symm ((1 / 2 : ℂ) •
            (clusterCNOTMat *ᵥ Qatlib.Foundations.PureStateMath.Ket (teleportOutcomeEquiv m))) := by
    intro m
    funext q
    simp only [relabelState, Function.comp_apply, Equiv.symm_symm, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, ket_apply]
    rw [Fintype.sum_eq_single (teleportOutcomeEquiv m) (fun k hk => by
      rw [if_neg hk, mul_zero]), if_pos rfl, mul_one]
  unfold clusterCNOTActualBranchCore
  rw [clusterCNOTFrame_matUnit, hcolI, hcolJ, matOuter_sandwich,
    clusterCNOTLeafColumn a d x y, clusterCNOTLeafColumn a d x' y',
    relabelGate_matOuter, htr, hcol (x, y), hcol (x', y'), hsymm _, relabelGate_matOuter,
    matOuter_smul_smul, hεreal, hεsq, ← clusterCZ_mul_matUnit_conj]

theorem clusterCNOTActualBranchMap_apply (a d : Bool) (ρ : Operator 4) :
    clusterCNOTActualBranchMap a d ρ = (1 / 4 : ℂ) • conjBranch clusterCNOTMat ρ := by
  have hsmul : ∀ p : Fin 4 × Fin 4,
      clusterCNOTActualBranchMap a d (ρ p.1 p.2 • clusterCZMatUnit p.1 p.2)
      = ((1 / 4 : ℂ) * ρ p.1 p.2)
          • (clusterCNOTMat * clusterCZMatUnit p.1 p.2 * clusterCNOTMat.conjTranspose) := by
    intro p
    have h1 : clusterCNOTActualBranchMap a d (ρ p.1 p.2 • clusterCZMatUnit p.1 p.2)
        = ρ p.1 p.2 • clusterCNOTActualBranchCore a d (clusterCZMatUnit p.1 p.2) :=
      map_smul _ _ _
    rw [h1, clusterCNOTActualBranchCore_matUnit a d p.1 p.2, smul_smul,
      mul_comm (ρ p.1 p.2) (1 / 4 : ℂ)]
  have hsumdistr : clusterCNOTActualBranchMap a d
      (∑ p : Fin 4 × Fin 4, ρ p.1 p.2 • clusterCZMatUnit p.1 p.2)
      = ∑ p : Fin 4 × Fin 4, ((1 / 4 : ℂ) * ρ p.1 p.2)
          • (clusterCNOTMat * clusterCZMatUnit p.1 p.2 * clusterCNOTMat.conjTranspose) := by
    show clusterCNOTActualBranchMap a d _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun p _ => hsmul p)
  rw [clusterCZMatUnit_decomp ρ, hsumdistr,
    map_sum (conjBranch clusterCNOTMat)
      (fun p : Fin 4 × Fin 4 => ρ p.1 p.2 • clusterCZMatUnit p.1 p.2) Finset.univ,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [conjBranch_apply, Matrix.mul_smul, Matrix.smul_mul, smul_smul]

theorem cluster_cnot_actual_branch_and_reference_channel :
  ∀ a b : Bool, ∀ ρ : Operator 4,
    clusterCNOTActualBranchMap a b ρ = (1 / 4 : ℂ) • conjBranch clusterCNOTMat ρ ∧
    ∀ (r : ℕ) (σ : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) ℂ),
      tensorLeft (clusterCNOTActualBranchMap a b) σ
        = (1 / 4 : ℂ) • (TensorGate clusterCNOTMat (1 : Operator r) * σ *
            (TensorGate clusterCNOTMat (1 : Operator r))ᴴ) ∧
      (∑ o : Bool × Bool, tensorLeft (clusterCNOTActualBranchMap o.1 o.2) σ)
        = TensorGate clusterCNOTMat (1 : Operator r) * σ *
            (TensorGate clusterCNOTMat (1 : Operator r))ᴴ := by
  intro a b ρ
  refine ⟨clusterCNOTActualBranchMap_apply a b ρ, ?_⟩
  intro r σ

  have hgen : ∀ a' d' : Bool, tensorLeft (clusterCNOTActualBranchMap a' d') σ
      = (1 / 4 : ℂ) • tensorLeft (conjBranch clusterCNOTMat) σ := by
    intro a' d'
    ext ⟨x1, x2⟩ ⟨y1, y2⟩
    simp only [tensorLeft, clusterCNOTActualBranchMap_apply, Matrix.smul_apply, smul_eq_mul]
  constructor
  · rw [hgen a b, tensorLeft_conjBranch]
  · rw [Finset.sum_congr rfl fun o _ => by rw [hgen o.1 o.2, tensorLeft_conjBranch],
      sum_univ_boolPair_smul, show ((4 : ℂ) * (1 / 4)) = 1 from by norm_num, one_smul]

theorem cluster_cnot_actual_program_and_feedback_cost :
  observedLeafCount clusterCNOTRawProgram = 4 ∧ observedLeafCount clusterCNOTProgram = 4 ∧
    Function.Bijective (fun o : Bool × Bool => clusterCNOTLeaf o.1 o.2) ∧
    (∀ a b : Bool,
      (observedLeaf 1 clusterCNOTRawProgram (clusterCNOTRawLeaf a b)).accepted = true ∧
      (observedLeaf 1 clusterCNOTRawProgram (clusterCNOTRawLeaf a b)).queries = 0 ∧
      (observedLeaf 1 clusterCNOTRawProgram (clusterCNOTRawLeaf a b)).gates = 7 ∧
      (observedLeaf 1 clusterCNOTRawProgram (clusterCNOTRawLeaf a b)).measurements = 2 ∧
      (observedLeaf 1 clusterCNOTRawProgram (clusterCNOTRawLeaf a b)).outcomes
        = [(2, (boolEquivFin2 a).val), (2, (boolEquivFin2 b).val)]) ∧
    (∀ a b : Bool,
      (observedLeaf 1 clusterCNOTProgram (clusterCNOTLeaf a b)).accepted = true ∧
      (observedLeaf 1 clusterCNOTProgram (clusterCNOTLeaf a b)).queries = 0 ∧
      (observedLeaf 1 clusterCNOTProgram (clusterCNOTLeaf a b)).gates = 10 ∧
      (observedLeaf 1 clusterCNOTProgram (clusterCNOTLeaf a b)).measurements = 2 ∧
      (observedLeaf 1 clusterCNOTProgram (clusterCNOTLeaf a b)).outcomes
        = [(2, (boolEquivFin2 a).val), (2, (boolEquivFin2 b).val)]) ∧
    (∀ a b : Bool, clusterCNOTMessage a b = [a, b] ∧ (clusterCNOTMessage a b).length = 2) ∧
    Function.Injective (fun o : Bool × Bool => clusterCNOTMessage o.1 o.2) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change Function.Bijective (fun o : Bool × Bool => teleportOutcomeEquiv o)
    exact teleportOutcomeEquiv.bijective
  · intro a b
    cases a <;> cases b <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  · intro a b
    cases a <;> cases b <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  · intro a b
    exact ⟨rfl,rfl⟩
  · intro x y h
    have hc : x.1 = y.1 ∧ x.2 = y.2 := by simpa [clusterCNOTMessage] using h
    exact Prod.ext hc.1 hc.2

end Qatlib.Concepts.ClusterPatterns.WireComposition
