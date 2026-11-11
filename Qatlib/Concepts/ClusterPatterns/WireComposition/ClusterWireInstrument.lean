/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError
import Qatlib.Concepts.QuditTeleport.TeleportCore.BellTeleportationInstrument
import Qatlib.Concepts.ClusterPatterns.WireComposition.PauliMixtureTwirling
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Single-wire cluster gates and instruments

This module constructs the one-wire cluster measurement step `clusterJ` from a phase gate and a
Hadamard. It defines the two-qubit input and prepared frames, the raw measurement Kraus
operators, and their outcome-dependent X correction.

For unit-modulus phase parameters, each corrected branch has probability one half on density
inputs and implements the same logical gate after conditioning. The forgotten channel and its
arbitrary reference extensions agree with unitary conjugation, as in [RaussendorfBriegel2000].

## Main statements

* `cluster_wire_preparation_frames`: isometric preparation of the input tensored with plus.
* `cluster_wire_raw_and_corrected_kraus`: raw byproducts, corrected Kraus operators, and
  completeness.
* `cluster_wire_reference_channel`: corrected branch and forgotten-channel action with a
  reference system.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.ClusterPatterns.WireComposition

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder

set_option linter.unusedSectionVars false

/-- Summing the same scalar multiple over both Boolean values multiplies its scalar by two. -/
theorem sum_univ_bool_smul {M : Type*} [AddCommMonoid M] [Module ℂ M] (c : ℂ) (x : M) :
    (∑ _b : Bool, c • x) = ((2 : ℂ) * c) • x := by
  rw [Fintype.sum_bool, ← add_smul]
  congr 1
  ring

/-- An optional Pauli X gate squares to the identity. -/
theorem pauliXChoice_mul_self (b : Bool) : pauliXChoice b * pauliXChoice b = 1 := by
  cases b
  · rw [pauliXChoice_false, Matrix.one_mul]
  · rw [pauliXChoice_true, ← teleportRelabelGate_mul,
      show PauliX * PauliX = 1 from permMatrix_mul_self Bool.not_not,
      teleportRelabelGate_one]

/-- Scaling a matrix by a real scalar scales its conjugation map by the square of that scalar. -/
theorem conjBranch_real_smul {D : ℕ} (c : ℝ) (M : Operator D) (ρ : Operator D) :
    conjBranch (((c : ℝ) : ℂ) • M) ρ = ((c * c : ℝ) : ℂ) • conjBranch M ρ := by
  simp only [conjBranch_apply, Matrix.smul_mul, Matrix.mul_smul, conjTranspose_smul,
    smul_smul]
  have hc : star ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) = ((c * c : ℝ) : ℂ) := by
    have h := Complex.normSq_eq_conj_mul_self (z := ((c : ℝ) : ℂ))
    rw [Complex.normSq_ofReal] at h
    exact h.symm
  rw [hc]

/-- The one-qubit diagonal phase matrix with entries one and `ζ`. -/
noncomputable def clusterPhase (ζ : ℂ) : Operator 2 :=
  Matrix.diagonal fun i : Fin 2 => if i = 0 then 1 else ζ

/-- The one-qubit cluster step consisting of `clusterPhase ζ` followed by a Hadamard. -/
noncomputable def clusterJ (ζ : ℂ) : Operator 2 :=
  relabelGate boolEquivFin2 Hadamard * clusterPhase ζ

/-- The Boolean-coordinate CZ matrix, diagonal with a negative sign only on the all-true basis
pair. -/
noncomputable def clusterCZb : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.diagonal fun p => if p.1 && p.2 then (-1 : ℂ) else 1

/-- The logical CZ matrix relabeled to `Fin 4`. -/
noncomputable def clusterCZ : Operator 4 := relabelGate teleportOutcomeEquiv clusterCZb

/-- The Hadamard on the second qubit in Boolean pair coordinates. -/
noncomputable def clusterWireHbB : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  TensorGate (1 : Matrix Bool Bool ℂ) Hadamard

/-- The second-qubit Hadamard relabeled to `Fin 4`. -/
noncomputable def clusterWireHbGate : Operator 4 :=
  relabelGate teleportOutcomeEquiv clusterWireHbB

/-- The Hadamard on the first qubit in Boolean pair coordinates. -/
noncomputable def clusterWireHaB : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  TensorGate Hadamard (1 : Matrix Bool Bool ℂ)

/-- The first-qubit Hadamard relabeled to `Fin 4`. -/
noncomputable def clusterWireHaGate : Operator 4 :=
  relabelGate teleportOutcomeEquiv clusterWireHaB

/-- The phase gate with parameter `ζ` acting on the first qubit of a Boolean pair. -/
noncomputable def clusterWirePhaseB (ζ : ℂ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  TensorGate (Matrix.diagonal fun a : Bool => if a then ζ else 1) (1 : Matrix Bool Bool ℂ)

/-- The first-qubit phase gate relabeled to `Fin 4`. -/
noncomputable def clusterWirePhaseGate (ζ : ℂ) : Operator 4 :=
  relabelGate teleportOutcomeEquiv (clusterWirePhaseB ζ)

/-- The embedding of a logical qubit into the first physical qubit with the second initialized
to zero. -/
def clusterWireInitialFrame : Matrix (Fin 4) (Fin 2) ℂ :=
  Matrix.of fun r i =>
    if r = teleportOutcomeEquiv (boolEquivFin2.symm i, false) then 1 else 0

/-- The input frame after a Hadamard prepares the second physical qubit in the plus state. -/
noncomputable def clusterWirePreparedFrame : Matrix (Fin 4) (Fin 2) ℂ :=
  clusterWireHbGate * clusterWireInitialFrame

/-- The logical Kraus operator extracted at first-qubit outcome `b` after phase application,
entanglement, and Hadamard decoding. -/
noncomputable def clusterWireRawKraus (ζ : ℂ) (b : Bool) : Operator 2 :=
  Matrix.of fun c i =>
    (clusterWireHaGate * clusterCZ * clusterWirePhaseGate ζ * clusterWirePreparedFrame)
      (teleportOutcomeEquiv (b, boolEquivFin2.symm c)) i

/-- The cluster phase matrix is unitary when its phase parameter has modulus one. -/
theorem clusterPhase_unitary {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    clusterPhase ζ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  unfold clusterPhase
  refine diagonal_mem_unitaryGroup _ fun i => ?_
  by_cases h : i = 0
  · rw [if_pos h]
    simp
  · rw [if_neg h]
    exact hζ

/-- The cluster step `clusterJ ζ` is unitary when `ζ` has modulus one. -/
theorem clusterJ_unitary {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    clusterJ ζ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Submonoid.mul_mem _
    (teleportRelabelGate_mem_unitaryGroup hadamard_unitary boolEquivFin2)
    (clusterPhase_unitary hζ)

/-- The Boolean-coordinate CZ matrix is self-adjoint. -/
theorem clusterCZb_conjTranspose : clusterCZbᴴ = clusterCZb := by
  unfold clusterCZb
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;> simp

/-- The logical CZ matrix is unitary. -/
theorem clusterCZ_unitary : clusterCZ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  unfold clusterCZ
  refine teleportRelabelGate_mem_unitaryGroup ?_ _
  unfold clusterCZb
  refine diagonal_mem_unitaryGroup _ fun p => ?_
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;> simp

/-- The logical CZ matrix squares to the identity. -/
theorem clusterCZ_mul_self : clusterCZ * clusterCZ = 1 := by
  have h := (Matrix.mem_unitaryGroup_iff').mp clusterCZ_unitary
  rw [Matrix.star_eq_conjTranspose] at h
  have hc : (clusterCZ : Operator 4)ᴴ = clusterCZ := by
    rw [show (clusterCZ : Operator 4) = relabelGate teleportOutcomeEquiv clusterCZb from rfl,
      teleportRelabelGate_conjTranspose, clusterCZb_conjTranspose]
  rwa [hc] at h

/-- CZ acts pointwise by a negative sign exactly on the basis vector with both bits true. -/
theorem clusterCZ_apply (w : QState (Fin 4)) :
    ApplyGate clusterCZ w = fun r =>
      (if (teleportOutcomeEquiv.symm r).1 && (teleportOutcomeEquiv.symm r).2
          then (-1 : ℂ) else 1) * w r := by
  have hentry : ∀ r k : Fin 4, clusterCZ r k
      = if k = r then (if (teleportOutcomeEquiv.symm r).1 && (teleportOutcomeEquiv.symm r).2
            then (-1 : ℂ) else 1) else 0 := by
    intro r k
    simp only [clusterCZ, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
      clusterCZb, Matrix.diagonal_apply]
    by_cases hk : k = r
    · subst hk
      simp
    · rw [if_neg (fun h => hk (Equiv.injective _ h).symm), if_neg hk]
  funext r
  simp only [ApplyGate, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single r (fun k hk => by
    rw [hentry r k, if_neg hk, zero_mul]),
    hentry r r, if_pos rfl]

/-- For a unit-modulus phase parameter, the phase and cluster-step gates are unitary, and CZ is
a unitary involution with its stated computational-basis signs. -/
theorem cluster_phase_and_entangler_laws :
    ∀ ζ : ℂ, ‖ζ‖ = 1 →
      clusterPhase ζ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        clusterJ ζ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        clusterCZ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧ clusterCZ * clusterCZ = 1 ∧
        (∀ a b : Bool, ApplyGate clusterCZ (relabelState teleportOutcomeEquiv (Qatlib.Foundations.PureStateMath.Ket (a, b)))
          = (if a && b then (-1 : ℂ) else 1)
              • relabelState teleportOutcomeEquiv (Qatlib.Foundations.PureStateMath.Ket (a, b))) := by
  intro ζ hζ
  refine ⟨clusterPhase_unitary hζ, clusterJ_unitary hζ, clusterCZ_unitary,
    clusterCZ_mul_self, fun a b => ?_⟩
  rw [clusterCZ_apply]
  funext r
  simp only [relabelState, Function.comp_apply, Pi.smul_apply, smul_eq_mul, ket_apply]
  by_cases h : teleportOutcomeEquiv.symm r = (a, b)
  · have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [h1, h2, if_pos h, mul_one]
  · simp [if_neg h]

/-- Each column of the wire input frame is the relabeled basis pair with its logical bit first
and a false ancillary bit. -/
theorem clusterWireInitialFrame_column (i : Fin 2) (r : Fin 4) :
    clusterWireInitialFrame r i
      = relabelState teleportOutcomeEquiv (Qatlib.Foundations.PureStateMath.Ket (boolEquivFin2.symm i, false)) r := by
  by_cases h : r = teleportOutcomeEquiv (boolEquivFin2.symm i, false)
  · subst h
    simp [clusterWireInitialFrame, relabelState, Qatlib.Foundations.PureStateMath.Ket,
        Equiv.symm_apply_apply]
  · have h2 : teleportOutcomeEquiv.symm r ≠ (boolEquivFin2.symm i, false) := by
      intro hc
      apply h
      have h3 := congrArg teleportOutcomeEquiv hc
      rwa [Equiv.apply_symm_apply] at h3
    simp [clusterWireInitialFrame, relabelState, Qatlib.Foundations.PureStateMath.Ket, h, h2]

/-- The wire input frame is an isometry. -/
theorem clusterWireInitialFrame_isometry : IsIsometry clusterWireInitialFrame := by
  have hInj : ∀ i j : Fin 2,
      teleportOutcomeEquiv (boolEquivFin2.symm i, false)
        = teleportOutcomeEquiv (boolEquivFin2.symm j, false) → i = j := by
    intro i j hab
    have h2 := congrArg teleportOutcomeEquiv.symm hab
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h2
    exact boolEquivFin2.symm.injective (congrArg Prod.fst h2)
  have h : clusterWireInitialFrameᴴ * clusterWireInitialFrame = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have hval : ∀ r : Fin 4, clusterWireInitialFrameᴴ i r * clusterWireInitialFrame r i
          = if r = teleportOutcomeEquiv (boolEquivFin2.symm i, false)
              then (1 : ℂ) else 0 := by
        intro r
        rw [conjTranspose_apply]
        unfold clusterWireInitialFrame
        simp only [Matrix.of_apply]
        by_cases hr : r = teleportOutcomeEquiv (boolEquivFin2.symm i, false)
        · rw [if_pos hr]; simp
        · rw [if_neg hr]; simp
      rw [Matrix.mul_apply,
        Finset.sum_congr rfl (fun r _ => hval r),
        Finset.sum_ite_eq' Finset.univ
          (teleportOutcomeEquiv (boolEquivFin2.symm i, false))
          (fun _ => (1 : ℂ)),
        if_pos (Finset.mem_univ _)]
      simp
    · have hzero : ∀ r : Fin 4,
          clusterWireInitialFrameᴴ i r * clusterWireInitialFrame r j = 0 := by
        intro r
        rw [conjTranspose_apply]
        unfold clusterWireInitialFrame
        simp only [Matrix.of_apply]
        by_cases hr : r = teleportOutcomeEquiv (boolEquivFin2.symm i, false)
        · rw [if_pos hr, if_neg (fun hc => hij (hInj i j (hr.symm.trans hc))), mul_zero]
        · rw [if_neg hr, star_zero, zero_mul]
      rw [Matrix.mul_apply, Finset.sum_congr rfl (fun r _ => hzero r),
        Finset.sum_const_zero]
      simp [hij]
  exact h

/-- The second-qubit Hadamard is unitary. -/
theorem clusterWireHbGate_unitary : clusterWireHbGate ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  teleportRelabelGate_mem_unitaryGroup
    (tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary) _

/-- The first-qubit Hadamard is unitary. -/
theorem clusterWireHaGate_unitary : clusterWireHaGate ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  teleportRelabelGate_mem_unitaryGroup
    (tensorGate_unitary hadamard_unitary (Submonoid.one_mem _)) _

/-- The Boolean-coordinate first-qubit phase gate is unitary for a unit-modulus phase parameter. -/
theorem clusterWirePhaseB_unitary {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    clusterWirePhaseB ζ ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  unfold clusterWirePhaseB
  exact tensorGate_unitary (diagonal_mem_unitaryGroup _ fun a => by
    cases a <;> simp [hζ]) (Submonoid.one_mem _)

/-- The finite-index first-qubit phase gate is unitary for a unit-modulus phase parameter. -/
theorem clusterWirePhaseGate_unitary {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    clusterWirePhaseGate ζ ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  teleportRelabelGate_mem_unitaryGroup (clusterWirePhaseB_unitary hζ) _

/-- The plus-prepared wire frame is an isometry. -/
theorem clusterWirePreparedFrame_isometry : IsIsometry clusterWirePreparedFrame := by
  have hU : clusterWireHbGateᴴ * clusterWireHbGate = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp clusterWireHbGate_unitary
    rwa [Matrix.star_eq_conjTranspose] at h
  show clusterWirePreparedFrameᴴ * clusterWirePreparedFrame = 1
  rw [clusterWirePreparedFrame, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc clusterWireHbGateᴴ clusterWireHbGate clusterWireInitialFrame, hU,
    Matrix.one_mul]
  exact clusterWireInitialFrame_isometry

/-- Applying a Hadamard to the second qubit of `(x, false)` gives the tensor product of the
basis state `x` and plus. -/
theorem clusterWireHbB_ket (x : Bool) :
    ApplyGate clusterWireHbB (Qatlib.Foundations.PureStateMath.Ket (x, false)) = TensorState (Qatlib.Foundations.PureStateMath.Ket x) Plus := by
  rw [show (Qatlib.Foundations.PureStateMath.Ket (x, false) : QState (Bool × Bool)) = TensorState (Qatlib.Foundations.PureStateMath.Ket x) (Qatlib.Foundations.PureStateMath.Ket false) from
      (tensorState_ket_ket x false).symm,
    show clusterWireHbB = TensorGate (1 : Matrix Bool Bool ℂ) Hadamard from rfl,
    applyGate_tensorGate, applyGate_one, applyGate_hadamard_ket_false]

/-- The initial and plus-prepared wire frames are isometries, and the prepared frame embeds any
input as that input tensored with plus. -/
theorem cluster_wire_preparation_frames :
    IsIsometry clusterWireInitialFrame ∧
      clusterWirePreparedFrame = clusterWireHbGate * clusterWireInitialFrame ∧
      IsIsometry clusterWirePreparedFrame ∧
      (∀ ψ : QState (Fin 2), clusterWirePreparedFrame *ᵥ ψ =
        relabelState teleportOutcomeEquiv
          (TensorState (relabelState boolEquivFin2.symm ψ) Plus)) := by
  refine ⟨clusterWireInitialFrame_isometry, rfl, clusterWirePreparedFrame_isometry,
    fun ψ => ?_⟩
  have hinit : clusterWireInitialFrame *ᵥ ψ
      = relabelState teleportOutcomeEquiv
          (TensorState (relabelState boolEquivFin2.symm ψ) (Qatlib.Foundations.PureStateMath.Ket false)) := by
    funext r
    simp only [Matrix.mulVec, dotProduct, clusterWireInitialFrame, Matrix.of_apply,
      relabelState, Function.comp_apply, TensorState, ket_apply]
    by_cases hq : (teleportOutcomeEquiv.symm r).2 = false
    · have hp : teleportOutcomeEquiv.symm r
            = (boolEquivFin2.symm (boolEquivFin2 (teleportOutcomeEquiv.symm r).1), false) :=
          Prod.ext ((Equiv.symm_apply_apply boolEquivFin2
            (teleportOutcomeEquiv.symm r).1).symm) hq
      have hkey : r = teleportOutcomeEquiv
          (boolEquivFin2.symm (boolEquivFin2 (teleportOutcomeEquiv.symm r).1), false) :=
        ((Equiv.apply_symm_apply teleportOutcomeEquiv r).symm).trans
          (congrArg teleportOutcomeEquiv hp)
      rw [if_pos hq, mul_one, Fintype.sum_eq_single
        (boolEquivFin2 (teleportOutcomeEquiv.symm r).1), if_pos hkey, one_mul,
        Equiv.symm_symm]
      · intro k hk
        rw [if_neg (fun hc => hk (by
              have h1 := congrArg teleportOutcomeEquiv.symm hc
              rw [Equiv.symm_apply_apply] at h1
              have h2 : boolEquivFin2 (teleportOutcomeEquiv.symm r).1 = k := by
                rw [show (teleportOutcomeEquiv.symm r).1 = boolEquivFin2.symm k from by
                  rw [h1], Equiv.apply_symm_apply]
              exact h2.symm)), zero_mul]
    · have hzero : ∀ k : Fin 2,
          (if r = teleportOutcomeEquiv (boolEquivFin2.symm k, false) then (1 : ℂ) else 0)
            * ψ k = 0 := by
        intro k
        have h' : ¬ (r = teleportOutcomeEquiv (boolEquivFin2.symm k, false)) := by
          intro hc
          have h1 := congrArg teleportOutcomeEquiv.symm hc
          rw [Equiv.symm_apply_apply] at h1
          rw [congrArg Prod.snd h1] at hq
          exact hq rfl
        rw [if_neg h', zero_mul]
      rw [if_neg hq, mul_zero]
      exact Fintype.sum_eq_zero _ hzero
  show clusterWirePreparedFrame *ᵥ ψ = _
  rw [clusterWirePreparedFrame, ← mulVec_mulVec, hinit]
  show ApplyGate clusterWireHbGate (relabelState teleportOutcomeEquiv
      (TensorState (relabelState boolEquivFin2.symm ψ) (Qatlib.Foundations.PureStateMath.Ket false))) = _
  rw [show clusterWireHbGate = relabelGate teleportOutcomeEquiv clusterWireHbB from rfl,
    applyGate_relabelGate,
    show clusterWireHbB = TensorGate (1 : Matrix Bool Bool ℂ) Hadamard from rfl,
    applyGate_tensorGate, applyGate_one, applyGate_hadamard_ket_false]

/-- The first-qubit Hadamard forms the normalized sum or difference of the two first-qubit
amplitudes. -/
theorem clusterWireHaB_apply (ψ : QState (Bool × Bool)) :
    ApplyGate clusterWireHaB ψ
      = fun p => ((Real.sqrt 2 : ℂ)⁻¹) *
          (ψ (false, p.2) + (if p.1 then (-1 : ℂ) else 1) * ψ (true, p.2)) := by
  rw [show clusterWireHaB = TensorGate Hadamard (1 : Matrix Bool Bool ℂ) from rfl,
    applyGate_firstFactor]
  funext p
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Hadamard, Matrix.of_apply,
    Fintype.sum_bool]
  cases p.1 <;> cases p.2 <;> simp <;> ring

/-- Preparing the second qubit in plus and applying a first-qubit phase gives the stated
basis-state amplitudes. -/
theorem clusterWirePreparedB (ζ : ℂ) (x : Bool) :
    ApplyGate (clusterWirePhaseB ζ * clusterWireHbB) (Qatlib.Foundations.PureStateMath.Ket (x, false))
      = fun p => (if x then ζ else 1) * Qatlib.Foundations.PureStateMath.Ket x p.1 * ((Real.sqrt 2 : ℂ)⁻¹) := by
  rw [applyGate_mul, clusterWireHbB_ket,
    show clusterWirePhaseB ζ = TensorGate (Matrix.diagonal fun a : Bool => if a then ζ else 1)
        (1 : Matrix Bool Bool ℂ) from rfl,
    applyGate_tensorGate, applyGate_one, applyGate_diagonal]
  funext p
  simp only [TensorState, Plus, hadamard_apply_false, ket_apply]
  cases p.1 <;> cases x <;> simp

/-- The decoded wire circuit has the displayed amplitudes in terms of the input bit, phase
parameter, and XOR of the output bits. -/
theorem clusterWireDecodedColumn (ζ : ℂ) (x : Bool) :
    ApplyGate (clusterWireHaB * clusterCZb * clusterWirePhaseB ζ * clusterWireHbB)
        (Qatlib.Foundations.PureStateMath.Ket (x, false))
      = fun p => (1 / 2 : ℂ) * ((if x then (0 : ℂ) else 1)
          + (if p.1 ^^ p.2 then (-1 : ℂ) else 1) * (if x then ζ else 0)) := by
  rw [Matrix.mul_assoc, applyGate_mul, clusterWirePreparedB ζ, applyGate_mul,
    show clusterCZb = Matrix.diagonal fun q : Bool × Bool => if q.1 && q.2 then (-1 : ℂ) else 1
      from rfl,
    applyGate_diagonal, clusterWireHaB_apply]
  funext p
  cases p.1 <;> cases p.2 <;> cases x <;>
    simp [Qatlib.Foundations.PureStateMath.Ket, sqrt2_inv_sq, mul_comm, mul_left_comm]

/-- Each raw wire Kraus entry is one half of the displayed phase-weighted expression determined
by the input, output, and measurement bits. -/
theorem clusterWireRawKraus_apply (ζ : ℂ) (b : Bool) (c i : Fin 2) :
    clusterWireRawKraus ζ b c i
      = (1 / 2 : ℂ) * ((if boolEquivFin2.symm i then (0 : ℂ) else 1)
          + (if b ^^ (boolEquivFin2.symm c) then (-1 : ℂ) else 1)
            * (if boolEquivFin2.symm i then ζ else 0)) := by
  have hG : clusterWireHaGate * clusterCZ * clusterWirePhaseGate ζ * clusterWireHbGate
      = relabelGate teleportOutcomeEquiv
          (clusterWireHaB * clusterCZb * clusterWirePhaseB ζ * clusterWireHbB) := by
    unfold clusterWireHaGate clusterCZ clusterWirePhaseGate clusterWireHbGate
    rw [← teleportRelabelGate_mul, ← teleportRelabelGate_mul, ← teleportRelabelGate_mul]
  have hcol : (fun r : Fin 4 => clusterWireInitialFrame r i)
      = relabelState teleportOutcomeEquiv (Qatlib.Foundations.PureStateMath.Ket (boolEquivFin2.symm i, false)) := by
    funext r
    exact clusterWireInitialFrame_column i r
  simp only [clusterWireRawKraus, Matrix.of_apply]
  rw [clusterWirePreparedFrame, ← Matrix.mul_assoc, hG, matrix_mul_column, hcol,
    applyGate_relabelGate, clusterWireDecodedColumn]
  simp only [relabelState, Function.comp_apply, Equiv.symm_apply_apply]

/-- The cluster-step matrix has rows `(1, ζ) / √2` and `(1, -ζ) / √2`. -/
theorem clusterJ_entry (ζ : ℂ) (c i : Fin 2) :
    clusterJ ζ c i = ((Real.sqrt 2 : ℂ)⁻¹) *
      (if c = 0 then (if i = 0 then 1 else ζ)
        else (if i = 0 then 1 else -ζ)) := by
  fin_cases c <;> fin_cases i <;>
    simp [clusterJ, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
      clusterPhase, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_two, Hadamard,
      boolEquivFin2, mul_comm]

/-- For a unit-modulus parameter, the adjoint of the phase matrix multiplied by the matrix
equals the identity. -/
theorem clusterPhase_conj_mul (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    (clusterPhase ζ)ᴴ * clusterPhase ζ = 1 := by
  unfold clusterPhase
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [Pi.star_apply]
  have hz : star ζ * ζ = 1 := by
    have h2 := Complex.normSq_eq_conj_mul_self (z := ζ)
    rw [Complex.normSq_eq_norm_sq, hζ, one_pow] at h2
    exact h2.symm
  by_cases h0 : i = 0
  · rw [h0]
    norm_num
  · simp only [if_neg h0]
    exact hz

/-- For a unit-modulus parameter, the adjoint of the cluster-step matrix multiplied by the
matrix equals the identity. -/
theorem clusterJ_conj_mul (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    (clusterJ ζ)ᴴ * clusterJ ζ = 1 := by
  have hH : (relabelGate boolEquivFin2 Hadamard)ᴴ * relabelGate boolEquivFin2 Hadamard = 1 := by
    rw [teleportRelabelGate_conjTranspose, ← teleportRelabelGate_mul,
      hadamard_conjTranspose, hadamard_mul_self, teleportRelabelGate_one]
  unfold clusterJ
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (relabelGate boolEquivFin2 Hadamard)ᴴ
      (relabelGate boolEquivFin2 Hadamard) (clusterPhase ζ), hH, Matrix.one_mul,
    clusterPhase_conj_mul ζ hζ]

/-- For a unit-modulus parameter, the raw Kraus operator is `X^b * clusterJ ζ / √2`, X feedback
removes the byproduct, and the corrected family is complete. See [RaussendorfBriegel2000]. -/
theorem cluster_wire_raw_and_corrected_kraus :
    ∀ (ζ : ℂ) (b : Bool), ‖ζ‖ = 1 →
      clusterWireRawKraus ζ b = ((Real.sqrt 2 : ℂ)⁻¹) • (pauliXChoice b * clusterJ ζ) ∧
        pauliXChoice b * clusterWireRawKraus ζ b = ((Real.sqrt 2 : ℂ)⁻¹) • clusterJ ζ ∧
        (∑ b : Bool, (pauliXChoice b * clusterWireRawKraus ζ b)ᴴ
            * (pauliXChoice b * clusterWireRawKraus ζ b)) = 1 := by
  intro ζ b hζ
  have hmain : ∀ b' : Bool, clusterWireRawKraus ζ b'
      = ((Real.sqrt 2 : ℂ)⁻¹) • (pauliXChoice b' * clusterJ ζ) := by
    intro b'
    ext c i
    rw [clusterWireRawKraus_apply ζ b' c i, Matrix.smul_apply, smul_eq_mul]
    cases b' <;> fin_cases c <;> fin_cases i <;>
      simp [pauliXChoice, clusterJ_entry, Matrix.mul_apply, Fin.sum_univ_two, sqrt2_inv_sq,
        boolEquivFin2, PauliX, permMatrix, relabelGate, Matrix.reindex_apply,
        Matrix.submatrix_apply, mul_comm, mul_left_comm]
  have hcorr : ∀ b' : Bool, pauliXChoice b' * clusterWireRawKraus ζ b'
      = ((Real.sqrt 2 : ℂ)⁻¹) • clusterJ ζ := by
    intro b'
    rw [hmain b', Matrix.mul_smul, ← Matrix.mul_assoc, pauliXChoice_mul_self, Matrix.one_mul]
  refine ⟨hmain b, hcorr b, ?_⟩
  have hconj : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    have h := Complex.conj_ofReal ((Real.sqrt 2 : ℝ)⁻¹)
    rw [Complex.ofReal_inv] at h
    exact h
  have hterm : (((Real.sqrt 2 : ℂ)⁻¹) • clusterJ ζ)ᴴ * (((Real.sqrt 2 : ℂ)⁻¹) • clusterJ ζ)
      = (1 / 2 : ℂ) • (1 : Operator 2) := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hconj,
      clusterJ_conj_mul ζ hζ, sqrt2_inv_sq]
  rw [Fintype.sum_bool, hcorr true, hcorr false, hterm, ← add_smul,
    show (1 / 2 + 1 / 2 : ℂ) = 1 from by norm_num, one_smul]

/-- The raw wire Kraus operator followed by the Pauli X correction selected by the outcome bit. -/
noncomputable def clusterWireCorrectedKraus (ζ : ℂ) (b : Bool) : Operator 2 :=
  pauliXChoice b * clusterWireRawKraus ζ b

/-- For a unit-modulus phase parameter, the corrected wire Kraus operators satisfy completeness. -/
theorem clusterWireKrausComplete (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ∑ b : Bool, (clusterWireCorrectedKraus ζ b)ᴴ * clusterWireCorrectedKraus ζ b = 1 :=
  (cluster_wire_raw_and_corrected_kraus ζ false hζ).2.2

/-- The binary instrument defined by the corrected wire Kraus operators for a unit-modulus phase
parameter. -/
noncomputable def clusterWireInstrument (ζ : ℂ) (hζ : ‖ζ‖ = 1) : Instrument Bool 2 2 :=
  Instrument.ofKraus (clusterWireCorrectedKraus ζ) (clusterWireKrausComplete ζ hζ)

/-- Each corrected wire branch is one half of conjugation by `clusterJ ζ`. -/
theorem clusterWireInstrument_branch_apply (ζ : ℂ) (hζ : ‖ζ‖ = 1) (ρ : Operator 2)
    (b : Bool) :
    (clusterWireInstrument ζ hζ).branch b ρ = (1 / 2 : ℂ) • conjBranch (clusterJ ζ) ρ := by
  rw [show ((clusterWireInstrument ζ hζ).branch b) ρ
      = (clusterWireCorrectedKraus ζ b) * ρ * (clusterWireCorrectedKraus ζ b).conjTranspose
        from rfl,
    clusterWireCorrectedKraus, (cluster_wire_raw_and_corrected_kraus ζ b hζ).2.1]
  have hconj : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    have h := Complex.conj_ofReal ((Real.sqrt 2 : ℝ)⁻¹)
    rw [Complex.ofReal_inv] at h
    exact h
  simp only [conjBranch_apply, Matrix.smul_mul, Matrix.mul_smul, conjTranspose_smul,
    smul_smul, hconj, sqrt2_inv_sq]

/-- Each corrected wire branch is one half of cluster-step conjugation, its probability is the
real input trace divided by two, and forgetting outcomes gives cluster-step conjugation. -/
theorem cluster_wire_instrument_probability :
    ∀ (ζ : ℂ) (hζ : ‖ζ‖ = 1) (ρ : Operator 2) (b : Bool),
      (clusterWireInstrument ζ hζ).branch b ρ = (1 / 2 : ℂ) • conjBranch (clusterJ ζ) ρ ∧
        instrumentProb (clusterWireInstrument ζ hζ) ρ b = (Matrix.trace ρ).re / 2 ∧
        (clusterWireInstrument ζ hζ).forget.map ρ = conjBranch (clusterJ ζ) ρ := by
  intro ζ hζ ρ b
  refine ⟨clusterWireInstrument_branch_apply ζ hζ ρ b, ?_, ?_⟩
  · rw [instrumentProb, clusterWireInstrument_branch_apply ζ hζ ρ b, Matrix.trace_smul,
      smul_eq_mul, trace_conjBranch_unitary (clusterJ ζ) (clusterJ_unitary hζ) ρ,
      Complex.mul_re]
    simp
    ring
  · rw [Instrument.forget_apply,
      Finset.sum_congr rfl fun b' _ => clusterWireInstrument_branch_apply ζ hζ ρ b',
      sum_univ_bool_smul, show ((2 : ℂ) * (1 / 2 : ℂ)) = 1 from by norm_num, one_smul]

set_option linter.unusedVariables false in

/-- For a density input, both wire outcomes have probability one half and their conditional
output is conjugation by `clusterJ ζ`. -/
theorem cluster_wire_conditional_output :
    ∀ (ζ : ℂ) (hζ : ‖ζ‖ = 1) (ρ : Operator 2) (hρ : IsDensityOperator ρ) (b : Bool),
      instrumentProb (clusterWireInstrument ζ hζ) ρ b = 1 / 2 ∧
        (∀ h : 0 < instrumentProb (clusterWireInstrument ζ hζ) ρ b,
          (clusterWireInstrument ζ hζ).conditionalState ρ b h = conjBranch (clusterJ ζ) ρ) := by
  intro ζ hζ ρ hρ b
  have htr : Matrix.trace ρ = 1 := hρ.2
  have hprob : instrumentProb (clusterWireInstrument ζ hζ) ρ b = 1 / 2 := by
    rw [(cluster_wire_instrument_probability ζ hζ ρ b).2.1, htr]
    norm_num
  refine ⟨hprob, fun h => ?_⟩
  have hrecon := (Instrument.conditionalState_reconstruction
    (clusterWireInstrument ζ hζ) ρ b h).1
  rw [hprob, clusterWireInstrument_branch_apply] at hrecon
  have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  rw [hhalf] at hrecon
  have hscaled := congrArg (fun σ : Operator 2 => (2 : ℂ) • σ) hrecon
  simpa only [smul_smul, show (2 : ℂ) * (1 / 2) = 1 from by norm_num, one_smul] using hscaled

/-- Each corrected wire branch acts as one half of cluster-step conjugation tensored with the
reference identity, and summing outcomes gives the full reference-extended unitary channel.
See [RaussendorfBriegel2000]. -/
theorem cluster_wire_reference_channel :
    ∀ (ζ : ℂ) (hζ : ‖ζ‖ = 1) (r : ℕ)
      (ρ : Matrix (Fin 2 × Fin r) (Fin 2 × Fin r) ℂ) (b : Bool),
      tensorLeft ((clusterWireInstrument ζ hζ).branch b) ρ
        = (1 / 2 : ℂ) • (TensorGate (clusterJ ζ) (1 : Operator r) * ρ
            * (TensorGate (clusterJ ζ) (1 : Operator r))ᴴ) ∧
        (∑ b : Bool, tensorLeft ((clusterWireInstrument ζ hζ).branch b) ρ)
          = TensorGate (clusterJ ζ) (1 : Operator r) * ρ
            * (TensorGate (clusterJ ζ) (1 : Operator r))ᴴ := by
  intro ζ hζ r ρ b
  have hgen : ∀ b' : Bool,
      tensorLeft ((clusterWireInstrument ζ hζ).branch b') ρ
        = (1 / 2 : ℂ) • tensorLeft (conjBranch (clusterJ ζ)) ρ := by
    intro b'
    ext ⟨x1, x2⟩ ⟨y1, y2⟩
    simp only [tensorLeft, clusterWireInstrument_branch_apply, Matrix.smul_apply,
      smul_eq_mul]
  constructor
  · rw [hgen b, tensorLeft_conjBranch]
  · rw [Finset.sum_congr rfl fun b' _ => by rw [hgen b', tensorLeft_conjBranch],
      sum_univ_bool_smul, show ((2 : ℂ) * (1 / 2 : ℂ)) = 1 from by norm_num, one_smul]

end Qatlib.Concepts.ClusterPatterns.WireComposition
