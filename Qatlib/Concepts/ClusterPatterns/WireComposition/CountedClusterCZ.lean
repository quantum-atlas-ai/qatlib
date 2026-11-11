/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.ClusterCZInstrument
import Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterWire

/-!
# Counted cluster CZ execution

This module defines the observed four-qubit CZ program, including its outcome-dependent physical
Pauli feedback. Exact leaf formulas preserve the outcome-dependent sign at vector level, and
tracing out the measured pair identifies each physical branch with `clusterCZInstrument`.

Every logical branch is one quarter of CZ conjugation, also with an arbitrary reference system.
The final resource theorem counts thirteen gates and two measurements per branch for this
implementation of the cluster gate scheme in [RaussendorfBriegel2000].

## Main statements

* `cluster_cz_actual_leaf_frame_with_outcome_phase`: exact physical branch amplitudes and signs.
* `cluster_cz_actual_program_instrument_bridge`: agreement between the observed program and the
  logical instrument.
* `cluster_cz_actual_reference_channel`: branch and forgotten-channel formulas with references.
* `cluster_cz_actual_program_and_feedback_cost`: well-formedness, leaf enumeration, and exact
  resource counts.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false


open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel

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

set_option linter.unusedSectionVars false

/-- The partial trace over the first Boolean pair preserves addition of four-qubit matrices. -/
theorem traceLeft_add4 (A B : Matrix ((Bool × Bool) × (Bool × Bool)) ((Bool × Bool) × (Bool × Bool)) ℂ) :
    Matrix.traceLeft (A + B) = Matrix.traceLeft A + Matrix.traceLeft B := by
  ext c c'
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.add_apply, Finset.sum_add_distrib]

/-- The partial trace over the first Boolean pair commutes with complex scalar multiplication. -/
theorem traceLeft_smul4 (r : ℂ)
    (A : Matrix ((Bool × Bool) × (Bool × Bool)) ((Bool × Bool) × (Bool × Bool)) ℂ) :
    Matrix.traceLeft (r • A) = r • Matrix.traceLeft A := by
  ext c' c''
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.smul_apply, Finset.mul_sum, smul_eq_mul]

/-- The CZ matrix is diagonal in Boolean-pair coordinates, with a negative entry only when both
bits are true. -/
theorem clusterCZ_tele_entry (b c x y : Bool) :
    clusterCZ (teleportOutcomeEquiv (b, c)) (teleportOutcomeEquiv (x, y))
      = if (b, c) = (x, y) then (if b && c then (-1 : ℂ) else 1) else 0 := by
  simp [clusterCZ, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, clusterCZb, Matrix.diagonal_apply]

/-- The measurement label reading physical vertex `a` from a finite-index four-qubit basis
state. -/
def clusterCZLabelA (r : Fin 16) : Fin 2 :=
  boolEquivFin2 (clusterCZRegisterEquiv.symm r).1.1

/-- The measurement label reading physical vertex `d` from a finite-index four-qubit basis
state. -/
def clusterCZLabelD (r : Fin 16) : Fin 2 :=
  boolEquivFin2 (clusterCZRegisterEquiv.symm r).1.2

/-- The optional Pauli X on output vertex `b` in Boolean product coordinates. -/
noncomputable def clusterCZXbB (a : Bool) :
    Matrix ((Bool × Bool) × (Bool × Bool)) ((Bool × Bool) × (Bool × Bool)) ℂ :=
  TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (TensorGate (if a then PauliX else 1) (1 : Matrix Bool Bool ℂ))

/-- The optional Pauli Z on output vertex `b` in Boolean product coordinates. -/
noncomputable def clusterCZZbB (d : Bool) :
    Matrix ((Bool × Bool) × (Bool × Bool)) ((Bool × Bool) × (Bool × Bool)) ℂ :=
  TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (TensorGate (if d then PauliZ else 1) (1 : Matrix Bool Bool ℂ))

/-- The optional Pauli X on output vertex `c` in Boolean product coordinates. -/
noncomputable def clusterCZXcB (d : Bool) :
    Matrix ((Bool × Bool) × (Bool × Bool)) ((Bool × Bool) × (Bool × Bool)) ℂ :=
  TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (TensorGate (1 : Matrix Bool Bool ℂ) (if d then PauliX else 1))

/-- The optional Pauli Z on output vertex `c` in Boolean product coordinates. -/
noncomputable def clusterCZZcB (a : Bool) :
    Matrix ((Bool × Bool) × (Bool × Bool)) ((Bool × Bool) × (Bool × Bool)) ℂ :=
  TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (TensorGate (1 : Matrix Bool Bool ℂ) (if a then PauliZ else 1))

/-- The optional Pauli X on vertex `b` relabeled to `Fin 16`. -/
noncomputable def clusterCZXbGate (a : Bool) : Operator 16 :=
  relabelGate clusterCZRegisterEquiv (clusterCZXbB a)

/-- The optional Pauli Z on vertex `b` relabeled to `Fin 16`. -/
noncomputable def clusterCZZbGate (d : Bool) : Operator 16 :=
  relabelGate clusterCZRegisterEquiv (clusterCZZbB d)

/-- The optional Pauli X on vertex `c` relabeled to `Fin 16`. -/
noncomputable def clusterCZXcGate (d : Bool) : Operator 16 :=
  relabelGate clusterCZRegisterEquiv (clusterCZXcB d)

/-- The optional Pauli Z on vertex `c` relabeled to `Fin 16`. -/
noncomputable def clusterCZZcGate (a : Bool) : Operator 16 :=
  relabelGate clusterCZRegisterEquiv (clusterCZZcB a)

/-- Choosing either Pauli X or the identity according to a Boolean bit gives a unitary matrix. -/
theorem clusterCZPauliChoiceX_unitary (a : Bool) :
    (if a then PauliX else (1 : Matrix Bool Bool ℂ)) ∈ Matrix.unitaryGroup Bool ℂ := by
  cases a
  · exact Submonoid.one_mem _
  · exact pauliX_unitary

/-- Choosing either Pauli Z or the identity according to a Boolean bit gives a unitary matrix. -/
theorem clusterCZPauliChoiceZ_unitary (d : Bool) :
    (if d then PauliZ else (1 : Matrix Bool Bool ℂ)) ∈ Matrix.unitaryGroup Bool ℂ := by
  cases d
  · exact Submonoid.one_mem _
  · exact pauliZ_unitary

/-- The optional physical X correction on vertex `b` is unitary. -/
theorem clusterCZXbGate_unitary (a : Bool) :
    clusterCZXbGate a ∈ Matrix.unitaryGroup (Fin 16) ℂ :=
  teleportRelabelGate_mem_unitaryGroup
    (tensorGate_unitary (Submonoid.one_mem _)
      (tensorGate_unitary (clusterCZPauliChoiceX_unitary a) (Submonoid.one_mem _))) _

/-- The optional physical Z correction on vertex `b` is unitary. -/
theorem clusterCZZbGate_unitary (d : Bool) :
    clusterCZZbGate d ∈ Matrix.unitaryGroup (Fin 16) ℂ :=
  teleportRelabelGate_mem_unitaryGroup
    (tensorGate_unitary (Submonoid.one_mem _)
      (tensorGate_unitary (clusterCZPauliChoiceZ_unitary d) (Submonoid.one_mem _))) _

/-- The optional physical X correction on vertex `c` is unitary. -/
theorem clusterCZXcGate_unitary (d : Bool) :
    clusterCZXcGate d ∈ Matrix.unitaryGroup (Fin 16) ℂ :=
  teleportRelabelGate_mem_unitaryGroup
    (tensorGate_unitary (Submonoid.one_mem _)
      (tensorGate_unitary (Submonoid.one_mem _) (clusterCZPauliChoiceX_unitary d))) _

/-- The optional physical Z correction on vertex `c` is unitary. -/
theorem clusterCZZcGate_unitary (a : Bool) :
    clusterCZZcGate a ∈ Matrix.unitaryGroup (Fin 16) ℂ :=
  teleportRelabelGate_mem_unitaryGroup
    (tensorGate_unitary (Submonoid.one_mem _)
      (tensorGate_unitary (Submonoid.one_mem _) (clusterCZPauliChoiceZ_unitary a))) _

/-- The observed CZ program comprising resource preparation, decoding, two measurements, and
four outcome-dependent Pauli correction gates. -/
noncomputable def clusterCZProgram : ObservedCircuit (Fin 16) :=
  .step (.gate clusterCZHaGate) (.step (.gate clusterCZHdGate)
    (.step (.gate clusterCZHbGate) (.step (.gate clusterCZHcGate)
      (.step (.gate clusterCZEdgeAbGate) (.step (.gate clusterCZEdgeDcGate)
        (.step (.gate clusterCZEdgeBcGate) (.step (.gate clusterCZHaGate)
          (.step (.gate clusterCZHdGate)
            (.measure 2 clusterCZLabelA (fun ka =>
              .measure 2 clusterCZLabelD (fun kd =>
                .step (.gate (clusterCZXbGate (boolEquivFin2.symm ka)))
                  (.step (.gate (clusterCZZbGate (boolEquivFin2.symm kd)))
                    (.step (.gate (clusterCZXcGate (boolEquivFin2.symm kd)))
                      (.step (.gate (clusterCZZcGate (boolEquivFin2.symm ka)))
                        (.halt true)))))))))))))))

/-- The CZ program leaf selected by its two Boolean measurement outcomes. -/
noncomputable def clusterCZLeaf (a d : Bool) :
    Fin (observedLeafCount clusterCZProgram) :=
  Fin.cast (by rfl) (teleportOutcomeEquiv (a, d))

/-- The two-bit classical message containing the CZ measurement outcomes in order. -/
def clusterCZMessage (a d : Bool) : List Bool := [a, d]

/-- The CZ leaf operator is the ordered product of its preparation, decoding, selected outcome
projectors, and Pauli feedback gates. -/
theorem clusterCZLeafOperator_eq (a d : Bool) :
    (observedLeaf 1 clusterCZProgram (clusterCZLeaf a d)).operator
      = (((((((((((((((1 : Operator 16)
            * clusterCZZcGate (boolEquivFin2.symm (boolEquivFin2 a)))
            * clusterCZXcGate (boolEquivFin2.symm (boolEquivFin2 d)))
            * clusterCZZbGate (boolEquivFin2.symm (boolEquivFin2 d)))
            * clusterCZXbGate (boolEquivFin2.symm (boolEquivFin2 a)))
          * Projector (Finset.univ.filter (fun i => clusterCZLabelD i = boolEquivFin2 d)))
          * Projector (Finset.univ.filter (fun i => clusterCZLabelA i = boolEquivFin2 a)))
          * clusterCZHdGate) * clusterCZHaGate)
          * clusterCZEdgeBcGate) * clusterCZEdgeDcGate)
          * clusterCZEdgeAbGate) * clusterCZHcGate) * clusterCZHbGate)
          * clusterCZHdGate) * clusterCZHaGate := by
  cases a <;> cases d <;> rfl

/-- The optional X correction on `b` acts by XOR with its control bit in that output coordinate. -/
theorem clusterCZXbB_apply (a : Bool) (ψ : QState ((Bool × Bool) × (Bool × Bool))) :
    ApplyGate (clusterCZXbB a) ψ = fun p => ψ (p.1, (p.2.1 ^^ a, p.2.2)) := by
  rw [show clusterCZXbB a = TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
      (TensorGate (if a then PauliX else 1) (1 : Matrix Bool Bool ℂ)) from rfl,
    applyGate_secondFactor]
  funext p
  obtain ⟨⟨a0, d0⟩, ⟨b0, c0⟩⟩ := p
  rw [applyGate_firstFactor]
  cases a
  · simp only [if_neg (by decide : ¬(false = true))]
    rw [congrFun (applyGate_one _) b0, Bool.xor_false]
  · simp only [if_true]
    exact (applyGate_permMatrix Bool.not_not _ _).trans (by rw [Bool.xor_true])

/-- The optional Z correction on `b` multiplies an amplitude by minus one exactly when its
control and the `b` bit are true. -/
theorem clusterCZZbB_apply (d : Bool) (ψ : QState ((Bool × Bool) × (Bool × Bool))) :
    ApplyGate (clusterCZZbB d) ψ
      = fun p => (if d && p.2.1 then (-1 : ℂ) else 1) * ψ p := by
  rw [show clusterCZZbB d = TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
      (TensorGate (if d then PauliZ else 1) (1 : Matrix Bool Bool ℂ)) from rfl,
    applyGate_secondFactor]
  funext p
  obtain ⟨⟨a0, d0⟩, ⟨b0, c0⟩⟩ := p
  rw [applyGate_firstFactor]
  cases d
  · simp only [if_neg (by decide : ¬(false = true))]
    rw [congrFun (applyGate_one _) b0]
    simp
  · simp only [if_true]
    have hz : ApplyGate PauliZ (fun i => ψ ((a0, d0), (i, c0))) b0
        = (if b0 then (-1 : ℂ) else 1) * ψ ((a0, d0), (b0, c0)) := by
      simp only [ApplyGate, Matrix.mulVec, dotProduct, PauliZ, Matrix.diagonal_apply]
      cases b0 <;> simp
    rw [hz]
    cases b0 <;> simp

/-- The optional X correction on `c` acts by XOR with its control bit in that output coordinate. -/
theorem clusterCZXcB_apply (d : Bool) (ψ : QState ((Bool × Bool) × (Bool × Bool))) :
    ApplyGate (clusterCZXcB d) ψ = fun p => ψ (p.1, (p.2.1, p.2.2 ^^ d)) := by
  rw [show clusterCZXcB d = TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
      (TensorGate (1 : Matrix Bool Bool ℂ) (if d then PauliX else 1)) from rfl,
    applyGate_secondFactor]
  funext p
  obtain ⟨⟨a0, d0⟩, ⟨b0, c0⟩⟩ := p
  rw [applyGate_secondFactor]
  cases d
  · simp only [if_neg (by decide : ¬(false = true))]
    rw [congrFun (applyGate_one _) c0, Bool.xor_false]
  · simp only [if_true]
    exact (applyGate_permMatrix Bool.not_not _ _).trans (by rw [Bool.xor_true])

/-- The optional Z correction on `c` multiplies an amplitude by minus one exactly when its
control and the `c` bit are true. -/
theorem clusterCZZcB_apply (a : Bool) (ψ : QState ((Bool × Bool) × (Bool × Bool))) :
    ApplyGate (clusterCZZcB a) ψ
      = fun p => (if a && p.2.2 then (-1 : ℂ) else 1) * ψ p := by
  rw [show clusterCZZcB a = TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
      (TensorGate (1 : Matrix Bool Bool ℂ) (if a then PauliZ else 1)) from rfl,
    applyGate_secondFactor]
  funext p
  obtain ⟨⟨a0, d0⟩, ⟨b0, c0⟩⟩ := p
  rw [applyGate_secondFactor]
  cases a
  · simp only [if_neg (by decide : ¬(false = true))]
    rw [congrFun (applyGate_one _) c0]
    simp
  · simp only [if_true]
    have hz : ApplyGate PauliZ (fun j => ψ ((a0, d0), (b0, j))) c0
        = (if c0 then (-1 : ℂ) else 1) * ψ ((a0, d0), (b0, c0)) := by
      simp only [ApplyGate, Matrix.mulVec, dotProduct, PauliZ, Matrix.diagonal_apply]
      cases c0 <;> simp
    rw [hz]
    cases c0 <;> simp

set_option maxHeartbeats 4000000 in

/-- Each CZ leaf column is supported on its measured pair and equals the logical CZ column times
one half and the sign determined by the two outcomes. -/
theorem clusterCZLeafColumn (a d x y : Bool) :
    ApplyGate ((observedLeaf 1 clusterCZProgram (clusterCZLeaf a d)).operator)
        (relabelState clusterCZRegisterEquiv (Ket ((x, y), (false, false))))
      = relabelState clusterCZRegisterEquiv
          (fun q : (Bool × Bool) × (Bool × Bool) =>
            if q.1 = (a, d) then ((if a && d then (-1 : ℂ) else 1) / 2) *
              clusterCZ (teleportOutcomeEquiv q.2) (teleportOutcomeEquiv (x, y)) else 0) := by
  have hG : clusterCZHdGate * (clusterCZHaGate * clusterCZPreparationGate)
      = relabelGate clusterCZRegisterEquiv
          (clusterCZHdB * (clusterCZHaB * clusterCZPreparationB)) := by
    rw [clusterCZPreparationGate_eq_relabel]
    unfold clusterCZHdGate clusterCZHaGate
    rw [← teleportRelabelGate_mul, ← teleportRelabelGate_mul]
  have hPAsymm : Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelA r
          = boolEquivFin2 a))
      = relabelGate clusterCZRegisterEquiv (relabelGate clusterCZRegisterEquiv.symm
          (Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelA r
            = boolEquivFin2 a)))) :=
    (relabelGate_relabelGate _ _).symm
  have hPlabA : relabelGate clusterCZRegisterEquiv.symm
        (Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelA r
          = boolEquivFin2 a)))
      = relabelGate clusterCZRegisterEquiv.symm
          (Projector (Finset.univ.filter (fun r : Fin 16 =>
            (boolEquivFin2 ∘ (fun q : (Bool × Bool) × (Bool × Bool) => q.1.1)
              ∘ clusterCZRegisterEquiv.symm) r = boolEquivFin2 a))) := rfl
  have hPDsymm : Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelD r
          = boolEquivFin2 d))
      = relabelGate clusterCZRegisterEquiv (relabelGate clusterCZRegisterEquiv.symm
          (Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelD r
            = boolEquivFin2 d)))) :=
    (relabelGate_relabelGate _ _).symm
  have hPlabD : relabelGate clusterCZRegisterEquiv.symm
        (Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelD r
          = boolEquivFin2 d)))
      = relabelGate clusterCZRegisterEquiv.symm
          (Projector (Finset.univ.filter (fun r : Fin 16 =>
            (boolEquivFin2 ∘ (fun q : (Bool × Bool) × (Bool × Bool) => q.1.2)
              ∘ clusterCZRegisterEquiv.symm) r = boolEquivFin2 d))) := rfl
  rw [clusterCZLeafOperator_eq a d,
    show boolEquivFin2.symm (boolEquivFin2 a) = a from Equiv.symm_apply_apply _ _,
    show boolEquivFin2.symm (boolEquivFin2 d) = d from Equiv.symm_apply_apply _ _,
    Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc, one_mul,
    show clusterCZEdgeBcGate * (clusterCZEdgeDcGate * (clusterCZEdgeAbGate *
        (clusterCZHcGate * (clusterCZHbGate * (clusterCZHdGate * clusterCZHaGate)))))
      = clusterCZPreparationGate from rfl, hG,
    applyGate_mul, applyGate_mul, applyGate_mul, applyGate_mul, applyGate_mul, applyGate_mul,
    applyGate_relabelGate, clusterCZDecoded,
    hPAsymm, hPlabA, applyGate_relabelGate,
    applyGate_relabelBoolProjector (comp := fun q : (Bool × Bool) × (Bool × Bool) => q.1.1),
    hPDsymm, hPlabD, applyGate_relabelGate,
    applyGate_relabelBoolProjector (comp := fun q : (Bool × Bool) × (Bool × Bool) => q.1.2),
    show clusterCZXbGate a = relabelGate clusterCZRegisterEquiv (clusterCZXbB a) from rfl,
    applyGate_relabelGate, clusterCZXbB_apply,
    show clusterCZZbGate d = relabelGate clusterCZRegisterEquiv (clusterCZZbB d) from rfl,
    applyGate_relabelGate, clusterCZZbB_apply,
    show clusterCZXcGate d = relabelGate clusterCZRegisterEquiv (clusterCZXcB d) from rfl,
    applyGate_relabelGate, clusterCZXcB_apply,
    show clusterCZZcGate a = relabelGate clusterCZRegisterEquiv (clusterCZZcB a) from rfl,
    applyGate_relabelGate, clusterCZZcB_apply]
  funext r
  obtain ⟨⟨⟨a', d'⟩, ⟨b, c⟩⟩, hr⟩ : ∃ p : (Bool × Bool) × (Bool × Bool),
      r = clusterCZRegisterEquiv p := ⟨_, (Equiv.apply_symm_apply _ _).symm⟩
  subst hr
  simp only [relabelState, Function.comp_apply, Equiv.symm_apply_apply]
  rw [clusterCZ_tele_entry]
  cases a <;> cases d <;> cases a' <;> cases d' <;> cases b <;> cases c <;>
    cases x <;> cases y <;> simp <;> norm_num

/-- The physical CZ leaf composed with the input frame has support only on its outcome pair and
equals the logical CZ matrix scaled by `(-1)^(a * d) / 2`. -/
theorem cluster_cz_actual_leaf_frame_with_outcome_phase :
    ∀ (a d a' d' : Bool) (c i : Fin 4),
      ((observedLeaf 1 clusterCZProgram (clusterCZLeaf a d)).operator
          * clusterCZInitialFrame)
        (clusterCZRegisterEquiv ((a', d'), teleportOutcomeEquiv.symm c)) i =
      if (a', d') = (a, d) then ((if a && d then (-1 : ℂ) else 1) / 2) * clusterCZ c i
        else 0 := by
  intro a d a' d' c i
  obtain ⟨⟨x, y⟩, rfl⟩ : ∃ q : Bool × Bool, i = teleportOutcomeEquiv q :=
    ⟨_, (Equiv.apply_symm_apply _ _).symm⟩
  rw [matrix_mul_column]
  rw [show (fun r : Fin 16 => clusterCZInitialFrame r (teleportOutcomeEquiv (x, y)))
      = relabelState clusterCZRegisterEquiv (Ket ((x, y), (false, false))) from by
        funext r
        rw [clusterCZInitialFrame_column, Equiv.symm_apply_apply]]
  rw [clusterCZLeafColumn]
  simp only [relabelState, Function.comp_apply, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply]

/-- The four-dimensional matrix unit with a single one in row `i` and column `j`. -/
noncomputable def clusterCZMatUnit (i j : Fin 4) : Operator 4 :=
  Matrix.of fun c c' => if c = i ∧ c' = j then (1 : ℂ) else 0

/-- Every four-dimensional operator is the sum of its entries multiplied by their corresponding
matrix units. -/
theorem clusterCZMatUnit_decomp (ρ : Operator 4) :
    ρ = ∑ p : Fin 4 × Fin 4, ρ p.1 p.2 • clusterCZMatUnit p.1 p.2 := by
  ext c c'
  have hentry : ∀ p : Fin 4 × Fin 4,
      (ρ p.1 p.2 • clusterCZMatUnit p.1 p.2) c c'
        = if c = p.1 ∧ c' = p.2 then ρ p.1 p.2 else 0 := by
    intro p
    simp only [Matrix.smul_apply, clusterCZMatUnit, Matrix.of_apply, smul_eq_mul]
    by_cases h1 : c = p.1 <;> by_cases h2 : c' = p.2 <;> simp [h1, h2]
  rw [Matrix.sum_apply, Finset.sum_congr rfl (fun p _ => hentry p),
    Fintype.sum_eq_single (c, c')]
  · rw [if_pos ⟨rfl, rfl⟩]
  · intro p hp
    have hnc : ¬ (c = p.1 ∧ c' = p.2) := by
      intro hc
      apply hp
      rw [Prod.mk.injEq]
      exact ⟨hc.1.symm, hc.2.symm⟩
    rw [if_neg hnc]

/-- Embedding a matrix unit by the CZ input frame gives the outer product of the corresponding
frame columns. -/
theorem clusterCZFrame_matUnit (i j : Fin 4) :
    clusterCZInitialFrame * clusterCZMatUnit i j * clusterCZInitialFrame.conjTranspose
      = matOuter (fun r => clusterCZInitialFrame r i)
          (fun r => clusterCZInitialFrame r j) := by
  ext r r'
  have hinner : ∀ k : Fin 4,
      (∑ b : Fin 4, clusterCZInitialFrame r b * (if b = i ∧ k = j then (1 : ℂ) else 0))
      = if k = j then clusterCZInitialFrame r i else 0 := by
    intro k
    rw [Fintype.sum_eq_single i]
    · by_cases haj : k = j
      · rw [if_pos ⟨rfl, haj⟩, mul_one, if_pos haj]
      · rw [if_neg (fun hc => haj hc.2), mul_zero, if_neg haj]
    · intro b hb
      rw [if_neg (fun hc => hb hc.1), mul_zero]
  have houter : ∀ k : Fin 4,
      ((∑ b : Fin 4, clusterCZInitialFrame r b * (if b = i ∧ k = j then (1 : ℂ) else 0))
          * (starRingEnd ℂ) (clusterCZInitialFrame r' k))
      = (if k = j then clusterCZInitialFrame r i else 0)
          * (starRingEnd ℂ) (clusterCZInitialFrame r' k) :=
    fun k => congrArg (· * (starRingEnd ℂ) (clusterCZInitialFrame r' k)) (hinner k)
  simp only [Matrix.mul_apply, conjTranspose_apply, clusterCZMatUnit, Matrix.of_apply,
    matOuter, RCLike.star_def]
  rw [Finset.sum_congr rfl fun k _ => houter k, Fintype.sum_eq_single j]
  · rw [if_pos rfl]
  · intro k hk
    rw [if_neg hk, zero_mul]

/-- Conjugating a matrix unit by `M` gives the outer product of `M` applied to its two basis
vectors. -/
theorem clusterCZ_mul_matUnit_conj (M : Operator 4) (i j : Fin 4) :
    M * clusterCZMatUnit i j * M.conjTranspose = matOuter (M *ᵥ Ket i) (M *ᵥ Ket j) := by
  have hu : clusterCZMatUnit i j = matOuter (Ket i) (Ket j) := by
    ext r r'
    simp only [clusterCZMatUnit, Matrix.of_apply, matOuter, ket_apply]
    by_cases h1 : r = i <;> by_cases h2 : r' = j <;> simp [h1, h2]
  rw [hu, matOuter_sandwich]
  rfl

/-- The logical output of a physical CZ branch obtained by input embedding, branch conjugation,
and tracing out the measured pair. -/
noncomputable def clusterCZActualBranchCore (a d : Bool) (ρ : Operator 4) : Operator 4 :=
  relabelGate teleportOutcomeEquiv (Matrix.traceLeft
    (relabelGate clusterCZRegisterEquiv.symm
      ((observedLeaf 1 clusterCZProgram (clusterCZLeaf a d)).operator
        * (clusterCZInitialFrame * ρ * clusterCZInitialFrame.conjTranspose)
        * (observedLeaf 1 clusterCZProgram (clusterCZLeaf a d)).operator.conjTranspose)))

/-- The complex-linear map packaging `clusterCZActualBranchCore`. -/
noncomputable def clusterCZActualBranchMap (a d : Bool) : Operator 4 →ₗ[ℂ] Operator 4 where
  toFun := clusterCZActualBranchCore a d
  map_add' := by
    intro ρ σ
    unfold clusterCZActualBranchCore
    simp only [Matrix.mul_add, Matrix.add_mul, relabelGate_add', traceLeft_add4]
  map_smul' := by
    intro r ρ
    unfold clusterCZActualBranchCore
    simp only [Matrix.mul_smul, Matrix.smul_mul, relabelGate_smul', traceLeft_smul4,
      RingHom.id_apply]

/-- On every matrix unit, the physical CZ branch equals one quarter of conjugation by the
logical CZ. -/
theorem clusterCZActualBranchCore_matUnit (a d : Bool) (i j : Fin 4) :
    clusterCZActualBranchCore a d (clusterCZMatUnit i j)
      = (1 / 4 : ℂ) • (clusterCZ * clusterCZMatUnit i j * clusterCZ.conjTranspose) := by
  obtain ⟨⟨x, y⟩, rfl⟩ : ∃ q : Bool × Bool, i = teleportOutcomeEquiv q :=
    ⟨_, (Equiv.apply_symm_apply _ _).symm⟩
  obtain ⟨⟨x', y'⟩, rfl⟩ : ∃ q : Bool × Bool, j = teleportOutcomeEquiv q :=
    ⟨_, (Equiv.apply_symm_apply _ _).symm⟩
  have hcolI : (fun r : Fin 16 => clusterCZInitialFrame r (teleportOutcomeEquiv (x, y)))
      = relabelState clusterCZRegisterEquiv (Ket ((x, y), (false, false))) := by
    funext r
    rw [clusterCZInitialFrame_column, Equiv.symm_apply_apply]
  have hcolJ : (fun r : Fin 16 => clusterCZInitialFrame r (teleportOutcomeEquiv (x', y')))
      = relabelState clusterCZRegisterEquiv (Ket ((x', y'), (false, false))) := by
    funext r
    rw [clusterCZInitialFrame_column, Equiv.symm_apply_apply]
  have hεreal : (starRingEnd ℂ) ((if a && d then (-1 : ℂ) else 1) / 2)
      = (if a && d then (-1 : ℂ) else 1) / 2 := by
    cases a <;> cases d <;> simp [Complex.conj_ofNat]
  have hεsq : (if a && d then (-1 : ℂ) else 1) / 2 * ((if a && d then (-1 : ℂ) else 1) / 2)
      = 1 / 4 := by
    cases a <;> cases d <;> norm_num
  have htr := traceLeft_matOuter_supported (I := Bool × Bool) (J := Bool × Bool) (a, d)
    (fun q : Bool × Bool => ((if a && d then (-1 : ℂ) else 1) / 2) *
      clusterCZ (teleportOutcomeEquiv q) (teleportOutcomeEquiv (x, y)))
    (fun q : Bool × Bool => ((if a && d then (-1 : ℂ) else 1) / 2) *
      clusterCZ (teleportOutcomeEquiv q) (teleportOutcomeEquiv (x', y')))
  have hsymm : ∀ X : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      relabelGate teleportOutcomeEquiv X
        = relabelGate teleportOutcomeEquiv.symm.symm X := fun X =>
    (congrArg (fun e => relabelGate e X) (Equiv.symm_symm teleportOutcomeEquiv)).symm
  have hcol : ∀ m : Bool × Bool,
      (fun q : Bool × Bool => ((if a && d then (-1 : ℂ) else 1) / 2) *
          clusterCZ (teleportOutcomeEquiv q) (teleportOutcomeEquiv m))
        = relabelState teleportOutcomeEquiv.symm (((if a && d then (-1 : ℂ) else 1) / 2) •
            (clusterCZ *ᵥ Ket (teleportOutcomeEquiv m))) := by
    intro m
    funext q
    simp only [relabelState, Function.comp_apply, Equiv.symm_symm, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, ket_apply]
    rw [Fintype.sum_eq_single (teleportOutcomeEquiv m) (fun k hk => by
      rw [if_neg hk, mul_zero]), if_pos rfl, mul_one]
  unfold clusterCZActualBranchCore
  rw [clusterCZFrame_matUnit, hcolI, hcolJ, matOuter_sandwich,
    clusterCZLeafColumn a d x y, clusterCZLeafColumn a d x' y',
    relabelGate_matOuter, htr, hcol (x, y), hcol (x', y'), hsymm _, relabelGate_matOuter,
    matOuter_smul_smul, hεreal, hεsq, ← clusterCZ_mul_matUnit_conj]

/-- Each physical CZ branch map equals one quarter of conjugation by `clusterCZ`. -/
theorem clusterCZActualBranchMap_apply (a d : Bool) (ρ : Operator 4) :
    clusterCZActualBranchMap a d ρ = (1 / 4 : ℂ) • conjBranch clusterCZ ρ := by
  have hsmul : ∀ p : Fin 4 × Fin 4,
      clusterCZActualBranchMap a d (ρ p.1 p.2 • clusterCZMatUnit p.1 p.2)
      = ((1 / 4 : ℂ) * ρ p.1 p.2)
          • (clusterCZ * clusterCZMatUnit p.1 p.2 * clusterCZ.conjTranspose) := by
    intro p
    have h1 : clusterCZActualBranchMap a d (ρ p.1 p.2 • clusterCZMatUnit p.1 p.2)
        = ρ p.1 p.2 • clusterCZActualBranchCore a d (clusterCZMatUnit p.1 p.2) :=
      map_smul _ _ _
    rw [h1, clusterCZActualBranchCore_matUnit a d p.1 p.2, smul_smul,
      mul_comm (ρ p.1 p.2) (1 / 4 : ℂ)]
  have hsumdistr : clusterCZActualBranchMap a d
      (∑ p : Fin 4 × Fin 4, ρ p.1 p.2 • clusterCZMatUnit p.1 p.2)
      = ∑ p : Fin 4 × Fin 4, ((1 / 4 : ℂ) * ρ p.1 p.2)
          • (clusterCZ * clusterCZMatUnit p.1 p.2 * clusterCZ.conjTranspose) := by
    show clusterCZActualBranchMap a d _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun p _ => hsmul p)
  rw [clusterCZMatUnit_decomp ρ, hsumdistr,
    map_sum (conjBranch clusterCZ)
      (fun p : Fin 4 × Fin 4 => ρ p.1 p.2 • clusterCZMatUnit p.1 p.2) Finset.univ,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [conjBranch_apply, Matrix.mul_smul, Matrix.smul_mul, smul_smul]

/-- Each physical CZ branch map equals the corresponding branch of `clusterCZInstrument` and is
one quarter of CZ conjugation. -/
theorem cluster_cz_actual_program_instrument_bridge :
    ∀ a d : Bool,
      clusterCZActualBranchMap a d = clusterCZInstrument.branch (a, d) ∧
      (∀ ρ : Operator 4, clusterCZActualBranchMap a d ρ
        = (1 / 4 : ℂ) • conjBranch clusterCZ ρ) := by
  intro a d
  refine ⟨?_, fun ρ => clusterCZActualBranchMap_apply a d ρ⟩
  apply LinearMap.ext
  intro ρ
  rw [clusterCZActualBranchMap_apply a d ρ, clusterCZInstrument_branch_apply ρ a d]

/-- Each physical CZ branch acts on an arbitrary reference extension as one quarter of CZ
conjugation tensored with the identity, and summing the branches gives the full unitary
channel. See [RaussendorfBriegel2000]. -/
theorem cluster_cz_actual_reference_channel :
    ∀ (r : ℕ) (ρ : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) ℂ) (a d : Bool),
      tensorLeft (clusterCZActualBranchMap a d) ρ =
        (1 / 4 : ℂ) • (TensorGate clusterCZ (1 : Operator r) * ρ *
          (TensorGate clusterCZ (1 : Operator r))ᴴ) ∧
      (∑ o : Bool × Bool, tensorLeft (clusterCZActualBranchMap o.1 o.2) ρ) =
        TensorGate clusterCZ (1 : Operator r) * ρ *
          (TensorGate clusterCZ (1 : Operator r))ᴴ := by
  intro r ρ a d
  have hgen : ∀ a' d' : Bool, tensorLeft (clusterCZActualBranchMap a' d') ρ
      = (1 / 4 : ℂ) • tensorLeft (conjBranch clusterCZ) ρ := by
    intro a' d'
    ext ⟨x1, x2⟩ ⟨y1, y2⟩
    simp only [tensorLeft, clusterCZActualBranchMap_apply, Matrix.smul_apply, smul_eq_mul]
  constructor
  · rw [hgen a d, tensorLeft_conjBranch]
  · rw [Finset.sum_congr rfl fun o _ => by rw [hgen o.1 o.2, tensorLeft_conjBranch],
      sum_univ_boolPair_smul, show ((4 : ℂ) * (1 / 4)) = 1 from by norm_num, one_smul]

/-- The CZ program is well formed and has four bijectively indexed accepting, query-free leaves,
each with thirteen gates, two measurements, and an injective two-bit message. -/
theorem cluster_cz_actual_program_and_feedback_cost :
    observedWellFormed clusterCZProgram ∧ observedLeafCount clusterCZProgram = 4 ∧
      Function.Bijective (fun o : Bool × Bool => clusterCZLeaf o.1 o.2) ∧
      (∀ a d : Bool,
        (observedLeaf 1 clusterCZProgram (clusterCZLeaf a d)).accepted = true ∧
        (observedLeaf 1 clusterCZProgram (clusterCZLeaf a d)).queries = 0 ∧
        (observedLeaf 1 clusterCZProgram (clusterCZLeaf a d)).gates = 13 ∧
        (observedLeaf 1 clusterCZProgram (clusterCZLeaf a d)).measurements = 2 ∧
        (observedLeaf 1 clusterCZProgram (clusterCZLeaf a d)).outcomes =
          [(2, (boolEquivFin2 a).val), (2, (boolEquivFin2 d).val)] ∧
        clusterCZMessage a d = [a, d] ∧ (clusterCZMessage a d).length = 2) ∧
      Function.Injective (fun o : Bool × Bool => clusterCZMessage o.1 o.2) := by
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · simp only [clusterCZProgram, observedWellFormed]
    exact ⟨clusterCZHaGate_unitary, clusterCZHdGate_unitary, clusterCZHbGate_unitary,
      clusterCZHcGate_unitary, clusterCZEdgeAbGate_unitary, clusterCZEdgeDcGate_unitary,
      clusterCZEdgeBcGate_unitary, clusterCZHaGate_unitary, clusterCZHdGate_unitary,
      fun ka kd =>
        ⟨clusterCZXbGate_unitary _, clusterCZZbGate_unitary _, clusterCZXcGate_unitary _,
          clusterCZZcGate_unitary _, trivial⟩⟩
  · constructor
    · intro x y hxy
      have hv : (clusterCZLeaf x.1 x.2).val = (clusterCZLeaf y.1 y.2).val :=
        congrArg Fin.val hxy
      rcases x with ⟨x1, x2⟩
      rcases y with ⟨y1, y2⟩
      simp only [clusterCZLeaf, Fin.val_cast, teleportOutcomeEquiv_val] at hv
      cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> simp_all [boolEquivFin2]
    · intro j
      refine ⟨teleportOutcomeEquiv.symm
          (j.cast (rfl : observedLeafCount clusterCZProgram = 4)), ?_⟩
      have hval : (clusterCZLeaf
          (teleportOutcomeEquiv.symm
            (j.cast (rfl : observedLeafCount clusterCZProgram = 4))).1
          (teleportOutcomeEquiv.symm
            (j.cast (rfl : observedLeafCount clusterCZProgram = 4))).2).val = j.val := by
        fin_cases j <;> simp [clusterCZLeaf] <;> rfl
      exact Fin.eq_of_val_eq hval
  · intro a d
    cases a <;> cases d <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro x y hxy
    simp [clusterCZMessage] at hxy
    rcases x with ⟨x1, x2⟩
    rcases y with ⟨y1, y2⟩
    simp_all

end Qatlib.Concepts.ClusterPatterns.WireComposition
