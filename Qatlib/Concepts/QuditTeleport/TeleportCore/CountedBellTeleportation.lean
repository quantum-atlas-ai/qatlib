/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.BellTeleportationInstrument
import Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedInstrument

/-!
# Counted Bell teleportation circuits

This module implements Bell teleportation as the observed circuit `teleportProgram` and
identifies its actual reduced branches with the corrected instrument branches. Matrix unit
calculations establish recovery of arbitrary operators and preservation of an arbitrary finite
reference.

The circuit is well formed with four accepted leaves, six gates and one measurement per leaf,
and no queries. `teleportMessage` gives an injective two bit encoding of Alice's outcome, as in
the qubit protocol of [BennettEtAl1993Teleportation].

## Main statements

* `bell_actual_program_legality_and_counts`: circuit validity and exact leaf counts.
* `bell_actual_program_branch_bridge`: equality of actual and instrument branches.
* `bell_actual_program_reference_recovery`: recovery with a reference register.
* `bell_classical_message_cost`: two bits distinguish the four outcomes.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.QuditTeleport.TeleportCore

open Matrix
open scoped ComplexOrder

set_option linter.unusedSectionVars false

/-- Relabeling matrix indices preserves addition. -/
theorem relabelGate_add' {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (A B : Matrix I I ℂ) :
    relabelGate e (A + B) = relabelGate e A + relabelGate e B := by
  ext x y
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply]

/-- Relabeling matrix indices preserves complex scalar multiplication. -/
theorem relabelGate_smul' {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (c : ℂ) (A : Matrix I I ℂ) :
    relabelGate e (c • A) = c • relabelGate e A := by
  ext x y
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply,
    smul_eq_mul]

/-- Tracing out Alice's Boolean register pair preserves addition. -/
theorem traceLeft_add' (A B : Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ) :
    Matrix.traceLeft (A + B) = Matrix.traceLeft A + Matrix.traceLeft B := by
  ext c c'
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.add_apply, Finset.sum_add_distrib]

/-- Tracing out Alice's Boolean register pair preserves complex scalar multiplication. -/
theorem traceLeft_smul' (c : ℂ)
    (A : Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ) :
    Matrix.traceLeft (c • A) = c • Matrix.traceLeft A := by
  ext c' c''
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.smul_apply, Finset.mul_sum, smul_eq_mul]

/-- The rank one matrix with entries `u r * conj (w r')`. -/
noncomputable def matOuter {I : Type*} [Fintype I] [DecidableEq I]
    (u w : QState I) : Matrix I I ℂ :=
  Matrix.of fun r r' => u r * (starRingEnd ℂ) (w r')

/-- Scaling the two vectors in `matOuter` scales the matrix by the first scalar times the
conjugate of the second. -/
theorem matOuter_smul_smul {I : Type*} [Fintype I] [DecidableEq I] (c d : ℂ) (u w : QState I) :
    matOuter (c • u) (d • w) = (c * (starRingEnd ℂ) d) • matOuter u w := by
  ext r r'
  simp only [matOuter, Matrix.of_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
    map_mul]
  ring

/-- Conjugation of `matOuter u w` by `L` applies `L` to both of its defining vectors. -/
theorem matOuter_sandwich {I : Type*} [Fintype I] [DecidableEq I] (L : Matrix I I ℂ)
    (u w : QState I) :
    L * matOuter u w * Lᴴ = matOuter (ApplyGate L u) (ApplyGate L w) := by
  ext r r'
  simp only [Matrix.mul_apply, matOuter, Matrix.of_apply, Matrix.conjTranspose_apply,
    ApplyGate, Matrix.mulVec, dotProduct, RCLike.star_def]
  have h1 : ∀ q : I, (∑ p : I, L r p * (u p * (starRingEnd ℂ) (w q)))
      = (∑ p : I, L r p * u p) * (starRingEnd ℂ) (w q) := by
    intro q
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => (mul_assoc _ _ _).symm
  simp only [h1]
  rw [Finset.sum_congr rfl (fun q _ => show ((∑ p : I, L r p * u p) * (starRingEnd ℂ) (w q))
        * (starRingEnd ℂ) (L r' q)
        = (∑ p : I, L r p * u p) * ((starRingEnd ℂ) (w q) * (starRingEnd ℂ) (L r' q)) from
        mul_assoc _ _ _),
    ← Finset.mul_sum,
    Finset.sum_congr rfl (fun q _ => show (starRingEnd ℂ) (w q) * (starRingEnd ℂ) (L r' q)
        = (starRingEnd ℂ) (L r' q * w q) from by rw [map_mul]; ring),
    ← map_sum (starRingEnd ℂ) (fun q => L r' q * w q)]

/-- Relabeling both vectors of `matOuter` and then relabeling the matrix back recovers the
original matrix. -/
theorem relabelGate_matOuter {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (u w : QState I) :
    relabelGate e.symm (matOuter (relabelState e u) (relabelState e w)) = matOuter u w := by
  ext x y
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, matOuter,
    Matrix.of_apply, relabelState, Function.comp_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply]

/-- The Pauli X correction on Bob's register selected by the second bit of the encoded outcome
`k`. -/
noncomputable def teleportBobXGate (k : Fin 4) : Operator 8 :=
  relabelGate teleportRegisterEquiv (teleportXcB (teleportOutcomeEquiv.symm k).2)

/-- The Pauli Z correction on Bob's register selected by the first bit of the encoded outcome
`k`. -/
noncomputable def teleportBobZGate (k : Fin 4) : Operator 8 :=
  relabelGate teleportRegisterEquiv (teleportZcB (teleportOutcomeEquiv.symm k).1)

/-- The encoded pair of Alice's Boolean register values extracted from a flattened three qubit
index. -/
def teleportAliceLabel (r : Fin 8) : Fin 4 :=
  teleportOutcomeEquiv (teleportRegisterEquiv.symm r).1

/-- The projector onto the register subspace whose Alice label is `k`. -/
noncomputable def teleportAliceProjectorGate (k : Fin 4) : Operator 8 :=
  Projector (Finset.univ.filter (fun i => teleportAliceLabel i = k))

/-- The observed Bell teleportation circuit with resource preparation, Bell decoding, Alice's
four outcome measurement, and Bob's two conditional Pauli gates. -/
noncomputable def teleportProgram : ObservedCircuit (Fin 8) :=
  .step (.gate teleportHbGate) (.step (.gate teleportCnotBcGate)
    (.step (.gate teleportCnotAbGate) (.step (.gate teleportHaGate)
      (.measure 4 teleportAliceLabel
        (fun k => .step (.gate (teleportBobXGate k))
          (.step (.gate (teleportBobZGate k)) (.halt true)))))))

/-- The leaf index corresponding to Alice's Boolean outcome pair. -/
noncomputable def teleportProgramLeaf (o : Bool × Bool) :
    Fin (observedLeafCount teleportProgram) :=
  Fin.cast (by rfl) (teleportOutcomeEquiv o)

/-- The two bit message listing Alice's first and second measurement outcomes. -/
def teleportMessage (o : Bool × Bool) : List Bool := [o.1, o.2]

/-- Expands the selected program leaf operator as the ordered product of preparation gates,
decoding gates, Alice's projector, and Bob's corrections. -/
theorem teleportLeafOperator_eq (o : Bool × Bool) :
    (observedLeaf (1 : Operator 8) teleportProgram (teleportProgramLeaf o)).operator
      = ((((((((1 : Operator 8) * teleportBobZGate (teleportOutcomeEquiv o))
        * teleportBobXGate (teleportOutcomeEquiv o))
        * teleportAliceProjectorGate (teleportOutcomeEquiv o))
        * teleportHaGate)
        * teleportCnotAbGate)
        * teleportCnotBcGate)
        * teleportHbGate) := by
  rcases o with ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- Bob's output operator for a selected actual circuit leaf, obtained by embedding the input,
applying the leaf operator, and tracing out Alice. -/
noncomputable def teleportActualBranchCore (o : Bool × Bool) (ρ : Operator 2) : Operator 2 :=
  relabelGate boolEquivFin2 (Matrix.traceLeft
    (relabelGate teleportRegisterEquiv.symm
      ((observedLeaf (1 : Operator 8) teleportProgram (teleportProgramLeaf o)).operator
        * (teleportInitialFrame * ρ * teleportInitialFrame.conjTranspose)
        * (observedLeaf (1 : Operator 8) teleportProgram (teleportProgramLeaf o)).operator.conjTranspose)))

/-- The complex linear map on input operators induced by a selected actual Bell circuit branch. -/
noncomputable def teleportActualBranchMap (o : Bool × Bool) : Operator 2 →ₗ[ℂ] Operator 2 where
  toFun := teleportActualBranchCore o
  map_add' := by
    intro ρ σ
    unfold teleportActualBranchCore
    simp only [Matrix.mul_add, Matrix.add_mul, relabelGate_add', traceLeft_add']
  map_smul' := by
    intro r ρ
    unfold teleportActualBranchCore
    simp only [Matrix.mul_smul, Matrix.smul_mul, relabelGate_smul', traceLeft_smul',
      RingHom.id_apply]

/-- The conditional Pauli X gate on Bob's Boolean register is unitary. -/
theorem teleportXcB_unitary (β : Bool) :
    teleportXcB β ∈ Matrix.unitaryGroup ((Bool × Bool) × Bool) ℂ := by
  cases β
  · simp only [teleportXcB, if_neg (by decide : ¬(false = true)), tensorGate_one]
    exact Submonoid.one_mem _
  · simp only [teleportXcB, if_true]
    exact tensorGate_unitary (Submonoid.one_mem _) pauliX_unitary

/-- The conditional Pauli Z gate on Bob's Boolean register is unitary. -/
theorem teleportZcB_unitary (α : Bool) :
    teleportZcB α ∈ Matrix.unitaryGroup ((Bool × Bool) × Bool) ℂ := by
  cases α
  · simp only [teleportZcB, if_neg (by decide : ¬(false = true)), tensorGate_one]
    exact Submonoid.one_mem _
  · simp only [teleportZcB, if_true]
    exact tensorGate_unitary (Submonoid.one_mem _) pauliZ_unitary

/-- The flattened Bob X correction selected by an encoded outcome is unitary. -/
theorem teleportBobXGate_unitary (k : Fin 4) :
    teleportBobXGate k ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  teleportRelabelGate_mem_unitaryGroup (teleportXcB_unitary _) _

/-- The flattened Bob Z correction selected by an encoded outcome is unitary. -/
theorem teleportBobZGate_unitary (k : Fin 4) :
    teleportBobZGate k ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  teleportRelabelGate_mem_unitaryGroup (teleportZcB_unitary _) _

/-- The flattened Hadamard gate on register `b` is unitary. -/
theorem teleportHbGate_unitary : teleportHbGate ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  teleportRelabelGate_mem_unitaryGroup
    (tensorGate_unitary
      (tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary) (Submonoid.one_mem _)) _

/-- The flattened CNOT gate from `b` to `c` is unitary. -/
theorem teleportCnotBcGate_unitary : teleportCnotBcGate ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  teleportRelabelGate_mem_unitaryGroup
    (teleportRelabelGate_mem_unitaryGroup
      (tensorGate_unitary (Submonoid.one_mem _) cnot_unitary) _) _

/-- The flattened CNOT gate from `a` to `b` is unitary. -/
theorem teleportCnotAbGate_unitary : teleportCnotAbGate ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  teleportRelabelGate_mem_unitaryGroup
    (tensorGate_unitary cnot_unitary (Submonoid.one_mem _)) _

/-- The flattened Hadamard gate on register `a` is unitary. -/
theorem teleportHaGate_unitary : teleportHaGate ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  teleportRelabelGate_mem_unitaryGroup
    (tensorGate_unitary
      (tensorGate_unitary hadamard_unitary (Submonoid.one_mem _)) (Submonoid.one_mem _)) _

/-- Alice's outcome projector expressed in the three Boolean register coordinates. -/
noncomputable def teleportProjectorB (o : Bool × Bool) :
    Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ :=
  relabelGate teleportRegisterEquiv.symm
    (teleportAliceProjectorGate (teleportOutcomeEquiv o))

/-- Extracting Alice's label after flattening a Boolean register triple gives the encoding of
its first two bits. -/
theorem teleportAliceLabel_congr (q : ((Bool × Bool) × Bool)) :
    teleportAliceLabel (teleportRegisterEquiv q) = teleportOutcomeEquiv q.1 := by
  simp only [teleportAliceLabel, Equiv.symm_apply_apply]

/-- Alice's projector retains precisely the amplitudes whose encoded Alice outcome equals the
selected outcome. -/
theorem teleportProjectorB_apply (o : Bool × Bool) (ψ : QState ((Bool × Bool) × Bool)) :
    ApplyGate (teleportProjectorB o) ψ
      = fun p => if teleportOutcomeEquiv p.1 = teleportOutcomeEquiv (o.1, o.2)
        then ψ p else 0 := by
  have hentry : ∀ p q : ((Bool × Bool) × Bool),
      (teleportProjectorB o) p q
        = if teleportOutcomeEquiv p.1 = teleportOutcomeEquiv (o.1, o.2)
          then (if p = q then (1 : ℂ) else 0) else 0 := by
    intro p q
    have h1 : (teleportProjectorB o) p q
        = (teleportAliceProjectorGate (teleportOutcomeEquiv (o.1, o.2)))
            (teleportRegisterEquiv p) (teleportRegisterEquiv q) := by
      simp only [teleportProjectorB, relabelGate, Matrix.reindex_apply,
        Matrix.submatrix_apply, Equiv.symm_symm]
    rw [h1]
    simp only [teleportAliceProjectorGate, Projector, Matrix.diagonal_apply,
      Finset.mem_filter, Finset.mem_univ, true_and, teleportAliceLabel_congr]
    by_cases hpq : teleportRegisterEquiv p = teleportRegisterEquiv q
    · have hpq' : p = q := Equiv.injective _ hpq
      rw [if_pos hpq, if_pos hpq']
    · have hpq' : ¬ p = q := fun hc => hpq (by rw [hc])
      rw [if_neg hpq]
      by_cases hl : teleportOutcomeEquiv p.1 = teleportOutcomeEquiv (o.1, o.2)
      · rw [if_pos hl, if_neg hpq']
      · rw [if_neg hl]

  funext p
  have hsum : ∑ q : ((Bool × Bool) × Bool), (teleportProjectorB o) p q * ψ q
      = (teleportProjectorB o) p p * ψ p :=
    Fintype.sum_eq_single p (fun q hq => by
      rw [hentry p q]
      by_cases hl : teleportOutcomeEquiv p.1 = teleportOutcomeEquiv (o.1, o.2)
      · rw [if_pos hl, if_neg (fun hc => hq (by rw [hc])), zero_mul]
      · rw [if_neg hl, zero_mul])
  simp only [ApplyGate, Matrix.mulVec, dotProduct]
  rw [hsum, hentry p p]
  by_cases hl : teleportOutcomeEquiv p.1 = teleportOutcomeEquiv (o.1, o.2)
  · rw [if_pos hl, if_pos hl, if_pos rfl, one_mul]
  · rw [if_neg hl, if_neg hl, zero_mul]

/-- The conditional X correction acts on amplitudes by replacing Bob's bit with its exclusive or
with `β`. -/
theorem teleportXcB_apply' (β : Bool) (ψ : QState ((Bool × Bool) × Bool)) :
    ApplyGate (teleportXcB β) ψ = fun p => ψ (p.1, p.2 ^^ β) := by
  rw [teleportXcB_apply]
  funext p
  cases β <;> simp

/-- A selected circuit leaf sends an initialized input basis vector to one half of the basis
vector carrying Alice's selected outcome and the same input on Bob. -/
theorem teleportLeafColumn (o : Bool × Bool) (i : Fin 2) :
    ApplyGate ((observedLeaf (1 : Operator 8) teleportProgram (teleportProgramLeaf o)).operator)
        (relabelState teleportRegisterEquiv (Qatlib.Foundations.PureStateMath.Ket ((boolEquivFin2.symm i, false), false)))
      = (1/2 : ℂ) • relabelState teleportRegisterEquiv
          (Qatlib.Foundations.PureStateMath.Ket ((o.1, o.2), boolEquivFin2.symm i)) := by
  rw [teleportLeafOperator_eq o, applyGate_mul, applyGate_mul, applyGate_mul, applyGate_mul,
    applyGate_mul, applyGate_mul, applyGate_mul, applyGate_one,
    show teleportHbGate = relabelGate teleportRegisterEquiv teleportHbB from rfl,
    applyGate_relabelGate,
    show teleportCnotBcGate = relabelGate teleportRegisterEquiv teleportCnotBcB from rfl,
    applyGate_relabelGate,
    show teleportCnotAbGate = relabelGate teleportRegisterEquiv teleportCnotAbB from rfl,
    applyGate_relabelGate,
    show teleportHaGate = relabelGate teleportRegisterEquiv teleportHaB from rfl,
    applyGate_relabelGate,
    teleportHbB_ket, teleportCnotBcB_tensorState, teleportCnotAbB_apply, teleportHaB_apply,
    show teleportAliceProjectorGate (teleportOutcomeEquiv o)
        = relabelGate teleportRegisterEquiv (teleportProjectorB o) from by
      rw [teleportProjectorB]
      exact (relabelGate_relabelGate _ _).symm,
    applyGate_relabelGate, teleportProjectorB_apply,
    show teleportBobXGate (teleportOutcomeEquiv o)
        = relabelGate teleportRegisterEquiv (teleportXcB o.2) from by
      rw [teleportBobXGate, Equiv.symm_apply_apply],
    applyGate_relabelGate, teleportXcB_apply',
    show teleportBobZGate (teleportOutcomeEquiv o)
        = relabelGate teleportRegisterEquiv (teleportZcB o.1) from by
      rw [teleportBobZGate, Equiv.symm_apply_apply],
    applyGate_relabelGate, teleportZcB_apply]
  funext r
  simp only [Pi.smul_apply, smul_eq_mul, relabelState, Function.comp_apply]
  by_cases hα : (teleportRegisterEquiv.symm r).1.1 = o.1
  · by_cases hβ : (teleportRegisterEquiv.symm r).1.2 = o.2
    · rw [show teleportRegisterEquiv.symm r
          = (((teleportRegisterEquiv.symm r).1.1, (teleportRegisterEquiv.symm r).1.2),
            (teleportRegisterEquiv.symm r).2) from rfl,
        hα, hβ]
      cases o.1 <;> cases o.2 <;> cases hc : (teleportRegisterEquiv.symm r).2 <;>
        cases (boolEquivFin2.symm i) <;>
        simp [teleportBellResource_apply', Qatlib.Foundations.PureStateMath.Ket, sqrt2_inv_sq]
    · have hne : ¬ (teleportOutcomeEquiv ((teleportRegisterEquiv.symm r).1.1,
            (teleportRegisterEquiv.symm r).1.2) = teleportOutcomeEquiv (o.1, o.2)) :=
          fun hcon => hβ (congrArg Prod.snd (teleportOutcomeEquiv.injective hcon))
      rw [if_neg hne, mul_zero, Qatlib.Foundations.PureStateMath.Ket,
        if_neg (fun hp => by
          rw [Prod.mk.injEq] at hp
          exact hβ (congrArg Prod.snd hp.1)), mul_zero]
  · have hne : ¬ (teleportOutcomeEquiv ((teleportRegisterEquiv.symm r).1.1,
          (teleportRegisterEquiv.symm r).1.2) = teleportOutcomeEquiv (o.1, o.2)) :=
        fun hcon => hα (congrArg Prod.fst (teleportOutcomeEquiv.injective hcon))
    rw [if_neg hne, mul_zero, Qatlib.Foundations.PureStateMath.Ket,
      if_neg (fun hp => by
        rw [Prod.mk.injEq] at hp
        exact hα (congrArg Prod.fst hp.1)), mul_zero]

/-- The qubit matrix unit with its single nonzero entry in row `i` and column `j`. -/
noncomputable def teleportMatUnit (i j : Fin 2) : Operator 2 :=
  Matrix.of fun c c' => if c = i ∧ c' = j then (1 : ℂ) else 0

/-- Expands any qubit operator as the sum of its entries times the corresponding matrix units. -/
theorem teleportMatUnit_decomp (ρ : Operator 2) :
    ρ = ∑ p : Fin 2 × Fin 2, ρ p.1 p.2 • teleportMatUnit p.1 p.2 := by
  ext c c'
  have hentry : ∀ p : Fin 2 × Fin 2,
      (ρ p.1 p.2 • teleportMatUnit p.1 p.2) c c'
        = if c = p.1 ∧ c' = p.2 then ρ p.1 p.2 else 0 := by
    intro p
    simp only [Matrix.smul_apply, teleportMatUnit, Matrix.of_apply, smul_eq_mul]
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

/-- Embedding a matrix unit by the initial frame gives the outer matrix of the corresponding two
frame columns. -/
theorem teleportFrame_matUnit (i j : Fin 2) :
    teleportInitialFrame * teleportMatUnit i j * teleportInitialFrame.conjTranspose
      = matOuter (fun r => teleportInitialFrame r i)
          (fun r => teleportInitialFrame r j) := by
  ext r r'
  have hinner : ∀ a : Fin 2,
      (∑ b : Fin 2, teleportInitialFrame r b * (if b = i ∧ a = j then (1 : ℂ) else 0))
      = if a = j then teleportInitialFrame r i else 0 := by
    intro a
    rw [Fintype.sum_eq_single i]
    · by_cases haj : a = j
      · rw [if_pos ⟨rfl, haj⟩, mul_one, if_pos haj]
      · rw [if_neg (fun hc => haj hc.2), mul_zero, if_neg haj]
    · intro b hb
      rw [if_neg (fun hc => hb hc.1), mul_zero]
  have houter : ∀ a : Fin 2,
      ((∑ b : Fin 2, teleportInitialFrame r b * (if b = i ∧ a = j then (1 : ℂ) else 0))
          * (starRingEnd ℂ) (teleportInitialFrame r' a))
      = (if a = j then teleportInitialFrame r i else 0)
          * (starRingEnd ℂ) (teleportInitialFrame r' a) :=
    fun a => congrArg (· * (starRingEnd ℂ) (teleportInitialFrame r' a)) (hinner a)
  simp only [Matrix.mul_apply, conjTranspose_apply, teleportMatUnit, Matrix.of_apply,
    matOuter, RCLike.star_def]
  rw [Finset.sum_congr rfl fun a _ => houter a, Fintype.sum_eq_single j]
  · rw [if_pos rfl]
  · intro a ha
    rw [if_neg ha, zero_mul]

/-- Tracing out a fixed Alice basis label from a basis ket bra matrix leaves the ket bra matrix
on Bob's register. -/
theorem traceLeft_matOuter_ket (o : Bool × Bool) (x y : Bool) :
    Matrix.traceLeft (matOuter (Qatlib.Foundations.PureStateMath.Ket ((o.1, o.2), x)) (Qatlib.Foundations.PureStateMath.Ket ((o.1, o.2), y)))
      = matOuter (Qatlib.Foundations.PureStateMath.Ket x) (Qatlib.Foundations.PureStateMath.Ket y) := by
  ext c c'
  simp only [Matrix.traceLeft, Matrix.of_apply, matOuter, ket_apply, Prod.mk.injEq]
  cases o.1 <;> cases o.2 <;> cases x <;> cases y <;> cases c <;> cases c' <;> simp

/-- Relabeling Boolean basis ket bra matrices to `Fin 2` gives the corresponding qubit matrix
units. -/
theorem relabelGate_matOuter_ket (i j : Fin 2) :
    relabelGate boolEquivFin2
        (matOuter (Qatlib.Foundations.PureStateMath.Ket (boolEquivFin2.symm i)) (Qatlib.Foundations.PureStateMath.Ket (boolEquivFin2.symm j)))
      = teleportMatUnit i j := by
  ext c c'
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, matOuter,
    Matrix.of_apply, ket_apply, teleportMatUnit]
  by_cases h1 : c = i
  · by_cases h2 : c' = j
    · subst h1
      subst h2
      simp
    · subst h1
      have hne : boolEquivFin2.symm c' ≠ boolEquivFin2.symm j :=
        fun hc => h2 (boolEquivFin2.symm.injective hc)
      simp [hne, h2]
  · have hne : boolEquivFin2.symm c ≠ boolEquivFin2.symm i :=
      fun hc => h1 (boolEquivFin2.symm.injective hc)
    simp [hne, h1]

/-- Every actual Bell circuit branch sends a matrix unit to one quarter of itself. -/
theorem teleportActualBranchMap_matUnit (o : Bool × Bool) (i j : Fin 2) :
    teleportActualBranchMap o (teleportMatUnit i j) = (1/4:ℂ) • teleportMatUnit i j := by
  have hcolI : (fun r : Fin 8 => teleportInitialFrame r i)
      = relabelState teleportRegisterEquiv
          (Qatlib.Foundations.PureStateMath.Ket ((boolEquivFin2.symm i, false), false)) := by
    funext r; exact teleportInitialFrame_column i r
  have hcolJ : (fun r : Fin 8 => teleportInitialFrame r j)
      = relabelState teleportRegisterEquiv
          (Qatlib.Foundations.PureStateMath.Ket ((boolEquivFin2.symm j, false), false)) := by
    funext r; exact teleportInitialFrame_column j r
  show relabelGate boolEquivFin2 (Matrix.traceLeft
      (relabelGate teleportRegisterEquiv.symm
        ((observedLeaf (1 : Operator 8) teleportProgram (teleportProgramLeaf o)).operator
          * (teleportInitialFrame * teleportMatUnit i j * teleportInitialFrame.conjTranspose)
          * (observedLeaf (1 : Operator 8) teleportProgram (teleportProgramLeaf o)).operator.conjTranspose)))
    = (1/4:ℂ) • teleportMatUnit i j
  rw [teleportFrame_matUnit i j, hcolI, hcolJ, matOuter_sandwich,
    teleportLeafColumn o i, teleportLeafColumn o j, matOuter_smul_smul,
    relabelGate_smul', relabelGate_matOuter, traceLeft_smul',
    traceLeft_matOuter_ket, relabelGate_smul', relabelGate_matOuter_ket]
  congr 1
  have h3 : ((1/2:ℂ)) = ((1/2:ℝ):ℂ) := by push_cast; norm_num
  rw [h3, Complex.conj_ofReal]
  norm_num

/-- Every actual Bell circuit branch sends any qubit operator to one quarter of itself. -/
theorem teleportActualBranchMap_apply (o : Bool × Bool) (ρ : Operator 2) :
    teleportActualBranchMap o ρ = (1/4:ℂ) • ρ := by
  have hsmul : ∀ p : Fin 2 × Fin 2,
      teleportActualBranchMap o (ρ p.1 p.2 • teleportMatUnit p.1 p.2)
      = ((1/4:ℂ) * ρ p.1 p.2) • teleportMatUnit p.1 p.2 := by
    intro p
    have h1 : teleportActualBranchMap o (ρ p.1 p.2 • teleportMatUnit p.1 p.2)
        = ρ p.1 p.2 • teleportActualBranchMap o (teleportMatUnit p.1 p.2) := by
      show teleportActualBranchCore o ((ρ p.1 p.2 : ℂ) • teleportMatUnit p.1 p.2)
          = ρ p.1 p.2 • teleportActualBranchCore o (teleportMatUnit p.1 p.2)
      unfold teleportActualBranchCore
      simp only [Matrix.mul_smul, Matrix.smul_mul, relabelGate_smul', traceLeft_smul']
    rw [h1, teleportActualBranchMap_matUnit o p.1 p.2,
      smul_smul, mul_comm (ρ p.1 p.2) (1/4:ℂ)]
  have hsumdistr : teleportActualBranchMap o
      (∑ p : Fin 2 × Fin 2, ρ p.1 p.2 • teleportMatUnit p.1 p.2)
      = ∑ p : Fin 2 × Fin 2, ((1/4:ℂ) * ρ p.1 p.2) • teleportMatUnit p.1 p.2 := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun p _ => hsmul p)
  rw [teleportMatUnit_decomp ρ, hsumdistr, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [smul_smul]

/-- The Bell teleportation program is well formed with four leaves, bijectively indexed by
Alice's outcomes. Each leaf is accepted and records zero queries, six gates, one
measurement, and the selected outcome. -/
theorem bell_actual_program_legality_and_counts :
    observedWellFormed teleportProgram ∧ observedLeafCount teleportProgram = 4 ∧
      (∀ o, (observedLeaf 1 teleportProgram (teleportProgramLeaf o)).accepted = true ∧
        (observedLeaf 1 teleportProgram (teleportProgramLeaf o)).queries = 0 ∧
        (observedLeaf 1 teleportProgram (teleportProgramLeaf o)).gates = 6 ∧
        (observedLeaf 1 teleportProgram (teleportProgramLeaf o)).measurements = 1 ∧
        (observedLeaf 1 teleportProgram (teleportProgramLeaf o)).outcomes = [(4,(teleportOutcomeEquiv o).val)]) ∧
      Function.Bijective teleportProgramLeaf := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp only [teleportProgram, observedWellFormed]
    exact ⟨teleportHbGate_unitary, teleportCnotBcGate_unitary, teleportCnotAbGate_unitary,
      teleportHaGate_unitary, fun k => ⟨teleportBobXGate_unitary k,
        ⟨teleportBobZGate_unitary k, trivial⟩⟩⟩
  · intro o
    rcases o with ⟨a, b⟩
    cases a <;> cases b <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · constructor
    · rintro ⟨a1, a2⟩ ⟨b1, b2⟩ hab
      revert hab
      cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> decide
    · intro j
      refine ⟨teleportOutcomeEquiv.symm (j.cast (rfl : observedLeafCount teleportProgram = 4)), ?_⟩
      have hval : (teleportProgramLeaf
          (teleportOutcomeEquiv.symm (j.cast (rfl : observedLeafCount teleportProgram = 4)))).val
          = j.val := by
        simp only [teleportProgramLeaf, Fin.val_cast, Equiv.apply_symm_apply]
      exact Fin.eq_of_val_eq hval

/-- Each actual Bell circuit branch map equals the corresponding corrected instrument branch
[BennettEtAl1993Teleportation]. -/
theorem bell_actual_program_branch_bridge :
    ∀ o : Bool × Bool, teleportActualBranchMap o = teleportCorrectedInstrument.branch o := by
  intro o
  apply LinearMap.ext
  intro ρ
  rw [teleportActualBranchMap_apply o ρ, teleportCorrectedInstrument_branch_apply ρ o]

/-- With any finite reference register, each actual Bell circuit branch gives one quarter of the
joint operator and summing all branches recovers it [BennettEtAl1993Teleportation]. -/
theorem bell_actual_program_reference_recovery :
    ∀ (R : ℕ) (ρ : Matrix (Fin 2 × Fin R) (Fin 2 × Fin R) ℂ) (o : Bool × Bool),
      tensorLeft (teleportActualBranchMap o) ρ = (1/4:ℂ) • ρ ∧
      (∑ o : Bool × Bool, tensorLeft (teleportActualBranchMap o) ρ) = ρ := by
  intro R ρ o
  rw [bell_actual_program_branch_bridge o,
    Finset.sum_congr rfl (fun o' _ => by rw [bell_actual_program_branch_bridge o'])]
  exact bell_reference_channel_identity R ρ o

/-- Alice's outcome message has exactly two bits, distinguishes all outcomes, and has a four
element outcome domain [BennettEtAl1993Teleportation]. -/
theorem bell_classical_message_cost :
    (∀ o : Bool × Bool, (teleportMessage o).length = 2) ∧
      Function.Injective teleportMessage ∧ Fintype.card (Bool × Bool) = 4 := by
  refine ⟨fun o => by simp [teleportMessage], ?_, by simp⟩
  intro a b hab
  simp [teleportMessage] at hab
  rcases a with ⟨a1, a2⟩
  rcases b with ⟨b1, b2⟩
  simp_all

/-- The maximally mixed qubit state is a density operator that is not pure and is recovered by
the sum of actual Bell branches. The branches also recover every pure outer product on the
input and a qubit reference. -/
theorem bell_mixed_entangled_consumer :
    IsDensityOperator ((1/2:ℂ) • (1:Operator 2)) ∧
      ¬ IsPureDensityOperator ((1/2:ℂ) • (1:Operator 2)) ∧
      (∑ o : Bool × Bool, teleportActualBranchMap o ((1/2:ℂ) • (1:Operator 2))) = (1/2:ℂ) • (1:Operator 2) ∧
      (∀ ψ : QState (Fin 2 × Fin 2), (∑ o : Bool × Bool, tensorLeft (teleportActualBranchMap o) (outerProduct ψ)) = outerProduct ψ) := by
  have hone : (1 : Operator 2).PosSemidef := Matrix.PosSemidef.one
  refine ⟨⟨Matrix.PosSemidef.smul hone (by simp), ?_⟩, ?_, ?_, ?_⟩
  · rw [Matrix.trace_smul, Matrix.trace_one]
    norm_num
  · intro ⟨⟨_, _⟩, hmul⟩
    have h00 := congrArg (fun M : Operator 2 => M 0 0) hmul
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      Fin.sum_univ_two] at h00
    norm_num at h00
  · rw [Finset.sum_congr rfl (fun o _ => teleportActualBranchMap_apply o _),
    sum_univ_boolPair_smul, show ((4 : ℂ) * (1/4 : ℂ)) = 1 from by norm_num, one_smul]
  · intro ψ
    rw [Finset.sum_congr rfl (fun o _ => by rw [bell_actual_program_branch_bridge o])]
    exact (bell_reference_channel_identity 2 (outerProduct ψ) (false, false)).2

end Qatlib.Concepts.QuditTeleport.TeleportCore
