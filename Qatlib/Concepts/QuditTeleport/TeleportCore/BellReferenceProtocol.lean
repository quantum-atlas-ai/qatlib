/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding

/-!
# Bell teleportation resource and branch operators

This module constructs the three register qubit teleportation circuit, its Bell resource, and
Alice's decoded branch Kraus operators. Boolean register indices are related to `Fin 8` by
`teleportRegisterEquiv`, and the initial and prepared frames embed the input with zero ancillas
and with the Bell resource, respectively.

The explicit branch calculation gives `X^β Z^α / 2`; Bob's correction `Z^α X^β` cancels it to
half the identity. This realizes the qubit protocol of [BennettEtAl1993Teleportation].

## Main statements

* `bell_resource_preparation_laws`: resource normalization and preparation frame identities.
* `bell_decoded_branch_operators`: unitarity of decoding and the Pauli branch formulas.
* `bell_pauli_corrections`: unitary corrections and exact branch cancellation.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.Execution.WorkspaceCP

namespace Qatlib.Concepts.QuditTeleport.TeleportCore

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
set_option linter.unusedSectionVars false

/-- Flattens the three Boolean teleportation registers into `Fin 8`, with the input register as
the most significant bit. -/
def teleportRegisterEquiv : ((Bool × Bool) × Bool) ≃ Fin 8 :=
  (Equiv.prodCongr (Equiv.prodCongr boolEquivFin2 boolEquivFin2) boolEquivFin2).trans
    ((Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin 2))).trans finProdFinEquiv)

/-- Encodes Alice's pair of Boolean outcomes as an element of `Fin 4`. -/
def teleportOutcomeEquiv : Bool × Bool ≃ Fin 4 :=
  (Equiv.prodCongr boolEquivFin2 boolEquivFin2).trans finProdFinEquiv

/-- The flattened three register index has binary value `c + 2 * (b + 2 * a)` under
`boolEquivFin2`. -/
@[simp] theorem teleportRegisterEquiv_val (a b c : Bool) :
    (teleportRegisterEquiv ((a, b), c)).val
      = (boolEquivFin2 c).val + 2 * ((boolEquivFin2 b).val + 2 * (boolEquivFin2 a).val) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- The encoded outcome pair has binary value `b + 2 * a` under `boolEquivFin2`. -/
@[simp] theorem teleportOutcomeEquiv_val (a b : Bool) :
    (teleportOutcomeEquiv (a, b)).val = (boolEquivFin2 b).val + 2 * (boolEquivFin2 a).val := by
  cases a <;> cases b <;> rfl

/-- Relabeling matrix indices along an equivalence preserves multiplication. -/
theorem teleportRelabelGate_mul {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (A B : Matrix I I ℂ) :
    relabelGate e (A * B) = relabelGate e A * relabelGate e B := by
  ext x y
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  exact (Equiv.sum_comp e.symm
    (fun k => A (e.symm x) k * B k (e.symm y))).symm

/-- Relabeling matrix indices along an equivalence preserves the identity matrix. -/
theorem teleportRelabelGate_one {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) : relabelGate e (1 : Matrix I I ℂ) = 1 := by
  ext x y
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
  by_cases h : e.symm x = e.symm y
  · rw [if_pos h, if_pos (e.symm.injective h)]
  · rw [if_neg h, if_neg (fun hxy => h (by rw [hxy]))]

/-- Relabeling a matrix commutes with taking its conjugate transpose. -/
theorem teleportRelabelGate_conjTranspose {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (U : Matrix I I ℂ) :
    (relabelGate e U)ᴴ = relabelGate e Uᴴ := rfl

/-- Relabeling matrix indices along an equivalence preserves unitarity. -/
theorem teleportRelabelGate_mem_unitaryGroup {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) (e : I ≃ J) :
    relabelGate e U ∈ Matrix.unitaryGroup J ℂ := by
  have hU' : Uᴴ * U = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, teleportRelabelGate_conjTranspose,
    ← teleportRelabelGate_mul, hU', teleportRelabelGate_one]

/-- A column entry of a matrix product is obtained by applying the left matrix to the
corresponding column of the right matrix. -/
theorem matrix_mul_column {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℂ) (B : Matrix I J ℂ) (r : I) (j : J) :
    (A * B) r j = ApplyGate A (fun r' => B r' j) r := rfl

/-- The Bell resource vector prepared by applying CNOT to `Plus` tensored with the zero basis
state. -/
noncomputable def teleportBellResource : QState (Bool × Bool) :=
  ApplyGate CNOT (TensorState Plus (Ket false))

/-- The Bell resource has amplitude `1 / √2` on equal Boolean indices and zero on unequal
indices, using the real normalization factor. -/
theorem teleportBellResource_apply (b c : Bool) :
    teleportBellResource (b, c) = if b = c then ((Real.sqrt 2)⁻¹ : ℝ) else 0 := by
  have hp : Plus b = ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) := by
    show Hadamard b false = _
    rw [hadamard_apply_false]
  have h1 : teleportBellResource (b, c) = Plus b * Ket false (c ^^ b) :=
    applyGate_permMatrix cnotFlip_involutive _ (b, c)
  rw [h1, hp]
  cases b <;> cases c <;> simp [Ket]

/-- The Bell resource has amplitude `1 / √2` on equal Boolean indices and zero on unequal
indices, using the complex normalization factor. -/
theorem teleportBellResource_apply' (b c : Bool) :
    teleportBellResource (b, c) = if b = c then ((Real.sqrt 2 : ℂ)⁻¹) else 0 := by
  rw [teleportBellResource_apply]
  cases b <;> cases c <;> simp

/-- The prepared Bell resource vector is normalized. -/
theorem teleportBellResource_normalized : Normalized teleportBellResource :=
  normalized_applyGate cnot_unitary (normalized_tensorState normalized_plus (normalized_ket false))

/-- The product of two complex inverse square root two factors equals one half. -/
theorem sqrt2_inv_sq : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
  rw [inv_sqrt2_mul_self]; norm_num

/-- The Hadamard gate on register `b`, acting as the identity on registers `a` and `c`. -/
noncomputable def teleportHbB : Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ :=
  TensorGate (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard) (1 : Matrix Bool Bool ℂ)

/-- The CNOT gate from register `b` to register `c`, acting as the identity on register `a`. -/
noncomputable def teleportCnotBcB : Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ :=
  relabelGate (Equiv.prodAssoc Bool Bool Bool).symm (TensorGate (1 : Matrix Bool Bool ℂ) CNOT)

/-- The CNOT gate from register `a` to register `b`, acting as the identity on register `c`. -/
noncomputable def teleportCnotAbB : Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ :=
  TensorGate CNOT (1 : Matrix Bool Bool ℂ)

/-- The Hadamard gate on register `a`, acting as the identity on registers `b` and `c`. -/
noncomputable def teleportHaB : Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ :=
  TensorGate (TensorGate Hadamard (1 : Matrix Bool Bool ℂ)) (1 : Matrix Bool Bool ℂ)

/-- The conditional Pauli X gate on register `c`, enabled by the Boolean value `β`. -/
noncomputable def teleportXcB (β : Bool) :
    Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ :=
  TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) (if β then PauliX else 1)

/-- The conditional Pauli Z gate on register `c`, enabled by the Boolean value `α`. -/
noncomputable def teleportZcB (α : Bool) :
    Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ :=
  TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) (if α then PauliZ else 1)

/-- The Hadamard gate on register `b`, relabeled onto the flattened eight dimensional register
space. -/
noncomputable def teleportHbGate : Operator 8 := relabelGate teleportRegisterEquiv teleportHbB

/-- The CNOT gate from `b` to `c`, relabeled onto the flattened eight dimensional register
space. -/
noncomputable def teleportCnotBcGate : Operator 8 :=
  relabelGate teleportRegisterEquiv teleportCnotBcB

/-- The CNOT gate from `a` to `b`, relabeled onto the flattened eight dimensional register
space. -/
noncomputable def teleportCnotAbGate : Operator 8 :=
  relabelGate teleportRegisterEquiv teleportCnotAbB

/-- The Hadamard gate on register `a`, relabeled onto the flattened eight dimensional register
space. -/
noncomputable def teleportHaGate : Operator 8 := relabelGate teleportRegisterEquiv teleportHaB

/-- The Bell resource preparation operator, applying Hadamard on `b` followed by CNOT from `b`
to `c`. -/
noncomputable def teleportPreparationGate : Operator 8 :=
  teleportCnotBcGate * teleportHbGate

/-- Alice's Bell decoding operator, applying CNOT from `a` to `b` followed by Hadamard on `a`. -/
noncomputable def teleportDecodeGate : Operator 8 :=
  teleportHaGate * teleportCnotAbGate

/-- Embeds a qubit input into register `a` with registers `b` and `c` initialized to zero. -/
def teleportInitialFrame : Matrix (Fin 8) (Fin 2) ℂ :=
  Matrix.of fun r i =>
    if r = teleportRegisterEquiv ((boolEquivFin2.symm i, false), false) then 1 else 0

/-- Embeds a qubit input alongside the Bell resource on registers `b` and `c`. -/
noncomputable def teleportPreparedFrame : Matrix (Fin 8) (Fin 2) ℂ :=
  Matrix.of fun r i =>
    if (teleportRegisterEquiv.symm r).1.1 = boolEquivFin2.symm i
      then teleportBellResource ((teleportRegisterEquiv.symm r).1.2,
        (teleportRegisterEquiv.symm r).2)
      else 0

/-- Bob's branch Kraus operator obtained by decoding the prepared frame and selecting Alice's
outcome pair. -/
noncomputable def teleportBranchKraus (o : Bool × Bool) : Operator 2 :=
  Matrix.of fun c i =>
    (teleportDecodeGate * teleportPreparedFrame)
      (teleportRegisterEquiv ((o.1, o.2), boolEquivFin2.symm c)) i

/-- Bob's outcome dependent correction `Z^α X^β`, relabeled from Boolean indices to `Fin 2`. -/
noncomputable def teleportCorrection (o : Bool × Bool) : Operator 2 :=
  relabelGate boolEquivFin2 ((if o.1 then PauliZ else 1) * (if o.2 then PauliX else 1))

/-- Applying `U` on the first tensor factor acts on each slice with the second coordinate fixed. -/
theorem applyGate_firstFactor {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (U : Matrix I I ℂ) (ψ : QState (I × J)) :
    ApplyGate (TensorGate U (1 : Matrix J J ℂ)) ψ
      = fun p => ApplyGate U (fun i => ψ (i, p.2)) p.1 := by
  funext p
  obtain ⟨i0, j0⟩ := p
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    tensorGate_apply, Matrix.one_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : ∀ l : J, (U i0 k * (if j0 = l then (1 : ℂ) else 0)) * ψ (k, l)
      = U i0 k * ((if j0 = l then (1 : ℂ) else 0) * ψ (k, l)) := fun l => mul_assoc _ _ _
  rw [Finset.sum_congr rfl (fun l _ => h1 l), ← Finset.mul_sum]
  simp only [ite_mul, zero_mul, one_mul]
  rw [Finset.sum_ite_eq Finset.univ j0 (fun l => ψ (k, l)), if_pos (Finset.mem_univ j0)]

/-- Applying `V` on the second tensor factor acts on each slice with the first coordinate fixed. -/
theorem applyGate_secondFactor {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (V : Matrix J J ℂ) (ψ : QState (I × J)) :
    ApplyGate (TensorGate (1 : Matrix I I ℂ) V) ψ
      = fun p => ApplyGate V (fun j => ψ (p.1, j)) p.2 := by
  funext p
  obtain ⟨i0, j0⟩ := p
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    tensorGate_apply, Matrix.one_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h1 : ∀ k : I, ((if i0 = k then (1 : ℂ) else 0) * V j0 l) * ψ (k, l)
      = V j0 l * ((if i0 = k then (1 : ℂ) else 0) * ψ (k, l)) := fun k => by ring
  rw [Finset.sum_congr rfl (fun k _ => h1 k), ← Finset.mul_sum]
  simp only [ite_mul, zero_mul, one_mul]
  rw [Finset.sum_ite_eq Finset.univ i0 (fun k => ψ (k, l)), if_pos (Finset.mem_univ i0)]

/-- Computes the action of the Hadamard gate on register `b` as the signed sum of its two input
amplitudes divided by `√2`. -/
theorem teleportHbB_apply (ψ : QState ((Bool × Bool) × Bool)) :
    ApplyGate teleportHbB ψ = fun p => ((Real.sqrt 2 : ℂ)⁻¹) *
      (ψ ((p.1.1, false), p.2) + (if p.1.2 then (-1 : ℂ) else 1) * ψ ((p.1.1, true), p.2)) := by
  rw [show teleportHbB = TensorGate (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard)
      (1 : Matrix Bool Bool ℂ) from rfl,
    applyGate_firstFactor]
  funext p
  obtain ⟨⟨a0, b0⟩, c0⟩ := p
  rw [applyGate_secondFactor]
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Hadamard, Matrix.of_apply,
    Fintype.sum_bool]
  cases a0 <;> cases b0 <;> simp <;> ring

/-- Computes the action of the Hadamard gate on register `a` as the signed sum of its two input
amplitudes divided by `√2`. -/
theorem teleportHaB_apply (ψ : QState ((Bool × Bool) × Bool)) :
    ApplyGate teleportHaB ψ = fun p => ((Real.sqrt 2 : ℂ)⁻¹) *
      (ψ ((false, p.1.2), p.2) + (if p.1.1 then (-1 : ℂ) else 1) * ψ ((true, p.1.2), p.2)) := by
  rw [show teleportHaB = TensorGate (TensorGate Hadamard (1 : Matrix Bool Bool ℂ))
      (1 : Matrix Bool Bool ℂ) from rfl,
    applyGate_firstFactor]
  funext p
  obtain ⟨⟨a0, b0⟩, c0⟩ := p
  rw [applyGate_firstFactor]
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Hadamard, Matrix.of_apply,
    Fintype.sum_bool]
  cases a0 <;> cases b0 <;> simp <;> ring

/-- The CNOT gate from `a` to `b` acts on amplitudes by replacing `b` with `b ^^ a`. -/
theorem teleportCnotAbB_apply (ψ : QState ((Bool × Bool) × Bool)) :
    ApplyGate teleportCnotAbB ψ = fun p => ψ ((p.1.1, p.1.2 ^^ p.1.1), p.2) := by
  rw [show teleportCnotAbB = TensorGate CNOT (1 : Matrix Bool Bool ℂ) from rfl,
    applyGate_firstFactor]
  funext p
  exact applyGate_permMatrix cnotFlip_involutive _ p.1

/-- The conditional Pauli X gate flips Bob's amplitude index precisely when `β` is true. -/
theorem teleportXcB_apply (β : Bool) (ψ : QState ((Bool × Bool) × Bool)) :
    ApplyGate (teleportXcB β) ψ = fun p => if β then ψ (p.1, !p.2) else ψ p := by
  rw [show teleportXcB β = TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
      (if β then PauliX else 1) from rfl,
    applyGate_secondFactor]
  funext p
  cases β
  · simp only [if_neg (by decide : ¬(false = true))]
    exact congrFun (applyGate_one _) p.2
  · exact applyGate_permMatrix Bool.not_not (fun j => ψ (p.1, j)) p.2

/-- The conditional Pauli Z gate multiplies an amplitude by minus one precisely when both `α`
and Bob's bit are true. -/
theorem teleportZcB_apply (α : Bool) (ψ : QState ((Bool × Bool) × Bool)) :
    ApplyGate (teleportZcB α) ψ
      = fun p => (if α && p.2 then (-1 : ℂ) else 1) * ψ ((p.1.1, p.1.2), p.2) := by
  rw [show teleportZcB α = TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
      (if α then PauliZ else 1) from rfl,
    applyGate_secondFactor]
  funext p
  cases α
  · simp only [Bool.false_and, if_neg (by decide : ¬(false = true))]
    rw [congrFun (applyGate_one _) p.2, one_mul]
  · simp only [Bool.true_and, if_true]
    have hz : ApplyGate PauliZ (fun j => ψ ((p.1.1, p.1.2), j)) p.2
        = (if p.2 then (-1 : ℂ) else 1) * ψ ((p.1.1, p.1.2), p.2) := by
      simp only [ApplyGate, Matrix.mulVec, dotProduct, PauliZ, Matrix.diagonal_apply]
      cases p.2 <;> simp
    rw [hz]

/-- The Boolean index transformation for CNOT from `b` to `c` is an involution. -/
theorem teleportCnotBcFlip_involutive :
    Function.Involutive (fun p : ((Bool × Bool) × Bool) => ((p.1.1, p.1.2), p.2 ^^ p.1.2)) := by
  intro ⟨⟨a1, a2⟩, a3⟩
  show ((a1, a2), (a3 ^^ a2) ^^ a2) = ((a1, a2), a3)
  rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The CNOT gate from `b` to `c` is the permutation matrix for the corresponding Boolean index
transformation. -/
theorem teleportCnotBcB_eq_permMatrix :
    teleportCnotBcB
      = permMatrix (fun p : ((Bool × Bool) × Bool) => ((p.1.1, p.1.2), p.2 ^^ p.1.2)) := by
  ext ⟨⟨a1, a2⟩, a3⟩ ⟨⟨b1, b2⟩, b3⟩
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases a3 <;> cases b3 <;>
    simp [teleportCnotBcB, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
      tensorGate_apply, CNOT, cnotFlip, permMatrix, Matrix.of_apply]

/-- The CNOT gate from `b` to `c` acts on amplitudes by replacing `c` with `c ^^ b`. -/
theorem teleportCnotBcB_apply (ψ : QState ((Bool × Bool) × Bool)) :
    ApplyGate teleportCnotBcB ψ = fun p => ψ ((p.1.1, p.1.2), p.2 ^^ p.1.2) := by
  rw [teleportCnotBcB_eq_permMatrix]
  exact funext fun i => applyGate_permMatrix teleportCnotBcFlip_involutive ψ i

/-- Applying Hadamard on `b` to the initialized basis input produces the input ket tensored with
`Plus` and the zero ket. -/
theorem teleportHbB_ket (x : Bool) :
    ApplyGate teleportHbB (Ket ((x, false), false))
      = TensorState (TensorState (Ket x) Plus) (Ket false) := by
  have hK : (Ket ((x, false), false) : QState ((Bool × Bool) × Bool))
      = TensorState (TensorState (Ket x) (Ket false)) (Ket false) := by
    rw [← tensorState_ket_ket, ← tensorState_ket_ket]
  rw [hK,
    show teleportHbB = TensorGate (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard)
      (1 : Matrix Bool Bool ℂ) from rfl,
    applyGate_tensorGate, applyGate_tensorGate, applyGate_one, applyGate_one,
    applyGate_hadamard_ket_false]

/-- Applying CNOT from `b` to `c` to the prepared plus state creates the Bell resource while
retaining the input basis vector. -/
theorem teleportCnotBcB_tensorState (x : Bool) :
    ApplyGate teleportCnotBcB (TensorState (TensorState (Ket x) Plus) (Ket false))
      = fun p => Ket x p.1.1 * teleportBellResource (p.1.2, p.2) := by
  have hA : TensorState (TensorState (Ket x) Plus) (Ket false)
      = relabelState (Equiv.prodAssoc Bool Bool Bool).symm
          (TensorState (Ket x) (TensorState Plus (Ket false))) := by
    funext ⟨⟨a, b⟩, c⟩
    show (Ket x a * Plus b) * Ket false c = Ket x a * (Plus b * Ket false c)
    exact mul_assoc _ _ _
  rw [hA,
    show teleportCnotBcB = relabelGate (Equiv.prodAssoc Bool Bool Bool).symm
      (TensorGate (1 : Matrix Bool Bool ℂ) CNOT) from rfl,
    applyGate_relabelGate, applyGate_tensorGate, applyGate_one]
  funext ⟨⟨a, b⟩, c⟩
  rfl

/-- The resource preparation circuit sends an initialized input basis vector to that vector
tensored with the Bell resource. -/
theorem teleportPreparedColumn (x : Bool) :
    ApplyGate (teleportCnotBcB * teleportHbB) (Ket ((x, false), false))
      = fun p => Ket x p.1.1 * teleportBellResource (p.1.2, p.2) := by
  rw [applyGate_mul, teleportHbB_ket, teleportCnotBcB_tensorState]

/-- Computes each amplitude after resource preparation and Bell decoding: it has magnitude one
half, with the outcome dependent Pauli sign and bit shift. -/
theorem teleportDecodedColumn (x : Bool) :
    ApplyGate (teleportHaB * teleportCnotAbB * (teleportCnotBcB * teleportHbB))
        (Ket ((x, false), false))
      = fun p => (1 / 2 : ℂ) * ((if p.1.1 && x then (-1 : ℂ) else 1)
          * (if p.2 = (x ^^ p.1.2) then 1 else 0)) := by
  rw [applyGate_mul, applyGate_mul, teleportPreparedColumn, teleportCnotAbB_apply,
    teleportHaB_apply]
  funext ⟨⟨α, β⟩, c⟩
  simp only
  cases x <;> cases α <;> cases β <;> cases c <;>
    simp [Ket, teleportBellResource_apply', sqrt2_inv_sq]

/-- Each column of the initial frame is the relabeled basis vector with that input and two zero
ancillary bits. -/
theorem teleportInitialFrame_column (i : Fin 2) (r : Fin 8) :
    teleportInitialFrame r i
      = relabelState teleportRegisterEquiv (Ket ((boolEquivFin2.symm i, false), false)) r := by
  by_cases h : r = teleportRegisterEquiv ((boolEquivFin2.symm i, false), false)
  · subst h
    simp [teleportInitialFrame, relabelState, Ket, Equiv.symm_apply_apply]
  · have h2 : teleportRegisterEquiv.symm r ≠ ((boolEquivFin2.symm i, false), false) := by
      intro hc
      apply h
      have h3 := congrArg teleportRegisterEquiv hc
      rwa [Equiv.apply_symm_apply] at h3
    simp [teleportInitialFrame, relabelState, Ket, h, h2]

/-- The initial qubit embedding frame is an isometry. -/
theorem teleportInitialFrame_isometry : IsIsometry teleportInitialFrame := by
  have hInj : ∀ i j : Fin 2,
      teleportRegisterEquiv ((boolEquivFin2.symm i, false), false)
        = teleportRegisterEquiv ((boolEquivFin2.symm j, false), false) → i = j := by
    intro i j hab
    have h2 := congrArg teleportRegisterEquiv.symm hab
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h2
    exact boolEquivFin2.symm.injective (congrArg Prod.fst (congrArg Prod.fst h2))
  have h : teleportInitialFrameᴴ * teleportInitialFrame = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have hval : ∀ r : Fin 8, teleportInitialFrameᴴ i r * teleportInitialFrame r i
          = if r = teleportRegisterEquiv ((boolEquivFin2.symm i, false), false)
              then (1 : ℂ) else 0 := by
        intro r
        rw [conjTranspose_apply]
        unfold teleportInitialFrame
        simp only [Matrix.of_apply]
        by_cases hr : r = teleportRegisterEquiv ((boolEquivFin2.symm i, false), false)
        · rw [if_pos hr]; simp
        · rw [if_neg hr]; simp
      rw [Matrix.mul_apply,
        Finset.sum_congr rfl (fun r _ => hval r),
        Finset.sum_ite_eq' Finset.univ
          (teleportRegisterEquiv ((boolEquivFin2.symm i, false), false))
          (fun _ => (1 : ℂ)),
        if_pos (Finset.mem_univ _)]
      simp
    · have hzero : ∀ r : Fin 8, teleportInitialFrameᴴ i r * teleportInitialFrame r j = 0 := by
        intro r
        rw [conjTranspose_apply]
        unfold teleportInitialFrame
        simp only [Matrix.of_apply]
        by_cases hr : r = teleportRegisterEquiv ((boolEquivFin2.symm i, false), false)
        · rw [if_pos hr, if_neg (fun hc => hij (hInj i j (hr.symm.trans hc))), mul_zero]
        · rw [if_neg hr, star_zero, zero_mul]
      rw [Matrix.mul_apply, Finset.sum_congr rfl (fun r _ => hzero r),
        Finset.sum_const_zero]
      simp [hij]
  exact h

/-- The Bell resource preparation operator is unitary. -/
theorem teleportPreparationGate_unitary :
    teleportPreparationGate ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  have hHb : teleportHbB ∈ Matrix.unitaryGroup ((Bool × Bool) × Bool) ℂ :=
    tensorGate_unitary
      (tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary) (Submonoid.one_mem _)
  have hCb : teleportCnotBcB ∈ Matrix.unitaryGroup ((Bool × Bool) × Bool) ℂ :=
    teleportRelabelGate_mem_unitaryGroup
      (tensorGate_unitary (Submonoid.one_mem _) cnot_unitary) _
  unfold teleportPreparationGate teleportCnotBcGate teleportHbGate
  rw [← teleportRelabelGate_mul]
  exact teleportRelabelGate_mem_unitaryGroup (Submonoid.mul_mem _ hCb hHb) _

/-- The Bell decoding operator is unitary. -/
theorem teleportDecodeGate_unitary : teleportDecodeGate ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  have hCa : teleportCnotAbB ∈ Matrix.unitaryGroup ((Bool × Bool) × Bool) ℂ :=
    tensorGate_unitary cnot_unitary (Submonoid.one_mem _)
  have hHa : teleportHaB ∈ Matrix.unitaryGroup ((Bool × Bool) × Bool) ℂ :=
    tensorGate_unitary
      (tensorGate_unitary hadamard_unitary (Submonoid.one_mem _)) (Submonoid.one_mem _)
  unfold teleportDecodeGate teleportHaGate teleportCnotAbGate
  rw [← teleportRelabelGate_mul]
  exact teleportRelabelGate_mem_unitaryGroup (Submonoid.mul_mem _ hHa hCa) _

/-- The prepared frame is the product of the preparation gate and the initial embedding frame. -/
theorem teleportPreparedFrame_eq_mul :
    teleportPreparedFrame = teleportPreparationGate * teleportInitialFrame := by
  ext r i
  rw [matrix_mul_column]
  have hcol : (fun r' : Fin 8 => teleportInitialFrame r' i)
      = relabelState teleportRegisterEquiv (Ket ((boolEquivFin2.symm i, false), false)) := by
    funext r'; exact teleportInitialFrame_column i r'
  have hgate : teleportPreparationGate
      = relabelGate teleportRegisterEquiv (teleportCnotBcB * teleportHbB) := by
    unfold teleportPreparationGate teleportCnotBcGate teleportHbGate
    rw [← teleportRelabelGate_mul]
  rw [hgate, hcol, applyGate_relabelGate, applyGate_mul, teleportHbB_ket,
    teleportCnotBcB_tensorState]
  show (if (teleportRegisterEquiv.symm r).1.1 = boolEquivFin2.symm i
        then teleportBellResource ((teleportRegisterEquiv.symm r).1.2,
          (teleportRegisterEquiv.symm r).2)
        else 0)
      = Ket (boolEquivFin2.symm i) (teleportRegisterEquiv.symm r).1.1
        * teleportBellResource ((teleportRegisterEquiv.symm r).1.2,
          (teleportRegisterEquiv.symm r).2)
  rw [ket_apply]
  by_cases h : (teleportRegisterEquiv.symm r).1.1 = boolEquivFin2.symm i
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul]

/-- The embedding of an input alongside the Bell resource is an isometry. -/
theorem teleportPreparedFrame_isometry : IsIsometry teleportPreparedFrame := by
  have hU : teleportPreparationGateᴴ * teleportPreparationGate = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp teleportPreparationGate_unitary
    rwa [Matrix.star_eq_conjTranspose] at h
  show teleportPreparedFrameᴴ * teleportPreparedFrame = 1
  rw [teleportPreparedFrame_eq_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc teleportPreparationGateᴴ teleportPreparationGate
      teleportInitialFrame, hU, Matrix.one_mul]
  exact teleportInitialFrame_isometry

/-- Computes the entries of `X^β Z^α` as a phase sign times the indicator of the corresponding
bit shift. -/
theorem pauli_prod_entry (α β b b' : Bool) :
    ((if β then PauliX else 1) * (if α then PauliZ else 1)) b b'
      = (if α && b' then (-1 : ℂ) else 1) * (if b = (b' ^^ β) then 1 else 0) := by
  cases α <;> cases β <;>
    simp [Matrix.mul_apply, Matrix.one_apply, PauliX, PauliZ, permMatrix,
      Matrix.diagonal_apply] <;>
    cases b <;> cases b' <;> simp

/-- Computes the entries of the decoded prepared frame in flattened register coordinates. -/
theorem teleportDecode_mul_prepared_apply (r : Fin 8) (i : Fin 2) :
    (teleportDecodeGate * teleportPreparedFrame) r i
      = (1 / 2 : ℂ) * ((if (teleportRegisterEquiv.symm r).1.1 && boolEquivFin2.symm i
            then (-1 : ℂ) else 1)
          * (if (teleportRegisterEquiv.symm r).2
              = (boolEquivFin2.symm i ^^ (teleportRegisterEquiv.symm r).1.2) then 1 else 0)) := by
  rw [matrix_mul_column,
    show (fun r' : Fin 8 => teleportPreparedFrame r' i)
      = ApplyGate teleportPreparationGate
          (fun r'' : Fin 8 => teleportInitialFrame r'' i) from by
      funext r'
      rw [teleportPreparedFrame_eq_mul, matrix_mul_column],
    ← applyGate_mul,
    show (fun r'' : Fin 8 => teleportInitialFrame r'' i)
      = relabelState teleportRegisterEquiv (Ket ((boolEquivFin2.symm i, false), false)) from by
      funext r'; exact teleportInitialFrame_column i r',
    show teleportDecodeGate * teleportPreparationGate
      = relabelGate teleportRegisterEquiv
          (teleportHaB * teleportCnotAbB * (teleportCnotBcB * teleportHbB)) from by
      unfold teleportDecodeGate teleportPreparationGate teleportHaGate teleportCnotAbGate
        teleportCnotBcGate teleportHbGate
      rw [← teleportRelabelGate_mul, ← teleportRelabelGate_mul, ← teleportRelabelGate_mul],
    applyGate_relabelGate, teleportDecodedColumn]
  rfl

/-- Collects normalization and amplitude formulas for the Bell resource, unitarity of
preparation, and the isometry and factorization properties of the embedding frames
[BennettEtAl1993Teleportation]. -/
theorem bell_resource_preparation_laws :
    Normalized teleportBellResource ∧
      (∀ b c, teleportBellResource (b,c) = if b=c then ((Real.sqrt 2)⁻¹:ℝ) else 0) ∧
      teleportPreparationGate ∈ Matrix.unitaryGroup (Fin 8) ℂ ∧
      IsIsometry teleportInitialFrame ∧ IsIsometry teleportPreparedFrame ∧
      teleportPreparedFrame = teleportPreparationGate * teleportInitialFrame :=
  ⟨teleportBellResource_normalized, fun b c => teleportBellResource_apply b c,
    teleportPreparationGate_unitary, teleportInitialFrame_isometry,
    teleportPreparedFrame_isometry, teleportPreparedFrame_eq_mul⟩

/-- Bell decoding is unitary, and each decoded branch operator is one half of the relabeled
Pauli product `X^β Z^α` [BennettEtAl1993Teleportation]. -/
theorem bell_decoded_branch_operators :
    teleportDecodeGate ∈ Matrix.unitaryGroup (Fin 8) ℂ ∧
      (∀ o : Bool × Bool, teleportBranchKraus o = (1/2:ℂ) •
        relabelGate boolEquivFin2 ((if o.2 then PauliX else 1) * (if o.1 then PauliZ else 1))) :=
  ⟨teleportDecodeGate_unitary, fun o => by
    funext c i
    simp only [teleportBranchKraus, Matrix.of_apply, Matrix.smul_apply, relabelGate,
      Matrix.reindex_apply, Matrix.submatrix_apply, smul_eq_mul]
    rw [teleportDecode_mul_prepared_apply
      (teleportRegisterEquiv ((o.1, o.2), boolEquivFin2.symm c)) i,
      Equiv.symm_apply_apply]
    exact congrArg ((1 / 2 : ℂ) * ·) (pauli_prod_entry o.1 o.2
      (boolEquivFin2.symm c) (boolEquivFin2.symm i)).symm⟩

/-- Each Pauli correction is unitary and cancels its decoded branch operator to one half of the
identity [BennettEtAl1993Teleportation]. -/
theorem bell_pauli_corrections :
    ∀ o : Bool × Bool, teleportCorrection o ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      teleportCorrection o * teleportBranchKraus o = (1/2:ℂ) • (1:Operator 2) := by
  intro ⟨a, b⟩
  have hK : teleportBranchKraus (a, b) = (1/2:ℂ) •
      relabelGate boolEquivFin2 ((if b then PauliX else 1) * (if a then PauliZ else 1)) :=
    bell_decoded_branch_operators.2 (a, b)
  have hZX : (if a then PauliZ else 1) * (if b then PauliX else 1)
      ∈ Matrix.unitaryGroup Bool ℂ := by
    cases a <;> cases b
    · simp only [if_neg (by decide : ¬(false = true)), one_mul]
      exact Submonoid.one_mem _
    · simp only [if_neg (by decide : ¬(false = true)), one_mul]
      exact pauliX_unitary
    · simp only [if_neg (by decide : ¬(false = true)), mul_one]
      exact pauliZ_unitary
    · exact Submonoid.mul_mem _ pauliZ_unitary pauliX_unitary
  refine ⟨teleportRelabelGate_mem_unitaryGroup hZX boolEquivFin2, ?_⟩
  rw [hK, teleportCorrection, mul_smul_comm, ← teleportRelabelGate_mul]
  have hXX : (if b then PauliX else 1) * (if b then PauliX else 1) = 1 := by
    cases b
    · simp only [if_neg (by decide : ¬(false = true)), one_mul]
    · exact permMatrix_mul_self Bool.not_not
  have hZZ : (if a then PauliZ else 1) * (if a then PauliZ else 1) = 1 := by
    cases a
    · simp only [if_neg (by decide : ¬(false = true)), one_mul]
    · exact pauliZ_mul_self
  have hprod : (if a then PauliZ else 1) * (if b then PauliX else 1)
        * ((if b then PauliX else 1) * (if a then PauliZ else 1)) = 1 := by
    rw [Matrix.mul_assoc (if a then PauliZ else 1) (if b then PauliX else 1)
        ((if b then PauliX else 1) * (if a then PauliZ else 1)),
      ← Matrix.mul_assoc (if b then PauliX else 1) (if b then PauliX else 1)
        (if a then PauliZ else 1), hXX, Matrix.one_mul, hZZ]
  rw [hprod, teleportRelabelGate_one]

end Qatlib.Concepts.QuditTeleport.TeleportCore
