/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound.TeleporterMessageBound
import Qatlib.Concepts.FiniteLocc.LOCCProgram.Entanglement
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound
open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FiniteLocc.LOCCProgram

noncomputable def teleporterRegisterEquiv (n a d : ℕ) :
    (Fin n × (Fin a × Fin d)) ≃ (Fin d × Fin (n * a)) :=
  (Equiv.prodAssoc (Fin n) (Fin a) (Fin d)).symm.trans
    ((Equiv.prodComm (Fin n × Fin a) (Fin d)).trans
      (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv))

noncomputable def teleporterAppendedJoint {n a d : ℕ}
    (ω : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) :
    Operator n →ₗ[ℂ] Matrix (Fin n × (Fin a × Fin d)) (Fin n × (Fin a × Fin d)) ℂ where
  toFun ρ := TensorGate ρ ω
  map_add' := by intros; simp [TensorGate, Matrix.add_kronecker]
  map_smul' := by intros; simp [TensorGate, Matrix.smul_kronecker]

noncomputable def teleporterPreparedJoint {n a d : ℕ}
    (ω : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) :
    Operator n →ₗ[ℂ] Matrix (Fin d × Fin (n * a)) (Fin d × Fin (n * a)) ℂ :=
  (MatrixMap.submatrix ℂ (teleporterRegisterEquiv n a d).symm).comp
    (teleporterAppendedJoint ω)

theorem teleporterPreparedJoint_entry {n a d : ℕ}
    (ω : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) (ρ : Operator n)
    (x y : Fin d × Fin (n * a)) :
    teleporterPreparedJoint ω ρ x y =
      ρ ((finProdFinEquiv (m := n) (n := a)).symm x.2).1
        ((finProdFinEquiv (m := n) (n := a)).symm y.2).1 *
      ω (((finProdFinEquiv (m := n) (n := a)).symm x.2).2,x.1)
        (((finProdFinEquiv (m := n) (n := a)).symm y.2).2,y.1) := by
  rfl

noncomputable def teleporterRawBranch {n a d : ℕ}
    (ω : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ)
    (K : Operator (n * a)) : Operator n →ₗ[ℂ] Operator d :=
  (CPTPMap.traceRight (d₁ := Fin d) (d₂ := Fin (n * a))).toLinearMap.comp
    ((MatrixMap.conj (TensorGate (1 : Operator d) K)).comp
      (teleporterPreparedJoint ω))

theorem teleporterRawBranch_apply {n a d : ℕ}
    (ω : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ)
    (K : Operator (n * a)) (ρ : Operator n) :
    teleporterRawBranch ω K ρ =
      PartialTrace (TensorGate (1 : Operator d) K * teleporterPreparedJoint ω ρ *
        (TensorGate (1 : Operator d) K)ᴴ) := by
  rfl

theorem teleporterRawBranch_cp {n a d : ℕ}
    (ω : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) (hω : ω.PosSemidef)
    (K : Operator (n * a)) : CompletelyPositive (teleporterRawBranch ω K) := by
  apply (Qatlib.Concepts.ChannelTheory.Stinespring.completelyPositive_iff_physlib _).mpr
  have hprep : MatrixMap.IsCompletelyPositive (teleporterPreparedJoint (n := n) ω) := by
    unfold teleporterPreparedJoint
    exact (MatrixMap.kron_kronecker_const (A := Fin n) hω).comp
      (MatrixMap.IsCompletelyPositive.submatrix (teleporterRegisterEquiv n a d).symm)
  exact (hprep.comp (MatrixMap.congruence_CP (TensorGate (1 : Operator d) K))).comp
    (CPTPMap.traceRight (d₁ := Fin d) (d₂ := Fin (n * a))).cp

theorem teleporterRawBranch_sum {n a d k : ℕ}
    (ω : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ)
    (K : Fin k → Operator (n * a)) (hK : ∑ m, (K m)ᴴ * K m = 1)
    (ρ : Operator n) :
    (∑ m, teleporterRawBranch ω (K m) ρ) = Matrix.trace ρ • Matrix.traceLeft ω := by
  simp_rw [teleporterRawBranch_apply]
  rw [← partialTrace_sum, partialTrace_right_instrument K hK]
  ext i j
  simp only [PartialTrace, teleporterPreparedJoint_entry, Matrix.smul_apply,
    smul_eq_mul, Matrix.traceLeft, Matrix.of_apply]
  rw [← (finProdFinEquiv (m := n) (n := a)).sum_comp]
  simp [Fintype.sum_prod_type, Matrix.trace, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem physical_teleporter_message_count {n a d k : ℕ}
    (ω : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ)
    (hω : ω.PosSemidef) (htrace : Matrix.trace ω = 1)
    (K : Fin k → Operator (n * a)) (hK : ∑ m, (K m)ᴴ * K m = 1)
    (S : Fin k → QuantumChannel d n)
    (hexact : ∀ ρ, IsDensityOperator ρ →
      ∑ m, (S m).map (teleporterRawBranch ω (K m) ρ) = ρ) :
    n * n ≤ k := by
  simpa using! exact_one_way_teleporter_messages
    (fun m => teleporterRawBranch ω (K m)) (fun m => teleporterRawBranch_cp ω hω (K m))
    S (Matrix.traceLeft ω) (by simpa using! htrace)
    (teleporterRawBranch_sum ω K hK) hexact

theorem physical_teleporter_bit_count {n a d b : ℕ}
    (ω : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ)
    (hω : ω.PosSemidef) (htrace : Matrix.trace ω = 1)
    (K : Fin (2 ^ b) → Operator (n * a)) (hK : ∑ m, (K m)ᴴ * K m = 1)
    (S : Fin (2 ^ b) → QuantumChannel d n)
    (hexact : ∀ ρ, IsDensityOperator ρ →
      ∑ m, (S m).map (teleporterRawBranch ω (K m) ρ) = ρ) :
    Nat.clog 2 (n * n) ≤ b :=
  Nat.clog_le_of_le_pow (physical_teleporter_message_count ω hω htrace K hK S hexact)

noncomputable def teleporterMessageBranch {n a d l k : ℕ}
    (ω : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ)
    (K : Fin l → Operator (n * a)) (f : Fin l → Fin k) (m : Fin k) :
    Operator n →ₗ[ℂ] Operator d :=
  ∑ j, if f j = m then teleporterRawBranch ω (K j) else 0

theorem teleporterMessageBranch_cp {n a d l k : ℕ}
    (ω : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) (hω : ω.PosSemidef)
    (K : Fin l → Operator (n * a)) (f : Fin l → Fin k) (m : Fin k) :
    CompletelyPositive (teleporterMessageBranch ω K f m) := by
  apply CompletelyPositive.sum
  intro j _
  split_ifs
  · exact teleporterRawBranch_cp ω hω (K j)
  · intro r A _
    simpa [ChannelAmplification] using!
      (Matrix.PosSemidef.zero : (0 : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ).PosSemidef)

theorem teleporterMessageBranch_sum {n a d l k : ℕ}
    (ω : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ)
    (K : Fin l → Operator (n * a)) (hK : ∑ j, (K j)ᴴ * K j = 1)
    (f : Fin l → Fin k) (ρ : Operator n) :
    (∑ m, teleporterMessageBranch ω K f m ρ) =
      Matrix.trace ρ • Matrix.traceLeft ω := by
  have he : (∑ m, teleporterMessageBranch ω K f m ρ) =
      ∑ j, teleporterRawBranch ω (K j) ρ := by
    simp only [teleporterMessageBranch, LinearMap.sum_apply]
    have hi (m : Fin k) (j : Fin l) :
        (if f j = m then teleporterRawBranch ω (K j) else 0) ρ =
          if f j = m then teleporterRawBranch ω (K j) ρ else 0 := by
      split_ifs <;> rfl
    simp_rw [hi]
    rw [Finset.sum_comm]
    simp
  rw [he, teleporterRawBranch_sum ω K hK]

theorem physical_teleporter_coarsened_message_count {n a d l k : ℕ}
    (ω : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ)
    (hω : ω.PosSemidef) (htrace : Matrix.trace ω = 1)
    (K : Fin l → Operator (n * a)) (hK : ∑ j, (K j)ᴴ * K j = 1)
    (f : Fin l → Fin k) (S : Fin k → QuantumChannel d n)
    (hexact : ∀ ρ, IsDensityOperator ρ →
      ∑ m, (S m).map (teleporterMessageBranch ω K f m ρ) = ρ) :
    n * n ≤ k := by
  simpa using! exact_one_way_teleporter_messages (teleporterMessageBranch ω K f)
    (teleporterMessageBranch_cp ω hω K f) S (Matrix.traceLeft ω)
    (by simpa using! htrace) (teleporterMessageBranch_sum ω K hK f) hexact

end Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound
