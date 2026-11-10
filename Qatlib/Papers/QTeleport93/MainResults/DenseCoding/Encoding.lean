/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationProtocol
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Qatlib.Papers.QTeleport93.MainResults.DenseCoding
open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.PureStateMath.BornBridge

noncomputable def denseEncodingGate (n : ℕ) [NeZero n] :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  quditSUM n * TensorGate (QFTMatrix n) (1 : Operator n)

theorem denseEncodingGate_unitary (n : ℕ) [NeZero n] :
    denseEncodingGate n ∈ Matrix.unitaryGroup (Fin n × Fin n) ℂ := by
  exact (Matrix.unitaryGroup (Fin n × Fin n) ℂ).mul_mem (quditSUM_unitary n)
    (tensorGate_unitary (qftMatrix_unitary (NeZero.pos n)) (by simp))

theorem denseEncodingGate_entry (n : ℕ) [NeZero n] (r o : Fin n × Fin n) :
    denseEncodingGate n r o =
      if r.2 = quditAdd n o.2 r.1 then QFTMatrix n r.1 o.1 else 0 := by
  classical
  rcases r with ⟨j,k⟩
  rcases o with ⟨a,b⟩
  simp [denseEncodingGate, Matrix.mul_apply, Fintype.sum_prod_type,
    quditSUM, tensorGate_apply, Matrix.one_apply, ite_and]
  rw [Finset.sum_eq_single b]
  · simp
  · intro x _ hxb
    simp [hxb]
  · simp

noncomputable def denseLocalGate (n : ℕ) [NeZero n] (o : Fin n × Fin n) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  TensorGate (1 : Operator n)
    (quditX n ((ZMod.finEquiv n) o.2) * quditZ n ((ZMod.finEquiv n) o.1))

theorem denseLocalGate_unitary (n : ℕ) [NeZero n] (o : Fin n × Fin n) :
    denseLocalGate n o ∈ Matrix.unitaryGroup (Fin n × Fin n) ℂ := by
  exact tensorGate_unitary (by simp)
    ((Matrix.unitaryGroup (Fin n) ℂ).mul_mem (quditX_unitary n _)
      (quditZ_unitary n _))

theorem denseLocalGate_resource_entry (n : ℕ) [NeZero n] (o r : Fin n × Fin n) :
    (denseLocalGate n o *ᵥ quditResource n) r = denseEncodingGate n r o := by
  classical
  rcases r with ⟨j,k⟩
  rcases o with ⟨a,b⟩
  rw [denseEncodingGate_entry, quditQFT_entry]
  have hshift : ((ZMod.finEquiv n) k = (ZMod.finEquiv n) j + (ZMod.finEquiv n) b) ↔
      k = quditAdd n b j := by
    constructor
    · intro h
      apply (ZMod.finEquiv n).injective
      simp [quditAdd, h, add_comm]
    · intro h
      rw [h]
      simp [quditAdd, add_comm]
  simp [denseLocalGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    tensorGate_apply, Matrix.one_apply, quditResource, quditZ, quditX,
    Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, ite_mul]
  rw [Finset.sum_eq_single j]
  · simp [hshift, mul_comm]
  · intro x _ hxj
    simp [Ne.symm hxj]
  · simp

theorem denseLocalGate_decode (n : ℕ) [NeZero n] (o : Fin n × Fin n) :
    (denseEncodingGate n)ᴴ *ᵥ (denseLocalGate n o *ᵥ quditResource n) = Ket o := by
  have hcode : denseLocalGate n o *ᵥ quditResource n = denseEncodingGate n *ᵥ Ket o := by
    funext r
    have hcol : (denseEncodingGate n *ᵥ Ket o) r = denseEncodingGate n r o := by
      simp [Matrix.mulVec, dotProduct, Ket]
    rw [hcol]
    exact denseLocalGate_resource_entry n o r
  rw [hcode, Matrix.mulVec_mulVec]
  have h := Matrix.mem_unitaryGroup_iff'.mp (denseEncodingGate_unitary n)
  rw [show (denseEncodingGate n)ᴴ * denseEncodingGate n = 1 from h, Matrix.one_mulVec]

end Qatlib.Papers.QTeleport93.MainResults.DenseCoding
