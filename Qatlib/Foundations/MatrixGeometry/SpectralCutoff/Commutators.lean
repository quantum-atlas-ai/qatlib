/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.SpectralCutoff.Compression
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem compressed_commutator (H : Matrix I I ℂ) (hH : H.IsHermitian) (Λ : ℝ)
    (A B : Matrix I I ℂ) :
    low H hH Λ*(A*B-B*A)*low H hH Λ=
      (low H hH Λ*A*low H hH Λ)*(low H hH Λ*B*low H hH Λ)-
      (low H hH Λ*B*low H hH Λ)*(low H hH Λ*A*low H hH Λ)+
      low H hH Λ*A*high H hH Λ*B*low H hH Λ-
      low H hH Λ*B*high H hH Λ*A*low H hH Λ := by
  have hp:=low_square H hH Λ
  have hr (X : Matrix I I ℂ) : low H hH Λ*(low H hH Λ*X)=low H hH Λ*X := by rw [← mul_assoc,hp]
  simp only [high]
  noncomm_ring
  simp only [hr]
  abel

theorem compressed_commutator_norm (H : Matrix I I ℂ) (hH : H.IsHermitian) (Λ : ℝ)
    (A B : Matrix I I ℂ) :
    ‖low H hH Λ*(A*B-B*A)*low H hH Λ‖ ≤
      2*‖low H hH Λ*A*low H hH Λ‖*‖low H hH Λ*B*low H hH Λ‖+
      ‖low H hH Λ*A*high H hH Λ‖*‖high H hH Λ*B*low H hH Λ‖+
      ‖low H hH Λ*B*high H hH Λ‖*‖high H hH Λ*A*low H hH Λ‖ := by
  let P:=low H hH Λ
  let Q:=high H hH Λ
  have hq:=high_square H hH Λ
  have ha : P*A*Q*B*P=(P*A*Q)*(Q*B*P) := by
    calc
      _=P*A*(Q*Q)*(B*P) := by rw [hq]; noncomm_ring
      _=_ := by noncomm_ring
  have hb : P*B*Q*A*P=(P*B*Q)*(Q*A*P) := by
    calc
      _=P*B*(Q*Q)*(A*P) := by rw [hq]; noncomm_ring
      _=_ := by noncomm_ring
  rw [compressed_commutator]
  change ‖(P*A*P)*(P*B*P)-(P*B*P)*(P*A*P)+P*A*Q*B*P-P*B*Q*A*P‖ ≤ _
  rw [ha,hb]
  calc
    _ ≤ ‖(P*A*P)*(P*B*P)-(P*B*P)*(P*A*P)+(P*A*Q)*(Q*B*P)‖+
      ‖(P*B*Q)*(Q*A*P)‖ := norm_sub_le _ _
    _ ≤ (‖(P*A*P)*(P*B*P)-(P*B*P)*(P*A*P)‖+‖(P*A*Q)*(Q*B*P)‖)+
      ‖(P*B*Q)*(Q*A*P)‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (‖(P*A*P)*(P*B*P)‖+‖(P*B*P)*(P*A*P)‖+‖(P*A*Q)*(Q*B*P)‖)+
      ‖(P*B*Q)*(Q*A*P)‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ (‖P*A*P‖*‖P*B*P‖+‖P*B*P‖*‖P*A*P‖+‖P*A*Q‖*‖Q*B*P‖)+
      ‖P*B*Q‖*‖Q*A*P‖ := by gcongr <;> exact norm_mul_le _ _
    _=_ := by dsimp [P,Q]; ring

theorem psd_compressed_commutator_norm (H A B : Matrix I I ℂ) (hH : H.PosSemidef)
    (hA : A.PosSemidef) (hHA : (H-A).PosSemidef) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ‖low H hH.isHermitian Λ*(A*B-B*A)*low H hH.isHermitian Λ‖ ≤
      2*Λ*‖low H hH.isHermitian Λ*B*low H hH.isHermitian Λ‖+
      ‖low H hH.isHermitian Λ*A*high H hH.isHermitian Λ‖*‖high H hH.isHermitian Λ*B*low H hH.isHermitian Λ‖+
      ‖low H hH.isHermitian Λ*B*high H hH.isHermitian Λ‖*‖high H hH.isHermitian Λ*A*low H hH.isHermitian Λ‖ := by
  exact (compressed_commutator_norm H hH.isHermitian Λ A B).trans (by
    gcongr
    exact compression_norm H A hH hA hHA Λ hΛ)

end Qatlib.Foundations.MatrixGeometry.SpectralCutoff
