/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform
import Qatlib.Concepts.QuditTeleport.TeleportCore.BellReferenceProtocol
import Qatlib.Concepts.BlockEncoding.LinearCombination
set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Concepts.QuditTeleport.TeleportCore
open Matrix
open scoped Classical BigOperators ComplexOrder Kronecker

abbrev QuditTriple (n : ℕ) := (Fin n × Fin n) × Fin n

def quditRegisterEquiv (n : ℕ) : QuditTriple n ≃ Fin (n*n*n) :=
  (Equiv.prodCongr (finProdFinEquiv : (Fin n × Fin n) ≃ Fin (n*n))
    (Equiv.refl (Fin n))).trans finProdFinEquiv

def quditOutcomeEquiv (n : ℕ) : (Fin n × Fin n) ≃ Fin (n*n) := finProdFinEquiv

def quditAdd (n : ℕ) [NeZero n] (x y : Fin n) : Fin n :=
  (ZMod.finEquiv n).symm ((ZMod.finEquiv n) x + (ZMod.finEquiv n) y)

noncomputable def quditX (n : ℕ) [NeZero n] (b : ZMod n) : Operator n :=
  fun x y => if (ZMod.finEquiv n) x=(ZMod.finEquiv n) y+b then 1 else 0
noncomputable def quditZ (n : ℕ) [NeZero n] (a : ZMod n) : Operator n :=
  Matrix.diagonal fun x => ZMod.stdAddChar (a*(ZMod.finEquiv n) x)
noncomputable def quditSUM (n : ℕ) [NeZero n] : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun x y => if x.1=y.1 ∧ x.2=quditAdd n y.2 y.1 then 1 else 0
noncomputable def quditResource (n : ℕ) [NeZero n] : QState (Fin n × Fin n) :=
  fun x => if x.1=x.2 then (Real.sqrt (n:ℝ):ℂ)⁻¹ else 0

noncomputable def quditHbB (n : ℕ) [NeZero n] : Matrix (QuditTriple n) (QuditTriple n) ℂ :=
  TensorGate (TensorGate (1:Operator n) (QFTMatrix n)) (1:Operator n)
noncomputable def quditSUMbcB (n : ℕ) [NeZero n] : Matrix (QuditTriple n) (QuditTriple n) ℂ :=
  relabelGate (Equiv.prodAssoc (Fin n) (Fin n) (Fin n)).symm
    (TensorGate (1:Operator n) (quditSUM n))
noncomputable def quditSUMabInvB (n : ℕ) [NeZero n] : Matrix (QuditTriple n) (QuditTriple n) ℂ :=
  TensorGate (quditSUM n)ᴴ (1:Operator n)
noncomputable def quditHaInvB (n : ℕ) [NeZero n] : Matrix (QuditTriple n) (QuditTriple n) ℂ :=
  TensorGate (TensorGate (QFTMatrix n)ᴴ (1:Operator n)) (1:Operator n)
noncomputable def quditBobXB (n : ℕ) [NeZero n] (o : Fin n × Fin n) :
    Matrix (QuditTriple n) (QuditTriple n) ℂ :=
  TensorGate (1:Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (quditX n (-((ZMod.finEquiv n) o.2)))
noncomputable def quditBobZB (n : ℕ) [NeZero n] (o : Fin n × Fin n) :
    Matrix (QuditTriple n) (QuditTriple n) ℂ :=
  TensorGate (1:Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (quditZ n ((ZMod.finEquiv n) o.1))
noncomputable def quditInitialFrame (n : ℕ) [NeZero n] : Matrix (Fin (n*n*n)) (Fin n) ℂ :=
  fun r j => let t := (quditRegisterEquiv n).symm r
    if t.1.1=j ∧ t.1.2=0 ∧ t.2=0 then 1 else 0
noncomputable def quditPreparedFrame (n : ℕ) [NeZero n] : Matrix (Fin (n*n*n)) (Fin n) ℂ :=
  relabelGate (quditRegisterEquiv n) (quditSUMbcB n*quditHbB n)*quditInitialFrame n
noncomputable def quditBranchKraus (n : ℕ) [NeZero n] (o : Fin n × Fin n) : Operator n :=
  fun k j =>
    (relabelGate (quditRegisterEquiv n) (quditHaInvB n*quditSUMabInvB n)*quditPreparedFrame n)
      ((quditRegisterEquiv n) (o,k)) j
noncomputable def quditCorrection (n : ℕ) [NeZero n] (o : Fin n × Fin n) : Operator n :=
  quditZ n ((ZMod.finEquiv n) o.1)*quditX n (-((ZMod.finEquiv n) o.2))

theorem qudit_equiv_perm_unitary {I : Type} [Fintype I] [DecidableEq I] (e : I ≃ I) :
    permMatrix e ∈ Matrix.unitaryGroup I ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext x y
  simp only [Matrix.star_eq_conjTranspose,Matrix.mul_apply,Matrix.conjTranspose_apply,permMatrix,Matrix.of_apply]
  rw [Finset.sum_eq_single (e.symm x)]
  · simp [Matrix.one_apply,eq_comm]
  · intro j hj hn
    have hx : x ≠ e j := by
      intro he
      apply hn
      rw [he]
      simp
    simp [hx]
  · simp

def quditShiftEquiv (n : ℕ) [NeZero n] (b : ZMod n) : Fin n ≃ Fin n where
  toFun y := (ZMod.finEquiv n).symm ((ZMod.finEquiv n) y+b)
  invFun x := (ZMod.finEquiv n).symm ((ZMod.finEquiv n) x-b)
  left_inv y := by simp
  right_inv x := by simp

theorem quditX_perm (n : ℕ) [NeZero n] (b : ZMod n) : quditX n b = permMatrix (quditShiftEquiv n b) := by
  ext x y
  unfold quditX permMatrix
  simp only [Matrix.of_apply,quditShiftEquiv,Equiv.coe_fn_mk]
  congr 1
  exact propext (Equiv.apply_eq_iff_eq_symm_apply (ZMod.finEquiv n).toEquiv)

theorem quditX_unitary (n : ℕ) [NeZero n] (b : ZMod n) : quditX n b ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [quditX_perm]
  exact qudit_equiv_perm_unitary _

theorem quditZ_unitary (n : ℕ) [NeZero n] (a : ZMod n) : quditZ n a ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [quditZ,Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal,← Matrix.diagonal_one]
  congr 1
  funext i
  have he : ((Complex.normSq (ZMod.stdAddChar (a*(ZMod.finEquiv n) i)):ℝ):ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq,norm_stdAddChar]
    norm_num
  rw [Complex.normSq_eq_conj_mul_self] at he
  exact he

def quditSumEquiv (n : ℕ) [NeZero n] : (Fin n × Fin n) ≃ (Fin n × Fin n) where
  toFun y := (y.1,quditAdd n y.2 y.1)
  invFun x := (x.1,(ZMod.finEquiv n).symm ((ZMod.finEquiv n) x.2-(ZMod.finEquiv n) x.1))
  left_inv y := by simp [quditAdd]
  right_inv x := by simp [quditAdd]

theorem quditSUM_unitary (n : ℕ) [NeZero n] : quditSUM n ∈ Matrix.unitaryGroup (Fin n × Fin n) ℂ := by
  have he : quditSUM n = permMatrix (quditSumEquiv n) := by
    ext ⟨a,b⟩ ⟨c,d⟩
    simp [quditSUM,permMatrix,quditSumEquiv,Prod.ext_iff]
  rw [he]
  exact qudit_equiv_perm_unitary _

theorem quditResource_normalized (n : ℕ) [NeZero n] : Normalized (quditResource n) := by
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have he (a : Fin n) : (∑ b : Fin n,‖quditResource n (a,b)‖^2) = ‖(Real.sqrt (n:ℝ):ℂ)⁻¹‖^2 := by
    rw [Finset.sum_eq_single a]
    · simp [quditResource]
    · intro b hb hn
      simp [quditResource,Ne.symm hn]
    · simp
  change (∑ p : Fin n × Fin n,‖quditResource n p‖^2) = 1
  rw [Fintype.sum_prod_type]
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg n),mul_inv_cancel₀ hn]

theorem quditInitialFrame_isometry (n : ℕ) [NeZero n] : IsIsometry (quditInitialFrame n) := by
  change (quditInitialFrame n)ᴴ*quditInitialFrame n = 1
  ext i j
  rw [Matrix.mul_apply,← (quditRegisterEquiv n).sum_comp]
  simp [quditInitialFrame,Matrix.conjTranspose_apply,Fintype.sum_prod_type,Matrix.one_apply,eq_comm,ite_and]

theorem qudit_resource_and_weyl_access_laws : ∀ (n : ℕ) [NeZero n],
  Normalized (quditResource n) ∧ IsIsometry (quditInitialFrame n) ∧
  (∀ (b : ZMod n), quditX n b ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
  (∀ (a : ZMod n), quditZ n a ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
  quditSUM n ∈ Matrix.unitaryGroup (Fin n × Fin n) ℂ := by
  intro n _
  exact ⟨quditResource_normalized n,quditInitialFrame_isometry n,quditX_unitary n,quditZ_unitary n,quditSUM_unitary n⟩

theorem qudit_perm_apply {I : Type} [Fintype I] [DecidableEq I] (e : I ≃ I) (ψ : QState I) (x : I) :
    ApplyGate (permMatrix e) ψ x = ψ (e.symm x) := by
  simp only [ApplyGate,permMatrix,Matrix.mulVec,dotProduct,Matrix.of_apply]
  rw [Finset.sum_eq_single (e.symm x)]
  · simp
  · intro j hj hn
    have hx : x ≠ e j := by intro he; apply hn; rw [he]; simp
    simp [hx]
  · simp

theorem qudit_perm_adjoint {I : Type} [Fintype I] [DecidableEq I] (e : I ≃ I) :
    (permMatrix e)ᴴ = permMatrix e.symm := by
  ext x y
  simp only [Matrix.conjTranspose_apply,permMatrix,Matrix.of_apply]
  have he : (y = e x) ↔ x = e.symm y := by rw [eq_comm]; exact Equiv.apply_eq_iff_eq_symm_apply e
  simp [he]

theorem qudit_tensor_perm {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ I) (f : J ≃ J) : TensorGate (permMatrix e) (permMatrix f) = permMatrix (e.prodCongr f) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  simp only [tensorGate_apply,permMatrix,Matrix.of_apply,Equiv.prodCongr_apply]
  by_cases h1 : a = e c <;> by_cases h2 : b = f d <;> simp [h1,h2]

def quditSumBcEquiv (n : ℕ) [NeZero n] : QuditTriple n ≃ QuditTriple n where
  toFun y := (y.1,quditAdd n y.2 y.1.2)
  invFun x := (x.1,(ZMod.finEquiv n).symm ((ZMod.finEquiv n) x.2-(ZMod.finEquiv n) x.1.2))
  left_inv y := by simp [quditAdd]
  right_inv x := by simp [quditAdd]

theorem quditSUMbc_perm (n : ℕ) [NeZero n] : quditSUMbcB n = permMatrix (quditSumBcEquiv n) := by
  ext ⟨⟨a,b⟩,c⟩ ⟨⟨d,e⟩,f⟩
  simp [quditSUMbcB,relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,TensorGate,Matrix.kroneckerMap_apply,
    quditSUM,permMatrix,quditSumBcEquiv,Matrix.one_apply,Prod.ext_iff,ite_and,and_assoc]
  split_ifs <;> simp_all

theorem quditInitialFrame_column (n : ℕ) [NeZero n] (j : Fin n) :
    (fun r => quditInitialFrame n r j) = relabelState (quditRegisterEquiv n) (Ket ((j,0),0)) := by
  ext r
  simp [quditInitialFrame,relabelState,Ket,Prod.ext_iff,eq_comm,and_assoc]

theorem quditQFT_entry (n : ℕ) [NeZero n] (x y : Fin n) :
    QFTMatrix n x y = (Real.sqrt (n:ℝ):ℂ)⁻¹*ZMod.stdAddChar ((ZMod.finEquiv n) x*(ZMod.finEquiv n) y) := by
  simpa only [RingEquiv.symm_apply_apply] using
      qftMatrix_stdAddChar ((ZMod.finEquiv n) x) ((ZMod.finEquiv n) y)

theorem quditHb_seed (n : ℕ) [NeZero n] (j : Fin n) :
    ApplyGate (quditHbB n) (Ket ((j,0),0)) =
      fun r : QuditTriple n => if r.1.1 = j ∧ r.2 = 0 then (Real.sqrt (n:ℝ):ℂ)⁻¹ else 0 := by
  ext ⟨⟨a,b⟩,c⟩
  simp only [ApplyGate]
  rw [mulVec_ket_apply]
  simp only [quditHbB,tensorGate_apply,quditQFT_entry,finEquiv_apply_val]
  simp [Matrix.one_apply,ite_and]
  split_ifs <;> simp_all

theorem quditPreparedFrame_resource (n : ℕ) [NeZero n] (r : QuditTriple n) (j : Fin n) :
    quditPreparedFrame n ((quditRegisterEquiv n) r) j =
      (if r.1.1 = j then quditResource n (r.1.2,r.2) else 0) := by
  rw [quditPreparedFrame,matrix_mul_column,quditInitialFrame_column,applyGate_relabelGate,applyGate_mul]
  rw [quditHb_seed,quditSUMbc_perm]
  simp only [relabelState,Function.comp_apply,Equiv.symm_apply_apply]
  rw [qudit_perm_apply]
  simp only [quditSumBcEquiv,Equiv.coe_fn_symm_mk]
  have he : (ZMod.finEquiv n).symm ((ZMod.finEquiv n) r.2-(ZMod.finEquiv n) r.1.2) = 0 ↔ r.1.2 = r.2 := by
    have h0 : (ZMod.finEquiv n) (0:Fin n) = 0 := by simp [finEquiv_apply_val]
    constructor
    · intro hz
      have hv := congrArg (ZMod.finEquiv n) hz
      simp only [RingEquiv.apply_symm_apply,h0] at hv
      exact ((ZMod.finEquiv n).injective (sub_eq_zero.mp hv)).symm
    · intro hx
      rw [← hx]
      simp
  simp only [he,quditResource]
  by_cases h1 : r.1.1 = j <;> by_cases h2 : r.1.2 = r.2 <;> simp [h1,h2]

theorem quditSUM_perm (n : ℕ) [NeZero n] : quditSUM n = permMatrix (quditSumEquiv n) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  simp [quditSUM,permMatrix,quditSumEquiv,Prod.ext_iff]

theorem quditSUMabInv_state (n : ℕ) [NeZero n] (ψ : QState (QuditTriple n)) :
    ApplyGate (quditSUMabInvB n) ψ = fun r => ψ ((r.1.1,quditAdd n r.1.2 r.1.1),r.2) := by
  have hid : (1:Operator n) = permMatrix (Equiv.refl (Fin n)) := by
    ext i j; simp [permMatrix,Matrix.one_apply]
  have he : quditSUMabInvB n = permMatrix ((quditSumEquiv n).symm.prodCongr (Equiv.refl (Fin n))) := by
    rw [quditSUMabInvB,quditSUM_perm,qudit_perm_adjoint,hid,qudit_tensor_perm]
  ext r
  rw [he,qudit_perm_apply]
  rfl

theorem quditHaInv_apply (n : ℕ) [NeZero n] (ψ : QState (QuditTriple n)) (r : QuditTriple n) :
    ApplyGate (quditHaInvB n) ψ r = ∑ j : Fin n,(QFTMatrix n)ᴴ r.1.1 j*ψ ((j,r.1.2),r.2) := by
  rcases r with ⟨⟨a,b⟩,c⟩
  simp only [ApplyGate,Matrix.mulVec,dotProduct,Fintype.sum_prod_type]
  simp only [quditHaInvB,tensorGate_apply,Matrix.one_apply,mul_ite,ite_mul]
  simp

theorem quditPreparedFrame_column (n : ℕ) [NeZero n] (j : Fin n) :
    (fun r => quditPreparedFrame n r j) = relabelState (quditRegisterEquiv n)
      (fun r : QuditTriple n => if r.1.1 = j then quditResource n (r.1.2,r.2) else 0) := by
  ext r
  have he := quditPreparedFrame_resource n ((quditRegisterEquiv n).symm r) j
  simpa only [Equiv.apply_symm_apply,relabelState,Function.comp_apply] using he

theorem quditQFT_adjoint_entry (n : ℕ) [NeZero n] (a j : Fin n) :
    (QFTMatrix n)ᴴ a j = (Real.sqrt (n:ℝ):ℂ)⁻¹*
      ZMod.stdAddChar (-((ZMod.finEquiv n) a*(ZMod.finEquiv n) j)) := by
  rw [Matrix.conjTranspose_apply,quditQFT_entry]
  change (starRingEnd ℂ)
      ((Real.sqrt (n:ℝ):ℂ)⁻¹*ZMod.stdAddChar ((ZMod.finEquiv n) j*(ZMod.finEquiv n) a)) = _
  rw [(starRingEnd ℂ).map_mul,conj_stdAddChar]
  simp [mul_comm]

theorem qudit_sqrt_inverse_square (n : ℕ) [NeZero n] :
    (Real.sqrt (n:ℝ):ℂ)⁻¹*(Real.sqrt (n:ℝ):ℂ)⁻¹ = 1/(n:ℂ) := by
  have hs : (Real.sqrt (n:ℝ):ℂ)^2 = (n:ℂ) := by exact_mod_cast (Real.sq_sqrt (Nat.cast_nonneg n))
  rw [← mul_inv,← pow_two,hs,one_div]

theorem quditDecodedFrame_apply (n : ℕ) [NeZero n] (r : QuditTriple n) (j : Fin n) :
    (relabelGate (quditRegisterEquiv n) (quditHaInvB n*quditSUMabInvB n)*quditPreparedFrame n)
      ((quditRegisterEquiv n) r) j =
      (if r.2 = quditAdd n r.1.2 j then
        (1/(n:ℂ))*ZMod.stdAddChar (-((ZMod.finEquiv n) r.1.1*(ZMod.finEquiv n) j)) else 0) := by
  rw [matrix_mul_column,quditPreparedFrame_column,applyGate_relabelGate,applyGate_mul,quditSUMabInv_state]
  simp only [relabelState,Function.comp_apply,Equiv.symm_apply_apply]
  rw [quditHaInv_apply]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [quditQFT_adjoint_entry]
  unfold quditResource
  by_cases he : r.2 = quditAdd n r.1.2 j
  · simp only [he,eq_comm,ite_true]
    rw [mul_assoc, mul_comm (ZMod.stdAddChar _),← mul_assoc,qudit_sqrt_inverse_square]
  · simp [he,Ne.symm he]

theorem quditXZ_entry (n : ℕ) [NeZero n] (b a : ZMod n) (k j : Fin n) :
    (quditX n b*quditZ n a) k j =
      if (ZMod.finEquiv n) k=(ZMod.finEquiv n) j+b then ZMod.stdAddChar (a*(ZMod.finEquiv n) j) else 0 := by
  rw [quditZ,Matrix.mul_diagonal]
  simp [quditX]

theorem quditBranchKraus_formula (n : ℕ) [NeZero n] (o : Fin n × Fin n) :
    quditBranchKraus n o = (1/(n:ℂ)) •
      (quditX n ((ZMod.finEquiv n) o.2)*quditZ n (-((ZMod.finEquiv n) o.1))) := by
  ext k j
  rw [quditBranchKraus,quditDecodedFrame_apply,Matrix.smul_apply,quditXZ_entry]
  have he : k = quditAdd n o.2 j ↔ (ZMod.finEquiv n) k=(ZMod.finEquiv n) j+(ZMod.finEquiv n) o.2 := by
    rw [← (ZMod.finEquiv n).injective.eq_iff]
    simp [quditAdd,add_comm]
  simp only [he,neg_mul]
  split_ifs <;> simp

theorem quditX_adjoint (n : ℕ) [NeZero n] (b : ZMod n) : (quditX n b)ᴴ = quditX n (-b) := by
  rw [quditX_perm,qudit_perm_adjoint,quditX_perm]
  congr 1
  ext x
  simp [quditShiftEquiv,sub_eq_add_neg]

theorem quditZ_adjoint (n : ℕ) [NeZero n] (a : ZMod n) : (quditZ n a)ᴴ = quditZ n (-a) := by
  rw [quditZ,Matrix.diagonal_conjTranspose,quditZ]
  congr 1
  funext x
  change (starRingEnd ℂ) (ZMod.stdAddChar (a*(ZMod.finEquiv n) x)) = _
  rw [conj_stdAddChar,neg_mul]

theorem quditCorrection_cancel (n : ℕ) [NeZero n] (o : Fin n × Fin n) :
    quditCorrection n o*quditBranchKraus n o = (1/(n:ℂ)) • (1:Operator n) := by
  have hx : quditX n (-((ZMod.finEquiv n) o.2))*quditX n ((ZMod.finEquiv n) o.2) = 1 := by
    rw [← quditX_adjoint]
    simpa only [Matrix.star_eq_conjTranspose] using (quditX_unitary n ((ZMod.finEquiv n) o.2)).1
  have hz : quditZ n ((ZMod.finEquiv n) o.1)*quditZ n (-((ZMod.finEquiv n) o.1)) = 1 := by
    rw [← quditZ_adjoint]
    simpa only [Matrix.star_eq_conjTranspose] using (quditZ_unitary n ((ZMod.finEquiv n) o.1)).2
  rw [quditCorrection,quditBranchKraus_formula,Matrix.mul_smul,Matrix.mul_assoc,
    ← Matrix.mul_assoc (quditX n _) (quditX n _) (quditZ n _),hx,Matrix.one_mul,hz]

theorem qudit_actual_resource_decoding_and_correction : ∀ (n : ℕ) [NeZero n] (r : QuditTriple n) (j : Fin n),
  quditPreparedFrame n ((quditRegisterEquiv n) r) j=
    (if r.1.1=j then quditResource n (r.1.2,r.2) else 0) ∧
  ∀ o : Fin n × Fin n,
    quditBranchKraus n o=(1/(n:ℂ)) •
      (quditX n ((ZMod.finEquiv n) o.2)*quditZ n (-((ZMod.finEquiv n) o.1))) ∧
    quditCorrection n o*quditBranchKraus n o=(1/(n:ℂ)) • (1:Operator n) := by
  intro n _ r j
  exact ⟨quditPreparedFrame_resource n r j,fun o => ⟨quditBranchKraus_formula n o,quditCorrection_cancel n o⟩⟩

end Qatlib.Concepts.QuditTeleport.TeleportCore
