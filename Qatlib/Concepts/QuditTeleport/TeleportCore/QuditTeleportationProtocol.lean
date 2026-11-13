/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform
import Qatlib.Concepts.QuditTeleport.TeleportCore.BellReferenceProtocol
import Qatlib.Concepts.BlockEncoding.LinearCombination

/-!
# Qudit teleportation resources and Weyl corrections

This module constructs the three register qudit teleportation protocol using modular Weyl
shifts, phase gates, a Fourier transform, and controlled modular addition. `quditInitialFrame`
embeds the input with zero ancillas, and `quditPreparedFrame` prepares the standard maximally
entangled resource on the remaining registers.

Explicit decoding gives branch operator `X(b) * Z(-a) / n` for Alice's outcome `(a, b)`. The
correction `Z(a) * X(-b)` cancels this operator to `1 / n` times the identity, providing the
operator calculation for the qudit protocol of [BennettEtAl1993Teleportation].

## Main statements

* `qudit_resource_and_weyl_access_laws`: resource normalization, an isometric input frame, and
  unitary Weyl and SUM gates.
* `quditBranchKraus_formula`: the explicit decoded branch operator.
* `quditCorrection_cancel`: exact cancellation by the outcome dependent correction.
* `qudit_actual_resource_decoding_and_correction`: the resource, decoding, and correction
  identities together.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

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

/-- The three qudit register index type `(Fin n × Fin n) × Fin n`, grouping Alice's two
registers together. -/
abbrev QuditTriple (n : ℕ) := (Fin n × Fin n) × Fin n

/-- Flattens the three qudit register indices into `Fin (n * n * n)`. -/
def quditRegisterEquiv (n : ℕ) : QuditTriple n ≃ Fin (n*n*n) :=
  (Equiv.prodCongr (finProdFinEquiv : (Fin n × Fin n) ≃ Fin (n*n))
    (Equiv.refl (Fin n))).trans finProdFinEquiv

/-- Flattens Alice's pair of qudit measurement outcomes into `Fin (n * n)`. -/
def quditOutcomeEquiv (n : ℕ) : (Fin n × Fin n) ≃ Fin (n*n) := finProdFinEquiv

/-- Addition modulo `n` on `Fin n`, transported through its equivalence with `ZMod n`. -/
def quditAdd (n : ℕ) [NeZero n] (x y : Fin n) : Fin n :=
  (ZMod.finEquiv n).symm ((ZMod.finEquiv n) x + (ZMod.finEquiv n) y)

/-- The Weyl shift matrix sending basis index `y` to `y + b` modulo `n`. -/
noncomputable def quditX (n : ℕ) [NeZero n] (b : ZMod n) : Operator n :=
  fun x y => if (ZMod.finEquiv n) x=(ZMod.finEquiv n) y+b then 1 else 0
/-- The diagonal Weyl phase matrix whose entry at `x` is the standard additive character of `a *
x`. -/
noncomputable def quditZ (n : ℕ) [NeZero n] (a : ZMod n) : Operator n :=
  Matrix.diagonal fun x => ZMod.stdAddChar (a*(ZMod.finEquiv n) x)
/-- The controlled modular addition matrix sending a basis pair `(a, b)` to `(a, b + a)`. -/
noncomputable def quditSUM (n : ℕ) [NeZero n] : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun x y => if x.1=y.1 ∧ x.2=quditAdd n y.2 y.1 then 1 else 0
/-- The standard maximally entangled qudit vector with amplitude `1 / √n` on equal indices and
zero elsewhere. -/
noncomputable def quditResource (n : ℕ) [NeZero n] : QState (Fin n × Fin n) :=
  fun x => if x.1=x.2 then (Real.sqrt (n:ℝ):ℂ)⁻¹ else 0

/-- The qudit Fourier transform on register `b`, tensored with identities on registers `a` and
`c`. -/
noncomputable def quditHbB (n : ℕ) [NeZero n] : Matrix (QuditTriple n) (QuditTriple n) ℂ :=
  TensorGate (TensorGate (1:Operator n) (QFTMatrix n)) (1:Operator n)
/-- The controlled modular addition from register `b` to register `c`, leaving register `a`
unchanged. -/
noncomputable def quditSUMbcB (n : ℕ) [NeZero n] : Matrix (QuditTriple n) (QuditTriple n) ℂ :=
  relabelGate (Equiv.prodAssoc (Fin n) (Fin n) (Fin n)).symm
    (TensorGate (1:Operator n) (quditSUM n))
/-- The adjoint controlled modular addition from register `a` to register `b`, leaving register
`c` unchanged. -/
noncomputable def quditSUMabInvB (n : ℕ) [NeZero n] : Matrix (QuditTriple n) (QuditTriple n) ℂ :=
  TensorGate (quditSUM n)ᴴ (1:Operator n)
/-- The adjoint qudit Fourier transform on register `a`, with identities on the other registers. -/
noncomputable def quditHaInvB (n : ℕ) [NeZero n] : Matrix (QuditTriple n) (QuditTriple n) ℂ :=
  TensorGate (TensorGate (QFTMatrix n)ᴴ (1:Operator n)) (1:Operator n)
/-- Bob's lifted Weyl shift by the negative of Alice's second outcome index. -/
noncomputable def quditBobXB (n : ℕ) [NeZero n] (o : Fin n × Fin n) :
    Matrix (QuditTriple n) (QuditTriple n) ℂ :=
  TensorGate (1:Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (quditX n (-((ZMod.finEquiv n) o.2)))
/-- Bob's lifted Weyl phase operator parameterized by Alice's first outcome index. -/
noncomputable def quditBobZB (n : ℕ) [NeZero n] (o : Fin n × Fin n) :
    Matrix (QuditTriple n) (QuditTriple n) ℂ :=
  TensorGate (1:Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (quditZ n ((ZMod.finEquiv n) o.1))
/-- Embeds an input qudit into register `a` with registers `b` and `c` initialized to zero. -/
noncomputable def quditInitialFrame (n : ℕ) [NeZero n] : Matrix (Fin (n*n*n)) (Fin n) ℂ :=
  fun r j => let t := (quditRegisterEquiv n).symm r
    if t.1.1=j ∧ t.1.2=0 ∧ t.2=0 then 1 else 0
/-- The input embedding after Fourier transformation on `b` and controlled addition from `b` to
`c` prepare the entangled resource. -/
noncomputable def quditPreparedFrame (n : ℕ) [NeZero n] : Matrix (Fin (n*n*n)) (Fin n) ℂ :=
  relabelGate (quditRegisterEquiv n) (quditSUMbcB n*quditHbB n)*quditInitialFrame n
/-- Bob's uncorrected branch operator obtained by inverse SUM and inverse Fourier decoding and
selecting Alice's outcome pair. -/
noncomputable def quditBranchKraus (n : ℕ) [NeZero n] (o : Fin n × Fin n) : Operator n :=
  fun k j =>
    (relabelGate (quditRegisterEquiv n) (quditHaInvB n*quditSUMabInvB n)*quditPreparedFrame n)
      ((quditRegisterEquiv n) (o,k)) j
/-- The outcome dependent Weyl correction `Z(a) * X(-b)` for Alice's outcome pair `(a, b)`. -/
noncomputable def quditCorrection (n : ℕ) [NeZero n] (o : Fin n × Fin n) : Operator n :=
  quditZ n ((ZMod.finEquiv n) o.1)*quditX n (-((ZMod.finEquiv n) o.2))

/-- The permutation matrix associated with an equivalence of a finite index type is unitary. -/
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

/-- The equivalence of `Fin n` given by translation by `b` modulo `n`, with inverse translation
by `-b`. -/
def quditShiftEquiv (n : ℕ) [NeZero n] (b : ZMod n) : Fin n ≃ Fin n where
  toFun y := (ZMod.finEquiv n).symm ((ZMod.finEquiv n) y+b)
  invFun x := (ZMod.finEquiv n).symm ((ZMod.finEquiv n) x-b)
  left_inv y := by simp
  right_inv x := by simp

/-- The Weyl shift matrix is the permutation matrix for modular translation. -/
theorem quditX_perm (n : ℕ) [NeZero n] (b : ZMod n) : quditX n b = permMatrix (quditShiftEquiv n b) := by
  ext x y
  unfold quditX permMatrix
  simp only [Matrix.of_apply,quditShiftEquiv,Equiv.coe_fn_mk]
  congr 1
  exact propext (Equiv.apply_eq_iff_eq_symm_apply (ZMod.finEquiv n).toEquiv)

/-- Every qudit Weyl shift matrix is unitary. -/
theorem quditX_unitary (n : ℕ) [NeZero n] (b : ZMod n) : quditX n b ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [quditX_perm]
  exact qudit_equiv_perm_unitary _

/-- Every qudit Weyl phase matrix is unitary. -/
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

/-- The equivalence sending `(a, b)` to `(a, b + a)` modulo `n`, with inverse given by
subtraction. -/
def quditSumEquiv (n : ℕ) [NeZero n] : (Fin n × Fin n) ≃ (Fin n × Fin n) where
  toFun y := (y.1,quditAdd n y.2 y.1)
  invFun x := (x.1,(ZMod.finEquiv n).symm ((ZMod.finEquiv n) x.2-(ZMod.finEquiv n) x.1))
  left_inv y := by simp [quditAdd]
  right_inv x := by simp [quditAdd]

/-- The qudit controlled modular addition matrix is unitary. -/
theorem quditSUM_unitary (n : ℕ) [NeZero n] : quditSUM n ∈ Matrix.unitaryGroup (Fin n × Fin n) ℂ := by
  have he : quditSUM n = permMatrix (quditSumEquiv n) := by
    ext ⟨a,b⟩ ⟨c,d⟩
    simp [quditSUM,permMatrix,quditSumEquiv,Prod.ext_iff]
  rw [he]
  exact qudit_equiv_perm_unitary _

/-- The standard maximally entangled qudit resource vector is normalized in positive dimension. -/
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

/-- The initial qudit input embedding frame is an isometry. -/
theorem quditInitialFrame_isometry (n : ℕ) [NeZero n] : IsIsometry (quditInitialFrame n) := by
  change (quditInitialFrame n)ᴴ*quditInitialFrame n = 1
  ext i j
  rw [Matrix.mul_apply,← (quditRegisterEquiv n).sum_comp]
  simp [quditInitialFrame,Matrix.conjTranspose_apply,Fintype.sum_prod_type,Matrix.one_apply,eq_comm,ite_and]

/-- In every positive dimension, the qudit resource is normalized, the initial frame is an
isometry, and the Weyl shift, phase, and SUM gates are unitary
[BennettEtAl1993Teleportation]. -/
theorem qudit_resource_and_weyl_access_laws : ∀ (n : ℕ) [NeZero n],
  Normalized (quditResource n) ∧ IsIsometry (quditInitialFrame n) ∧
  (∀ (b : ZMod n), quditX n b ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
  (∀ (a : ZMod n), quditZ n a ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
  quditSUM n ∈ Matrix.unitaryGroup (Fin n × Fin n) ℂ := by
  intro n _
  exact ⟨quditResource_normalized n,quditInitialFrame_isometry n,quditX_unitary n,quditZ_unitary n,quditSUM_unitary n⟩

/-- A permutation matrix acts on vector coordinates by precomposition with the inverse
equivalence. -/
theorem qudit_perm_apply {I : Type} [Fintype I] [DecidableEq I] (e : I ≃ I) (ψ : QState I) (x : I) :
    ApplyGate (permMatrix e) ψ x = ψ (e.symm x) := by
  simp only [ApplyGate,permMatrix,Matrix.mulVec,dotProduct,Matrix.of_apply]
  rw [Finset.sum_eq_single (e.symm x)]
  · simp
  · intro j hj hn
    have hx : x ≠ e j := by intro he; apply hn; rw [he]; simp
    simp [hx]
  · simp

/-- The conjugate transpose of a permutation matrix is the permutation matrix of the inverse
equivalence. -/
theorem qudit_perm_adjoint {I : Type} [Fintype I] [DecidableEq I] (e : I ≃ I) :
    (permMatrix e)ᴴ = permMatrix e.symm := by
  ext x y
  simp only [Matrix.conjTranspose_apply,permMatrix,Matrix.of_apply]
  have he : (y = e x) ↔ x = e.symm y := by rw [eq_comm]; exact Equiv.apply_eq_iff_eq_symm_apply e
  simp [he]

/-- The tensor product of two permutation matrices is the permutation matrix for the product
equivalence. -/
theorem qudit_tensor_perm {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ I) (f : J ≃ J) : TensorGate (permMatrix e) (permMatrix f) = permMatrix (e.prodCongr f) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  simp only [tensorGate_apply,permMatrix,Matrix.of_apply,Equiv.prodCongr_apply]
  by_cases h1 : a = e c <;> by_cases h2 : b = f d <;> simp [h1,h2]

/-- The three register equivalence that adds register `b` to register `c` modulo `n` and fixes
Alice's registers. -/
def quditSumBcEquiv (n : ℕ) [NeZero n] : QuditTriple n ≃ QuditTriple n where
  toFun y := (y.1,quditAdd n y.2 y.1.2)
  invFun x := (x.1,(ZMod.finEquiv n).symm ((ZMod.finEquiv n) x.2-(ZMod.finEquiv n) x.1.2))
  left_inv y := by simp [quditAdd]
  right_inv x := by simp [quditAdd]

/-- The lifted SUM gate from `b` to `c` is the permutation matrix of `quditSumBcEquiv`. -/
theorem quditSUMbc_perm (n : ℕ) [NeZero n] : quditSUMbcB n = permMatrix (quditSumBcEquiv n) := by
  ext ⟨⟨a,b⟩,c⟩ ⟨⟨d,e⟩,f⟩
  simp [quditSUMbcB,relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,TensorGate,Matrix.kroneckerMap_apply,
    quditSUM,permMatrix,quditSumBcEquiv,Matrix.one_apply,Prod.ext_iff,ite_and,and_assoc]
  split_ifs <;> simp_all

/-- Each initial frame column is the relabeled basis vector with the given input index and two
zero ancillary indices. -/
theorem quditInitialFrame_column (n : ℕ) [NeZero n] (j : Fin n) :
    (fun r => quditInitialFrame n r j) = relabelState (quditRegisterEquiv n) (Ket ((j,0),0)) := by
  ext r
  simp [quditInitialFrame,relabelState,Ket,Prod.ext_iff,eq_comm,and_assoc]

/-- Expresses a qudit Fourier matrix entry as `1 / √n` times the standard additive character of
the product of its two indices. -/
theorem quditQFT_entry (n : ℕ) [NeZero n] (x y : Fin n) :
    QFTMatrix n x y = (Real.sqrt (n:ℝ):ℂ)⁻¹*ZMod.stdAddChar ((ZMod.finEquiv n) x*(ZMod.finEquiv n) y) := by
  simpa only [RingEquiv.symm_apply_apply] using
      qftMatrix_stdAddChar ((ZMod.finEquiv n) x) ((ZMod.finEquiv n) y)

/-- Fourier transformation on register `b` sends an initialized input basis vector to uniform
amplitudes on `b`, with the input and Bob's zero index fixed. -/
theorem quditHb_seed (n : ℕ) [NeZero n] (j : Fin n) :
    ApplyGate (quditHbB n) (Ket ((j,0),0)) =
      fun r : QuditTriple n => if r.1.1 = j ∧ r.2 = 0 then (Real.sqrt (n:ℝ):ℂ)⁻¹ else 0 := by
  ext ⟨⟨a,b⟩,c⟩
  simp only [ApplyGate]
  rw [mulVec_ket_apply]
  simp only [quditHbB,tensorGate_apply,quditQFT_entry,finEquiv_apply_val]
  simp [Matrix.one_apply,ite_and]
  split_ifs <;> simp_all

/-- Each prepared frame entry is the resource amplitude on registers `b` and `c` when register
`a` equals the input basis index, and is zero otherwise. -/
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

/-- The qudit SUM matrix is the permutation matrix for controlled modular addition. -/
theorem quditSUM_perm (n : ℕ) [NeZero n] : quditSUM n = permMatrix (quditSumEquiv n) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  simp [quditSUM,permMatrix,quditSumEquiv,Prod.ext_iff]

/-- The inverse SUM gate from `a` to `b` acts on amplitudes by adding the output `a` index to
the output `b` index. -/
theorem quditSUMabInv_state (n : ℕ) [NeZero n] (ψ : QState (QuditTriple n)) :
    ApplyGate (quditSUMabInvB n) ψ = fun r => ψ ((r.1.1,quditAdd n r.1.2 r.1.1),r.2) := by
  have hid : (1:Operator n) = permMatrix (Equiv.refl (Fin n)) := by
    ext i j; simp [permMatrix,Matrix.one_apply]
  have he : quditSUMabInvB n = permMatrix ((quditSumEquiv n).symm.prodCongr (Equiv.refl (Fin n))) := by
    rw [quditSUMabInvB,quditSUM_perm,qudit_perm_adjoint,hid,qudit_tensor_perm]
  ext r
  rw [he,qudit_perm_apply]
  rfl

/-- The inverse Fourier gate on register `a` acts by summing against the adjoint Fourier matrix
while fixing the other two register indices. -/
theorem quditHaInv_apply (n : ℕ) [NeZero n] (ψ : QState (QuditTriple n)) (r : QuditTriple n) :
    ApplyGate (quditHaInvB n) ψ r = ∑ j : Fin n,(QFTMatrix n)ᴴ r.1.1 j*ψ ((j,r.1.2),r.2) := by
  rcases r with ⟨⟨a,b⟩,c⟩
  simp only [ApplyGate,Matrix.mulVec,dotProduct,Fintype.sum_prod_type]
  simp only [quditHaInvB,tensorGate_apply,Matrix.one_apply,mul_ite,ite_mul]
  simp

/-- Each prepared frame column is the relabeled product of the input basis vector and the
standard entangled resource vector. -/
theorem quditPreparedFrame_column (n : ℕ) [NeZero n] (j : Fin n) :
    (fun r => quditPreparedFrame n r j) = relabelState (quditRegisterEquiv n)
      (fun r : QuditTriple n => if r.1.1 = j then quditResource n (r.1.2,r.2) else 0) := by
  ext r
  have he := quditPreparedFrame_resource n ((quditRegisterEquiv n).symm r) j
  simpa only [Equiv.apply_symm_apply,relabelState,Function.comp_apply] using he

/-- An adjoint Fourier matrix entry is `1 / √n` times the standard additive character of the
negative product of its indices. -/
theorem quditQFT_adjoint_entry (n : ℕ) [NeZero n] (a j : Fin n) :
    (QFTMatrix n)ᴴ a j = (Real.sqrt (n:ℝ):ℂ)⁻¹*
      ZMod.stdAddChar (-((ZMod.finEquiv n) a*(ZMod.finEquiv n) j)) := by
  rw [Matrix.conjTranspose_apply,quditQFT_entry]
  change (starRingEnd ℂ)
      ((Real.sqrt (n:ℝ):ℂ)⁻¹*ZMod.stdAddChar ((ZMod.finEquiv n) j*(ZMod.finEquiv n) a)) = _
  rw [(starRingEnd ℂ).map_mul,conj_stdAddChar]
  simp [mul_comm]

/-- The product of two inverse square root dimension factors equals `1 / n` in positive
dimension. -/
theorem qudit_sqrt_inverse_square (n : ℕ) [NeZero n] :
    (Real.sqrt (n:ℝ):ℂ)⁻¹*(Real.sqrt (n:ℝ):ℂ)⁻¹ = 1/(n:ℂ) := by
  have hs : (Real.sqrt (n:ℝ):ℂ)^2 = (n:ℂ) := by exact_mod_cast (Real.sq_sqrt (Nat.cast_nonneg n))
  rw [← mul_inv,← pow_two,hs,one_div]

/-- The decoded frame has amplitude `1 / n` times the negative Fourier phase when Bob's index is
the input index plus Alice's second index, and zero otherwise. -/
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

/-- Computes an entry of a Weyl shift followed by a phase operator as the phase character times
the indicator of the modular shift. -/
theorem quditXZ_entry (n : ℕ) [NeZero n] (b a : ZMod n) (k j : Fin n) :
    (quditX n b*quditZ n a) k j =
      if (ZMod.finEquiv n) k=(ZMod.finEquiv n) j+b then ZMod.stdAddChar (a*(ZMod.finEquiv n) j) else 0 := by
  rw [quditZ,Matrix.mul_diagonal]
  simp [quditX]

/-- The decoded qudit branch operator is `1 / n` times the Weyl product `X(b) * Z(-a)` for
Alice's outcome `(a, b)`. -/
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

/-- The adjoint of a Weyl shift is the shift with negated parameter. -/
theorem quditX_adjoint (n : ℕ) [NeZero n] (b : ZMod n) : (quditX n b)ᴴ = quditX n (-b) := by
  rw [quditX_perm,qudit_perm_adjoint,quditX_perm]
  congr 1
  ext x
  simp [quditShiftEquiv,sub_eq_add_neg]

/-- The adjoint of a Weyl phase operator is the phase operator with negated parameter. -/
theorem quditZ_adjoint (n : ℕ) [NeZero n] (a : ZMod n) : (quditZ n a)ᴴ = quditZ n (-a) := by
  rw [quditZ,Matrix.diagonal_conjTranspose,quditZ]
  congr 1
  funext x
  change (starRingEnd ℂ) (ZMod.stdAddChar (a*(ZMod.finEquiv n) x)) = _
  rw [conj_stdAddChar,neg_mul]

/-- Bob's Weyl correction cancels its decoded branch operator to `1 / n` times the identity. -/
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

/-- Collects the prepared resource frame identity, the decoded Weyl branch formula, and
cancellation of each branch by Bob's correction to `1 / n` times the identity
[BennettEtAl1993Teleportation]. -/
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
