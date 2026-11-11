/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationInstrument

/-!
# Qudit teleportation messages and reference recovery

This module gives fixed width binary messages for qudit outcomes and proves decoding and
injectivity when each index fits the chosen width. It records the observed circuit's exact
counts and proves recovery of arbitrary operators with a finite reference, extending the
protocol setting of [BennettEtAl1993Teleportation].

The examples include a maximally entangled qutrit density, an uncorrected branch that shifts a
basis state, correct decoding with two bits per qutrit index, and the identity branch in
dimension one.

## Main statements

* `qudit_actual_fixed_width_message`: message length, decoding, injectivity, and a logarithmic
  width bound.
* `qudit_actual_program_legality_and_counts`: circuit validity and six gates per leaf.
* `qudit_actual_entangled_reference_recovery`: uniform branches and summed recovery with a
  reference.
* `qudit_qutrit_entangled_and_trivial_consumers`: qutrit and dimension one examples.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Concepts.QuditTeleport.TeleportCore
open Matrix
open scoped Classical BigOperators ComplexOrder Kronecker

/-- Encodes the lowest `k` bits of `x` as a Boolean list, with the least significant bit first. -/
def quditEncode (k : ℕ) (x : ℕ) : List Bool :=
  List.ofFn (fun i : Fin k => x.testBit i.val)
/-- Concatenates the `k` bit encodings of the two qudit outcome indices. -/
def quditMessage (n k : ℕ) (o : Fin n × Fin n) : List Bool :=
  quditEncode k o.1.val ++ quditEncode k o.2.val

/-- Interprets a Boolean list as a natural number with the least significant bit first. -/
def quditDecodeNat (s : List Bool) : ℕ := s.foldr (fun b v => (if b then 1 else 0)+2*v) 0

/-- Decodes a list of length `2 * k` into two `k` bit indices, returning an outcome only when
both decoded values are below `n`. -/
def quditDecodeMessage (n k : ℕ) (s : List Bool) : Option (Fin n × Fin n) :=
  if _hlen : s.length=2*k then
    let a := quditDecodeNat (s.take k)
    let b := quditDecodeNat (s.drop k)
    if ha : a<n then if hb : b<n then some (⟨a,ha⟩,⟨b,hb⟩) else none else none
  else none

/-- An encoding of width `k + 1` consists of the lowest bit followed by the width `k` encoding
of `x / 2`. -/
theorem quditEncode_succ (k x : ℕ) : quditEncode (k+1) x = x.testBit 0 :: quditEncode k (x/2) := by
  simp [quditEncode,List.ofFn_succ,Nat.testBit_succ]

/-- The natural value of the lowest bit of `x` equals `x % 2`. -/
theorem qudit_low_bit (x : ℕ) : (if x.testBit 0 then 1 else 0) = x%2 := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [Nat.testBit_zero,h]

/-- Splits reduction modulo `2^(k + 1)` into the lowest bit and twice the remaining `k` bit
residue. -/
theorem qudit_mod_split (k x : ℕ) : x%2^(k+1) = x%2+2*((x/2)%2^k) := by
  have hp : 0 < 2^k := by positivity
  have hrem := Nat.mod_lt (x/2) hp
  have hbit := Nat.mod_lt x (by decide : 0 < 2)
  have ha : x%2+2*((x/2)%2^k) < 2^(k+1) := by rw [pow_succ]; omega
  have he : x = (2^(k+1))*((x/2)/2^k)+(x%2+2*((x/2)%2^k)) := by
    have h1 := Nat.div_add_mod x 2
    have h2 := Nat.div_add_mod (x/2) (2^k)
    rw [pow_succ]
    nlinarith
  conv_lhs => rw [he]
  simp [Nat.add_mod,Nat.mod_eq_of_lt ha]

/-- Decoding the width `k` encoding of `x` returns `x % 2^k`. -/
theorem quditDecodeNat_encode (k x : ℕ) : quditDecodeNat (quditEncode k x) = x%2^k := by
  induction k generalizing x with
  | zero => simpa [quditEncode,quditDecodeNat] using (Nat.mod_one x).symm
  | succ k ih =>
    rw [quditEncode_succ]
    change (if x.testBit 0 then 1 else 0)+2*quditDecodeNat (quditEncode k (x/2)) = _
    rw [ih,qudit_low_bit]
    exact (qudit_mod_split k x).symm

/-- Decoding the width `k` encoding of a number below `2^k` returns that number. -/
theorem quditDecodeNat_exact (k x : ℕ) (hx : x < 2^k) : quditDecodeNat (quditEncode k x) = x := by
  rw [quditDecodeNat_encode,Nat.mod_eq_of_lt hx]

/-- If the dimension fits in `k` bits, every encoded outcome message has length `2 * k` and
decodes to that outcome. -/
theorem quditMessage_decode (n k : ℕ) (hw : n ≤ 2^k) (o : Fin n × Fin n) :
    (quditMessage n k o).length = 2*k ∧ quditDecodeMessage n k (quditMessage n k o) = some o := by
  have hl (x : ℕ) : (quditEncode k x).length = k := by simp [quditEncode]
  have hlen : (quditMessage n k o).length = 2*k := by simp [quditMessage,hl,← two_mul]
  refine ⟨hlen,?_⟩
  have ht : (quditMessage n k o).take k = quditEncode k o.1.val := by
    unfold quditMessage
    exact List.take_left' (hl o.1.val)
  have hd : (quditMessage n k o).drop k = quditEncode k o.2.val := by
    unfold quditMessage
    exact List.drop_left' (hl o.1.val)
  have ha := quditDecodeNat_exact k o.1.val (o.1.isLt.trans_le hw)
  have hb := quditDecodeNat_exact k o.2.val (o.2.isLt.trans_le hw)
  simp only [quditDecodeMessage,hlen,dite_true,ht,hd,ha,hb,o.1.isLt,o.2.isLt]

/-- When `n ≤ 2^k`, qudit outcome messages have length `2 * k`, decode correctly, and
distinguish all `n²` outcomes. Also records the bound `n ≤ 2 ^ Nat.clog 2 n` for choosing a
width [BennettEtAl1993Teleportation]. -/
theorem qudit_actual_fixed_width_message : ∀ (n k : ℕ) (_hwidth : n ≤ 2^k),
  (∀ o : Fin n × Fin n,
    (quditMessage n k o).length=2*k ∧ quditDecodeMessage n k (quditMessage n k o)=some o) ∧
  Function.Injective (quditMessage n k) ∧ Fintype.card (Fin n × Fin n)=n*n ∧
  n ≤ 2^(Nat.clog 2 n) := by
  intro n k hw
  refine ⟨quditMessage_decode n k hw,?_,by simp,Nat.le_pow_clog (by decide) n⟩
  intro a b he
  have hd := congrArg (quditDecodeMessage n k) he
  rw [(quditMessage_decode n k hw a).2,(quditMessage_decode n k hw b).2] at hd
  exact Option.some.inj hd

/-- The outer product of the standard maximally entangled qudit resource vector. -/
noncomputable def quditEntangledDensity (n : ℕ) [NeZero n] :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  matOuter (quditResource n) (quditResource n)

/-- In every positive dimension the qudit program is well formed, has `n²` leaves, and
enumerates them by the outcome encoding. Each leaf is accepted with zero queries, six gates,
one measurement, and its encoded outcome record [BennettEtAl1993Teleportation]. -/
theorem qudit_actual_program_legality_and_counts : ∀ (n : ℕ) [NeZero n],
  observedWellFormed (quditProgram n) ∧ observedLeafCount (quditProgram n)=n*n ∧
  observedKrausLeaves 1 (quditProgram n)=
    List.ofFn (fun k : Fin (n*n) => quditProgramLeaf n ((quditOutcomeEquiv n).symm k)) ∧
  ∀ o : Fin n × Fin n,
    (quditProgramLeaf n o).accepted=true ∧ (quditProgramLeaf n o).queries=0 ∧
    (quditProgramLeaf n o).gates=6 ∧ (quditProgramLeaf n o).measurements=1 ∧
    (quditProgramLeaf n o).outcomes=[(n*n,((quditOutcomeEquiv n) o).val)] := by
  intro n _
  refine ⟨quditProgram_wellFormed n,quditProgram_leaf_count n,?_,quditProgramLeaf_counts n⟩
  rw [quditProgram_leaves]
  congr 1
  funext k
  rw [quditProgramLeaf_generated,Equiv.apply_symm_apply]

/-- Regroups a flattened teleportation register and a reference into Alice's outcome pair
followed by Bob's register paired with the reference. -/
def quditReferenceEquiv (n R : ℕ) : Fin (n*n*n) × Fin R ≃ (Fin n × Fin n) × (Fin n × Fin R) :=
  (Equiv.prodCongr (quditRegisterEquiv n).symm (Equiv.refl (Fin R))).trans
    (Equiv.prodAssoc (Fin n × Fin n) (Fin n) (Fin R))

/-- After regrouping rows, the tensor product of an outcome frame with the reference identity is
the frame that fixes Alice's outcome and retains Bob and the reference. -/
theorem quditOutcomeFrame_reference_rows (n R : ℕ) (o : Fin n × Fin n) :
    (quditOutcomeFrame n o ⊗ₖ (1:Operator R)).submatrix (quditReferenceEquiv n R).symm id =
      quditFixedFrame (B:=Fin n × Fin R) o := by
  ext ⟨a,⟨b,r⟩⟩ ⟨j,s⟩
  simp [Matrix.submatrix_apply,quditReferenceEquiv,quditOutcomeFrame,Matrix.kroneckerMap_apply,
    Matrix.one_apply,quditFixedFrame,Prod.ext_iff,ite_and,and_assoc]
  split_ifs <;> simp_all

/-- Every actual qudit branch with a reference register sends the joint operator to `1 / n²`
times itself. -/
theorem quditActualReferenceCore_uniform (n R : ℕ) [NeZero n] (o : Fin n × Fin n)
    (X : Matrix (Fin n × Fin R) (Fin n × Fin R) ℂ) :
    quditActualReferenceCore n R o X = (1/(n:ℂ)^2) • X := by
  let F := quditInitialFrame n ⊗ₖ (1:Operator R)
  let L := TensorGate (quditProgramLeaf n o).operator (1:Operator R)
  have he : L*(F*X*Fᴴ)*Lᴴ = (L*F)*X*(L*F)ᴴ := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  have hf : L*F = (1/(n:ℂ)) • (quditOutcomeFrame n o ⊗ₖ (1:Operator R)) := by
    dsimp [L,F,TensorGate]
    rw [← Matrix.mul_kronecker_mul,Matrix.one_mul,quditProgramLeaf_frame,Matrix.smul_kronecker]
  unfold quditActualReferenceCore
  change Matrix.traceLeft (relabelGate (quditReferenceEquiv n R) (L*(F*X*Fᴴ)*Lᴴ)) = _
  rw [he,hf,qudit_relabel_frame_sandwich]
  simp only [Matrix.submatrix_smul,Pi.smul_apply,quditOutcomeFrame_reference_rows]
  rw [Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [Matrix.traceLeft_smul,quditFixedFrame_discard]
  congr 1
  exact qudit_scalar_square n

/-- Each actual qudit branch acts as `1 / n²` times the identity on any input and finite
reference operator, and summing the branches recovers that operator
[BennettEtAl1993Teleportation]. -/
theorem qudit_actual_entangled_reference_recovery : ∀ (n R : ℕ) [NeZero n]
    (X : Matrix (Fin n × Fin R) (Fin n × Fin R) ℂ),
  (∀ o : Fin n × Fin n, quditActualReferenceCore n R o X=(1/(n:ℂ)^2) • X) ∧
  (∑ o : Fin n × Fin n, quditActualReferenceCore n R o X)=X := by
  intro n R _ X
  refine ⟨fun o => quditActualReferenceCore_uniform n R o X,?_⟩
  simp only [quditActualReferenceCore_uniform,← Finset.sum_smul,qudit_uniform_scalar_sum,one_smul]

/-- Tracing out the first subsystem of the standard maximally entangled qudit density gives `1 /
n` times the identity. -/
theorem quditEntangledDensity_marginal (n : ℕ) [NeZero n] :
    Matrix.traceLeft (quditEntangledDensity n) = (1/(n:ℂ)) • (1:Operator n) := by
  ext i j
  simp only [quditEntangledDensity,Matrix.traceLeft,Matrix.of_apply,matOuter]
  rw [Finset.sum_eq_single i]
  · have hc : (starRingEnd ℂ) ((Real.sqrt (n:ℝ):ℂ)⁻¹) = (Real.sqrt (n:ℝ):ℂ)⁻¹ := by simp
    by_cases hij : i = j
    · subst j
      simp only [quditResource,ite_true,hc,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one]
      exact qudit_sqrt_inverse_square n
    · simp [quditResource,hij,Matrix.smul_apply,Matrix.one_apply_ne hij]
  · intro k hk hn
    simp [quditResource,hn]
  · simp

/-- The standard maximally entangled qudit outer product is a density operator after flattening
its two register indices. -/
theorem quditEntangledDensity_density (n : ℕ) [NeZero n] :
    IsDensityOperator (relabelGate (quditOutcomeEquiv n) (quditEntangledDensity n)) := by
  have he : relabelGate (quditOutcomeEquiv n) (quditEntangledDensity n) =
      outerProduct (relabelState (quditOutcomeEquiv n) (quditResource n)) := by
    ext i j
    rfl
  rw [he]
  exact isDensityOperator_outerProduct (normalized_relabelState _ (quditResource_normalized n))

/-- The uncorrected qutrit branch with outcome `(0, 1)` sends the zeroth basis vector to one
third of the first basis vector. -/
theorem quditRaw_qutrit_shift : ApplyGate (quditBranchKraus 3 (0,1)) (Qatlib.Foundations.PureStateMath.Ket (0:Fin 3)) =
    (1/3:ℂ) • Qatlib.Foundations.PureStateMath.Ket (1:Fin 3) := by
  ext k
  simp only [ApplyGate]
  rw [mulVec_ket_apply,quditBranchKraus_formula,Matrix.smul_apply,quditXZ_entry]
  fin_cases k <;> norm_num [finEquiv_apply_val,Qatlib.Foundations.PureStateMath.Ket,Pi.smul_apply,smul_eq_mul,AddChar.map_zero_eq_one]
  decide

/-- Collects qutrit density, marginal, uncorrected branch, reference recovery, and message
decoding examples. It also states that the unique branch in dimension one is the identity
[BennettEtAl1993Teleportation]. -/
theorem qudit_qutrit_entangled_and_trivial_consumers :
  IsDensityOperator (relabelGate (quditOutcomeEquiv 3) (quditEntangledDensity 3)) ∧
  Matrix.traceLeft (quditEntangledDensity 3) = (1/3:ℂ) • (1:Operator 3) ∧
  conjBranch (quditBranchKraus 3 (0,1)) (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0:Fin 3))) ≠
    (1/9:ℂ) • outerProduct (Qatlib.Foundations.PureStateMath.Ket (0:Fin 3)) ∧
  (∑ o : Fin 3 × Fin 3,
    quditActualReferenceCore 3 3 o (quditEntangledDensity 3))=quditEntangledDensity 3 ∧
  (∀ o : Fin 3 × Fin 3,
    quditDecodeMessage 3 2 (quditMessage 3 2 o)=some o) ∧
  (∀ rho : Operator 1, quditActualBranchCore 1 (0,0) rho=rho) := by
  refine ⟨quditEntangledDensity_density 3,quditEntangledDensity_marginal 3,?_,
    (qudit_actual_entangled_reference_recovery 3 3 (quditEntangledDensity 3)).2,?_,?_⟩
  · change (quditBranchKraus 3 (0,1)*matOuter (Qatlib.Foundations.PureStateMath.Ket (0:Fin 3)) (Qatlib.Foundations.PureStateMath.Ket (0:Fin 3))*
      (quditBranchKraus 3 (0,1))ᴴ) ≠ _
    rw [matOuter_sandwich,quditRaw_qutrit_shift]
    intro he
    have hz := congrArg (fun M : Operator 3 => M 0 0) he
    norm_num [matOuter,outerProduct,Qatlib.Foundations.PureStateMath.Ket,Pi.smul_apply,Matrix.smul_apply,smul_eq_mul] at hz
  · intro o
    exact (quditMessage_decode 3 2 (by decide) o).2
  · intro rho
    rw [quditActualBranchCore_uniform]
    norm_num

end Qatlib.Concepts.QuditTeleport.TeleportCore
