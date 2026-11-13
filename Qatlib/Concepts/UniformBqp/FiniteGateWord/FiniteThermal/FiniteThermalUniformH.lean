/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermal.FiniteThermalNativeInverse
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermal.FiniteThermalComparator
import Mathlib.Order.Interval.Finset.Fin

/-!
# Finite Hadamard words and uniform registers

`thermalLocalProduct` builds register matrices from single-qubit factors, and
`thermalUniformHWord` implements a Hadamard mask on distinct wires. The module computes uniform
amplitudes, counts binary values in intervals, and proves commutation with projectors onto clean
disjoint wires. The background is described in [NielsenChuang2010].

## Main statements

* `thermalUniformHWord_all`: the word on every wire realizes `HadamardN`.
* `thermalUniformHWord_zero_column`: explicit uniform amplitudes from clean selected wires.
* `thermalUniformBits_interval_sum`: binary interval counting.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
open Qatlib Matrix
open scoped BigOperators

/-- Relabeling a finite matrix by an equivalence preserves matrix multiplication. -/
private theorem relabel_mul {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (e : I≃J) (A B : Matrix I I ℂ) :
    Qatlib.Foundations.PureStateMath.BornBridge.relabelGate e (A*B)=Qatlib.Foundations.PureStateMath.BornBridge.relabelGate e A*Qatlib.Foundations.PureStateMath.BornBridge.relabelGate e B := by
  ext i j
  simp only [Qatlib.Foundations.PureStateMath.BornBridge.relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.mul_apply]
  exact (Equiv.sum_comp e.symm (fun k => A (e.symm i) k*B k (e.symm j))).symm

/-- The tensor product of a family of single-qubit matrices, indexed by Boolean register states. -/
def thermalLocalProduct {n : ℕ} (A : Fin n → Matrix Bool Bool ℂ) : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ :=
  Qatlib.Concepts.PauliClifford.ExactRank.pauliProductDensity (fun i => Qatlib.Foundations.PureStateMath.BornBridge.relabelGate Qatlib.Foundations.PureStateMath.boolEquivFin2 (A i))

/-- An entry of `thermalLocalProduct` is the product of the corresponding single-qubit matrix
entries. -/
theorem thermalLocalProduct_apply {n : ℕ} (A : Fin n → Matrix Bool Bool ℂ) (x y : Qatlib.Foundations.PureStateMath.Reg n) :
    thermalLocalProduct A x y=∏ i,A i (x i) (y i) := by
  simp [thermalLocalProduct,Qatlib.Concepts.PauliClifford.ExactRank.pauliProductDensity,Qatlib.Foundations.PureStateMath.BornBridge.relabelGate]

/-- Multiplication of local tensor products is the local tensor product of the componentwise
matrix products. -/
theorem thermalLocalProduct_mul {n : ℕ} (A B : Fin n → Matrix Bool Bool ℂ) :
    thermalLocalProduct A*thermalLocalProduct B=thermalLocalProduct (fun i => A i*B i) := by
  simp only [thermalLocalProduct,Qatlib.Concepts.PauliClifford.ExactRank.pauliProductDensity_mul,relabel_mul]

/-- Relabeling the identity matrix by an equivalence gives the identity matrix. -/
private theorem relabel_one {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (e : I≃J) : Qatlib.Foundations.PureStateMath.BornBridge.relabelGate e (1 : Matrix I I ℂ)=1 := by
  ext i j
  simp [Qatlib.Foundations.PureStateMath.BornBridge.relabelGate,Matrix.one_apply]

/-- The local tensor product of identity matrices is the identity on the whole register. -/
theorem thermalLocalProduct_one (n : ℕ) :
    thermalLocalProduct (fun _ : Fin n => (1 : Matrix Bool Bool ℂ))=1 := by
  simp only [thermalLocalProduct,relabel_one,Qatlib.Concepts.PauliClifford.ExactRank.pauliProductDensity_one]

/-- A gate acting on a single wire is the local tensor product with that gate on the chosen wire
and identities elsewhere. -/
theorem thermalLocalProduct_wire {n : ℕ} (w : Fin n) (U : Matrix Bool Bool ℂ) :
    Qatlib.Concepts.GateVocabulary.LocalReflectionGates.wireGate n w U=thermalLocalProduct (fun i => if i=w then U else 1) := by
  ext x y
  simp only [Qatlib.Concepts.GateVocabulary.LocalReflectionGates.wireGate,Qatlib.Concepts.ShadowModels.ShadowChannel.tensorPauliWireGate,Qatlib.Concepts.PauliClifford.ExactRank.tensorPauliProduct,Qatlib.Foundations.PureStateMath.BornBridge.relabelGate,thermalLocalProduct,
    Qatlib.Concepts.PauliClifford.ExactRank.pauliProductDensity,Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.of_apply,
    Equiv.apply_symm_apply]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i=w <;> simp [hi,Matrix.one_apply]

/-- The finite gate word applying a Hadamard gate to each wire in the given list, in list order. -/
def thermalUniformHWord {n : ℕ} (cs : List (Fin n)) : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode :=
  cs.map (fun w => .h w.val)

/-- The tensor product acting by Hadamard on wires belonging to `cs` and by the identity on all
other wires. -/
def thermalUniformHMatrix {n : ℕ} (cs : List (Fin n)) : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ :=
  thermalLocalProduct (fun i => if i∈cs then Qatlib.Foundations.PureStateMath.Hadamard else 1)

/-- Multiplying the masked Hadamard matrix by a Hadamard on a wire outside the mask adds that
wire to the mask. -/
private theorem mask_cons {n : ℕ} (w : Fin n) (cs : List (Fin n)) (hw : w∉cs) :
    thermalUniformHMatrix cs*Qatlib.Concepts.GateVocabulary.LocalReflectionGates.wireGate n w Qatlib.Foundations.PureStateMath.Hadamard=thermalUniformHMatrix (w::cs) := by
  rw [thermalLocalProduct_wire]
  simp only [thermalUniformHMatrix,thermalLocalProduct_mul]
  congr 1
  funext i
  by_cases hi : i=w
  · subst i
    simp [hw]
  · by_cases hc : i∈cs <;> simp [hi,hc]

/-- For a list of distinct wires, the finite Hadamard word has matrix `thermalUniformHMatrix
cs`. -/
theorem thermalUniformHWord_matrix {n : ℕ} (cs : List (Fin n)) (hn : cs.Nodup) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalUniformHWord cs)=thermalUniformHMatrix cs := by
  induction cs with
  | nil => exact (thermalLocalProduct_one n).symm
  | cons w cs ih =>
    have hs : thermalUniformHWord (w::cs)=[.h w.val]++thermalUniformHWord cs := rfl
    have hm : Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n [.h w.val]=Qatlib.Concepts.GateVocabulary.LocalReflectionGates.wireGate n w Qatlib.Foundations.PureStateMath.Hadamard := by
      simp [Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeMatrix,w.isLt]
    rw [hs,thermalWordMatrix_append,ih hn.tail,hm,mask_cons w cs (List.nodup_cons.mp hn).1]

/-- Applying the finite Hadamard word to all register wires gives the full tensor Hadamard
matrix. -/
theorem thermalUniformHWord_all (n : ℕ) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalUniformHWord (List.finRange n))=Qatlib.Foundations.PureStateMath.HadamardN n := by
  rw [thermalUniformHWord_matrix _ (List.nodup_finRange n)]
  ext x y
  simp [thermalUniformHMatrix,thermalLocalProduct_apply,Qatlib.Foundations.PureStateMath.HadamardN]

/-- The binary value of concatenated bit lists is the first value shifted by the length of the
second list, plus the second value. -/
theorem thermalBitValue_append (xs ys : List Bool) :
    thermalBitValue (xs++ys)=thermalBitValue xs*2^ys.length+thermalBitValue ys := by
  induction xs with
  | nil => simp [thermalBitValue]
  | cons b xs ih =>
    cases b <;> simp [thermalBitValue,List.length_append,pow_add,ih]
    ring

/-- The binary value of the list of register bits equals its value under `bitVecEquiv`. -/
theorem thermalBitValue_ofFn (b : ℕ) (x : Qatlib.Foundations.PureStateMath.Reg b) :
    thermalBitValue (List.ofFn x)=(Qatlib.Foundations.PureStateMath.bitVecEquiv b x).val := by
  induction b with
  | zero => simp [thermalBitValue]
  | succ b ih =>
    let pre : Qatlib.Foundations.PureStateMath.Reg b := fun i => x i.castSucc
    have he : (Qatlib.Foundations.PureStateMath.bitVecEquiv (b+1) x).val=
        2*(Qatlib.Foundations.PureStateMath.bitVecEquiv b pre).val+(if x (Fin.last b) then 1 else 0) := by
      change (Qatlib.Foundations.PureStateMath.boolEquivFin2 (x (Fin.last b))).val+2*(Qatlib.Foundations.PureStateMath.bitVecEquiv b pre).val=_
      cases x (Fin.last b) <;> simp
          [Qatlib.Foundations.PureStateMath.boolEquivFin2,Nat.add_comm]
    rw [List.ofFn_succ',List.concat_eq_append,thermalBitValue_append]
    change thermalBitValue (List.ofFn pre)*2+thermalBitValue [x (Fin.last b)]=_
    rw [ih,he]
    simp [thermalBitValue,Nat.mul_comm]

/-- Summing a function of binary value over all Boolean registers equals summing it over the
integers below `2^b`. -/
theorem thermalUniformBits_sum {M : Type*} [AddCommMonoid M] (b : ℕ) (f : ℕ → M) :
    (∑ x : Qatlib.Foundations.PureStateMath.Reg b,f (thermalBitValue (List.ofFn x)))=
      ∑ k : Fin (2^b),f k.val := by
  simp_rw [thermalBitValue_ofFn]
  exact Equiv.sum_comp (Qatlib.Foundations.PureStateMath.bitVecEquiv b) (fun k => f k.val)

/-- Every Hadamard word built from register wires is legal for that register size. -/
theorem thermalUniformHWord_legal {n : ℕ} (cs : List (Fin n)) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalUniformHWord cs)=true := by
  simp only [thermalUniformHWord,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,List.all_map,List.all_eq_true]
  intro w _
  simp [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal,w.isLt]

/-- The finite Hadamard word uses exactly one gate per listed wire and no oracle queries. -/
theorem thermalUniformHWord_cost {n : ℕ} (cs : List (Fin n)) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalUniformHWord cs))=cs.length ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalUniformHWord cs))=0 := by
  constructor
  · rw [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).2]
    exact List.length_map _
  · exact (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).1

/-- For a list of distinct wires, the masked Hadamard matrix is unitary. -/
theorem thermalUniformHMatrix_unitary {n : ℕ} (cs : List (Fin n)) (hn : cs.Nodup) :
    thermalUniformHMatrix cs ∈ Matrix.unitaryGroup (Qatlib.Foundations.PureStateMath.Reg n) ℂ := by
  rw [← thermalUniformHWord_matrix cs hn]
  exact (Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_code_word_determinant_invariant n _ (thermalUniformHWord_legal cs)).1

/-- Exactly `t` Boolean registers of width `b` have binary value below `t`, provided `t ≤ 2^b`. -/
theorem thermalUniformBits_less_nat (b t : ℕ) (ht : t≤2^b) :
    (∑ x : Qatlib.Foundations.PureStateMath.Reg b,if thermalBitValue (List.ofFn x)<t then (1:ℕ) else 0)=t := by
  rw [thermalUniformBits_sum b (fun v : ℕ => if v<t then (1:ℕ) else 0)]
  by_cases hlt : t<2^b
  · have he : (Finset.univ.filter (fun k : Fin (2^b) => k.val<t))=
        Finset.Iio (⟨t,hlt⟩ : Fin (2^b)) := by
      ext k
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio]
      rfl
    rw [Finset.sum_boole,he,Fin.card_Iio]
    simp
  · have he : t=2^b := by omega
    subst t
    simp

/-- The complex-valued sum of indicators for binary values below `t` equals `t`, provided `t ≤
2^b`. -/
theorem thermalUniformBits_less_complex (b t : ℕ) (ht : t≤2^b) :
    (∑ x : Qatlib.Foundations.PureStateMath.Reg b,if thermalBitValue (List.ofFn x)<t then (1:ℂ) else 0)=(t:ℂ) := by
  exact_mod_cast thermalUniformBits_less_nat b t ht

/-- The complex-valued count of binary values in the interval from `lo` inclusive to `hi`
exclusive is `hi - lo`, when the interval lies within the register range. -/
theorem thermalUniformBits_interval_sum (b lo hi : ℕ) (horder : lo≤hi) (hhi : hi≤2^b) :
    (∑ x : Qatlib.Foundations.PureStateMath.Reg b,if lo≤thermalBitValue (List.ofFn x) ∧ thermalBitValue (List.ofFn x)<hi
      then (1:ℂ) else 0)=((hi-lo:ℕ):ℂ) := by
  have he (v : ℕ) : (if lo≤v ∧ v<hi then (1:ℂ) else 0)=
      (if v<hi then 1 else 0)-(if v<lo then 1 else 0) := by
    by_cases ha : v<lo <;> by_cases hb : v<hi
    all_goals simp [ha,hb] <;> omega
  simp_rw [he]
  rw [Finset.sum_sub_distrib,thermalUniformBits_less_complex b hi hhi,
    thermalUniformBits_less_complex b lo (horder.trans hhi),Nat.cast_sub horder]

/-- For distinct Hadamard wires that are zero in the input, each output agreeing with the input
on all other wires has amplitude `(1 / sqrt 2)^cs.length`, and all other outputs have
amplitude zero. -/
theorem thermalUniformHMatrix_zero_column {n : ℕ} (cs : List (Fin n)) (hn : cs.Nodup)
    (x y : Qatlib.Foundations.PureStateMath.Reg n) (hy : ∀ w∈cs,y w=false) :
    thermalUniformHMatrix cs x y=
      if ∀ w : Fin n,w∉cs → x w=y w then ((Real.sqrt 2:ℂ)⁻¹)^cs.length else 0 := by
  rw [thermalUniformHMatrix,thermalLocalProduct_apply]
  by_cases ho : ∀ w : Fin n,w∉cs → x w=y w
  · rw [if_pos ho]
    have hf (w : Fin n) : (if w∈cs then Qatlib.Foundations.PureStateMath.Hadamard else (1:Matrix Bool Bool ℂ)) (x w) (y w)=
        if w∈cs then (Real.sqrt 2:ℂ)⁻¹ else 1 := by
      by_cases hw : w∈cs
      · rw [if_pos hw,if_pos hw,hy w hw,Qatlib.Foundations.PureStateMath.hadamard_apply_false]
      · rw [if_neg hw,if_neg hw,Matrix.one_apply,if_pos (ho w hw)]
    simp_rw [hf]
    rw [← Finset.prod_filter]
    have hs : (Finset.univ.filter (fun w : Fin n => w∈cs))=cs.toFinset := by ext w;simp
    rw [hs,Finset.prod_const,List.toFinset_card_of_nodup hn]
  · rw [if_neg ho]
    obtain ⟨w,hwn,hxy⟩ : ∃ w : Fin n,w∉cs ∧ x w≠y w := by
      simpa only [not_forall,exists_prop] using ho
    apply Finset.prod_eq_zero (Finset.mem_univ w)
    rw [if_neg hwn,Matrix.one_apply,if_neg hxy]

/-- An entry of the masked Hadamard matrix vanishes if its two basis labels differ on a wire
outside the mask. -/
theorem thermalUniformHMatrix_off_support {n : ℕ} (cs : List (Fin n)) (x y : Qatlib.Foundations.PureStateMath.Reg n)
    (h : ¬∀ w : Fin n,w∉cs → x w=y w) : thermalUniformHMatrix cs x y=0 := by
  rw [thermalUniformHMatrix,thermalLocalProduct_apply]
  obtain ⟨w,hwn,hxy⟩ : ∃ w : Fin n,w∉cs ∧ x w≠y w := by
    simpa only [not_forall,exists_prop] using h
  apply Finset.prod_eq_zero (Finset.mem_univ w)
  rw [if_neg hwn,Matrix.one_apply,if_neg hxy]

/-- The diagonal projector onto basis states whose wires in `ws` are all zero. -/
def thermalCleanProjector {n : ℕ} (ws : List (Fin n)) : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ :=
  Matrix.diagonal (fun x => if ∀ w∈ws,x w=false then 1 else 0)

/-- The projector onto states with zero bits on `ws` is idempotent. -/
theorem thermalCleanProjector_idempotent {n : ℕ} (ws : List (Fin n)) :
    thermalCleanProjector ws*thermalCleanProjector ws=thermalCleanProjector ws := by
  simp only [thermalCleanProjector,Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  by_cases hc : ∀ w∈ws,x w=false <;> simp [hc]

/-- The masked Hadamard matrix commutes with the zero-bit projector on a disjoint list of wires. -/
theorem thermalUniformHMatrix_clean_commute {n : ℕ} (cs ws : List (Fin n)) (hd : List.Disjoint cs ws) :
    thermalUniformHMatrix cs*thermalCleanProjector ws=
      thermalCleanProjector ws*thermalUniformHMatrix cs := by
  ext x y
  simp only [thermalCleanProjector,Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases ho : ∀ w : Fin n,w∉cs → x w=y w
  · have he : (∀ w∈ws,x w=false) ↔ (∀ w∈ws,y w=false) := by
      have hn (w : Fin n) (hw : w∈ws) : w∉cs := fun hc => (List.disjoint_left.mp hd) hc hw
      constructor
      · intro h w hw
        simpa only [← ho w (hn w hw)] using h w hw
      · intro h w hw
        simpa only [ho w (hn w hw)] using h w hw
    simp only [he]
    ring
  · rw [thermalUniformHMatrix_off_support cs x y ho]
    simp

/-- For distinct Hadamard wires, the compiled Hadamard word commutes with the zero-bit projector
on disjoint wires. -/
theorem thermalUniformHWord_clean_commute {n : ℕ} (cs ws : List (Fin n))
    (hn : cs.Nodup) (hd : List.Disjoint cs ws) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalUniformHWord cs)*thermalCleanProjector ws=
      thermalCleanProjector ws*Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalUniformHWord cs) := by
  rw [thermalUniformHWord_matrix cs hn]
  exact thermalUniformHMatrix_clean_commute cs ws hd

/-- Running the finite Hadamard word on an input zero on its distinct selected wires gives
uniform amplitude on outputs agreeing with the input elsewhere. -/
theorem thermalUniformHWord_zero_column {n : ℕ} (cs : List (Fin n)) (hn : cs.Nodup)
    (x y : Qatlib.Foundations.PureStateMath.Reg n) (hy : ∀ w∈cs,y w=false) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalUniformHWord cs))
      (Qatlib.Foundations.PureStateMath.Ket y) x =
      if ∀ w : Fin n,w∉cs → x w=y w then ((Real.sqrt 2:ℂ)⁻¹)^cs.length else 0 := by
  have h := thermalUniformHMatrix_zero_column cs hn x y hy
  rw [← thermalUniformHWord_matrix cs hn] at h
  simpa [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run,Qatlib.Foundations.PureStateMath.ApplyGate,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket] using h

end Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
