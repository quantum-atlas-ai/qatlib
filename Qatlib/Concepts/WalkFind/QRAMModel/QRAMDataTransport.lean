/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs
import Qatlib.Concepts.WalkFind.QRAMModel.TruncationHybridQuan
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Mathlib.Data.Nat.Bitwise
open Qatlib.Concepts.BlockEncoding.LinearCombination
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.WalkFind.SearchAlgorithm

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.WalkFind.UniqueCollision

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkFind.QRAMModel
open Matrix Qatlib.Concepts.WalkFind.UniqueCollision
open scoped Classical BigOperators

private theorem dataFlip_hxh : Hadamard * PauliX * Hadamard = PauliZ := by
  ext i j
  cases i <;> cases j <;>
    simp [Hadamard, PauliX, PauliZ, permMatrix, Matrix.mul_apply] <;>
    ring_nf <;> norm_num [sqrt2_sq]

def dataFlagFlip (flag : ℕ) : List SourceCode :=
  [.local (.h flag), .local (.x flag), .local (.h flag)]

theorem dataFlagFlip_legal (b flag : ℕ) (hflag : flag < b) :
    sourceWordLegal b (dataFlagFlip flag) := by
  simp [sourceWordLegal, dataFlagFlip, sourceCodeLegal, finiteCodeLegal, hflag]

theorem dataFlagFlip_queries (b flag : ℕ) :
    QueryCount (sourceCircuit b (dataFlagFlip flag)) = 0 := rfl

theorem dataFlagFlip_length (flag : ℕ) : (dataFlagFlip flag).length = 3 := rfl

theorem dataFlagFlip_unitary (b flag : ℕ) (hflag : flag < b) :
    IsUnitaryCircuit (sourceCircuit b (dataFlagFlip flag)) := by
  intro U hU
  simp only [sourceCircuit, dataFlagFlip, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hU
  rcases hU with h | h | h
  all_goals injection h with h
  all_goals subst U
  · exact finiteCodeMatrix_unitary b (.h flag) (by simp [finiteCodeLegal, hflag])
  · exact finiteCodeMatrix_unitary b (.x flag) (by simp [finiteCodeLegal, hflag])
  · exact finiteCodeMatrix_unitary b (.h flag) (by simp [finiteCodeLegal, hflag])

private theorem dataFlagFlip_wireZ (b : ℕ) (flag : Fin b) :
    wireGate b flag PauliZ = Matrix.diagonal (fun q : Reg b => if q flag then -1 else 1) := by
  ext q p
  have h := congrFun (applyGate_wireGate_ket b flag PauliZ p) q
  change (wireGate b flag PauliZ *ᵥ Qatlib.Foundations.PureStateMath.Ket p) q = _ at h
  rw [mulVec_ket_apply] at h
  by_cases hqp : q = p
  · subst q
    cases hp : p flag
    · have hu : Function.update p flag false = p := by rw [← hp, Function.update_eq_self]
      simpa [PauliZ, hp, hu, Qatlib.Foundations.PureStateMath.Ket,
          Matrix.diagonal_apply] using! h
    · have hu : Function.update p flag true = p := by rw [← hp, Function.update_eq_self]
      simpa [PauliZ, hp, hu, Qatlib.Foundations.PureStateMath.Ket,
          Matrix.diagonal_apply] using! h
  · cases hp : p flag
    · have hu : Function.update p flag false = p := by rw [← hp, Function.update_eq_self]
      simpa [PauliZ, hp, hu, Qatlib.Foundations.PureStateMath.Ket, Matrix.diagonal_apply,
          hqp] using! h
    · have hu : Function.update p flag true = p := by rw [← hp, Function.update_eq_self]
      simpa [PauliZ, hp, hu, Qatlib.Foundations.PureStateMath.Ket, Matrix.diagonal_apply,
          hqp] using! h

theorem dataFlagFlip_semantics (b flag : ℕ) (hflag : flag < b)
    (O : Matrix (Reg b) (Reg b) ℂ) (ψ : QState (Reg b)) :
    Run O (sourceCircuit b (dataFlagFlip flag)) ψ =
      fun q => if q ⟨flag,hflag⟩ then -ψ q else ψ q := by
  simp only [sourceCircuit, dataFlagFlip, List.map_cons, List.map_nil, Run,
    sourceCodeMatrix, finiteCodeMatrix, hflag, ↓reduceDIte]
  rw [← applyGate_mul, ← applyGate_mul, wireGate_mul, wireGate_mul,
    dataFlip_hxh, dataFlagFlip_wireZ]
  ext q
  simp [ApplyGate, Matrix.mulVec_diagonal]

theorem naturalBit_injective_below {a b width : ℕ} (ha : a < 2^width)
    (hb : b < 2^width) (hbits : ∀ i < width, naturalBit a i = naturalBit b i) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < width
  · simpa only [naturalBit, ← Nat.testBit_eq_decide_div_mod_eq] using! hbits i hi
  · have hp : 2^width ≤ 2^i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_eq_false_of_lt (ha.trans_le hp), Nat.testBit_eq_false_of_lt (hb.trans_le hp)]

theorem sum_naturalBit (n width : ℕ) :
    (∑ i ∈ Finset.range width, if naturalBit n i then 2^i else 0) = n % 2^width := by
  induction width with
  | zero => simp [Nat.mod_one]
  | succ width ih =>
    rw [Finset.sum_range_succ, ih, Nat.pow_succ, Nat.mod_mul]
    have hr := Nat.mod_lt (n / 2^width) (by omega : 0 < 2)
    by_cases h : n / 2^width % 2 = 1
    · simp [naturalBit, h]
    · have hz : n / 2^width % 2 = 0 := by omega
      simp [naturalBit, hz]

theorem dataBasis_record_bit {N M r : ℕ} (D : CollisionDataStructure N M r)
    (k w : ℕ) (x : Fin N → ZMod M) (h : Fin (2^D.seedBits)) (p : JRState N r)
    (j : Fin w) :
    dataBasis D k w x h p
      ⟨Nat.clog 2 (N+1)+Nat.clog 2 (M+1)+j.val, by unfold nativeWidth; omega⟩ =
      (D.encode p.val.1 x h)[j.val]?.getD false := by
  have hj := j.isLt
  simp only [dataBasis]
  split_ifs <;> try omega
  simp only [Nat.add_sub_cancel_left]

theorem dataBasis_address_bit {N M r : ℕ} (D : CollisionDataStructure N M r)
    (k w : ℕ) (x : Fin N → ZMod M) (h : Fin (2^D.seedBits)) (p : JRState N r)
    (j : Fin (Nat.clog 2 (N+1))) :
    dataBasis D k w x h p ⟨j.val, by unfold nativeWidth; omega⟩ =
      naturalBit p.val.2.val j.val := by
  simp [dataBasis, j.isLt]

theorem dataBasis_address {N M r : ℕ} (D : CollisionDataStructure N M r)
    (k w : ℕ) (x : Fin N → ZMod M) (h : Fin (2^D.seedBits)) (p : JRState N r) :
    addressValue (dataBasis D k w x h p) 0 (Nat.clog 2 (N+1)) = p.val.2.val := by
  unfold addressValue
  have hbits : (∑ i ∈ Finset.range (Nat.clog 2 (N+1)),
      if readBit (dataBasis D k w x h p) (0+i) then 2^i else 0) =
      ∑ i ∈ Finset.range (Nat.clog 2 (N+1)), if naturalBit p.val.2.val i then 2^i else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    have hib := Finset.mem_range.mp hi
    have hib' : i < nativeWidth N M k w := by unfold nativeWidth; omega
    simp only [zero_add, readBit, ↓reduceDIte, hib']
    rw [dataBasis_address_bit D k w x h p ⟨i,hib⟩]
  rw [hbits, sum_naturalBit, Nat.mod_eq_of_lt]
  exact p.val.2.isLt.trans_le ((Nat.le_succ N).trans (Nat.le_pow_clog (by omega) _))

theorem dataBasis_answer_zero {N M r : ℕ} (D : CollisionDataStructure N M r)
    (k w : ℕ) (x : Fin N → ZMod M) (h : Fin (2^D.seedBits)) (p : JRState N r) :
    addressValue (dataBasis D k w x h p) (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) = 0 := by
  unfold addressValue
  apply Finset.sum_eq_zero
  intro i hi
  have hib := Finset.mem_range.mp hi
  have hi' : Nat.clog 2 (N+1)+i < nativeWidth N M k w := by unfold nativeWidth; omega
  simp only [readBit, hi', ↓reduceDIte, dataBasis]
  split_ifs
  all_goals first | omega | simp_all

theorem sourceValueAction_dataBasis {N M r : ℕ} (D : CollisionDataStructure N M r)
    (k w : ℕ) (x : Fin N → ZMod M) (h : Fin (2^D.seedBits)) (p : JRState N r)
    (hM : 0 < M) :
    sourceValueAction x (dataBasis D k w x h p) =
      fun i => if Nat.clog 2 (N+1) ≤ i.val ∧ i.val < Nat.clog 2 (N+1)+Nat.clog 2 (M+1)
        then naturalBit (x p.val.2).val (i.val-Nat.clog 2 (N+1))
        else dataBasis D k w x h p i := by
  letI : NeZero M := ⟨ne_of_gt hM⟩
  unfold sourceValueAction
  (try dsimp only)
  rw [dataBasis_address, dataBasis_answer_zero]
  simp [p.val.2.isLt, hM, Nat.mod_eq_of_lt (x p.val.2).val_lt]

theorem dataBasis_injective_fixedWidth {N M r : ℕ} (D : CollisionDataStructure N M r)
    (k w : ℕ) (x : Fin N → ZMod M)
    (hlen : ∀ (p : JRState N r) (h : Fin (2^D.seedBits)), (D.encode p.val.1 x h).length = w) :
    Function.Injective (fun p : JRState N r × Fin (2^D.seedBits) =>
      dataBasis D k w x p.2 p.1) := by
  intro p q hpq
  have hrecord : D.encode p.1.val.1 x p.2 = D.encode q.1.val.1 x q.2 := by
    apply List.ext_getElem (by rw [hlen, hlen])
    intro i hi hj
    have hiw : i < w := by simpa only [hlen] using! hi
    have hb := congrFun hpq ⟨Nat.clog 2 (N+1)+Nat.clog 2 (M+1)+i,
      by unfold nativeWidth; omega⟩
    (try dsimp only at hb)
    rw [dataBasis_record_bit D k w x p.2 p.1 ⟨i,hiw⟩,
      dataBasis_record_bit D k w x q.2 q.1 ⟨i,hiw⟩] at hb
    simpa only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some] using!
        hb
  obtain ⟨hsubset, hseed, _⟩ := D.faithful _ _ _ _ _ _ hrecord
  have had : p.1.val.2 = q.1.val.2 := by
    apply Fin.ext
    have hN : N ≤ 2^(Nat.clog 2 (N+1)) := (Nat.le_succ N).trans (Nat.le_pow_clog (by omega) _)
    apply naturalBit_injective_below (p.1.val.2.isLt.trans_le hN) (q.1.val.2.isLt.trans_le hN)
    intro i hi
    have hb := congrFun hpq ⟨i, by unfold nativeWidth; omega⟩
    (try dsimp only at hb)
    simpa only [dataBasis_address_bit D k w x p.2 p.1 ⟨i,hi⟩,
      dataBasis_address_bit D k w x q.2 q.1 ⟨i,hi⟩] using! hb
  apply Prod.ext
  · apply Subtype.ext
    exact Prod.ext hsubset had
  · exact hseed

def recordContainsCollision {N M r : ℕ} (D : CollisionDataStructure N M r)
    (k : ℕ) (record : List Bool) : Prop :=
  ∃ (S : Finset (Fin N)) (x : Fin N → ZMod M) (h : Fin (2^D.seedBits)),
    D.encode S x h = record ∧ ∃ J ⊆ S, IsCollision k x J

theorem recordContainsCollision_encode {N M r : ℕ} (D : CollisionDataStructure N M r)
    (k : ℕ) (x : Fin N → ZMod M) (h : Fin (2^D.seedBits)) (S : Finset (Fin N)) :
    recordContainsCollision D k (D.encode S x h) ↔ ∃ J ⊆ S, IsCollision k x J := by
  constructor
  · rintro ⟨T, y, h', heq, J, hJT, hcard, v, hv⟩
    obtain ⟨hTS, _, hvalues⟩ := D.faithful T S y x h' h heq
    subst T
    refine ⟨J, hJT, hcard, v, ?_⟩
    intro i hi
    exact (hvalues i (hJT hi)).symm.trans (hv i hi)
  · intro hcollision
    exact ⟨S, x, h, rfl, hcollision⟩

def physicalDataRecord {N M r : ℕ} (_D : CollisionDataStructure N M r) (k w : ℕ)
    (q : Reg (nativeWidth N M k w)) : List Bool :=
  List.ofFn (fun i : Fin w => q
    ⟨Nat.clog 2 (N+1)+Nat.clog 2 (M+1)+i.val, by unfold nativeWidth; omega⟩)

theorem physicalDataRecord_basis {N M r : ℕ} (D : CollisionDataStructure N M r)
    (k w : ℕ) (x : Fin N → ZMod M) (h : Fin (2^D.seedBits)) (p : JRState N r)
    (hlen : (D.encode p.val.1 x h).length = w) :
    physicalDataRecord D k w (dataBasis D k w x h p) = D.encode p.val.1 x h := by
  apply List.ext_getElem (by simp [physicalDataRecord, hlen])
  intro i hi hj
  have hiw : i < w := by simpa only [physicalDataRecord, List.length_ofFn] using! hi
  simp only [physicalDataRecord, List.getElem_ofFn, dataBasis_record_bit,
    List.getElem?_eq_getElem hj, Option.getD_some]

theorem physicalDataRecord_marked {N M r : ℕ} (D : CollisionDataStructure N M r)
    (k w : ℕ) (x : Fin N → ZMod M) (h : Fin (2^D.seedBits)) (p : JRState N r)
    (hlen : (D.encode p.val.1 x h).length = w) :
    recordContainsCollision D k (physicalDataRecord D k w (dataBasis D k w x h p)) ↔
      markedInput k x p := by
  rw [physicalDataRecord_basis D k w x h p hlen, recordContainsCollision_encode]
  rfl

theorem dataLift_at_basis {N M r : ℕ} [NeZero M]
    (D : CollisionDataStructure N M r) (k w : ℕ) (x : Fin N → ZMod M)
    (hinj : Function.Injective (fun p : JRState N r × Fin (2^D.seedBits) =>
      dataBasis D k w x p.2 p.1))
    (ψ : QState (JRState N r × Fin (2^D.seedBits)))
    (p : JRState N r × Fin (2^D.seedBits)) :
    dataLift D k w x ψ (dataBasis D k w x p.2 p.1) = ψ p := by
  simp [dataLift, hinj.eq_iff]

theorem dataLift_isometry {N M r : ℕ} [NeZero M]
    (D : CollisionDataStructure N M r) (k w : ℕ) (x : Fin N → ZMod M)
    (hinj : Function.Injective (fun p : JRState N r × Fin (2^D.seedBits) =>
      dataBasis D k w x p.2 p.1)) :
    let E : Matrix (Reg (nativeWidth N M k w)) (JRState N r × Fin (2^D.seedBits)) ℂ :=
      fun q p => if q = dataBasis D k w x p.2 p.1 then 1 else 0
    Eᴴ*E = 1 := by
  (try dsimp only)
  ext p p'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (dataBasis D k w x p.2 p.1)]
  · simp [Matrix.one_apply, hinj.eq_iff]
  · intro q _ hq
    simp [hq]
  · simp

theorem dataLift_norm {N M r : ℕ} [NeZero M]
    (D : CollisionDataStructure N M r) (k w : ℕ) (x : Fin N → ZMod M)
    (hinj : Function.Injective (fun p : JRState N r × Fin (2^D.seedBits) =>
      dataBasis D k w x p.2 p.1)) (ψ : QState (JRState N r × Fin (2^D.seedBits))) :
    ‖toEuclidean_fromVec (dataLift D k w x ψ)‖ = ‖toEuclidean_fromVec ψ‖ := by
  let E : Matrix (Reg (nativeWidth N M k w)) (JRState N r × Fin (2^D.seedBits)) ℂ :=
    fun q p => if q = dataBasis D k w x p.2 p.1 then 1 else 0
  have hE : Eᴴ*E = 1 := dataLift_isometry D k w x hinj
  have hs : dataLift D k w x ψ = E *ᵥ ψ := by
    ext q
    simp [dataLift, E, Matrix.mulVec, dotProduct]
  have hi : Qatlib.Foundations.PureStateMath.Inner (E *ᵥ ψ) (E *ᵥ ψ) = Qatlib.Foundations.PureStateMath.Inner ψ ψ := by
    simp only [Qatlib.Foundations.PureStateMath.Inner, Matrix.star_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    rw [hE, Matrix.vecMul_one]
  have hn : ‖toEuclidean_fromVec (dataLift D k w x ψ)‖^2 = ‖toEuclidean_fromVec ψ‖^2 := by
    rw [hs, norm_toEuclidean_sq_eq_re_inner, norm_toEuclidean_sq_eq_re_inner, hi]
  nlinarith [norm_nonneg (toEuclidean_fromVec (dataLift D k w x ψ)), norm_nonneg (toEuclidean_fromVec ψ)]

theorem dataLift_sub {N M r : ℕ} [NeZero M]
    (D : CollisionDataStructure N M r) (k w : ℕ) (x : Fin N → ZMod M)
    (ψ φ : QState (JRState N r × Fin (2^D.seedBits))) :
    dataLift D k w x (ψ-φ) = dataLift D k w x ψ - dataLift D k w x φ := by
  ext q
  simp only [dataLift, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp

theorem dataLift_oneStep_error {N M r : ℕ} [NeZero M]
    (D : CollisionDataStructure N M r) (k w : ℕ) (x : Fin N → ZMod M)
    (hinj : Function.Injective (fun p : JRState N r × Fin (2^D.seedBits) =>
      dataBasis D k w x p.2 p.1))
    (U : Matrix (Reg (nativeWidth N M k w)) (Reg (nativeWidth N M k w)) ℂ)
    (V : Matrix (JRState N r × Fin (2^D.seedBits)) (JRState N r × Fin (2^D.seedBits)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Reg (nativeWidth N M k w)) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (JRState N r × Fin (2^D.seedBits)) ℂ)
    (ψ : QState (JRState N r × Fin (2^D.seedBits))) (clock : ℕ)
    (hgood : ∀ η : QState (JRState N r × Fin (2^D.seedBits)),
      (∀ z, ¬dataOperationsFast D x z.1.val.1 z.2 clock → η z = 0) →
      U *ᵥ dataLift D k w x η = dataLift D k w x (V *ᵥ η)) :
    let bad := fun z : JRState N r × Fin (2^D.seedBits) =>
      if dataOperationsFast D x z.1.val.1 z.2 clock then 0 else ψ z
    ‖toEuclidean_fromVec (U *ᵥ dataLift D k w x ψ - dataLift D k w x (V *ᵥ ψ))‖ ≤
      2*‖toEuclidean_fromVec bad‖ := by
  (try dsimp only)
  let bad : QState (JRState N r × Fin (2^D.seedBits)) :=
    fun z => if dataOperationsFast D x z.1.val.1 z.2 clock then 0 else ψ z
  have hfast := hgood (ψ-bad) (by intro z hz; simp [bad, hz])
  rw [dataLift_sub, Matrix.mulVec_sub, Matrix.mulVec_sub, dataLift_sub] at hfast
  have heq : U *ᵥ dataLift D k w x ψ - dataLift D k w x (V *ᵥ ψ) =
      U *ᵥ dataLift D k w x bad - dataLift D k w x (V *ᵥ bad) := by
    ext q
    have hh := congrFun hfast q
    simp only [Pi.sub_apply] at hh ⊢
    linear_combination hh
  rw [heq]
  have hnorm := norm_sub_le (toEuclidean_fromVec (U *ᵥ dataLift D k w x bad))
    (toEuclidean_fromVec (dataLift D k w x (V *ᵥ bad)))
  change ‖toEuclidean_fromVec (U *ᵥ dataLift D k w x bad - dataLift D k w x (V *ᵥ bad))‖ ≤
    ‖toEuclidean_fromVec (ApplyGate U (dataLift D k w x bad))‖ +
      ‖toEuclidean_fromVec (dataLift D k w x (V *ᵥ bad))‖ at hnorm
  rw [norm_applyGate_of_mem_unitaryGroup hU, dataLift_norm D k w x hinj,
    dataLift_norm D k w x hinj] at hnorm
  have hnv : ‖toEuclidean_fromVec (V *ᵥ bad)‖ = ‖toEuclidean_fromVec bad‖ :=
    norm_applyGate_of_mem_unitaryGroup hV bad
  rw [hnv] at hnorm
  simpa only [two_mul] using! hnorm

theorem dataFlagFlip_lift_semantics {N M r : ℕ} [NeZero M]
    (D : CollisionDataStructure N M r) (k w : ℕ) (hw : 0 < w)
    (x : Fin N → ZMod M)
    (hinj : Function.Injective (fun p : JRState N r × Fin (2^D.seedBits) =>
      dataBasis D k w x p.2 p.1))
    (hflag : ∀ (p : JRState N r) (h : Fin (2^D.seedBits)),
      (D.encode p.val.1 x h)[0]?.getD false = decide (markedInput k x p))
    (ψ : QState (JRState N r × Fin (2^D.seedBits))) :
    Run (sourceValueOracle (k:=k) (w:=w) x)
      (sourceCircuit (nativeWidth N M k w)
        (dataFlagFlip (Nat.clog 2 (N+1)+Nat.clog 2 (M+1)))) (dataLift D k w x ψ) =
      dataLift D k w x (fun z => if markedInput k x z.1 then -ψ z else ψ z) := by
  have hb : Nat.clog 2 (N+1)+Nat.clog 2 (M+1) < nativeWidth N M k w := by
    unfold nativeWidth
    omega
  rw [dataFlagFlip_semantics _ _ hb]
  ext q
  by_cases hq : ∃ p : JRState N r × Fin (2^D.seedBits), q = dataBasis D k w x p.2 p.1
  · obtain ⟨p, rfl⟩ := hq
    rw [dataLift_at_basis D k w x hinj, dataLift_at_basis D k w x hinj]
    have he := dataBasis_record_bit D k w x p.2 p.1 ⟨0,hw⟩
    (try dsimp only at he)
    simpa only [Nat.add_zero, hflag, Bool.decide_iff] using!
      congrArg (fun b : Bool => if b then -ψ p else ψ p) he
  · have hn : ∀ p : JRState N r × Fin (2^D.seedBits), q ≠ dataBasis D k w x p.2 p.1 :=
      fun p heq => hq ⟨p,heq⟩
    simp [dataLift, hn]

theorem dataLift_oneStep_approx_error {N M r : ℕ} [NeZero M]
    (D : CollisionDataStructure N M r) (k w : ℕ) (x : Fin N → ZMod M)
    (hinj : Function.Injective (fun p : JRState N r × Fin (2^D.seedBits) =>
      dataBasis D k w x p.2 p.1))
    (U : Matrix (Reg (nativeWidth N M k w)) (Reg (nativeWidth N M k w)) ℂ)
    (V : Matrix (JRState N r × Fin (2^D.seedBits)) (JRState N r × Fin (2^D.seedBits)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Reg (nativeWidth N M k w)) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (JRState N r × Fin (2^D.seedBits)) ℂ)
    (ψ : QState (JRState N r × Fin (2^D.seedBits))) (clock : ℕ) (δ : ℝ)
    (hgood : let bad := fun z : JRState N r × Fin (2^D.seedBits) =>
        if dataOperationsFast D x z.1.val.1 z.2 clock then 0 else ψ z
      ‖toEuclidean_fromVec (U *ᵥ dataLift D k w x (ψ-bad) -
        dataLift D k w x (V *ᵥ (ψ-bad)))‖ ≤ δ) :
    let bad := fun z : JRState N r × Fin (2^D.seedBits) =>
      if dataOperationsFast D x z.1.val.1 z.2 clock then 0 else ψ z
    ‖toEuclidean_fromVec (U *ᵥ dataLift D k w x ψ - dataLift D k w x (V *ᵥ ψ))‖ ≤
      δ+2*‖toEuclidean_fromVec bad‖ := by
  (try dsimp only at hgood ⊢)
  let bad : QState (JRState N r × Fin (2^D.seedBits)) :=
    fun z => if dataOperationsFast D x z.1.val.1 z.2 clock then 0 else ψ z
  let goodDefect := U *ᵥ dataLift D k w x (ψ-bad) - dataLift D k w x (V *ᵥ (ψ-bad))
  let badDefect := U *ᵥ dataLift D k w x bad - dataLift D k w x (V *ᵥ bad)
  have hgd : ‖toEuclidean_fromVec goodDefect‖ ≤ δ := hgood
  have heq : U *ᵥ dataLift D k w x ψ - dataLift D k w x (V *ᵥ ψ) = goodDefect+badDefect := by
    simp only [goodDefect, badDefect, dataLift_sub, Matrix.mulVec_sub]
    ext q
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hbd : ‖toEuclidean_fromVec badDefect‖ ≤ 2*‖toEuclidean_fromVec bad‖ := by
    have hnorm := norm_sub_le (toEuclidean_fromVec (U *ᵥ dataLift D k w x bad))
      (toEuclidean_fromVec (dataLift D k w x (V *ᵥ bad)))
    change ‖toEuclidean_fromVec badDefect‖ ≤
      ‖toEuclidean_fromVec (ApplyGate U (dataLift D k w x bad))‖ +
        ‖toEuclidean_fromVec (dataLift D k w x (V *ᵥ bad))‖ at hnorm
    rw [norm_applyGate_of_mem_unitaryGroup hU, dataLift_norm D k w x hinj,
      dataLift_norm D k w x hinj] at hnorm
    have hnv : ‖toEuclidean_fromVec (V *ᵥ bad)‖ = ‖toEuclidean_fromVec bad‖ :=
      norm_applyGate_of_mem_unitaryGroup hV bad
    rw [hnv] at hnorm
    simpa only [two_mul] using! hnorm
  rw [heq]
  change ‖toEuclidean_fromVec goodDefect+toEuclidean_fromVec badDefect‖ ≤ _
  exact (norm_add_le _ _).trans (add_le_add hgd hbd)

end Qatlib.Concepts.WalkFind.QRAMModel
