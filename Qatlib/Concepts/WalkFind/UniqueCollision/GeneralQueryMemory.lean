/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Native query algorithms and compact collision memory

This module constructs `nativeReadAll`, which reads an entire input through the alphabet oracle
and produces a verified collision result, together with the zero-query rejection algorithm
`nativeReject`. It proves correctness, exact query counts, and work-register bounds in the query
model of [NielsenChuang2010].

`NativeCompactMemory` stores a Johnson-walk state and its associated input values in a finite
bit register. These encodings and the full-input algorithm supply the large-memory case of the
collision-search tradeoff considered in [Ambainis2007ElementDistinctness].

## Main statements

* `nativeReadAll_correct`: correctness of complete input interrogation.
* `nativeCompactMemory_encoding`: an injective bit-register encoding of compact walk memory.
* `generalQueryMemory_large_memory`: query and memory bounds when `N ≤ 2*r`.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.WalkSpectrum

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkFind.UniqueCollision

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkFind.UniqueCollision
open Matrix Qatlib.Concepts.WalkFind.UniqueCollision
open scoped Classical BigOperators

/-- An input containing a collision of size `k` has at least `k` addresses. -/
theorem hasCollision_card_bound {N M k : ℕ} (x : Fin N → ZMod M) (h : HasCollision k x) : k ≤ N := by
  obtain ⟨S,hS,_⟩ := h
  rw [← hS]
  exact (Finset.card_le_card (Finset.subset_univ S)).trans_eq (by simp)

/-- The single-seed algorithm with no work bits and an empty circuit, initialized with a
negative output. -/
def nativeReject (N M k : ℕ) [NeZero M] (hN : 0 < N) : RandomQueryAlgorithm N M k where
  seeds := 1
  positiveSeeds := by decide
  workBits := 0
  program := fun _ => []
  start := fun _ => ((⟨0,hN⟩,0),(ZeroStr 0,false,fun _ => ⟨0,hN⟩))
  unitary := fun _ => by simp

/-- The rejection algorithm uses zero oracle queries. -/
theorem nativeReject_queries (N M k : ℕ) [NeZero M] (hN : 0 < N) (s : Fin 1) :
    QueryCount ((nativeReject N M k hN).program s) = 0 := rfl

/-- The rejection algorithm is correct when `N < k`, since a collision of size `k` cannot occur. -/
theorem nativeReject_correct (N M k : ℕ) [NeZero M] (hN : 0 < N) (hNk : N < k) :
    algorithmCorrect (nativeReject N M k hN) := by
  letI : Inhabited (Fin N) := ⟨⟨0,hN⟩⟩
  intro x
  have hn : ¬HasCollision k x := fun h => (not_le_of_gt hNk) (hasCollision_card_bound x h)
  have hre (P : OutputSpace N M k 0 → Prop)
      (hp : ¬ P ((⟨0,hN⟩,0),(ZeroStr 0,false,fun _ => ⟨0,hN⟩))) :
      MeasureProb (Qatlib.Foundations.PureStateMath.Ket ((⟨0,hN⟩,0),(ZeroStr 0,false,fun _ => ⟨0,hN⟩)))
        (Finset.univ.filter P) = 0 := by
    unfold MeasureProb
    apply Finset.sum_eq_zero
    intro q hq
    have hne : q ≠ ((⟨0,hN⟩,0),(ZeroStr 0,false,fun _ => ⟨0,hN⟩)) := by
      intro heq
      exact hp (heq ▸ (Finset.mem_filter.mp hq).2)
    simp [BornProb,Qatlib.Foundations.PureStateMath.Ket,hne]
  refine ⟨?_,fun h => False.elim (hn h),?_⟩
  · intro s
    simpa [nativeReject,Run,yesOutput,verifiedOutput] using!
        hre (fun q => yesOutput q ∧ ¬verifiedOutput x q) (by simp [yesOutput])
  · intro _ s
    simpa [nativeReject,Run,yesOutput,verifiedOutput] using! hre yesOutput (by simp [yesOutput])

/-- All length-`N` inputs over `ZMod M` fit in a register of `N * Nat.clog 2 (M+1)` bits. -/
theorem interrogation_record_capacity (N M : ℕ) [NeZero M] :
    Fintype.card (Fin N → ZMod M) ≤ 2^(N*Nat.clog 2 (M+1)) := by
  rw [Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.mul_comm N, pow_mul]
  have hM := Nat.le_pow_clog (by decide : 1 < 2) (M+1)
  exact Nat.pow_le_pow_left (by omega) N

/-- An injective encoding of the entire input into `N * Nat.clog 2 (M+1)` work bits. -/
def interrogationCode (N M : ℕ) [NeZero M] :
    (Fin N → ZMod M) ↪ Reg (N*Nat.clog 2 (M+1)) :=
  ⟨finiteBasisCode _ _ (interrogation_record_capacity N M),
    finiteBasisCode_injective (interrogation_record_capacity N M)⟩

/-- Embed an oracle register and a full input record into the output space, with a negative flag
and constant address tuple. -/
def interrogationEmbedding (N M k : ℕ) [NeZero M] (j : Fin N) :
    ((Fin N × ZMod M) × (Fin N → ZMod M)) ↪ OutputSpace N M k (N*Nat.clog 2 (M+1)) where
  toFun p := (p.1,(interrogationCode N M p.2,false,fun _ => j))
  inj' := by
    intro p q h
    apply Prod.ext
    · exact congrArg (fun z : OutputSpace N M k (N*Nat.clog 2 (M+1)) => z.1) h
    · apply (interrogationCode N M).injective
      exact congrArg (fun z => z.2.1) h

/-- Extend a permutation of the interrogation labels to a permutation of the full output space. -/
def interrogationPerm (N M k : ℕ) [NeZero M] (j : Fin N)
    (e : Equiv.Perm ((Fin N × ZMod M) × (Fin N → ZMod M))) :
    Equiv.Perm (OutputSpace N M k (N*Nat.clog 2 (M+1))) :=
  e.viaFintypeEmbedding (interrogationEmbedding N M k j)

/-- The extended interrogation permutation acts on encoded basis states by the original
permutation. -/
theorem interrogationPerm_semantics (N M k : ℕ) [NeZero M] (j : Fin N)
    (e : Equiv.Perm ((Fin N × ZMod M) × (Fin N → ZMod M)))
    (p : (Fin N × ZMod M) × (Fin N → ZMod M)) :
    permMatrix (interrogationPerm N M k j e) *ᵥ Qatlib.Foundations.PureStateMath.Ket (interrogationEmbedding N M k j p) =
      Qatlib.Foundations.PureStateMath.Ket (interrogationEmbedding N M k j (e p)) := by
  letI : Inhabited (Fin N) := ⟨j⟩
  ext z
  simp [Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,permMatrix,interrogationPerm]

/-- On encoded interrogation basis states, the alphabet oracle implements `alphabetShift`. -/
theorem interrogationEmbedding_query (N M k : ℕ) [NeZero M] (j : Fin N)
    (x : Fin N → ZMod M) (p : (Fin N × ZMod M) × (Fin N → ZMod M)) :
    alphabetOracle x *ᵥ Qatlib.Foundations.PureStateMath.Ket (interrogationEmbedding N M k j p) =
      Qatlib.Foundations.PureStateMath.Ket (interrogationEmbedding N M k j (alphabetShift x p)) := by
  letI : Inhabited (Fin N) := ⟨j⟩
  ext z
  simp [alphabetOracle,permMatrix,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,
    alphabetShift,interrogationEmbedding]

/-- The circuit that queries address `i`, swaps the answer into the record, and restores the
address register to `j`. -/
def interrogationNativeRound (N M k : ℕ) [NeZero M] (j i : Fin N) :
    Circuit (OutputSpace N M k (N*Nat.clog 2 (M+1))) :=
  [.gate (permMatrix (interrogationPerm N M k j (alphabetAddressSwap j i))),.query,
    .gate (permMatrix (interrogationPerm N M k j (alphabetStoreSwap i))),
    .gate (permMatrix (interrogationPerm N M k j (alphabetAddressSwap j i)))]

/-- Concatenate one interrogation round for each address in a list. -/
def interrogationNativeList (N M k : ℕ) [NeZero M] (j : Fin N) :
    List (Fin N) → Circuit (OutputSpace N M k (N*Nat.clog 2 (M+1)))
  | [] => []
  | i :: is => interrogationNativeRound N M k j i ++ interrogationNativeList N M k j is

/-- If record entry `i` is zero, an interrogation round stores `x i` there and restores the
oracle register. -/
theorem interrogationNativeRound_run (N M k : ℕ) [NeZero M] (j i : Fin N)
    (x s : Fin N → ZMod M) (hi : s i = 0) :
    Run (alphabetOracle x) (interrogationNativeRound N M k j i)
      (Qatlib.Foundations.PureStateMath.Ket (interrogationEmbedding N M k j ((j,0),s))) =
      Qatlib.Foundations.PureStateMath.Ket (interrogationEmbedding N M k j ((j,0),Function.update s i (x i))) := by
  simp only [interrogationNativeRound,Run,ApplyGate]
  rw [interrogationPerm_semantics]
  have hroute : alphabetAddressSwap (a:=M) j i ((j,0),s) = ((i,0),s) := by
    simp [alphabetAddressSwap,Equiv.prodCongr,Prod.map]
  rw [hroute,interrogationEmbedding_query]
  have hquery : alphabetShift x ((i,0),s) = ((i,x i),s) := by simp [alphabetShift]
  rw [hquery,interrogationPerm_semantics]
  simp only [alphabetStoreSwap,Equiv.coe_fn_mk,hi]
  rw [interrogationPerm_semantics]
  simp [alphabetAddressSwap,Equiv.prodCongr,Prod.map]

/-- For a list of distinct addresses with initially zero record entries, interrogation fills
precisely those entries with the corresponding input values. -/
theorem interrogationNativeList_run (N M k : ℕ) [NeZero M] (j : Fin N)
    (is : List (Fin N)) (hn : is.Nodup) (x s : Fin N → ZMod M)
    (hz : ∀ i ∈ is, s i = 0) :
    Run (alphabetOracle x) (interrogationNativeList N M k j is)
      (Qatlib.Foundations.PureStateMath.Ket (interrogationEmbedding N M k j ((j,0),s))) =
      Qatlib.Foundations.PureStateMath.Ket (interrogationEmbedding N M k j ((j,0),fun i => if i ∈ is then x i else s i)) := by
  induction is generalizing s with
  | nil => simp [interrogationNativeList]
  | cons i is ih =>
    have hnot := (List.nodup_cons.mp hn).1
    rw [interrogationNativeList,run_append,interrogationNativeRound_run N M k j i x s (hz i (by simp))]
    rw [ih (List.nodup_cons.mp hn).2 _ (by
      intro t ht
      have hti : t ≠ i := by intro heq; subst t; exact hnot ht
      simp [Function.update,hti,hz t (by simp [ht])])]
    apply congrArg
        (fun s => Qatlib.Foundations.PureStateMath.Ket (interrogationEmbedding N M k j ((j,0),s)))
    funext t
    by_cases ht : t = i
    · subst t; simp [hnot]
    · simp [ht,Function.update]

/-- The interrogation circuit is unitary and uses one oracle query per list entry. -/
theorem interrogationNativeList_resources (N M k : ℕ) [NeZero M] (j : Fin N) (is : List (Fin N)) :
    IsUnitaryCircuit (interrogationNativeList N M k j is) ∧
      QueryCount (interrogationNativeList N M k j is) = is.length := by
  have hu (e : Equiv.Perm ((Fin N × ZMod M) × (Fin N → ZMod M))) :=
    permMatrix_unitary_of_injective (interrogationPerm N M k j e).injective
  have hround (i : Fin N) : IsUnitaryCircuit (interrogationNativeRound N M k j i) := by
    simp [interrogationNativeRound,hu]
  induction is with
  | nil => simp [interrogationNativeList]
  | cons i is ih =>
    refine ⟨(isUnitaryCircuit_append _ _).mpr ⟨hround i,ih.1⟩,?_⟩
    simp [interrogationNativeList,interrogationNativeRound,QueryCount,ih.2]

/-- A collision of size `k` yields an injective tuple of `k` addresses on which the input is
constant. -/
theorem collisionTuple_exists {N M k : ℕ} (x : Fin N → ZMod M) (h : HasCollision k x) :
    ∃ addresses : Fin k → Fin N, Function.Injective addresses ∧
      ∃ v : ZMod M, ∀ i, x (addresses i) = v := by
  obtain ⟨S,hcard,v,hv⟩ := h
  exact ⟨S.orderEmbOfFin hcard,(S.orderEmbOfFin hcard).injective,v,
    fun i => hv _ (S.orderEmbOfFin_mem hcard i)⟩

/-- There is a unitary circuit using exactly `N` queries that encodes the entire input in the
work register and leaves the output flag negative. -/
theorem native_readAll_actual (N M k : ℕ) [NeZero M] (hN : 0 < N) :
    ∃ (C : Circuit (OutputSpace N M k (N*Nat.clog 2 (M+1))))
      (start : OutputSpace N M k (N*Nat.clog 2 (M+1))),
      IsUnitaryCircuit C ∧ QueryCount C = N ∧ ∀ x : Fin N → ZMod M,
      Run (alphabetOracle x) C (Qatlib.Foundations.PureStateMath.Ket start) =
        Qatlib.Foundations.PureStateMath.Ket ((⟨0,hN⟩,0),(interrogationCode N M x,false,fun _ => ⟨0,hN⟩)) := by
  let j : Fin N := ⟨0,hN⟩
  let is := (Finset.univ : Finset (Fin N)).toList
  obtain ⟨hu,hq⟩ := interrogationNativeList_resources N M k j is
  refine ⟨interrogationNativeList N M k j is,interrogationEmbedding N M k j ((j,0),fun _ => 0),hu,?_,?_⟩
  · simpa [is] using! hq
  · intro x
    have h :=
        interrogationNativeList_run N M k j is (Finset.nodup_toList _) x (fun _ => 0) (by simp)
    simpa [is,interrogationEmbedding,j] using! h

/-- Decode a valid full-input code, returning the zero input when the register is outside the
encoding range. -/
def interrogationDecode (N M : ℕ) [NeZero M] (z : Reg (N*Nat.clog 2 (M+1))) : Fin N → ZMod M :=
  if h : ∃ x, interrogationCode N M x = z then Classical.choose h else fun _ => 0

/-- Decoding an encoded input recovers that input. -/
theorem interrogationDecode_code (N M : ℕ) [NeZero M] (x : Fin N → ZMod M) :
    interrogationDecode N M (interrogationCode N M x) = x := by
  unfold interrogationDecode
  rw [dif_pos (show ∃ y, interrogationCode N M y = interrogationCode N M x from ⟨x,rfl⟩)]
  apply (interrogationCode N M).injective
  exact Classical.choose_spec
      (show ∃ y, interrogationCode N M y = interrogationCode N M x from ⟨x,rfl⟩)

/-- Choose an injective tuple of addresses witnessing the given collision. -/
def nativeCollisionTuple {N M k : ℕ} (x : Fin N → ZMod M) (h : HasCollision k x) : Fin k → Fin N :=
  Classical.choose (collisionTuple_exists x h)

/-- The chosen collision tuple is injective, and the input has a common value at all its
addresses. -/
theorem nativeCollisionTuple_valid {N M k : ℕ} (x : Fin N → ZMod M) (h : HasCollision k x) :
    Function.Injective (nativeCollisionTuple x h) ∧ ∃ v : ZMod M, ∀ i, x (nativeCollisionTuple x h i) = v :=
  Classical.choose_spec (collisionTuple_exists x h)

/-- Return a positive flag and a collision tuple when a collision exists, and a negative flag
with the constant tuple at `j` otherwise. -/
def nativeVerifiedResult (N M k : ℕ) (j : Fin N) (x : Fin N → ZMod M) : Bool × (Fin k → Fin N) :=
  if h : HasCollision k x then (true,nativeCollisionTuple x h) else (false,fun _ => j)

/-- The involutive permutation that swaps the default output with the verified result determined
by the decoded work register. -/
def nativeVerifyPermutation (N M k : ℕ) [NeZero M] (j : Fin N) :
    Equiv.Perm (OutputSpace N M k (N*Nat.clog 2 (M+1))) where
  toFun p :=
    let out := Equiv.swap (false,fun _ => j)
      (nativeVerifiedResult N M k j (interrogationDecode N M p.2.1)) (p.2.2)
    (p.1,(p.2.1,out))
  invFun p :=
    let out := Equiv.swap (false,fun _ => j)
      (nativeVerifiedResult N M k j (interrogationDecode N M p.2.1)) (p.2.2)
    (p.1,(p.2.1,out))
  left_inv p := by simp
  right_inv p := by simp

/-- The output basis label containing the encoded input and its verified collision result. -/
def nativeVerifiedLabel (N M k : ℕ) [NeZero M] (j : Fin N) (x : Fin N → ZMod M) :
    OutputSpace N M k (N*Nat.clog 2 (M+1)) :=
  ((j,0),(interrogationCode N M x,nativeVerifiedResult N M k j x))

/-- The verified label has a positive output flag exactly when the input contains a collision of
size `k`. -/
theorem nativeVerifiedLabel_yes (N M k : ℕ) [NeZero M] (j : Fin N) (x : Fin N → ZMod M) :
    yesOutput (nativeVerifiedLabel N M k j x) ↔ HasCollision k x := by
  simp only [yesOutput,nativeVerifiedLabel,nativeVerifiedResult]
  split_ifs <;> simp_all

/-- The verified label satisfies `verifiedOutput` exactly when the input contains a collision of
size `k`. -/
theorem nativeVerifiedLabel_verified (N M k : ℕ) [NeZero M] (j : Fin N) (x : Fin N → ZMod M) :
    verifiedOutput x (nativeVerifiedLabel N M k j x) ↔ HasCollision k x := by
  by_cases h : HasCollision k x
  · have ht := nativeCollisionTuple_valid x h
    simp [verifiedOutput,nativeVerifiedLabel,nativeVerifiedResult,h,ht.1,ht.2]
  · simp [verifiedOutput,nativeVerifiedLabel,nativeVerifiedResult,h]

/-- There is a unitary circuit using exactly `N` queries that produces the verified full-input
label on every input. -/
theorem native_readAll_verified (N M k : ℕ) [NeZero M] (hN : 0 < N) :
    ∃ (C : Circuit (OutputSpace N M k (N*Nat.clog 2 (M+1))))
      (start : OutputSpace N M k (N*Nat.clog 2 (M+1))),
      IsUnitaryCircuit C ∧ QueryCount C = N ∧ ∀ x : Fin N → ZMod M,
        Run (alphabetOracle x) C (Qatlib.Foundations.PureStateMath.Ket start) = Qatlib.Foundations.PureStateMath.Ket (nativeVerifiedLabel N M k ⟨0,hN⟩ x) := by
  letI : Inhabited (Fin N) := ⟨⟨0,hN⟩⟩
  obtain ⟨C,start,hu,hq,hsem⟩ := native_readAll_actual N M k hN
  let e := nativeVerifyPermutation N M k ⟨0,hN⟩
  have he := permMatrix_unitary_of_injective e.injective
  refine ⟨C++[.gate (permMatrix e)],start,(isUnitaryCircuit_append _ _).mpr ⟨hu,by simpa using! he⟩,?_,?_⟩
  · rw [queryCount_append]
    simpa [QueryCount] using! hq
  · intro x
    rw [run_append,hsem]
    ext z
    simp [Run,ApplyGate,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,permMatrix,e,nativeVerifyPermutation,
      interrogationDecode_code,nativeVerifiedLabel,Equiv.swap_apply_left]

/-- The single-seed collision algorithm obtained by complete input interrogation followed by
verification. -/
def nativeReadAll (N M k : ℕ) [NeZero M] (hN : 0 < N) : RandomQueryAlgorithm N M k :=
  let C := Classical.choose (native_readAll_verified N M k hN)
  let start := Classical.choose (Classical.choose_spec (native_readAll_verified N M k hN))
  { seeds := 1
    positiveSeeds := by decide
    workBits := N*Nat.clog 2 (M+1)
    program := fun _ => C
    start := fun _ => start
    unitary := fun _ => (Classical.choose_spec (Classical.choose_spec (native_readAll_verified N M k hN))).1 }

/-- Complete input interrogation uses exactly `N` oracle queries. -/
theorem nativeReadAll_queries (N M k : ℕ) [NeZero M] (hN : 0 < N) (s : Fin 1) :
    QueryCount ((nativeReadAll N M k hN).program s) = N :=
  (Classical.choose_spec (Classical.choose_spec (native_readAll_verified N M k hN))).2.1

/-- The complete input interrogation algorithm satisfies `algorithmCorrect`. -/
theorem nativeReadAll_correct (N M k : ℕ) [NeZero M] (hN : 0 < N) :
    algorithmCorrect (nativeReadAll N M k hN) := by
  dsimp only [algorithmCorrect,nativeReadAll]
  have hsem :=
      (Classical.choose_spec (Classical.choose_spec (native_readAll_verified N M k hN))).2.2
  letI : Inhabited (Fin N) := ⟨⟨0,hN⟩⟩
  intro x
  refine ⟨?_,?_,?_⟩
  · intro s
    rw [hsem x]
    unfold MeasureProb
    apply Finset.sum_eq_zero
    intro q hq
    have hne : q ≠ nativeVerifiedLabel N M k ⟨0,hN⟩ x := by
      intro heq
      have hh := (Finset.mem_filter.mp hq).2
      rw [heq,nativeVerifiedLabel_yes,nativeVerifiedLabel_verified] at hh
      exact hh.2 hh.1
    simp [BornProb,Qatlib.Foundations.PureStateMath.Ket,hne]
  · intro h
    have hm : MeasureProb (Qatlib.Foundations.PureStateMath.Ket (nativeVerifiedLabel N M k ⟨0,hN⟩ x))
        (Finset.univ.filter (verifiedOutput x)) = 1 := by
      unfold MeasureProb
      rw [Finset.sum_eq_single (nativeVerifiedLabel N M k ⟨0,hN⟩ x)]
      · simp [BornProb,Qatlib.Foundations.PureStateMath.Ket]
      · intro q _ hq; simp [BornProb,Qatlib.Foundations.PureStateMath.Ket,hq]
      · simp [nativeVerifiedLabel_verified,h]
    unfold averageSuccess
    simp only [hsem]
    simp only [hm]
    norm_num
  · intro h s
    rw [hsem x]
    unfold MeasureProb
    apply Finset.sum_eq_zero
    intro q hq
    have hne : q ≠ nativeVerifiedLabel N M k ⟨0,hN⟩ x := by
      intro heq
      have hh := (Finset.mem_filter.mp hq).2
      rw [heq,nativeVerifiedLabel_yes] at hh
      exact h hh
    simp [BornProb,Qatlib.Foundations.PureStateMath.Ket,hne]

/-- The work register of complete input interrogation uses at most `N * dataBits N M` bits. -/
theorem nativeReadAll_memory (N M k : ℕ) [NeZero M] (hN : 0 < N) :
    (nativeReadAll N M k hN).workBits ≤ N*dataBits N M := by
  dsimp only [nativeReadAll]
  apply Nat.mul_le_mul_left
  unfold dataBits
  omega

/-- The average positive-output probability of complete input interrogation is one on collision
inputs and zero otherwise. -/
theorem nativeReadAll_probability (N M k : ℕ) [NeZero M] (hN : 0 < N) (x : Fin N → ZMod M) :
    averageSuccess (nativeReadAll N M k hN) x = if HasCollision k x then 1 else 0 := by
  dsimp only [averageSuccess,nativeReadAll]
  letI : Inhabited (Fin N) := ⟨⟨0,hN⟩⟩
  have hsem :=
      (Classical.choose_spec (Classical.choose_spec (native_readAll_verified N M k hN))).2.2
  simp only [hsem]
  have hm : MeasureProb (Qatlib.Foundations.PureStateMath.Ket (nativeVerifiedLabel N M k ⟨0,hN⟩ x))
      (Finset.univ.filter (verifiedOutput x)) = if HasCollision k x then 1 else 0 := by
    unfold MeasureProb
    by_cases h : HasCollision k x
    · rw [if_pos h,Finset.sum_eq_single (nativeVerifiedLabel N M k ⟨0,hN⟩ x)]
      · simp [BornProb,Qatlib.Foundations.PureStateMath.Ket]
      · intro q _ hq; simp [BornProb,Qatlib.Foundations.PureStateMath.Ket,hq]
      · simp [nativeVerifiedLabel_verified,h]
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro q hq
      have hne : q ≠ nativeVerifiedLabel N M k ⟨0,hN⟩ x := by
        intro heq
        have hh := (Finset.mem_filter.mp hq).2
        rw [heq,nativeVerifiedLabel_verified] at hh
        exact h hh
      simp [BornProb,Qatlib.Foundations.PureStateMath.Ket,hne]
  simp [hm]

/-- A Johnson-walk state paired with `r+1` alphabet values for its stored addresses. -/
abbrev NativeCompactMemory (N M r : ℕ) := JRState N r × (Fin (r+1) → ZMod M)

/-- The stored domain formed by adjoining the distinguished address to the Johnson state's
subset. -/
def nativeCompactDomain {N r : ℕ} (p : JRState N r) : Finset (Fin N) := insert p.val.2 p.val.1

/-- The compact memory domain contains exactly `r+1` addresses. -/
theorem nativeCompactDomain_card {N r : ℕ} (p : JRState N r) :
    (nativeCompactDomain p).card = r+1 := by
  rw [nativeCompactDomain,Finset.card_insert_of_notMem p.property.2,p.property.1]

/-- Place the stored values at the ordered addresses of the compact domain and set all other
input coordinates to zero. -/
def nativeCompactDecode {N M r : ℕ} (p : JRState N r) (values : Fin (r+1) → ZMod M) : Fin N → ZMod M :=
  fun i => if h : i ∈ nativeCompactDomain p then
    values ((nativeCompactDomain p).orderIsoOfFin (nativeCompactDomain_card p) |>.symm |>.toEquiv <| ⟨i,h⟩) else 0

/-- Decoding compact memory returns each stored value at its corresponding ordered domain
address. -/
theorem nativeCompactDecode_at {N M r : ℕ} (p : JRState N r) (values : Fin (r+1) → ZMod M) (j : Fin (r+1)) :
    nativeCompactDecode p values (((nativeCompactDomain p).orderIsoOfFin (nativeCompactDomain_card p) j).val) = values j := by
  unfold nativeCompactDecode
  rw [dif_pos ((nativeCompactDomain p).orderIsoOfFin (nativeCompactDomain_card p) j).property]
  congr 1
  exact ((nativeCompactDomain p).orderIsoOfFin (nativeCompactDomain_card p)).symm_apply_apply j

/-- For a fixed Johnson state, decoding compact values is injective. -/
theorem nativeCompactDecode_injective {N M r : ℕ} (p : JRState N r) :
    Function.Injective (nativeCompactDecode (M:=M) p) := by
  intro values values' he
  funext j
  have h := congrFun he (((nativeCompactDomain p).orderIsoOfFin (nativeCompactDomain_card p) j).val)
  simpa only [nativeCompactDecode_at] using! h

/-- The number of compact memory states is bounded by the capacity of `(r+1) * (Nat.clog 2 (N+1)
+ Nat.clog 2 (M+1))` bits. -/
theorem nativeCompactMemory_capacity (N M r : ℕ) [NeZero M] :
    Fintype.card (NativeCompactMemory N M r) ≤
      2^((r+1)*(Nat.clog 2 (N+1)+Nat.clog 2 (M+1))) := by
  rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,ZMod.card,jrState_card]
  have hJ : N.choose r*(N-r) ≤ N^(r+1) := by
    rw [pow_succ]
    exact Nat.mul_le_mul (Nat.choose_le_pow N r) (Nat.sub_le N r)
  have hN : N ≤ 2^Nat.clog 2 (N+1) := by
    have hh := Nat.le_pow_clog (by decide : 1 < 2) (N+1)
    omega
  have hM : M ≤ 2^Nat.clog 2 (M+1) := by
    have hh := Nat.le_pow_clog (by decide : 1 < 2) (M+1)
    omega
  have hp := Nat.mul_le_mul (Nat.pow_le_pow_left hN (r+1)) (Nat.pow_le_pow_left hM (r+1))
  have hrhs : (2^Nat.clog 2 (N+1))^(r+1)*(2^Nat.clog 2 (M+1))^(r+1) =
      2^((r+1)*(Nat.clog 2 (N+1)+Nat.clog 2 (M+1))) := by
    rw [← mul_pow,← pow_add,← pow_mul,Nat.mul_comm (Nat.clog 2 (N+1)+Nat.clog 2 (M+1))]
  rw [hrhs] at hp
  exact (Nat.mul_le_mul_right (M^(r+1)) hJ).trans hp

/-- Compact memory states possess an injective encoding into the prescribed address-and-value
bit register. -/
theorem nativeCompactMemory_encoding (N M r : ℕ) [NeZero M] :
    ∃ e : NativeCompactMemory N M r → Reg ((r+1)*(Nat.clog 2 (N+1)+Nat.clog 2 (M+1))),
      Function.Injective e :=
  ⟨finiteBasisCode _ _ (nativeCompactMemory_capacity N M r),
    finiteBasisCode_injective (nativeCompactMemory_capacity N M r)⟩

/-- For `r ≥ 1`, the compact memory encoding width is at most `2*r*dataBits N M`. -/
theorem nativeCompactMemory_width (N M r : ℕ) (hr : 1 ≤ r) :
    (r+1)*(Nat.clog 2 (N+1)+Nat.clog 2 (M+1)) ≤ 2*r*dataBits N M := by
  have h := Nat.mul_le_mul (show r+1 ≤ 2*r by omega)
    (show Nat.clog 2 (N+1)+Nat.clog 2 (M+1) ≤ dataBits N M by unfold dataBits; omega)
  simpa only [Nat.mul_assoc] using! h

/-- When `2 ≤ k ≤ r ≤ N` and `N ≤ 2*r`, a correct algorithm uses at most `2*queryScale k N r`
queries per seed and at most `2*r*dataBits N M` work bits. -/
theorem generalQueryMemory_large_memory (k N M r : ℕ) [NeZero M]
    (hk : 2 ≤ k) (hkr : k ≤ r) (hrN : r ≤ N) (hlarge : N ≤ 2*r) :
    ∃ A : RandomQueryAlgorithm N M k, algorithmCorrect A ∧
      (∀ s, (QueryCount (A.program s) : ℝ) ≤ 2*queryScale k N r) ∧
      (A.workBits : ℝ) ≤ 2*r*dataBits N M := by
  have hN : 0 < N := by omega
  refine ⟨nativeReadAll N M k hN,nativeReadAll_correct N M k hN,?_,?_⟩
  · intro s
    rw [nativeReadAll_queries]
    have hr : (r : ℝ) ≤ queryScale k N r := by
      unfold queryScale
      exact le_add_of_nonneg_right (by positivity)
    have hl : (N : ℝ) ≤ 2*r := by exact_mod_cast hlarge
    linarith
  · have hh : (nativeReadAll N M k hN).workBits ≤ 2*r*dataBits N M :=
      (nativeReadAll_memory N M k hN).trans (Nat.mul_le_mul_right _ hlarge)
    exact_mod_cast hh

end Qatlib.Concepts.WalkFind.UniqueCollision
