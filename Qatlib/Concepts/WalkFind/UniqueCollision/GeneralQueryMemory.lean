/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Bounds
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

theorem hasCollision_card_bound {N M k : ℕ} (x : Fin N → ZMod M) (h : HasCollision k x) : k ≤ N := by
  obtain ⟨S,hS,_⟩ := h
  rw [← hS]
  exact (Finset.card_le_card (Finset.subset_univ S)).trans_eq (by simp)

def nativeReject (N M k : ℕ) [NeZero M] (hN : 0 < N) : RandomQueryAlgorithm N M k where
  seeds := 1
  positiveSeeds := by decide
  workBits := 0
  program := fun _ => []
  start := fun _ => ((⟨0,hN⟩,0),(ZeroStr 0,false,fun _ => ⟨0,hN⟩))
  unitary := fun _ => by simp

theorem nativeReject_queries (N M k : ℕ) [NeZero M] (hN : 0 < N) (s : Fin 1) :
    QueryCount ((nativeReject N M k hN).program s) = 0 := rfl

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

theorem interrogation_record_capacity (N M : ℕ) [NeZero M] :
    Fintype.card (Fin N → ZMod M) ≤ 2^(N*Nat.clog 2 (M+1)) := by
  rw [Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.mul_comm N, pow_mul]
  have hM := Nat.le_pow_clog (by decide : 1 < 2) (M+1)
  exact Nat.pow_le_pow_left (by omega) N

def interrogationCode (N M : ℕ) [NeZero M] :
    (Fin N → ZMod M) ↪ Reg (N*Nat.clog 2 (M+1)) :=
  ⟨finiteBasisCode _ _ (interrogation_record_capacity N M),
    finiteBasisCode_injective (interrogation_record_capacity N M)⟩

def interrogationEmbedding (N M k : ℕ) [NeZero M] (j : Fin N) :
    ((Fin N × ZMod M) × (Fin N → ZMod M)) ↪ OutputSpace N M k (N*Nat.clog 2 (M+1)) where
  toFun p := (p.1,(interrogationCode N M p.2,false,fun _ => j))
  inj' := by
    intro p q h
    apply Prod.ext
    · exact congrArg (fun z : OutputSpace N M k (N*Nat.clog 2 (M+1)) => z.1) h
    · apply (interrogationCode N M).injective
      exact congrArg (fun z => z.2.1) h

def interrogationPerm (N M k : ℕ) [NeZero M] (j : Fin N)
    (e : Equiv.Perm ((Fin N × ZMod M) × (Fin N → ZMod M))) :
    Equiv.Perm (OutputSpace N M k (N*Nat.clog 2 (M+1))) :=
  e.viaFintypeEmbedding (interrogationEmbedding N M k j)

theorem interrogationPerm_semantics (N M k : ℕ) [NeZero M] (j : Fin N)
    (e : Equiv.Perm ((Fin N × ZMod M) × (Fin N → ZMod M)))
    (p : (Fin N × ZMod M) × (Fin N → ZMod M)) :
    permMatrix (interrogationPerm N M k j e) *ᵥ Qatlib.Foundations.PureStateMath.Ket (interrogationEmbedding N M k j p) =
      Qatlib.Foundations.PureStateMath.Ket (interrogationEmbedding N M k j (e p)) := by
  letI : Inhabited (Fin N) := ⟨j⟩
  ext z
  simp [Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,permMatrix,interrogationPerm]

theorem interrogationEmbedding_query (N M k : ℕ) [NeZero M] (j : Fin N)
    (x : Fin N → ZMod M) (p : (Fin N × ZMod M) × (Fin N → ZMod M)) :
    alphabetOracle x *ᵥ Qatlib.Foundations.PureStateMath.Ket (interrogationEmbedding N M k j p) =
      Qatlib.Foundations.PureStateMath.Ket (interrogationEmbedding N M k j (alphabetShift x p)) := by
  letI : Inhabited (Fin N) := ⟨j⟩
  ext z
  simp [alphabetOracle,permMatrix,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,
    alphabetShift,interrogationEmbedding]

def interrogationNativeRound (N M k : ℕ) [NeZero M] (j i : Fin N) :
    Circuit (OutputSpace N M k (N*Nat.clog 2 (M+1))) :=
  [.gate (permMatrix (interrogationPerm N M k j (alphabetAddressSwap j i))),.query,
    .gate (permMatrix (interrogationPerm N M k j (alphabetStoreSwap i))),
    .gate (permMatrix (interrogationPerm N M k j (alphabetAddressSwap j i)))]

def interrogationNativeList (N M k : ℕ) [NeZero M] (j : Fin N) :
    List (Fin N) → Circuit (OutputSpace N M k (N*Nat.clog 2 (M+1)))
  | [] => []
  | i :: is => interrogationNativeRound N M k j i ++ interrogationNativeList N M k j is

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

theorem collisionTuple_exists {N M k : ℕ} (x : Fin N → ZMod M) (h : HasCollision k x) :
    ∃ addresses : Fin k → Fin N, Function.Injective addresses ∧
      ∃ v : ZMod M, ∀ i, x (addresses i) = v := by
  obtain ⟨S,hcard,v,hv⟩ := h
  exact ⟨S.orderEmbOfFin hcard,(S.orderEmbOfFin hcard).injective,v,
    fun i => hv _ (S.orderEmbOfFin_mem hcard i)⟩

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

def interrogationDecode (N M : ℕ) [NeZero M] (z : Reg (N*Nat.clog 2 (M+1))) : Fin N → ZMod M :=
  if h : ∃ x, interrogationCode N M x = z then Classical.choose h else fun _ => 0

theorem interrogationDecode_code (N M : ℕ) [NeZero M] (x : Fin N → ZMod M) :
    interrogationDecode N M (interrogationCode N M x) = x := by
  unfold interrogationDecode
  rw [dif_pos (show ∃ y, interrogationCode N M y = interrogationCode N M x from ⟨x,rfl⟩)]
  apply (interrogationCode N M).injective
  exact Classical.choose_spec
      (show ∃ y, interrogationCode N M y = interrogationCode N M x from ⟨x,rfl⟩)

def nativeCollisionTuple {N M k : ℕ} (x : Fin N → ZMod M) (h : HasCollision k x) : Fin k → Fin N :=
  Classical.choose (collisionTuple_exists x h)

theorem nativeCollisionTuple_valid {N M k : ℕ} (x : Fin N → ZMod M) (h : HasCollision k x) :
    Function.Injective (nativeCollisionTuple x h) ∧ ∃ v : ZMod M, ∀ i, x (nativeCollisionTuple x h i) = v :=
  Classical.choose_spec (collisionTuple_exists x h)

def nativeVerifiedResult (N M k : ℕ) (j : Fin N) (x : Fin N → ZMod M) : Bool × (Fin k → Fin N) :=
  if h : HasCollision k x then (true,nativeCollisionTuple x h) else (false,fun _ => j)

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

def nativeVerifiedLabel (N M k : ℕ) [NeZero M] (j : Fin N) (x : Fin N → ZMod M) :
    OutputSpace N M k (N*Nat.clog 2 (M+1)) :=
  ((j,0),(interrogationCode N M x,nativeVerifiedResult N M k j x))

theorem nativeVerifiedLabel_yes (N M k : ℕ) [NeZero M] (j : Fin N) (x : Fin N → ZMod M) :
    yesOutput (nativeVerifiedLabel N M k j x) ↔ HasCollision k x := by
  simp only [yesOutput,nativeVerifiedLabel,nativeVerifiedResult]
  split_ifs <;> simp_all

theorem nativeVerifiedLabel_verified (N M k : ℕ) [NeZero M] (j : Fin N) (x : Fin N → ZMod M) :
    verifiedOutput x (nativeVerifiedLabel N M k j x) ↔ HasCollision k x := by
  by_cases h : HasCollision k x
  · have ht := nativeCollisionTuple_valid x h
    simp [verifiedOutput,nativeVerifiedLabel,nativeVerifiedResult,h,ht.1,ht.2]
  · simp [verifiedOutput,nativeVerifiedLabel,nativeVerifiedResult,h]

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

def nativeReadAll (N M k : ℕ) [NeZero M] (hN : 0 < N) : RandomQueryAlgorithm N M k :=
  let C := Classical.choose (native_readAll_verified N M k hN)
  let start := Classical.choose (Classical.choose_spec (native_readAll_verified N M k hN))
  { seeds := 1
    positiveSeeds := by decide
    workBits := N*Nat.clog 2 (M+1)
    program := fun _ => C
    start := fun _ => start
    unitary := fun _ => (Classical.choose_spec (Classical.choose_spec (native_readAll_verified N M k hN))).1 }

theorem nativeReadAll_queries (N M k : ℕ) [NeZero M] (hN : 0 < N) (s : Fin 1) :
    QueryCount ((nativeReadAll N M k hN).program s) = N :=
  (Classical.choose_spec (Classical.choose_spec (native_readAll_verified N M k hN))).2.1

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

theorem nativeReadAll_memory (N M k : ℕ) [NeZero M] (hN : 0 < N) :
    (nativeReadAll N M k hN).workBits ≤ N*dataBits N M := by
  dsimp only [nativeReadAll]
  apply Nat.mul_le_mul_left
  unfold dataBits
  omega

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

abbrev NativeCompactMemory (N M r : ℕ) := JRState N r × (Fin (r+1) → ZMod M)

def nativeCompactDomain {N r : ℕ} (p : JRState N r) : Finset (Fin N) := insert p.val.2 p.val.1

theorem nativeCompactDomain_card {N r : ℕ} (p : JRState N r) :
    (nativeCompactDomain p).card = r+1 := by
  rw [nativeCompactDomain,Finset.card_insert_of_notMem p.property.2,p.property.1]

def nativeCompactDecode {N M r : ℕ} (p : JRState N r) (values : Fin (r+1) → ZMod M) : Fin N → ZMod M :=
  fun i => if h : i ∈ nativeCompactDomain p then
    values ((nativeCompactDomain p).orderIsoOfFin (nativeCompactDomain_card p) |>.symm |>.toEquiv <| ⟨i,h⟩) else 0

theorem nativeCompactDecode_at {N M r : ℕ} (p : JRState N r) (values : Fin (r+1) → ZMod M) (j : Fin (r+1)) :
    nativeCompactDecode p values (((nativeCompactDomain p).orderIsoOfFin (nativeCompactDomain_card p) j).val) = values j := by
  unfold nativeCompactDecode
  rw [dif_pos ((nativeCompactDomain p).orderIsoOfFin (nativeCompactDomain_card p) j).property]
  congr 1
  exact ((nativeCompactDomain p).orderIsoOfFin (nativeCompactDomain_card p)).symm_apply_apply j

theorem nativeCompactDecode_injective {N M r : ℕ} (p : JRState N r) :
    Function.Injective (nativeCompactDecode (M:=M) p) := by
  intro values values' he
  funext j
  have h := congrFun he (((nativeCompactDomain p).orderIsoOfFin (nativeCompactDomain_card p) j).val)
  simpa only [nativeCompactDecode_at] using! h

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

theorem nativeCompactMemory_encoding (N M r : ℕ) [NeZero M] :
    ∃ e : NativeCompactMemory N M r → Reg ((r+1)*(Nat.clog 2 (N+1)+Nat.clog 2 (M+1))),
      Function.Injective e :=
  ⟨finiteBasisCode _ _ (nativeCompactMemory_capacity N M r),
    finiteBasisCode_injective (nativeCompactMemory_capacity N M r)⟩

theorem nativeCompactMemory_width (N M r : ℕ) (hr : 1 ≤ r) :
    (r+1)*(Nat.clog 2 (N+1)+Nat.clog 2 (M+1)) ≤ 2*r*dataBits N M := by
  have h := Nat.mul_le_mul (show r+1 ≤ 2*r by omega)
    (show Nat.clog 2 (N+1)+Nat.clog 2 (M+1) ≤ dataBits N M by unfold dataBits; omega)
  simpa only [Nat.mul_assoc] using! h

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
