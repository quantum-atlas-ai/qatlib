/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessGates
import Qatlib.Concepts.TensorRegisters.RegisterModel.QmaCompletenessLocalSupport
import Qatlib.Concepts.UniformBqp.FiniteGateWord.QmaCompleteness
import Mathlib.Logic.Equiv.Fin.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib Matrix
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.TensorRegisters.RegisterModel
open scoped BigOperators Kronecker
set_option autoImplicit false

def flattenEquiv (m n : ℕ) : Reg (m+n)≃Clock m×Reg n :=
  (Fin.appendEquiv (α:=Bool) m n).symm

def nativeBit {m : ℕ} (c : Clock m) (k : ℕ) : Bool :=
  if hz : k=0 then true
  else if hk : k ≤ m then c ⟨k-1,by omega⟩ else false

def preBool {m : ℕ} (i : Fin m) (c : Clock m) : Bool :=
  nativeBit c i.val && !c i && !nativeBit c (i.val+2)

def postBool {m : ℕ} (i : Fin m) (c : Clock m) : Bool :=
  nativeBit c i.val && c i && !nativeBit c (i.val+2)

def hopBool {m : ℕ} (i : Fin m) (r c : Clock m) : Bool :=
  postBool i r && preBool i c && outsideEq i r c

theorem preBool_iff {m : ℕ} (i : Fin m) (c : Clock m) :
    preBool i c=true ↔ Pre i c := by
  simp only [preBool,Bool.and_eq_true,Bool.not_eq_true',Pre]
  change ((bit c i.val=true ∧ c i=false) ∧ bit c (i.val+2)=false) ↔ _
  tauto

theorem postBool_iff {m : ℕ} (i : Fin m) (c : Clock m) :
    postBool i c=true ↔ Post i c := by
  simp only [postBool,Bool.and_eq_true,Bool.not_eq_true',Post]
  change ((bit c i.val=true ∧ c i=true) ∧ bit c (i.val+2)=false) ↔ _
  tauto

theorem hopBool_iff {m : ℕ} (i : Fin m) (r c : Clock m) :
    hopBool i r c=true ↔ Post i r ∧ Pre i c ∧ Outside i r c := by
  simp only [hopBool,Bool.and_eq_true,preBool_iff,postBool_iff,outsideEq_true_iff,
    Qatlib.Concepts.UniformBqp.FiniteGateWord.Outside]
  tauto

def gateSites (n : ℕ) (g : FiniteGateCode) : Finset (Fin n) :=
  match g with
  | .h w | .x w | .t w | .tdg w => if h : w < n then {⟨w,h⟩} else ∅
  | .cx c t => if h : c < n ∧ t < n ∧ c≠t then {⟨c,h.1⟩,⟨t,h.2.1⟩} else ∅

def clockSites {m : ℕ} (i : Fin m) : Finset (Fin m) :=
  {i} ∪ (if h : 0 < i.val then {⟨i.val-1,by omega⟩} else ∅) ∪
    (if h : i.val+1 < m then {⟨i.val+1,h⟩} else ∅)

def propSites {m : ℕ} (n : ℕ) (i : Fin m) (g : FiniteGateCode) :
    Finset (Fin (m+n)) :=
  (clockSites i).image (Fin.castAdd n) ∪ (gateSites n g).image (Fin.natAdd m)

theorem gateSites_card (n : ℕ) (g : FiniteGateCode) : (gateSites n g).card≤2 := by
  cases g <;> dsimp only [gateSites] <;> split_ifs <;>
    first | exact le_trans (Finset.card_insert_le _ _) (by simp) | simp

theorem clockSites_card {m : ℕ} (i : Fin m) : (clockSites i).card≤3 := by
  let l : Finset (Fin m):=if h : 0 < i.val then {⟨i.val-1,by omega⟩} else ∅
  let r : Finset (Fin m):=if h : i.val+1 < m then {⟨i.val+1,h⟩} else ∅
  have hl : l.card≤1 := by dsimp [l]; split_ifs <;> simp
  have hr : r.card≤1 := by dsimp [r]; split_ifs <;> simp
  have h1:=Finset.card_union_le ({i}:Finset (Fin m)) l
  have h2:=Finset.card_union_le ({i}∪l) r
  change (({i}∪l)∪r).card≤3
  simp only [Finset.card_singleton] at h1
  omega

theorem propSites_card {m : ℕ} (n : ℕ) (i : Fin m) (g : FiniteGateCode) :
    (propSites n i g).card≤5 := by
  have hc := Finset.card_image_le (f:=Fin.castAdd n) (s:=clockSites i)
  have hg := Finset.card_image_le (f:=Fin.natAdd m) (s:=gateSites n g)
  have hu := Finset.card_union_le ((clockSites i).image (Fin.castAdd n))
    ((gateSites n g).image (Fin.natAdd m))
  have := clockSites_card i
  have := gateSites_card n g
  unfold propSites
  omega

structure IntegerLocalTerm (N : ℕ) where
  support : Finset (Fin N)
  re : Matrix (Reg support.card) (Reg support.card) ℤ
  im : Matrix (Reg support.card) (Reg support.card) ℤ

noncomputable def value {N : ℕ} (b : ℕ) (t : IntegerLocalTerm N) :
    Matrix (Reg N) (Reg N) ℂ :=
  Qatlib.Concepts.TensorRegisters.RegisterModel.partitionLift (split t.support)
    (fun u v => dyadicValue b (t.re u v) (t.im u v))

def table {N : ℕ} (t : IntegerLocalTerm N) : List (List (ℤ×ℤ)) :=
  List.ofFn (fun p : Fin (2^t.support.card) =>
    List.ofFn (fun q : Fin (2^t.support.card) =>
      (t.re ((bitVecEquiv _).symm p) ((bitVecEquiv _).symm q),
       t.im ((bitVecEquiv _).symm p) ((bitVecEquiv _).symm q))))

theorem table_rows {N : ℕ} (t : IntegerLocalTerm N) : (table t).length=2^t.support.card := by
  simp [table]

theorem table_row_length {N : ℕ} (t : IntegerLocalTerm N)
    (r : List (ℤ×ℤ)) (hr : r∈table t) : r.length=2^t.support.card := by
  obtain ⟨p,rfl⟩ := List.mem_ofFn.mp hr
  simp

theorem table_rows_le {N : ℕ} (t : IntegerLocalTerm N) (h : t.support.card≤5) :
    (table t).length≤32 := by
  rw [table_rows]
  exact_mod_cast Nat.pow_le_pow_right (by omega : 1≤2) h

def propagationCoeff {m : ℕ} (n b : ℕ) (i : Fin m) (g : FiniteGateCode)
    (p q : Clock m×Reg n) : ℤ×ℤ :=
  let diag : ℤ := if regEq p.1 q.1 && regEq p.2 q.2 then
      (if postBool i p.1 then (2:ℤ)^b else 0)+
      (if preBool i p.1 then (2:ℤ)^b else 0) else 0
  let fwd := if hopBool i p.1 q.1 then rawCoeff n b g p.2 q.2 else (0,0)
  let rev := if hopBool i q.1 p.1 then rawCoeff n b g q.2 p.2 else (0,0)
  (diag-fwd.1-rev.1,-fwd.2+rev.2)

def propagationTerm {m : ℕ} (n b : ℕ) (i : Fin m) (g : FiniteGateCode) :
    IntegerLocalTerm (m+n) :=
  let S:=propSites n i g
  let c:=fun u v : Reg S.card => propagationCoeff n b i g
    (flattenEquiv m n (fill S u)) (flattenEquiv m n (fill S v))
  ⟨S,fun u v => (c u v).1,fun u v => (c u v).2⟩

theorem propagationCoeff_bounds {m : ℕ} (n b : ℕ) (i : Fin m) (g : FiniteGateCode)
    (p q : Clock m×Reg n) :
    -2*(2:ℤ)^(b+1) ≤ (propagationCoeff n b i g p q).1 ∧
    (propagationCoeff n b i g p q).1 ≤ 2*(2:ℤ)^(b+1) ∧
    -2*(2:ℤ)^(b+1) ≤ (propagationCoeff n b i g p q).2 ∧
    (propagationCoeff n b i g p q).2 ≤ 2*(2:ℤ)^(b+1) := by
  have hf:=rawCoeff_bounds n b g p.2 q.2
  have hr:=rawCoeff_bounds n b g q.2 p.2
  have hd : 0 ≤ (2:ℤ)^b:=by positivity
  simp only [pow_succ]
  unfold propagationCoeff
  split_ifs <;> (try dsimp only) <;> omega

theorem propagationTerm_local {m : ℕ} (n b : ℕ) (i : Fin m) (g : FiniteGateCode) :
    (propagationTerm n b i g).support.card≤5 := propSites_card n i g

def boundarySites (m n : ℕ) (last : Bool) (j : Fin n) : Finset (Fin (m+n)) :=
  {j.natAdd m} ∪ (if hm : 0 < m then
    {(if last then (⟨m-1,by omega⟩:Fin m) else ⟨0,hm⟩).castAdd n} else ∅)

def boundaryCoeff (m n b : ℕ) (last : Bool) (j : Fin n)
    (x y : Reg (m+n)) : ℤ :=
  let p:=flattenEquiv m n x
  if regEq x y && (if last then nativeBit p.1 m && !p.2 j
    else !nativeBit p.1 1 && p.2 j) then (2:ℤ)^(b+1) else 0

def boundaryTerm (m n b : ℕ) (last : Bool) (j : Fin n) : IntegerLocalTerm (m+n) :=
  let S:=boundarySites m n last j
  ⟨S,fun u v => boundaryCoeff m n b last j (fill S u) (fill S v),fun _ _ => 0⟩

theorem boundaryTerm_local (m n b : ℕ) (last : Bool) (j : Fin n) :
    (boundaryTerm m n b last j).support.card≤2 := by
  change (boundarySites m n last j).card≤2
  unfold boundarySites
  split_ifs <;> exact le_trans (Finset.card_union_le _ _) (by simp)

def clockPairTerm (m n b J : ℕ) (i j : Fin m) : IntegerLocalTerm (m+n) :=
  let S:Finset (Fin (m+n)):={i.castAdd n,j.castAdd n}
  ⟨S,fun u v =>
    let x:=fill S u
    let y:=fill S v
    if regEq x y && decide (i < j) && !x (i.castAdd n) && x (j.castAdd n)
    then (J:ℤ)*(2:ℤ)^(b+1) else 0,fun _ _ => 0⟩

theorem clockPairTerm_local (m n b J : ℕ) (i j : Fin m) :
    (clockPairTerm m n b J i j).support.card≤2 :=
  le_trans (Finset.card_insert_le _ _) (by simp)

def outputTerms (n b : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) : List (IntegerLocalTerm (gs.length+n)) :=
  let m:=gs.length
  let J:=32*(m+aux.card+1)+1
  (List.finRange m).map (fun i => propagationTerm n b i (gs.get i)) ++
    (aux.sort).map (fun j => boundaryTerm m n b false j) ++
    [boundaryTerm m n b true out] ++
    (List.finRange m).flatMap (fun i =>
      (List.finRange m).map (fun j => clockPairTerm m n b J i j))

theorem outputTerms_length (n b : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    (outputTerms n b gs aux out).length=gs.length+aux.card+1+gs.length^2 := by
  simp [outputTerms,List.length_flatMap,List.sum_replicate,pow_two]
  omega

theorem outputTerms_local (n b : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    ∀t∈outputTerms n b gs aux out,t.support.card≤5 := by
  intro t ht
  simp only [outputTerms,List.mem_append,List.mem_map,List.mem_singleton,List.mem_flatMap] at ht
  rcases ht with ((⟨i,_,rfl⟩|⟨j,_,rfl⟩)|rfl)|⟨i,_,j,_,rfl⟩
  · exact propagationTerm_local _ _ _ _
  · exact (boundaryTerm_local _ _ _ _ _).trans (by omega)
  · exact (boundaryTerm_local _ _ _ _ _).trans (by omega)
  · exact (clockPairTerm_local _ _ _ _ _ _).trans (by omega)

end Qatlib.Concepts.QueryComplexity.DegreeMethod
