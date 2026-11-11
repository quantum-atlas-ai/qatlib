/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessGates
import Qatlib.Concepts.TensorRegisters.RegisterModel.QmaCompletenessLocalSupport
import Qatlib.Concepts.UniformBqp.FiniteGateWord.QmaCompleteness
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Native integer tables for clock Hamiltonians

This module constructs integer local tables for propagation, input, output, and clock-pair terms
from finite gate codes. The type `IntegerLocalTerm` stores a support and real and imaginary
integer matrices, while `value` interprets them as a dyadic matrix on the full register.

Propagation supports contain at most five sites and boundary and clock-pair supports contain at
most two. The list `outputTerms` assembles these pieces with explicit table-size and term-count
bounds for the circuit-to-Hamiltonian construction of [KitaevShenVyalyi2002].

## Main statements

* `propagationTerm_local`: Each propagation term acts on at most five sites.
* `boundaryTerm_local`: Each input or output boundary term acts on at most two sites.
* `outputTerms_length`: Counts the propagation, boundary, and ordered clock-pair terms.
* `outputTerms_local`: Every assembled term has support size at most five.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

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

/-- Splits an `(m + n)`-bit register into its `m`-bit clock and `n`-bit work registers. -/
def flattenEquiv (m n : ℕ) : Reg (m+n)≃Clock m×Reg n :=
  (Fin.appendEquiv (α:=Bool) m n).symm

/-- Reads a one-based clock bit, with the left sentinel true and indices beyond the clock false. -/
def nativeBit {m : ℕ} (c : Clock m) (k : ℕ) : Bool :=
  if hz : k=0 then true
  else if hk : k ≤ m then c ⟨k-1,by omega⟩ else false

/-- The Boolean pre-transition guard at the selected clock site. -/
def preBool {m : ℕ} (i : Fin m) (c : Clock m) : Bool :=
  nativeBit c i.val && !c i && !nativeBit c (i.val+2)

/-- The Boolean post-transition guard at the selected clock site. -/
def postBool {m : ℕ} (i : Fin m) (c : Clock m) : Bool :=
  nativeBit c i.val && c i && !nativeBit c (i.val+2)

/-- Tests a post-to-pre clock pair together with agreement away from the transition site. -/
def hopBool {m : ℕ} (i : Fin m) (r c : Clock m) : Bool :=
  postBool i r && preBool i c && outsideEq i r c

/-- The pre-transition Boolean guard is true exactly when the physical predicate `Pre` holds. -/
theorem preBool_iff {m : ℕ} (i : Fin m) (c : Clock m) :
    preBool i c=true ↔ Pre i c := by
  simp only [preBool,Bool.and_eq_true,Bool.not_eq_true',Pre]
  change ((bit c i.val=true ∧ c i=false) ∧ bit c (i.val+2)=false) ↔ _
  tauto

/-- The post-transition Boolean guard is true exactly when the physical predicate `Post` holds. -/
theorem postBool_iff {m : ℕ} (i : Fin m) (c : Clock m) :
    postBool i c=true ↔ Post i c := by
  simp only [postBool,Bool.and_eq_true,Bool.not_eq_true',Post]
  change ((bit c i.val=true ∧ c i=true) ∧ bit c (i.val+2)=false) ↔ _
  tauto

/-- The clock-hop test is true exactly when the row is post-transition, the column is
pre-transition, and they agree away from the transition site. -/
theorem hopBool_iff {m : ℕ} (i : Fin m) (r c : Clock m) :
    hopBool i r c=true ↔ Post i r ∧ Pre i c ∧ Outside i r c := by
  simp only [hopBool,Bool.and_eq_true,preBool_iff,postBool_iff,outsideEq_true_iff,
    Qatlib.Concepts.UniformBqp.FiniteGateWord.Outside]
  tauto

/-- The valid register wires used by a finite gate code, with empty support for an invalid wire
choice. -/
def gateSites (n : ℕ) (g : FiniteGateCode) : Finset (Fin n) :=
  match g with
  | .h w | .x w | .t w | .tdg w => if h : w < n then {⟨w,h⟩} else ∅
  | .cx c t => if h : c < n ∧ t < n ∧ c≠t then {⟨c,h.1⟩,⟨t,h.2.1⟩} else ∅

/-- The transition clock site together with its neighboring sites when those neighbors exist. -/
def clockSites {m : ℕ} (i : Fin m) : Finset (Fin m) :=
  {i} ∪ (if h : 0 < i.val then {⟨i.val-1,by omega⟩} else ∅) ∪
    (if h : i.val+1 < m then {⟨i.val+1,h⟩} else ∅)

/-- The flattened union of the clock-transition support and the finite gate's work-register
support. -/
def propSites {m : ℕ} (n : ℕ) (i : Fin m) (g : FiniteGateCode) :
    Finset (Fin (m+n)) :=
  (clockSites i).image (Fin.castAdd n) ∪ (gateSites n g).image (Fin.natAdd m)

/-- A finite gate code uses at most two work-register sites. -/
theorem gateSites_card (n : ℕ) (g : FiniteGateCode) : (gateSites n g).card≤2 := by
  cases g <;> dsimp only [gateSites] <;> split_ifs <;>
    first | exact le_trans (Finset.card_insert_le _ _) (by simp) | simp

/-- A clock-transition support contains at most three sites. -/
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

/-- A propagation support contains at most five sites. -/
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

/-- An integer encoding of a local matrix, consisting of a finite qubit support and real and
imaginary integer coefficient tables. -/
structure IntegerLocalTerm (N : ℕ) where
  support : Finset (Fin N)
  re : Matrix (Reg support.card) (Reg support.card) ℤ
  im : Matrix (Reg support.card) (Reg support.card) ℤ

/-- Interprets the local integer tables at dyadic width `b` and lifts the resulting matrix to
the full register. -/
noncomputable def value {N : ℕ} (b : ℕ) (t : IntegerLocalTerm N) :
    Matrix (Reg N) (Reg N) ℂ :=
  Qatlib.Concepts.TensorRegisters.RegisterModel.partitionLift (split t.support)
    (fun u v => dyadicValue b (t.re u v) (t.im u v))

/-- Lists the real and imaginary integer coefficients in rows indexed by the bit-vector
enumeration of the support. -/
def table {N : ℕ} (t : IntegerLocalTerm N) : List (List (ℤ×ℤ)) :=
  List.ofFn (fun p : Fin (2^t.support.card) =>
    List.ofFn (fun q : Fin (2^t.support.card) =>
      (t.re ((bitVecEquiv _).symm p) ((bitVecEquiv _).symm q),
       t.im ((bitVecEquiv _).symm p) ((bitVecEquiv _).symm q))))

/-- The coefficient table has `2^t.support.card` rows. -/
theorem table_rows {N : ℕ} (t : IntegerLocalTerm N) : (table t).length=2^t.support.card := by
  simp [table]

/-- Every row of the coefficient table has length `2^t.support.card`. -/
theorem table_row_length {N : ℕ} (t : IntegerLocalTerm N)
    (r : List (ℤ×ℤ)) (hr : r∈table t) : r.length=2^t.support.card := by
  obtain ⟨p,rfl⟩ := List.mem_ofFn.mp hr
  simp

/-- A coefficient table supported on at most five qubits has at most `32` rows. -/
theorem table_rows_le {N : ℕ} (t : IntegerLocalTerm N) (h : t.support.card≤5) :
    (table t).length≤32 := by
  rw [table_rows]
  exact_mod_cast Nat.pow_le_pow_right (by omega : 1≤2) h

/-- The integer real and imaginary propagation coefficients formed from the diagonal clock
guards and the forward and reverse gate coefficients. -/
def propagationCoeff {m : ℕ} (n b : ℕ) (i : Fin m) (g : FiniteGateCode)
    (p q : Clock m×Reg n) : ℤ×ℤ :=
  let diag : ℤ := if regEq p.1 q.1 && regEq p.2 q.2 then
      (if postBool i p.1 then (2:ℤ)^b else 0)+
      (if preBool i p.1 then (2:ℤ)^b else 0) else 0
  let fwd := if hopBool i p.1 q.1 then rawCoeff n b g p.2 q.2 else (0,0)
  let rev := if hopBool i q.1 p.1 then rawCoeff n b g q.2 p.2 else (0,0)
  (diag-fwd.1-rev.1,-fwd.2+rev.2)

/-- The integer local propagation term obtained by restricting the propagation coefficients to
the flattened propagation support. -/
def propagationTerm {m : ℕ} (n b : ℕ) (i : Fin m) (g : FiniteGateCode) :
    IntegerLocalTerm (m+n) :=
  let S:=propSites n i g
  let c:=fun u v : Reg S.card => propagationCoeff n b i g
    (flattenEquiv m n (fill S u)) (flattenEquiv m n (fill S v))
  ⟨S,fun u v => (c u v).1,fun u v => (c u v).2⟩

/-- Both components of each propagation coefficient lie between `-2 * 2^(b + 1)` and `2 * 2^(b +
1)`. -/
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

/-- Every native propagation term has support size at most five. -/
theorem propagationTerm_local {m : ℕ} (n b : ℕ) (i : Fin m) (g : FiniteGateCode) :
    (propagationTerm n b i g).support.card≤5 := propSites_card n i g

/-- The boundary support containing the designated work bit and, for a nonempty clock, the first
or last clock bit. -/
def boundarySites (m n : ℕ) (last : Bool) (j : Fin n) : Finset (Fin (m+n)) :=
  {j.natAdd m} ∪ (if hm : 0 < m then
    {(if last then (⟨m-1,by omega⟩:Fin m) else ⟨0,hm⟩).castAdd n} else ∅)

/-- The diagonal integer boundary coefficient, equal to `2^(b + 1)` on the selected boundary
violation and zero elsewhere. -/
def boundaryCoeff (m n b : ℕ) (last : Bool) (j : Fin n)
    (x y : Reg (m+n)) : ℤ :=
  let p:=flattenEquiv m n x
  if regEq x y && (if last then nativeBit p.1 m && !p.2 j
    else !nativeBit p.1 1 && p.2 j) then (2:ℤ)^(b+1) else 0

/-- The integer local table for the selected input or output boundary penalty. -/
def boundaryTerm (m n b : ℕ) (last : Bool) (j : Fin n) : IntegerLocalTerm (m+n) :=
  let S:=boundarySites m n last j
  ⟨S,fun u v => boundaryCoeff m n b last j (fill S u) (fill S v),fun _ _ => 0⟩

/-- Every native boundary term has support size at most two. -/
theorem boundaryTerm_local (m n b : ℕ) (last : Bool) (j : Fin n) :
    (boundaryTerm m n b last j).support.card≤2 := by
  change (boundarySites m n last j).card≤2
  unfold boundarySites
  split_ifs <;> exact le_trans (Finset.card_union_le _ _) (by simp)

/-- The integer local table for a clock-pair violation weighted by `J`, with zero imaginary
coefficients. -/
def clockPairTerm (m n b J : ℕ) (i j : Fin m) : IntegerLocalTerm (m+n) :=
  let S:Finset (Fin (m+n)):={i.castAdd n,j.castAdd n}
  ⟨S,fun u v =>
    let x:=fill S u
    let y:=fill S v
    if regEq x y && decide (i < j) && !x (i.castAdd n) && x (j.castAdd n)
    then (J:ℤ)*(2:ℤ)^(b+1) else 0,fun _ _ => 0⟩

/-- Every native clock-pair term has support size at most two. -/
theorem clockPairTerm_local (m n b J : ℕ) (i j : Fin m) :
    (clockPairTerm m n b J i j).support.card≤2 :=
  le_trans (Finset.card_insert_le _ _) (by simp)

/-- Assembles propagation terms, auxiliary input penalties, one output penalty, and all ordered
clock-pair penalties with weight `32 * (gs.length + aux.card + 1) + 1`. -/
def outputTerms (n b : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) : List (IntegerLocalTerm (gs.length+n)) :=
  let m:=gs.length
  let J:=32*(m+aux.card+1)+1
  (List.finRange m).map (fun i => propagationTerm n b i (gs.get i)) ++
    (aux.sort).map (fun j => boundaryTerm m n b false j) ++
    [boundaryTerm m n b true out] ++
    (List.finRange m).flatMap (fun i =>
      (List.finRange m).map (fun j => clockPairTerm m n b J i j))

/-- The assembled term list has length `gs.length + aux.card + 1 + gs.length^2`. -/
theorem outputTerms_length (n b : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    (outputTerms n b gs aux out).length=gs.length+aux.card+1+gs.length^2 := by
  simp [outputTerms,List.length_flatMap,List.sum_replicate,pow_two]
  omega

/-- Every term in the assembled output list has support size at most five. -/
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
