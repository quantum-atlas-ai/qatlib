/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessNativeOutput
import Qatlib.Concepts.QmaCompleteness.HistoryHam.QmaCompletenessRefined
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Papers.LocalHam06.MainResults

open Qatlib Matrix
open  Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.TensorRegisters.RegisterModel
open scoped Classical BigOperators
set_option autoImplicit false

def nativeWires {N : ℕ} (S : Finset (Fin N)) : List (Fin N) :=
  (List.finRange S.card).map (wireEmbedding S)

theorem nativeWires_length {N : ℕ} (S : Finset (Fin N)) :
    (nativeWires S).length=S.card := by
  simp [nativeWires]

theorem nativeWires_get {N : ℕ} (S : Finset (Fin N))
    (j : Fin (nativeWires S).length) :
    (nativeWires S).get j=wireEmbedding S (Fin.cast (nativeWires_length S) j) := by
  change ((List.finRange S.card).map (wireEmbedding S))[j.val]=_
  rw [List.getElem_map,List.getElem_finRange]
  rfl

theorem nativeWires_mem {N : ℕ} (S : Finset (Fin N)) (i : Fin N) :
    i∈nativeWires S ↔ i∈S := by
  rw [nativeWires,List.mem_map]
  constructor
  · rintro ⟨j,_,rfl⟩
    exact Finset.orderEmbOfFin_mem S rfl j
  · intro hi
    let j : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨i,hi⟩
    refine ⟨j,by simp,?_⟩
    exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨i,hi⟩)

theorem nativeWires_nodup {N : ℕ} (S : Finset (Fin N)) : (nativeWires S).Nodup := by
  rw [nativeWires,← List.ofFn_eq_map]
  exact List.nodup_ofFn_ofInjective (wireEmbedding S).injective

def nativeIndexDecode {N : ℕ} (S : Finset (Fin N))
    (p : Fin (2^(nativeWires S).length)) : Reg S.card :=
  fun j => (bitVecEquiv (nativeWires S).length).symm p
    (Fin.cast (nativeWires_length S).symm j)

theorem nativeIndexDecode_lhBitIndex {N : ℕ} (S : Finset (Fin N)) (x : Reg N) :
    nativeIndexDecode S (lhBitIndex (nativeWires S) x)=mask S x := by
  funext j
  simp only [nativeIndexDecode,lhBitIndex,Equiv.symm_apply_apply]
  change x ((nativeWires S).get (Fin.cast (nativeWires_length S).symm j))=
    x (wireEmbedding S j)
  rw [nativeWires_get]
  congr 1

theorem lhAgreeOutside_nativeWires_iff {N : ℕ} (S : Finset (Fin N)) (x y : Reg N) :
    lhAgreeOutside (nativeWires S) x y=true ↔ outside S x=outside S y := by
  constructor
  · intro h
    apply (outside_eq_iff S x y).mpr
    intro j hj
    have he := (List.all_eq_true.mp h) j (by simp)
    have hor : j∈nativeWires S ∨ x j=y j := by
      simpa only [Bool.or_eq_true,List.contains_iff_mem,beq_iff_eq] using he
    exact hor.resolve_left (fun hw => hj ((nativeWires_mem S j).mp hw))
  · intro h
    apply List.all_eq_true.mpr
    intro j _
    rw [Bool.or_eq_true,List.contains_iff_mem,beq_iff_eq]
    by_cases hj : j∈S
    · exact Or.inl ((nativeWires_mem S j).mpr hj)
    · exact Or.inr ((outside_eq_iff S x y).mp h j hj)

def toLhTerm {N : ℕ} (t : IntegerLocalTerm N) : LhTerm N where
  wires := nativeWires t.support
  re := fun p q => t.re (nativeIndexDecode t.support p) (nativeIndexDecode t.support q)
  im := fun p q => t.im (nativeIndexDecode t.support p) (nativeIndexDecode t.support q)

theorem toLhTerm_wire_length {N : ℕ} (t : IntegerLocalTerm N) :
    (toLhTerm t).wires.length=t.support.card := nativeWires_length t.support

theorem lhEmbedTerm_toLhTerm {N : ℕ} (b : ℕ) (t : IntegerLocalTerm N) :
    lhEmbedTerm b (toLhTerm t)=value b t := by
  ext x y
  change
    (if lhAgreeOutside (nativeWires t.support) x y then
      dyadicValue b
        (t.re (nativeIndexDecode t.support (lhBitIndex (nativeWires t.support) x))
          (nativeIndexDecode t.support (lhBitIndex (nativeWires t.support) y)))
        (t.im (nativeIndexDecode t.support (lhBitIndex (nativeWires t.support) x))
          (nativeIndexDecode t.support (lhBitIndex (nativeWires t.support) y)))
      else 0) =
    partitionLift (split t.support)
      (fun u v => dyadicValue b (t.re u v) (t.im u v)) x y
  rw [Qatlib.Concepts.TensorRegisters.RegisterModel.partitionLift_apply]
  simp only [nativeIndexDecode_lhBitIndex]
  by_cases ho : outside t.support x=outside t.support y
  · rw [if_pos ((lhAgreeOutside_nativeWires_iff t.support x y).mpr ho),if_pos ho]
  · have ha : lhAgreeOutside (nativeWires t.support) x y=false := by
      cases h : lhAgreeOutside (nativeWires t.support) x y
      · rfl
      · exact False.elim (ho ((lhAgreeOutside_nativeWires_iff t.support x y).mp h))
    simp [ha,ho]

def toLhEncoding {N : ℕ} (b : ℕ) (ts : List (IntegerLocalTerm N)) : LhEncoding where
  qubitCount := N
  width := b
  terms := ts.map toLhTerm

theorem toLhEncoding_semantics {N : ℕ} (b : ℕ) (ts : List (IntegerLocalTerm N)) :
    lhHamiltonian (toLhEncoding b ts)=(ts.map (value b)).foldr
      (fun A B : Matrix (Reg N) (Reg N) ℂ => A+B) (0:Matrix (Reg N) (Reg N) ℂ) := by
  simp only [lhHamiltonian,toLhEncoding,List.map_map,Function.comp_def,lhEmbedTerm_toLhTerm]

theorem toLhEncoding_local {N : ℕ} (b k : ℕ) (ts : List (IntegerLocalTerm N))
    (h : ∀t∈ts,t.support.card≤k) : lhLocal k (toLhEncoding b ts) := by
  intro t ht
  change t∈ts.map toLhTerm at ht
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
  change (nativeWires u.support).length ≤ k
  rw [nativeWires_length]
  exact h u hu

def actualEncoding (n b : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) : LhEncoding :=
  toLhEncoding (b+1) (outputTerms n b gs aux out)

theorem actualEncoding_local (n b : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    lhLocal 5 (actualEncoding n b gs aux out) :=
  toLhEncoding_local (b+1) 5 _ (outputTerms_local n b gs aux out)

theorem actualEncoding_term_count (n b : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    (actualEncoding n b gs aux out).terms.length=
      gs.length+aux.card+1+gs.length^2 := by
  simpa only [actualEncoding,toLhEncoding,List.length_map] using
    outputTerms_length n b gs aux out

theorem encoded_equality_implies_formal_equality {N M : ℕ} (b c : ℕ)
    (ts : List (IntegerLocalTerm N)) (us : List (IntegerLocalTerm M))
    (h : qmaClause3ToBits (toLhEncoding b ts)=qmaClause3ToBits (toLhEncoding c us)) :
    toLhEncoding b ts=toLhEncoding c us := clause3Aux_toBits_injective h

theorem encNat_length (v : ℕ) : (qmaClause3EncNat v).length=2*v.log2+3 := by
  simp [qmaClause3EncNat,qmaClause3GammaBits,clause3Aux_natBits_length]
  omega

theorem encInt_length (v : ℤ) : (qmaClause3EncInt v).length=2*v.natAbs.log2+4 := by
  simp only [qmaClause3EncInt,List.length_cons,encNat_length]

theorem log2_le_of_le_pow_two (v E : ℕ) (h : v≤2^E) : v.log2≤E := by
  rw [Nat.log2_eq_log_two]
  simpa only [Nat.log_pow (by decide : 1<2)] using (Nat.log_mono_right (b:=2) h)

theorem encInt_length_le_of_natAbs_le_pow (v : ℤ) (E : ℕ) (h : v.natAbs≤2^E) :
    (qmaClause3EncInt v).length≤2*E+4 := by
  rw [encInt_length]
  have hh := log2_le_of_le_pow_two v.natAbs E h
  omega

theorem encList_length {A : Type} (f : A→List Bool) (xs : List A) :
    (qmaClause3EncList f xs).length=
      xs.length+1+((xs.map f).map List.length).sum := by
  simp only [qmaClause3EncList,qmaClause3GammaBits,List.length_append,List.length_replicate,
    List.length_singleton,List.length_flatten]

end Qatlib.Papers.LocalHam06.MainResults
