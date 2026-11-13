/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermal.FiniteThermalMaskedX

/-!
# Reversible binary comparators and interval tests

This module compiles binary comparison with a fixed threshold into finite gate words using
masked controlled X operations. Binary lists are read with the most significant bit first, and
the basis and coherent semantics toggle only the target while restoring workspace initialized to
false.

The comparator and half-open interval constructions include legality, adjoint behavior, exact
gate counts, and quadratic upper bounds, using elementary reversible circuit techniques as in
[BarencoEtAl1995].

## Main statements

* `thermalLexLess_numeric`: lexicographic comparison agrees with comparison of binary values.
* `thermalComparatorWord_numeric`: the comparator toggles the target according to the threshold
  test.
* `thermalIntervalWord_coherent`: the interval word implements the half-open interval test on
  superpositions with clean workspace.
* `thermalIntervalWord_cost`: gives an exact count and the bound `2 + 64 * hi.length ^ 2`.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
open Qatlib Matrix
open scoped BigOperators

/-- The natural number represented by a Boolean list with its most significant bit first, with
the empty list representing zero. -/
def thermalBitValue : List Bool → ℕ
  | [] => 0
  | b::bs => (if b then 2^bs.length else 0)+thermalBitValue bs

/-- The value represented by a Boolean list is strictly less than two raised to its length. -/
theorem thermalBitValue_bound (bs : List Bool) : thermalBitValue bs < 2^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    simp only [thermalBitValue,List.length_cons,pow_succ]
    cases b <;> simp <;> omega

/-- The Boolean lexicographic comparison of two bit lists, returning false when either list is
empty and otherwise comparing the first unequal bits. -/
def thermalLexLess : List Bool → List Bool → Bool
  | [],_ => false
  | _,[] => false
  | x::xs,b::bs => if x=b then thermalLexLess xs bs else (!x && b)

/-- For bit lists of equal length, `thermalLexLess` equals the decision of strict comparison
between their binary values. -/
theorem thermalLexLess_numeric (xs bs : List Bool) (hlen : xs.length=bs.length) :
    thermalLexLess xs bs=decide (thermalBitValue xs < thermalBitValue bs) := by
  induction xs generalizing bs with
  | nil => cases bs <;> simp [thermalLexLess,thermalBitValue] at hlen ⊢
  | cons x xs ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hl : xs.length=bs.length := by simpa using hlen
      have hi:=ih bs hl
      have hx:=thermalBitValue_bound xs
      have hb:=thermalBitValue_bound bs
      rw [hl] at hx
      cases x with
      | false => cases b with
        | false => simpa [thermalLexLess,thermalBitValue] using hi
        | true =>
          apply Bool.eq_iff_iff.mpr
          simp [thermalLexLess,thermalBitValue]
          omega
      | true => cases b with
        | false =>
          apply Bool.eq_iff_iff.mpr
          simp [thermalLexLess,thermalBitValue,hl]
          omega
        | true => simpa [thermalLexLess,thermalBitValue,hl] using hi

/-- Two Boolean predicates agreeing on every member of a list give the same result under
`List.all`. -/
private theorem all_congr_mem {A : Type*} (as : List A) (p q : A → Bool)
    (h : ∀ a∈as,p a=q a) : as.all p=as.all q := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro hp a ha
    rw [← h a ha]
    exact hp a ha
  · intro hq a ha
    rw [h a ha]
    exact hq a ha

/-- Appending a control wire to a masked match conjoins the previous match with the positive or
negative test for that wire. -/
private theorem match_append {n : ℕ} (pre zs : List (Fin n)) (w : Fin n) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    thermalMatch (pre++[w]) zs x =
      (thermalMatch pre zs x && (if w∈zs then !x w else x w)) := by
  simp [thermalMatch]

/-- Appending a new control wire to both the control list and the zero-mask list conjoins the
previous match with the negation of that wire's bit. -/
private theorem match_append_zero {n : ℕ} (pre zs : List (Fin n)) (w : Fin n)
    (hw : w∉pre) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    thermalMatch (pre++[w]) (zs++[w]) x=(thermalMatch pre zs x && !x w) := by
  have he : pre.all (fun c => if c∈zs++[w] then !x c else x c) =
      pre.all (fun c => if c∈zs then !x c else x c) := by
    apply all_congr_mem
    intro c hc
    have hcw : c≠w := fun h => hw (h ▸ hc)
    simp [hcw]
  simp only [thermalMatch,List.all_append,List.all_cons,List.all_nil,Bool.and_true]
  rw [he]
  simp

/-- Changing a bit outside the control list leaves `thermalMatch` unchanged. -/
private theorem match_update {n : ℕ} (pre zs : List (Fin n)) (t : Fin n)
    (ht : t∉pre) (x : Qatlib.Foundations.PureStateMath.Reg n) (v : Bool) :
    thermalMatch pre zs (Function.update x t v)=thermalMatch pre zs x := by
  unfold thermalMatch
  apply all_congr_mem
  intro c hc
  have hct : c≠t := fun h => ht (h ▸ hc)
  simp [Function.update_of_ne hct]

/-- The recursive XOR of masked prefix matches contributing to comparison against the fixed
bits, beginning with control prefix `pre` and zero-mask prefix `zs`. -/
def thermalPrefixParity {n : ℕ} (pre zs : List (Fin n)) : List (Fin n × Bool) → Qatlib.Foundations.PureStateMath.Reg n → Bool
  | [],_ => false
  | (w,b)::rest,x =>
      (if b then thermalMatch (pre++[w]) (zs++[w]) x else false) ^^
      thermalPrefixParity (pre++[w]) (if b then zs else zs++[w]) rest x

/-- For distinct prefix and data wires and a zero-mask contained in the prefix,
`thermalPrefixParity` is the conjunction of the prefix match and lexicographic comparison of
the data bits with the fixed bits. -/
theorem thermalPrefixParity_lex {n : ℕ} (pre zs : List (Fin n))
    (ps : List (Fin n × Bool)) (hn : (pre++ps.map Prod.fst).Nodup)
    (hs : ∀ w∈zs,w∈pre) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    thermalPrefixParity pre zs ps x =
      (thermalMatch pre zs x && thermalLexLess (ps.map (fun p => x p.1)) (ps.map Prod.snd)) := by
  induction ps generalizing pre zs with
  | nil => simp [thermalPrefixParity,thermalLexLess]
  | cons p ps ih =>
    obtain ⟨w,b⟩ := p
    change (pre++w::ps.map Prod.fst).Nodup at hn
    have hw : w∉pre := by
      intro hp
      exact (List.disjoint_left.mp hn.disjoint) hp (by simp)
    have hwz : w∉zs := fun h => hw (hs w h)
    have hr : ((pre++[w])++ps.map Prod.fst).Nodup := by
      simpa [List.append_assoc] using hn
    have hp : ∀ u∈zs,u∈pre++[w] := by
      intro u hu
      exact List.mem_append_left [w] (hs u hu)
    have hz : ∀ u∈zs++[w],u∈pre++[w] := by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact List.mem_append_left [w] (hs u h)
      · exact List.mem_append_right pre h
    cases b with
    | false =>
      simp only [thermalPrefixParity,Bool.false_eq_true,if_false,Bool.false_xor,List.map_cons]
      rw [ih (pre++[w]) (zs++[w]) hr hz,match_append_zero pre zs w hw x]
      simp only [thermalLexLess]
      generalize thermalMatch pre zs x = P
      generalize x w = u
      generalize thermalLexLess (List.map (fun p => x p.1) ps) (List.map Prod.snd ps) = L
      cases P <;> cases u <;> cases L <;> rfl
    | true =>
      simp only [thermalPrefixParity,if_true,List.map_cons]
      rw [ih (pre++[w]) zs hr hp,match_append_zero pre zs w hw x,
        match_append pre zs w x,if_neg hwz]
      simp only [thermalLexLess]
      generalize thermalMatch pre zs x = P
      generalize x w = u
      generalize thermalLexLess (List.map (fun p => x p.1) ps) (List.map Prod.snd ps) = L
      cases P <;> cases u <;> cases L <;> rfl

/-- Changing a bit outside both the prefix and data wires leaves `thermalPrefixParity`
unchanged. -/
private theorem parity_update {n : ℕ} (pre zs : List (Fin n)) (ps : List (Fin n × Bool))
    (t : Fin n) (ht : t∉pre++ps.map Prod.fst) (x : Qatlib.Foundations.PureStateMath.Reg n) (v : Bool) :
    thermalPrefixParity pre zs ps (Function.update x t v)=thermalPrefixParity pre zs ps x := by
  induction ps generalizing pre zs with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨w,b⟩ := p
    have hr : t∉(pre++[w])++ps.map Prod.fst := by
      simpa [List.append_assoc] using ht
    have hp : t∉pre++[w] := fun h => hr (List.mem_append_left _ h)
    simp only [thermalPrefixParity]
    rw [match_update (pre++[w]) (zs++[w]) t hp x v,
      ih (pre++[w]) (if b then zs else zs++[w]) hr]

/-- The recursive finite gate word that accumulates masked prefix tests into target `t` to
compare the data bits with the fixed bits in the wire-bit list. -/
noncomputable def thermalLessWord {n : ℕ} (pre zs : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) : List (Fin n × Bool) → List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode
  | [] => []
  | (w,b)::rest =>
      (if b then thermalMaskedX (pre++[w]) (zs++[w]) t ws else []) ++
      thermalLessWord (pre++[w]) (if b then zs else zs++[w]) t ws rest

/-- For distinct listed wires, a distinct zero-mask contained in the prefix, sufficient
workspace, and workspace bits initially false, `thermalLessWord` toggles only `t` by
`thermalPrefixParity pre zs ps x`. -/
theorem thermalLessWord_basis {n : ℕ} (pre zs : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) (ps : List (Fin n × Bool))
    (hn : ((pre++ps.map Prod.fst)++t::ws).Nodup) (hz : zs.Nodup)
    (hs : ∀ w∈zs,w∈pre) (hlen : pre.length+ps.length ≤ ws.length+2)
    (x : Qatlib.Foundations.PureStateMath.Reg n) (hc : ∀ w∈ws,x w=false) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalLessWord pre zs t ws ps))
      (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ thermalPrefixParity pre zs ps x)) := by
  induction ps generalizing pre zs x with
  | nil => simp [thermalLessWord,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,thermalPrefixParity]
  | cons p ps ih =>
    obtain ⟨w,b⟩ := p
    have hcontrols : (pre++w::ps.map Prod.fst).Nodup := by
      simpa only [List.map_cons] using hn.of_append_left
    have hw : w∉pre := by
      intro hp
      exact (List.disjoint_left.mp hcontrols.disjoint) hp (by simp)
    have hwz : w∉zs := fun h => hw (hs w h)
    have hznew : (zs++[w]).Nodup := by
      simpa using (List.nodup_concat zs w).mpr ⟨hwz,hz⟩
    have hr : (((pre++[w])++ps.map Prod.fst)++t::ws).Nodup := by
      simpa [List.map_cons,List.append_assoc] using hn
    have hp : ∀ u∈zs,u∈pre++[w] := by
      intro u hu
      exact List.mem_append_left [w] (hs u hu)
    have hzs : ∀ u∈zs++[w],u∈pre++[w] := by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact List.mem_append_left [w] (hs u h)
      · exact List.mem_append_right pre h
    have hlr : (pre++[w]).length+ps.length ≤ ws.length+2 := by
      simp only [List.length_append,List.length_cons,List.length_nil] at hlen ⊢
      omega
    cases b with
    | false =>
      simpa only [thermalLessWord,thermalPrefixParity,Bool.false_eq_true,if_false,
        List.nil_append,Bool.false_xor] using ih (pre++[w]) (zs++[w]) hr hznew hzs hlr x hc
    | true =>
      have hsub : List.Sublist ((pre++[w])++t::ws) (((pre++[w])++ps.map Prod.fst)++t::ws) := by
        simpa only [List.append_assoc] using
          (List.sublist_append_right (ps.map Prod.fst) (t::ws)).append_left (pre++[w])
      have hmframe := List.Nodup.sublist hsub hr
      have hlm : (pre++[w]).length ≤ ws.length+2 := by
        have h := Nat.le_add_right (pre++[w]).length ps.length
        exact h.trans hlr
      have hm := thermalMaskedX_basis (pre++[w]) (zs++[w]) t ws hmframe hznew hzs hlm x hc
      let v := x t ^^ thermalMatch (pre++[w]) (zs++[w]) x
      let y := Function.update x t v
      have htws : t∉ws := (List.nodup_cons.mp hr.of_append_right).1
      have hyc : ∀ u∈ws,y u=false := by
        intro u hu
        have hut : u≠t := fun h => htws (h ▸ hu)
        simpa only [y,Function.update_of_ne hut] using hc u hu
      have htarget : t∉(pre++[w])++ps.map Prod.fst := by
        intro ht
        exact (List.disjoint_left.mp hr.disjoint) ht (by simp)
      have hrec := ih (pre++[w]) zs hr hz hp hlr y hyc
      rw [parity_update (pre++[w]) zs ps t htarget x v] at hrec
      simp only [thermalLessWord,if_true,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,List.map_append,Qatlib.Foundations.QueryWordCore.Circuit.run_append]
      change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalLessWord (pre++[w]) zs t ws ps))
        (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalMaskedX (pre++[w]) (zs++[w]) t ws))
          (Qatlib.Foundations.PureStateMath.Ket x)) = _
      rw [hm,hrec]
      dsimp only [y,v]
      simp [thermalPrefixParity]

/-- For distinct data, target, and workspace wires with sufficient workspace initially false,
the empty-prefix comparison word toggles only `t` according to strict comparison of the data
value with the fixed binary value. -/
theorem thermalLessWord_numeric {n : ℕ} (t : Fin n) (ws : List (Fin n))
    (ps : List (Fin n × Bool)) (hn : (ps.map Prod.fst++t::ws).Nodup)
    (hlen : ps.length ≤ ws.length+2) (x : Qatlib.Foundations.PureStateMath.Reg n) (hc : ∀ w∈ws,x w=false) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalLessWord [] [] t ws ps))
      (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (Function.update x t
        (x t ^^ decide (thermalBitValue (ps.map (fun p => x p.1)) < thermalBitValue (ps.map Prod.snd)))) := by
  have h := thermalLessWord_basis [] [] t ws ps (by simpa using hn) (by simp)
    (by simp) (by simpa using hlen) x hc
  rw [thermalPrefixParity_lex [] [] ps (by simpa using hn.of_append_left) (by simp)] at h
  simp only [thermalMatch,List.all_nil,Bool.true_and] at h
  rw [thermalLexLess_numeric _ _ (by simp)] at h
  exact h

/-- The recursive comparison word is legal when the prefix, data, target, and workspace wires
are distinct and `pre.length + ps.length ≤ ws.length + 2`. -/
theorem thermalLessWord_legal {n : ℕ} (pre zs : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) (ps : List (Fin n × Bool))
    (hn : ((pre++ps.map Prod.fst)++t::ws).Nodup)
    (hlen : pre.length+ps.length ≤ ws.length+2) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalLessWord pre zs t ws ps)=true := by
  induction ps generalizing pre zs with
  | nil => simp [thermalLessWord,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal]
  | cons p ps ih =>
    obtain ⟨w,b⟩ := p
    have hr : (((pre++[w])++ps.map Prod.fst)++t::ws).Nodup := by
      simpa [List.map_cons,List.append_assoc] using hn
    have hsub : List.Sublist ((pre++[w])++t::ws) (((pre++[w])++ps.map Prod.fst)++t::ws) := by
      simpa only [List.append_assoc] using
        (List.sublist_append_right (ps.map Prod.fst) (t::ws)).append_left (pre++[w])
    have hmframe := List.Nodup.sublist hsub hr
    have hlr : (pre++[w]).length+ps.length ≤ ws.length+2 := by
      simp only [List.length_append,List.length_cons,List.length_nil] at hlen ⊢
      omega
    have hlm : (pre++[w]).length ≤ ws.length+2 := (Nat.le_add_right _ _).trans hlr
    cases b with
    | false =>
      simpa only [thermalLessWord,Bool.false_eq_true,if_false,List.nil_append] using
        ih (pre++[w]) (zs++[w]) hr hlr
    | true =>
      have ha := thermalMaskedX_legal (pre++[w]) (zs++[w]) t ws hmframe hlm
      have hb := ih (pre++[w]) zs hr hlr
      simpa only [thermalLessWord,if_true,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,List.all_append,Bool.and_eq_true]
        using And.intro ha hb

/-- The recursive gate count for the strict-comparison construction, tracking the current prefix
length `k` and zero-mask length `z`. -/
def thermalLessCost (k z : ℕ) : List Bool → ℕ
  | [] => 0
  | b::bs => (if b then 2*(z+1)+(if k+1 ≤ 1 then 1 else 15*(2*(k+1)-3)) else 0) +
      thermalLessCost (k+1) (if b then z else z+1) bs

/-- When `pre.length + ps.length ≤ ws.length + 2`, the comparison word has gate count
`thermalLessCost pre.length zs.length (ps.map Prod.snd)` and zero queries. -/
theorem thermalLessWord_cost {n : ℕ} (pre zs : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) (ps : List (Fin n × Bool))
    (hlen : pre.length+ps.length ≤ ws.length+2) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalLessWord pre zs t ws ps)) =
      thermalLessCost pre.length zs.length (ps.map Prod.snd) ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalLessWord pre zs t ws ps))=0 := by
  refine ⟨?_,(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).1⟩
  rw [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).2]
  induction ps generalizing pre zs with
  | nil => simp [thermalLessWord,thermalLessCost]
  | cons p ps ih =>
    obtain ⟨w,b⟩ := p
    have hlr : (pre++[w]).length+ps.length ≤ ws.length+2 := by
      simp only [List.length_append,List.length_cons,List.length_nil] at hlen ⊢
      omega
    have hlm : (pre++[w]).length ≤ ws.length+2 := (Nat.le_add_right _ _).trans hlr
    cases b with
    | false =>
      simpa [thermalLessWord,thermalLessCost] using ih (pre++[w]) (zs++[w]) hlr
    | true =>
      have hm := (thermalMaskedX_cost (pre++[w]) (zs++[w]) t ws hlm).1
      rw [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).2] at hm
      have hr := ih (pre++[w]) zs hlr
      simp only [thermalLessWord,if_true,List.length_append,List.map_cons,thermalLessCost]
      rw [hm,hr]
      simp

/-- If `z ≤ k`, the recursive comparison cost is at most `32 * (k + bs.length) * bs.length`. -/
theorem thermalLessCost_bound (bs : List Bool) (k z : ℕ) (hz : z≤k) :
    thermalLessCost k z bs ≤ 32*(k+bs.length)*bs.length := by
  induction bs generalizing k z with
  | nil => simp [thermalLessCost]
  | cons b bs ih =>
    have hg : (if k+1 ≤ 1 then 1 else 15*(2*(k+1)-3)) ≤ 30*(k+1) := by
      split_ifs <;> omega
    have hs : 2*(z+1)+(if k+1 ≤ 1 then 1 else 15*(2*(k+1)-3)) ≤ 32*(k+1) := by
      omega
    cases b with
    | false =>
      have hr := ih (k+1) (z+1) (by omega)
      simp only [thermalLessCost,Bool.false_eq_true,if_false,Nat.zero_add,List.length_cons]
      nlinarith
    | true =>
      have hr := ih (k+1) z (by omega)
      simp only [thermalLessCost,if_true,List.length_cons]
      nlinarith

/-- The finite word that applies X to `t` when `full` is true and otherwise compares the data
bits with the fixed bits using `thermalLessWord`. -/
noncomputable def thermalComparatorWord {n : ℕ} (full : Bool) (ps : List (Fin n × Bool))
    (t : Fin n) (ws : List (Fin n)) : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode :=
  if full then [.x t.val] else thermalLessWord [] [] t ws ps

/-- For distinct listed wires and sufficient workspace initialized to false, the comparator
toggles only `t` when the data value is below the fixed threshold, taking the threshold as
`2 ^ ps.length` when `full` is true. -/
theorem thermalComparatorWord_numeric {n : ℕ} (full : Bool) (ps : List (Fin n × Bool))
    (t : Fin n) (ws : List (Fin n)) (hn : (ps.map Prod.fst++t::ws).Nodup)
    (hlen : ps.length ≤ ws.length+2) (x : Qatlib.Foundations.PureStateMath.Reg n) (hc : ∀ w∈ws,x w=false) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalComparatorWord full ps t ws))
      (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (Function.update x t
        (x t ^^ decide (thermalBitValue (ps.map (fun p => x p.1)) <
          (if full then 2^ps.length else thermalBitValue (ps.map Prod.snd))))) := by
  cases full with
  | false => simpa [thermalComparatorWord] using thermalLessWord_numeric t ws ps hn hlen x hc
  | true =>
    have hb := thermalBitValue_bound (ps.map (fun p => x p.1))
    simp only [List.length_map] at hb
    have h := thermalMultiX_basis ([] : List (Fin n)) t [] (by simp) (by simp) x (by simp)
    simpa [thermalComparatorWord,thermalMultiX,thermalControl,hb] using h

/-- The comparator word is legal for distinct data, target, and workspace wires with `ps.length
≤ ws.length + 2`. -/
theorem thermalComparatorWord_legal {n : ℕ} (full : Bool) (ps : List (Fin n × Bool))
    (t : Fin n) (ws : List (Fin n)) (hn : (ps.map Prod.fst++t::ws).Nodup)
    (hlen : ps.length ≤ ws.length+2) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalComparatorWord full ps t ws)=true := by
  cases full with
  | false =>
    simpa [thermalComparatorWord] using (thermalLessWord_legal [] [] t ws ps
      (by simpa using hn) (by simpa using hlen))
  | true => simp [thermalComparatorWord,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal,t.isLt]

/-- For distinct listed wires and sufficient workspace initialized to false, `finiteWordRun`
returns the basis state with `t` XORed by the strict threshold test, using threshold `2 ^
ps.length` when `full` is true. -/
theorem thermalComparatorWord_public {n : ℕ} (full : Bool) (ps : List (Fin n × Bool))
    (t : Fin n) (ws : List (Fin n)) (hn : (ps.map Prod.fst++t::ws).Nodup)
    (hlen : ps.length ≤ ws.length+2) (x : Qatlib.Foundations.PureStateMath.Reg n) (hc : ∀ w∈ws,x w=false) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordRun n (thermalComparatorWord full ps t ws) (Qatlib.Foundations.PureStateMath.Ket x) =
      some (Qatlib.Foundations.PureStateMath.Ket (Function.update x t
        (x t ^^ decide (thermalBitValue (ps.map (fun p => x p.1)) <
          (if full then 2^ps.length else thermalBitValue (ps.map Prod.snd)))))) := by
  simp only [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordRun,thermalComparatorWord_legal full ps t ws hn hlen,if_true]
  rw [thermalComparatorWord_numeric full ps t ws hn hlen x hc]

/-- With sufficient workspace, the comparator uses zero queries and one gate when `full` is
true, otherwise exactly `thermalLessCost 0 0 (ps.map Prod.snd)` gates and at most `32 *
ps.length ^ 2` gates. -/
theorem thermalComparatorWord_cost {n : ℕ} (full : Bool) (ps : List (Fin n × Bool))
    (t : Fin n) (ws : List (Fin n)) (hlen : ps.length ≤ ws.length+2) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalComparatorWord full ps t ws)) =
      (if full then 1 else thermalLessCost 0 0 (ps.map Prod.snd)) ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalComparatorWord full ps t ws))=0 ∧
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalComparatorWord full ps t ws)) ≤
      (if full then 1 else 32*ps.length^2) := by
  have he : Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalComparatorWord full ps t ws)) =
      (if full then 1 else thermalLessCost 0 0 (ps.map Prod.snd)) := by
    cases full with
    | false => simpa [thermalComparatorWord] using
        (thermalLessWord_cost [] [] t ws ps (by simpa using hlen)).1
    | true => rfl
  refine ⟨he,(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).1,?_⟩
  rw [he]
  cases full with
  | true => exact Nat.le_refl 1
  | false =>
    have hb := thermalLessCost_bound (ps.map Prod.snd) 0 0 (by decide)
    simpa [List.length_map,pow_two,Nat.mul_assoc] using hb

/-- For distinct listed wires and sufficient workspace, a state supported on basis labels with
workspace false is mapped to the sum of its basis amplitudes with `t` XORed by the
comparator's threshold test. -/
theorem thermalComparatorWord_coherent {n : ℕ} (full : Bool) (ps : List (Fin n × Bool))
    (t : Fin n) (ws : List (Fin n)) (hn : (ps.map Prod.fst++t::ws).Nodup)
    (hlen : ps.length ≤ ws.length+2) (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n))
    (hc : ∀ x : Qatlib.Foundations.PureStateMath.Reg n, (¬∀ w∈ws,x w=false) → psi x=0) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalComparatorWord full ps t ws)) psi =
      ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • Qatlib.Foundations.PureStateMath.Ket (Function.update x t
        (x t ^^ decide (thermalBitValue (ps.map (fun p => x p.1)) <
          (if full then 2^ps.length else thermalBitValue (ps.map Prod.snd))))) := by
  have he : psi = ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • Qatlib.Foundations.PureStateMath.Ket x := by
    funext z
    simp [Qatlib.Foundations.PureStateMath.Ket,Finset.sum_apply]
  rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run]
  conv_lhs => rw [he]
  simp only [Qatlib.Foundations.PureStateMath.ApplyGate,Matrix.mulVec_sum,Matrix.mulVec_smul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hcx : ∀ w∈ws,x w=false
  · have hb := thermalComparatorWord_numeric full ps t ws hn hlen x hcx
    rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run] at hb
    exact congrArg (fun v => psi x • v) hb
  · simp only [hc x hcx,zero_smul]

/-- Updating a wire outside the data-wire list leaves the extracted data-bit list unchanged. -/
private theorem data_bits_update {n : ℕ} (ps : List (Fin n × Bool)) (t : Fin n)
    (ht : t∉ps.map Prod.fst) (x : Qatlib.Foundations.PureStateMath.Reg n) (v : Bool) :
    ps.map (fun p => Function.update x t v p.1)=ps.map (fun p => x p.1) := by
  apply List.map_congr_left
  intro p hp
  have hpt : p.1≠t := fun h => ht (h ▸ List.mem_map_of_mem (f:=Prod.fst) hp)
  exact Function.update_of_ne hpt _ _

/-- The threshold `2 ^ ps.length` when `full` is true, and otherwise the binary value of the
fixed bits in `ps`. -/
def thermalCutoff {n : ℕ} (full : Bool) (ps : List (Fin n × Bool)) : ℕ :=
  if full then 2^ps.length else thermalBitValue (ps.map Prod.snd)

/-- The concatenation of the upper-threshold and lower-threshold comparator words on a common
target and workspace. -/
noncomputable def thermalIntervalWord {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (t : Fin n) (ws : List (Fin n)) :=
  thermalComparatorWord hiFull hi t ws ++ thermalComparatorWord loFull lo t ws

/-- For `a ≤ b`, the XOR of the Boolean tests `v < b` and `v < a` equals the test for membership
in the half-open interval `[a, b)`. -/
private theorem compare_interval (a v b : ℕ) (hab : a≤b) :
    (decide (v<b) ^^ decide (v<a))=decide (a≤v ∧ v<b) := by
  by_cases ha : v<a <;> by_cases hb : v<b
  all_goals simp [ha,hb] <;> omega

/-- For matching distinct data wires, sufficient clean workspace, and ordered cutoffs, the
interval word toggles only `t` according to membership of the data value in the half-open
interval between those cutoffs. -/
theorem thermalIntervalWord_numeric {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (t : Fin n) (ws : List (Fin n))
    (hwires : lo.map Prod.fst=hi.map Prod.fst) (hn : (hi.map Prod.fst++t::ws).Nodup)
    (hlen : hi.length ≤ ws.length+2) (horder : thermalCutoff loFull lo ≤ thermalCutoff hiFull hi)
    (x : Qatlib.Foundations.PureStateMath.Reg n) (hc : ∀ w∈ws,x w=false) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ)
      (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalIntervalWord loFull lo hiFull hi t ws))
      (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (Function.update x t
        (x t ^^ decide (thermalCutoff loFull lo ≤ thermalBitValue (hi.map (fun p => x p.1)) ∧
          thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff hiFull hi))) := by
  have hlo : lo.length=hi.length := by
    simpa only [List.length_map] using congrArg List.length hwires
  have hnlo : (lo.map Prod.fst++t::ws).Nodup := by rw [hwires]; exact hn
  have hllo : lo.length ≤ ws.length+2 := by omega
  have hdata : lo.map (fun p => x p.1)=hi.map (fun p => x p.1) := by
    simpa only [List.map_map] using! congrArg (List.map x) hwires
  have htlo : t∉lo.map Prod.fst := by
    intro h
    exact (List.disjoint_left.mp hnlo.disjoint) h (by simp)
  have htws : t∉ws := (List.nodup_cons.mp hn.of_append_right).1
  let v := x t ^^ decide (thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff hiFull hi)
  let y := Function.update x t v
  have hyc : ∀ u∈ws,y u=false := by
    intro u hu
    have hut : u≠t := fun h => htws (h ▸ hu)
    simpa only [y,Function.update_of_ne hut] using hc u hu
  have ha := thermalComparatorWord_numeric hiFull hi t ws hn hlen x hc
  change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalComparatorWord hiFull hi t ws))
    (Qatlib.Foundations.PureStateMath.Ket x)=Qatlib.Foundations.PureStateMath.Ket y at ha
  have hb := thermalComparatorWord_numeric loFull lo t ws hnlo hllo y hyc
  rw [data_bits_update lo t htlo x v,hdata] at hb
  simp only [thermalIntervalWord,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,List.map_append,Qatlib.Foundations.QueryWordCore.Circuit.run_append]
  change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalComparatorWord loFull lo t ws))
    (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalComparatorWord hiFull hi t ws)) (Qatlib.Foundations.PureStateMath.Ket x)) = _
  rw [ha,hb]
  dsimp only [y,v]
  simp only [Function.update_self,Function.update_idem,Bool.xor_assoc]
  change Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^
    (decide (thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff hiFull hi) ^^
      decide (thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff loFull lo)))) = _
  rw [compare_interval (thermalCutoff loFull lo) (thermalBitValue (hi.map (fun p => x p.1)))
    (thermalCutoff hiFull hi) horder]

/-- The interval word is legal when both threshold lists use the same data wires, all data,
target, and workspace wires are distinct, and the workspace is sufficient. -/
theorem thermalIntervalWord_legal {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (t : Fin n) (ws : List (Fin n))
    (hwires : lo.map Prod.fst=hi.map Prod.fst) (hn : (hi.map Prod.fst++t::ws).Nodup)
    (hlen : hi.length ≤ ws.length+2) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalIntervalWord loFull lo hiFull hi t ws)=true := by
  have hlo : lo.length=hi.length := by
    simpa only [List.length_map] using congrArg List.length hwires
  have hnlo : (lo.map Prod.fst++t::ws).Nodup := by rw [hwires]; exact hn
  have hllo : lo.length ≤ ws.length+2 := by omega
  have ha := thermalComparatorWord_legal hiFull hi t ws hn hlen
  have hb := thermalComparatorWord_legal loFull lo t ws hnlo hllo
  simpa only [thermalIntervalWord,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,List.all_append,Bool.and_eq_true] using And.intro ha hb

/-- For matching distinct data wires, sufficient clean workspace, and ordered cutoffs,
`finiteWordRun` returns the basis state with only `t` XORed by the half-open interval
membership test. -/
theorem thermalIntervalWord_public {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (t : Fin n) (ws : List (Fin n))
    (hwires : lo.map Prod.fst=hi.map Prod.fst) (hn : (hi.map Prod.fst++t::ws).Nodup)
    (hlen : hi.length ≤ ws.length+2) (horder : thermalCutoff loFull lo ≤ thermalCutoff hiFull hi)
    (x : Qatlib.Foundations.PureStateMath.Reg n) (hc : ∀ w∈ws,x w=false) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordRun n (thermalIntervalWord loFull lo hiFull hi t ws) (Qatlib.Foundations.PureStateMath.Ket x) =
      some (Qatlib.Foundations.PureStateMath.Ket (Function.update x t
        (x t ^^ decide (thermalCutoff loFull lo ≤ thermalBitValue (hi.map (fun p => x p.1)) ∧
          thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff hiFull hi)))) := by
  simp only [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordRun,thermalIntervalWord_legal loFull lo hiFull hi t ws hwires hn hlen,if_true]
  rw [thermalIntervalWord_numeric loFull lo hiFull hi t ws hwires hn hlen horder x hc]

/-- For matching distinct data wires, sufficient workspace, and ordered cutoffs, the interval
word acts on any state supported on false workspace by XORing `t` with the half-open
interval test in each basis component. -/
theorem thermalIntervalWord_coherent {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (t : Fin n) (ws : List (Fin n))
    (hwires : lo.map Prod.fst=hi.map Prod.fst) (hn : (hi.map Prod.fst++t::ws).Nodup)
    (hlen : hi.length ≤ ws.length+2) (horder : thermalCutoff loFull lo ≤ thermalCutoff hiFull hi)
    (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n)) (hc : ∀ x : Qatlib.Foundations.PureStateMath.Reg n, (¬∀ w∈ws,x w=false) → psi x=0) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ)
      (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalIntervalWord loFull lo hiFull hi t ws)) psi =
      ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • Qatlib.Foundations.PureStateMath.Ket (Function.update x t
        (x t ^^ decide (thermalCutoff loFull lo ≤ thermalBitValue (hi.map (fun p => x p.1)) ∧
          thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff hiFull hi))) := by
  have he : psi = ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • Qatlib.Foundations.PureStateMath.Ket x := by
    funext z
    simp [Qatlib.Foundations.PureStateMath.Ket,Finset.sum_apply]
  rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run]
  conv_lhs => rw [he]
  simp only [Qatlib.Foundations.PureStateMath.ApplyGate,Matrix.mulVec_sum,Matrix.mulVec_smul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hcx : ∀ w∈ws,x w=false
  · have hb := thermalIntervalWord_numeric loFull lo hiFull hi t ws hwires hn hlen horder x hcx
    rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run] at hb
    exact congrArg (fun v => psi x • v) hb
  · simp only [hc x hcx,zero_smul]

/-- For threshold lists using the same data wires and sufficient workspace, the interval word
has zero queries and gate count equal to the sum of the two comparator counts. This count is
at most `2 + 64 * hi.length ^ 2`. -/
theorem thermalIntervalWord_cost {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (t : Fin n) (ws : List (Fin n))
    (hwires : lo.map Prod.fst=hi.map Prod.fst) (hlen : hi.length ≤ ws.length+2) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalIntervalWord loFull lo hiFull hi t ws)) =
      (if hiFull then 1 else thermalLessCost 0 0 (hi.map Prod.snd)) +
      (if loFull then 1 else thermalLessCost 0 0 (lo.map Prod.snd)) ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalIntervalWord loFull lo hiFull hi t ws))=0 ∧
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalIntervalWord loFull lo hiFull hi t ws)) ≤ 2+64*hi.length^2 := by
  have hlo : lo.length=hi.length := by
    simpa only [List.length_map] using congrArg List.length hwires
  have hllo : lo.length ≤ ws.length+2 := by omega
  have ha := thermalComparatorWord_cost hiFull hi t ws hlen
  have hb := thermalComparatorWord_cost loFull lo t ws hllo
  have hsum : Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalIntervalWord loFull lo hiFull hi t ws)) =
      Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalComparatorWord hiFull hi t ws)) +
      Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalComparatorWord loFull lo t ws)) := by
    simp only [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).2,thermalIntervalWord,List.length_append]
  refine ⟨by rw [hsum,ha.1,hb.1],(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).1,?_⟩
  rw [hsum]
  have hba := ha.2.2
  have hbb := hb.2.2
  rw [hlo] at hbb
  split_ifs at hba hbb <;> omega

/-- For matching distinct data wires, sufficient clean workspace, and ordered cutoffs, the
adjoint interval word has the same target-toggle action as the forward interval word on
basis states. -/
theorem thermalIntervalWord_adjoint {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (t : Fin n) (ws : List (Fin n))
    (hwires : lo.map Prod.fst=hi.map Prod.fst) (hn : (hi.map Prod.fst++t::ws).Nodup)
    (hlen : hi.length ≤ ws.length+2) (horder : thermalCutoff loFull lo ≤ thermalCutoff hiFull hi)
    (x : Qatlib.Foundations.PureStateMath.Reg n) (hc : ∀ w∈ws,x w=false) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ)
      (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalIntervalWord loFull lo hiFull hi t ws)))
      (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (Function.update x t
        (x t ^^ decide (thermalCutoff loFull lo ≤ thermalBitValue (hi.map (fun p => x p.1)) ∧
          thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff hiFull hi))) := by
  let p := decide (thermalCutoff loFull lo ≤ thermalBitValue (hi.map (fun q => x q.1)) ∧
    thermalBitValue (hi.map (fun q => x q.1)) < thermalCutoff hiFull hi)
  let y := Function.update x t (x t ^^ p)
  have htdata : t∉hi.map Prod.fst := by
    intro h
    exact (List.disjoint_left.mp hn.disjoint) h (by simp)
  have htws : t∉ws := (List.nodup_cons.mp hn.of_append_right).1
  have hyc : ∀ u∈ws,y u=false := by
    intro u hu
    have hut : u≠t := fun h => htws (h ▸ hu)
    simpa only [y,Function.update_of_ne hut] using hc u hu
  have hf : Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ)
      (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalIntervalWord loFull lo hiFull hi t ws))
      (Qatlib.Foundations.PureStateMath.Ket y)=Qatlib.Foundations.PureStateMath.Ket x := by
    rw [thermalIntervalWord_numeric loFull lo hiFull hi t ws hwires hn hlen horder y hyc,
      data_bits_update hi t htdata x (x t ^^ p)]
    simp [y,p]
  have paid := (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finite_gate_word_paid_adjoint_semantics n
    (thermalIntervalWord loFull lo hiFull hi t ws) (Qatlib.Foundations.PureStateMath.Ket y)
    (thermalIntervalWord_legal loFull lo hiFull hi t ws hwires hn hlen)).2.2.1
  simp only [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,List.map_append,Qatlib.Foundations.QueryWordCore.Circuit.run_append] at paid
  change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalIntervalWord loFull lo hiFull hi t ws)))
    (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalIntervalWord loFull lo hiFull hi t ws))
      (Qatlib.Foundations.PureStateMath.Ket y))=Qatlib.Foundations.PureStateMath.Ket y at paid
  rw [hf] at paid
  exact paid

/-- For matching distinct data wires, sufficient workspace, and ordered cutoffs, the adjoint
interval word implements the same half-open interval target toggle on states supported on
false workspace. -/
theorem thermalIntervalWord_adjoint_coherent {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (t : Fin n) (ws : List (Fin n))
    (hwires : lo.map Prod.fst=hi.map Prod.fst) (hn : (hi.map Prod.fst++t::ws).Nodup)
    (hlen : hi.length ≤ ws.length+2) (horder : thermalCutoff loFull lo ≤ thermalCutoff hiFull hi)
    (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n)) (hc : ∀ x : Qatlib.Foundations.PureStateMath.Reg n, (¬∀ w∈ws,x w=false) → psi x=0) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ)
      (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalIntervalWord loFull lo hiFull hi t ws))) psi =
      ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • Qatlib.Foundations.PureStateMath.Ket (Function.update x t
        (x t ^^ decide (thermalCutoff loFull lo ≤ thermalBitValue (hi.map (fun p => x p.1)) ∧
          thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff hiFull hi))) := by
  have he : psi = ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • Qatlib.Foundations.PureStateMath.Ket x := by
    funext z
    simp [Qatlib.Foundations.PureStateMath.Ket,Finset.sum_apply]
  rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run]
  conv_lhs => rw [he]
  simp only [Qatlib.Foundations.PureStateMath.ApplyGate,Matrix.mulVec_sum,Matrix.mulVec_smul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hcx : ∀ w∈ws,x w=false
  · have hb := thermalIntervalWord_adjoint loFull lo hiFull hi t ws hwires hn hlen horder x hcx
    rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run] at hb
    exact congrArg (fun v => psi x • v) hb
  · simp only [hc x hcx,zero_smul]

end Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
