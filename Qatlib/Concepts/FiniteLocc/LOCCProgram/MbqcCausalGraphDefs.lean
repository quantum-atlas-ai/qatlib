/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlow
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCoreDefs
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCounterexamples

/-!
# Finite searches for MBQC flow and correction data

This module represents neighbourhoods and odd neighbourhoods by Boolean lists, enumerates finite
correction and rank functions, and defines `mbqcFlowSearch` and `mbqcGFlowSearch`. The flow
terminology follows [DanosKashefi2006] and [BrowneEtAl2007].

Ordinary flow is equivalent to successful search. Generalized-flow search is sound and complete
for the rank checker, and succeeds under `MbqcHasGFlowTotal`; it is not complete for
unrestricted `MbqcHasGFlow`. The module also defines gate charges and explicit two-qubit
measurement and correction operators.

## Main statements

* `mbqcOddBitset_iff`: Boolean odd-neighbourhood membership agrees with the finite-set
  definition.
* `mbqcHasFlow_iff_search`: ordinary flow is characterized by successful finite search.
* `mbqcGFlowSearch_not_complete`: generalized-flow existence alone does not ensure search
  success.

## References

* [Danos and Kashefi, 2006][DanosKashefi2006]
* [Browne et al., 2007][BrowneEtAl2007]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.FiniteLocc.LOCCProgram

set_option autoImplicit false

/-- Computes componentwise conjunction of two Boolean lists, stopping when either list ends. -/
def mbqcAndBits : List Bool → List Bool → List Bool
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, b :: bs => (a && b) :: mbqcAndBits as bs

/-- Computes componentwise exclusive-or, retaining the remaining suffix when one Boolean list
ends. -/
def mbqcXorBits : List Bool → List Bool → List Bool
  | [], [] => []
  | a :: as, [] => a :: as
  | [], b :: bs => b :: bs
  | a :: as, b :: bs => (xor a b) :: mbqcXorBits as bs

/-- Computes the exclusive-or of all entries of a Boolean list, with value `false` on the empty
list. -/
def mbqcParityBits : List Bool → Bool
  | [] => false
  | b :: bs => xor b (mbqcParityBits bs)

/-- Counts the entries equal to `true` in a Boolean list. -/
def mbqcCountTrue : List Bool → ℕ
  | [] => 0
  | true :: bs => mbqcCountTrue bs + 1
  | false :: bs => mbqcCountTrue bs

/-- The parity of a Boolean list is `true` exactly when its number of true entries is odd. -/
theorem mbqcParityBits_iff (l : List Bool) :
    mbqcParityBits l = true ↔ mbqcCountTrue l % 2 = 1 := by
  induction l with
  | nil => simp [mbqcParityBits, mbqcCountTrue]
  | cons b bs ih =>
    cases b with
    | false => simpa [mbqcParityBits, mbqcCountTrue] using ih
    | true =>
      simp only [mbqcParityBits, mbqcCountTrue]
      have hfalse : mbqcParityBits bs = false ↔ mbqcCountTrue bs % 2 = 0 := by
        cases hb : mbqcParityBits bs <;> simp_all
      have htrue : xor true (mbqcParityBits bs) = true ↔ mbqcParityBits bs = false := by
        cases hb : mbqcParityBits bs <;> simp_all
      rw [htrue, hfalse]
      omega

/-- Counting true values of a mapped predicate equals the length of the list filtered by that
predicate. -/
theorem mbqcCountTrue_map {α : Type} (p : α → Bool) (l : List α) :
    mbqcCountTrue (l.map p) = (l.filter p).length := by
  induction l with
  | nil => simp [mbqcCountTrue]
  | cons a l ih =>
    by_cases hp : p a
    · simp [mbqcCountTrue, ih, hp]
    · simp [mbqcCountTrue, ih, hp]

/-- For a list without duplicates, conversion to a finite set preserves its length as
cardinality. -/
theorem mbqcList_toFinset_card {α : Type} [DecidableEq α] {l : List α} (h : l.Nodup) :
    l.toFinset.card = l.length := by
  show l.toFinset.1.card = l.length
  rw [List.toFinset_val, List.dedup_eq_self.mpr h]
  rfl

/-- Counting true predicate values over `List.finRange n` equals the cardinality of the
corresponding filtered universe. -/
theorem mbqcCountTrue_finRange_eq_card {n : ℕ} (p : Fin n → Bool) :
    mbqcCountTrue ((List.finRange n).map p)
      = (Finset.univ.filter fun u => p u = true).card := by
  rw [mbqcCountTrue_map]
  have hfin : ((List.finRange n).filter p).toFinset
      = Finset.univ.filter fun u => p u = true := by
    ext u
    simp [Finset.mem_filter]
  rw [← hfin]
  exact (mbqcList_toFinset_card (List.Nodup.filter p (List.nodup_finRange n))).symm

/-- Reads the bit at the natural-number index of a vertex, returning `false` if the index is
outside the list. -/
def mbqcBitAt {n : ℕ} (bits : List Bool) (v : Fin n) : Bool := bits.getD v.1 false

/-- Reading the Boolean list obtained by mapping a function over `List.finRange n` recovers that
function at each vertex. -/
theorem mbqcBitAt_finRange_map : ∀ (n : ℕ) (f : Fin n → Bool) (v : Fin n),
    mbqcBitAt ((List.finRange n).map f) v = f v := by
  intro n
  induction n with
  | zero => intro f v; exact Fin.elim0 v
  | succ n ih =>
    intro f v
    have hsplit : List.finRange (Nat.succ n) = 0 :: (List.finRange n).map Fin.succ :=
      List.finRange_succ
    have hmap : ((List.finRange (Nat.succ n)).map f)
        = f 0 :: ((List.finRange n).map Fin.succ).map f := by
      rw [hsplit]
      simp only [List.map_cons]
    have hval : ((List.finRange (Nat.succ n)).map f).getD v.1 false
        = (f 0 :: ((List.finRange n).map Fin.succ).map f).getD v.1 false := by
      rw [hmap]
    rw [mbqcBitAt, hval]
    cases v using Fin.cases with
    | zero =>
      simp
    | succ i =>
      simp only [Fin.val_succ, List.getD_cons_succ, List.map_map]
      exact ih (fun j => f j.succ) i

/-- Lists the adjacency bits of a vertex in the order of `List.finRange n`. -/
def mbqcAdjBitset {n : ℕ} (G : MbqcGraph n) (v : Fin n) : List Bool :=
  (List.finRange n).map fun u => mbqcAdj G v u

/-- Encodes membership in a finite vertex set as a Boolean list indexed in vertex order. -/
def mbqcMemberBitset {n : ℕ} (S : Finset (Fin n)) : List Bool :=
  (List.finRange n).map fun u => decide (u ∈ S)

/-- Returns the vertices in `S` adjacent to `v`. -/
def mbqcNeighboursIn {n : ℕ} (G : MbqcGraph n) (S : Finset (Fin n)) (v : Fin n) :
    Finset (Fin n) :=
  S.filter fun u => mbqcAdj G v u = true

/-- Encodes odd-neighbourhood membership by taking the parity of the conjunction of adjacency
and membership bits. -/
def mbqcOddBitset {n : ℕ} (G : MbqcGraph n) (S : Finset (Fin n)) : List Bool :=
  (List.finRange n).map fun v =>
    mbqcParityBits (mbqcAndBits (mbqcAdjBitset G v) (mbqcMemberBitset S))

/-- Componentwise conjunction of two predicates mapped over the same list equals mapping their
pointwise conjunction. -/
theorem mbqcAndBits_map_map {α : Type} (p q : α → Bool) (l : List α) :
    mbqcAndBits (l.map p) (l.map q) = l.map (fun x => p x && q x) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [mbqcAndBits, ih]

/-- The bit for a vertex in `mbqcOddBitset G S` is true exactly when that vertex belongs to
`mbqcOdd G S`. -/
theorem mbqcOddBitset_iff {n : ℕ} (G : MbqcGraph n) (S : Finset (Fin n)) (v : Fin n) :
    mbqcBitAt (mbqcOddBitset G S) v = true ↔ v ∈ mbqcOdd G S := by
  have hcount : mbqcCountTrue (mbqcAndBits (mbqcAdjBitset G v) (mbqcMemberBitset S))
      = (mbqcNeighboursIn G S v).card := by
    have hbits : mbqcAndBits (mbqcAdjBitset G v) (mbqcMemberBitset S)
        = (List.finRange n).map (fun u => mbqcAdj G v u && decide (u ∈ S)) := by
      unfold mbqcAdjBitset mbqcMemberBitset
      exact mbqcAndBits_map_map _ _ _
    rw [hbits]
    rw [mbqcCountTrue_finRange_eq_card]
    have hfin : (Finset.univ.filter fun u => (mbqcAdj G v u && decide (u ∈ S)) = true)
        = mbqcNeighboursIn G S v := by
      ext u
      simp [mbqcNeighboursIn, Finset.mem_filter, and_comm]
    rw [hfin]
  have hparity : mbqcParityBits (mbqcAndBits (mbqcAdjBitset G v) (mbqcMemberBitset S)) = true
      ↔ (mbqcNeighboursIn G S v).card % 2 = 1 := by
    rw [mbqcParityBits_iff, hcount]
  have hbit : mbqcBitAt (mbqcOddBitset G S) v
      = mbqcParityBits (mbqcAndBits (mbqcAdjBitset G v) (mbqcMemberBitset S)) := by
    unfold mbqcBitAt mbqcOddBitset
    exact mbqcBitAt_finRange_map n
      (fun u => mbqcParityBits (mbqcAndBits (mbqcAdjBitset G u) (mbqcMemberBitset S))) v
  rw [hbit, hparity]
  simp [mbqcOdd, Finset.mem_filter, mbqcNeighboursIn]

/-- Defines the unique function from the empty finite type to any type. -/
def mbqcFinZeroFn {β : Type} : Fin 0 → β := fun x => Fin.elim0 x

/-- Every function with domain `Fin 0` equals `mbqcFinZeroFn`. -/
theorem mbqcFinZeroFn_eq {β : Type} (g : Fin 0 → β) : g = mbqcFinZeroFn := by
  funext x
  exact Fin.elim0 x

/-- Enumerates functions on `Fin n` by recursively choosing their values from a supplied list. -/
def mbqcFuncSpace {β : Type} : (n : ℕ) → List β → List (Fin n → β)
  | 0, _ => [fun x => Fin.elim0 x]
  | (n + 1), bs =>
      (mbqcFuncSpace n bs).flatMap fun g =>
        bs.map fun b => fun x => Fin.cases (motive := fun _ => β) b (fun i => g i) x

/-- If the supplied list contains every codomain element, `mbqcFuncSpace` contains every
function on `Fin n`. -/
theorem mbqcFuncSpace_complete {β : Type} :
    ∀ (n : ℕ) (bs : List β), (∀ b, b ∈ bs) → ∀ g : Fin n → β, g ∈ mbqcFuncSpace n bs := by
  intro n
  induction n with
  | zero =>
    intro bs hbs g
    have hfun : g = mbqcFinZeroFn := mbqcFinZeroFn_eq g
    rw [hfun]
    exact List.mem_singleton.mpr rfl
  | succ n ih =>
    intro bs hbs g
    have hg : (fun i => g i.succ) ∈ mbqcFuncSpace n bs :=
      ih bs hbs (fun i => g i.succ)
    refine List.mem_flatMap.mpr ⟨(fun i => g i.succ), hg, ?_⟩
    have hgl : g 0 ∈ bs := hbs (g 0)
    refine List.mem_map.mpr ⟨g 0, hgl, ?_⟩
    have hfun : (fun x => Fin.cases (motive := fun _ => β) (g 0) (fun i => g i.succ) x) = g := by
      funext x
      cases x using Fin.cases with
      | zero => rfl
      | succ i => rfl
    exact hfun

/-- Lists `none` and all values `some v` for vertices `v : Fin n`. -/
def mbqcOptionBasis (n : ℕ) : List (Option (Fin n)) :=
  none :: (List.finRange n).map some

/-- Every element of `Option (Fin n)` occurs in `mbqcOptionBasis n`. -/
theorem mbqcOptionBasis_complete (n : ℕ) (b : Option (Fin n)) : b ∈ mbqcOptionBasis n := by
  cases b with
  | none => simp [mbqcOptionBasis]
  | some i => simp [mbqcOptionBasis]

/-- Enumerates pairs consisting of an optional correction function and a vertex rank function. -/
def mbqcFlowCandidates (n : ℕ) :
    List ((Fin n → Option (Fin n)) × (Fin n → Fin n)) :=
  (mbqcFuncSpace n (mbqcOptionBasis n)).flatMap fun f =>
    (mbqcFuncSpace n (List.finRange n)).map fun r => (f, r)

/-- Every optional correction function and rank function occur together in `mbqcFlowCandidates
n`. -/
theorem mbqcFlowCandidates_complete {n : ℕ} (f : Fin n → Option (Fin n))
    (r : Fin n → Fin n) : (f, r) ∈ mbqcFlowCandidates n := by
  have hf : f ∈ mbqcFuncSpace n (mbqcOptionBasis n) := by
    refine mbqcFuncSpace_complete n (mbqcOptionBasis n) ?_ f
    intro b
    exact mbqcOptionBasis_complete n b
  have hr : r ∈ mbqcFuncSpace n (List.finRange n) := by
    refine mbqcFuncSpace_complete n (List.finRange n) ?_ r
    intro b
    exact List.mem_finRange b
  exact List.mem_flatMap.mpr ⟨f, hf, List.mem_map.mpr ⟨r, hr, rfl⟩⟩

/-- Converts a Boolean matrix into a function assigning to each vertex the finite set of true
entries in its row. -/
def mbqcGFromBits {n : ℕ} (b : Fin n → Fin n → Bool) : Fin n → Finset (Fin n) :=
  fun v => Finset.univ.filter fun u => b v u = true

/-- Membership in the set encoded by a Boolean row is equivalent to the corresponding entry
being true. -/
theorem mbqcGFromBits_mem {n : ℕ} (b : Fin n → Fin n → Bool) (v u : Fin n) :
    u ∈ mbqcGFromBits b v ↔ b v u = true := by
  simp [mbqcGFromBits]

/-- Encoding a finite-set-valued function by its membership bits and decoding it recovers the
original function. -/
theorem mbqcGFromBits_of {n : ℕ} (g : Fin n → Finset (Fin n)) :
    mbqcGFromBits (fun v u => decide (u ∈ g v)) = g := by
  funext v
  ext u
  simp [mbqcGFromBits]

/-- Enumerates pairs of Boolean correction matrices and vertex rank functions. -/
def mbqcGFlowCandidates (n : ℕ) :
    List ((Fin n → Fin n → Bool) × (Fin n → Fin n)) :=
  (mbqcFuncSpace n (mbqcFuncSpace n [false, true])).flatMap fun b =>
    (mbqcFuncSpace n (List.finRange n)).map fun r => (b, r)

/-- Every Boolean correction matrix and rank function occur together in `mbqcGFlowCandidates n`. -/
theorem mbqcGFlowCandidates_complete {n : ℕ} (b : Fin n → Fin n → Bool)
    (r : Fin n → Fin n) : (b, r) ∈ mbqcGFlowCandidates n := by
  have hb : b ∈ mbqcFuncSpace n (mbqcFuncSpace n [false, true]) := by
    refine mbqcFuncSpace_complete n (mbqcFuncSpace n [false, true]) ?_ b
    intro y
    refine mbqcFuncSpace_complete n [false, true] ?_ y
    intro c
    cases c <;> simp
  have hr : r ∈ mbqcFuncSpace n (List.finRange n) := by
    refine mbqcFuncSpace_complete n (List.finRange n) ?_ r
    intro c
    exact List.mem_finRange c
  exact List.mem_flatMap.mpr ⟨b, hb, List.mem_map.mpr ⟨r, hr, rfl⟩⟩

/-- Packages irreflexivity and transitivity of a vertex relation as an `IsStrictOrder` instance. -/
theorem mbqcIsStrictOrder {n : ℕ} {prec : Fin n → Fin n → Prop}
    (hirr : ∀ x : Fin n, ¬ prec x x)
    (htrans : ∀ a b c : Fin n, prec a b → prec b c → prec a c) :
    IsStrictOrder (Fin n) prec := by
  refine { irrefl := ?_, trans := ?_ }
  · exact hirr
  · exact htrans

/-- Ranks each vertex of a decidable strict order by the number of its predecessors, as an
element of `Fin n`. -/
def mbqcStrictOrderRank {n : ℕ} (prec : Fin n → Fin n → Prop) [DecidableRel prec]
    (hprec : IsStrictOrder (Fin n) prec) : Fin n → Fin n :=
  fun v =>
    ⟨(Finset.univ.filter fun u => prec u v).card, by
      have hne : v ∉ Finset.univ.filter fun u => prec u v := by
        simp only [Finset.mem_filter]
        exact fun h => hprec.irrefl v h.2
      have hcard : (Finset.univ.filter fun u => prec u v).card ≤ n - 1 := by
        have hsub : (Finset.univ.filter fun u => prec u v) ⊆ Finset.univ.erase v := by
          intro x hx
          have hx2 : prec x v := (Finset.mem_filter.mp hx).2
          have hxne : x ≠ v := by
            intro hxv
            rw [hxv] at hx2
            exact hprec.irrefl v hx2
          exact Finset.mem_erase.mpr ⟨hxne, Finset.mem_univ x⟩
        have h1 : (Finset.univ.filter fun u => prec u v).card
            ≤ (Finset.univ.erase v).card := Finset.card_le_card hsub
        have hcard' : (Finset.univ.erase v).card = n - 1 := by simp
        rw [hcard'] at h1
        exact h1
      have hn : 1 ≤ n := by
        have := v.isLt
        omega
      omega⟩

/-- The predecessor-count rank strictly increases along the given strict order. -/
theorem mbqcStrictOrderRank_lt {n : ℕ} {prec : Fin n → Fin n → Prop} [DecidableRel prec]
    (hprec : IsStrictOrder (Fin n) prec) {u v : Fin n} (h : prec u v) :
    (mbqcStrictOrderRank prec hprec u).val < (mbqcStrictOrderRank prec hprec v).val := by
  have hAB : (Finset.univ.filter fun x => prec x u)
      ⊆ (Finset.univ.filter fun x => prec x v) := by
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    obtain ⟨hx1, hx2⟩ := hx
    exact ⟨hx1, hprec.trans x u v hx2 h⟩
  have hne : (Finset.univ.filter fun x => prec x u)
      ≠ (Finset.univ.filter fun x => prec x v) := by
    intro heq
    have huB : u ∈ Finset.univ.filter fun x => prec x v := by
      simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ u, h⟩
    have huA : u ∉ Finset.univ.filter fun x => prec x u := by
      simp only [Finset.mem_filter]
      exact fun hx => hprec.irrefl u hx.2
    have huB' : u ∈ Finset.univ.filter fun x => prec x u := by
      rw [heq]
      exact huB
    exact huA huB'
  have hlt : (Finset.univ.filter fun x => prec x u).card
      < (Finset.univ.filter fun x => prec x v).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hAB, hne⟩)
  exact hlt

/-- The relation induced by strict comparison of vertex ranks is a strict order. -/
theorem mbqcRankPrec_isStrictOrder {n : ℕ} (r : Fin n → Fin n) :
    IsStrictOrder (Fin n) (mbqcRankPrec r) where
  irrefl x hx := by
    simp only [mbqcRankPrec] at hx
    exact absurd hx (Nat.lt_irrefl _)
  trans a b c hab hbc := by
    simp only [mbqcRankPrec] at hab hbc
    exact Nat.lt_trans hab hbc

/-- Searches the finite list of correction and rank pairs for the first pair satisfying
`mbqcFlowCheck`. -/
def mbqcFlowSearch {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n)) :
    Option ((Fin n → Option (Fin n)) × (Fin n → Fin n)) :=
  (mbqcFlowCandidates n).find? fun p => decide (mbqcFlowCheck G I O p.1 p.2)

/-- Every pair returned by `mbqcFlowSearch` satisfies `mbqcFlowCheck`. -/
theorem mbqcFlowSearch_sound {n : ℕ} {G : MbqcGraph n} {I O : Finset (Fin n)}
    {p : (Fin n → Option (Fin n)) × (Fin n → Fin n)}
    (h : mbqcFlowSearch G I O = some p) : mbqcFlowCheck G I O p.1 p.2 := by
  have hp : decide (mbqcFlowCheck G I O p.1 p.2) = true := by
    have hsome := List.find?_some h
    simpa [mbqcFlowSearch] using hsome
  exact of_decide_eq_true hp

/-- If a correction and rank pair satisfies `mbqcFlowCheck`, the search returns some pair
satisfying the checker. -/
theorem mbqcFlowSearch_complete {n : ℕ} {G : MbqcGraph n} {I O : Finset (Fin n)}
    (f : Fin n → Option (Fin n)) (r : Fin n → Fin n)
    (h : mbqcFlowCheck G I O f r) :
    ∃ p, mbqcFlowSearch G I O = some p ∧ mbqcFlowCheck G I O p.1 p.2 := by
  have hmem : (f, r) ∈ mbqcFlowCandidates n := mbqcFlowCandidates_complete f r
  have hdec : decide (mbqcFlowCheck G I O f r) = true := decide_eq_true h
  have hsome : (mbqcFlowCandidates n).find?
      (fun p => decide (mbqcFlowCheck G I O p.1 p.2)) |>.isSome := by
    rw [List.find?_isSome]
    exact ⟨(f, r), hmem, hdec⟩
  obtain ⟨p, hp⟩ : ∃ p, (mbqcFlowCandidates n).find?
      (fun q => decide (mbqcFlowCheck G I O q.1 q.2)) = some p := by
    cases h1 : (mbqcFlowCandidates n).find?
      (fun q => decide (mbqcFlowCheck G I O q.1 q.2)) with
    | none => exact absurd hsome (by simp [h1])
    | some v => exact ⟨v, rfl⟩
  refine ⟨p, ?_, ?_⟩
  · exact hp
  · exact mbqcFlowSearch_sound hp

/-- Searches Boolean correction matrices and ranks for the first pair satisfying
`mbqcGFlowCheck` after decoding the matrix. -/
def mbqcGFlowSearch {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (lam : Fin n → MbqcPlane) :
    Option ((Fin n → Fin n → Bool) × (Fin n → Fin n)) :=
  (mbqcGFlowCandidates n).find? fun p =>
    decide (mbqcGFlowCheck G I O lam (mbqcGFromBits p.1) p.2)

/-- Every pair returned by generalized-flow search satisfies the generalized-flow rank checker. -/
theorem mbqcGFlowSearch_sound {n : ℕ} {G : MbqcGraph n} {I O : Finset (Fin n)}
    {lam : Fin n → MbqcPlane}
    {p : (Fin n → Fin n → Bool) × (Fin n → Fin n)}
    (h : mbqcGFlowSearch G I O lam = some p) :
    mbqcGFlowCheck G I O lam (mbqcGFromBits p.1) p.2 := by
  have hp : decide (mbqcGFlowCheck G I O lam (mbqcGFromBits p.1) p.2) = true := by
    have hsome := List.find?_some h
    simpa [mbqcGFlowSearch] using hsome
  exact of_decide_eq_true hp

/-- If an encoded correction matrix and rank satisfy the generalized-flow checker, the search
returns a pair satisfying that checker. -/
theorem mbqcGFlowSearch_complete {n : ℕ} {G : MbqcGraph n} {I O : Finset (Fin n)}
    {lam : Fin n → MbqcPlane} (b : Fin n → Fin n → Bool) (r : Fin n → Fin n)
    (h : mbqcGFlowCheck G I O lam (mbqcGFromBits b) r) :
    ∃ p, mbqcGFlowSearch G I O lam = some p ∧
      mbqcGFlowCheck G I O lam (mbqcGFromBits p.1) p.2 := by
  have hmem : (b, r) ∈ mbqcGFlowCandidates n := mbqcGFlowCandidates_complete b r
  have hdec : decide (mbqcGFlowCheck G I O lam (mbqcGFromBits b) r) = true :=
    decide_eq_true h
  have hsome : (mbqcGFlowCandidates n).find?
      (fun p => decide (mbqcGFlowCheck G I O lam (mbqcGFromBits p.1) p.2)) |>.isSome := by
    rw [List.find?_isSome]
    exact ⟨(b, r), hmem, hdec⟩
  obtain ⟨p, hp⟩ : ∃ p, (mbqcGFlowCandidates n).find?
      (fun q => decide (mbqcGFlowCheck G I O lam (mbqcGFromBits q.1) q.2)) = some p := by
    cases h1 : (mbqcGFlowCandidates n).find?
      (fun q => decide (mbqcGFlowCheck G I O lam (mbqcGFromBits q.1) q.2)) with
    | none => exact absurd hsome (by simp [h1])
    | some v => exact ⟨v, rfl⟩
  refine ⟨p, ?_, ?_⟩
  · exact hp
  · exact mbqcGFlowSearch_sound hp

/-- Existence of an MBQC flow is equivalent to existence of a correction and rank pair
satisfying `mbqcFlowCheck`. -/
theorem mbqcHasFlow_iff_check {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n)) :
    MbqcHasFlow G I O ↔
      ∃ f : Fin n → Option (Fin n), ∃ r : Fin n → Fin n, mbqcFlowCheck G I O f r := by
  constructor
  · rintro ⟨f, prec, dp, hprec, hflow⟩
    letI := dp
    refine ⟨f, mbqcStrictOrderRank prec hprec, ?_⟩
    intro v hv
    obtain ⟨w, hfw, hadj, hwI, hprecvw, hprecvk⟩ := hflow v hv
    exact ⟨w, hfw, hadj, hwI, mbqcStrictOrderRank_lt hprec hprecvw,
      fun k hadjwk hk => mbqcStrictOrderRank_lt hprec (hprecvk k hadjwk hk)⟩
  · rintro ⟨f, r, hcheck⟩
    refine ⟨f, mbqcRankPrec r, inferInstance,
      ⟨mbqcRankPrec_isStrictOrder r, ?_⟩⟩
    intro v hv
    obtain ⟨w, hfw, hadj, hwI, hvw, hvk⟩ := hcheck v hv
    exact ⟨w, hfw, hadj, hwI, hvw, hvk⟩

/-- An MBQC flow exists exactly when `mbqcFlowSearch` returns a candidate. -/
theorem mbqcHasFlow_iff_search {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n)) :
    MbqcHasFlow G I O ↔ (mbqcFlowSearch G I O).isSome := by
  constructor
  · intro h
    obtain ⟨f, r, hcheck⟩ := (mbqcHasFlow_iff_check G I O).mp h
    obtain ⟨p, hp, _⟩ := mbqcFlowSearch_complete f r hcheck
    rw [hp]
    trivial
  · intro h
    have hex : ∃ x, x ∈ mbqcFlowCandidates n ∧
        decide (mbqcFlowCheck G I O x.1 x.2) = true := by
      unfold mbqcFlowSearch at h
      rw [List.find?_isSome] at h
      obtain ⟨x, hx, hp⟩ := h
      refine ⟨x, ?_, ?_⟩
      · exact mbqcFlowCandidates_complete x.1 x.2
      · exact hp
    obtain ⟨x, hx, hp⟩ := hex
    exact (mbqcHasFlow_iff_check G I O).mpr
      ⟨x.1, x.2, of_decide_eq_true hp⟩

/-- A correction function and rank satisfying `mbqcGFlowCheck` yield an MBQC generalized flow. -/
theorem mbqcHasGFlow_of_check {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (lam : Fin n → MbqcPlane) (g : Fin n → Finset (Fin n)) (r : Fin n → Fin n)
    (h : mbqcGFlowCheck G I O lam g r) : MbqcHasGFlow G I O lam := by
  refine ⟨g, mbqcRankPrec r, inferInstance,
    ⟨?_, ⟨mbqcRankPrec_isStrictOrder r, ?_, ?_, ?_⟩⟩⟩
  · intro v hv u hu
    exact (h v hv).1 u hu
  · intro v hv u hu hne
    exact (h v hv).2.1 u hu hne
  · intro v hv u hprec
    exact (h v hv).2.2.1 u hprec
  · intro v hv
    have hplane := (h v hv).2.2.2
    rw [mbqcGFlowPlaneCondB_iff] at hplane
    simpa only [decide_eq_true_eq] using hplane

/-- Successful generalized-flow search implies existence of an MBQC generalized flow. -/
theorem mbqcHasGFlow_of_search {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (lam : Fin n → MbqcPlane) (h : (mbqcGFlowSearch G I O lam).isSome) :
    MbqcHasGFlow G I O lam := by
  have hex : ∃ x, x ∈ mbqcGFlowCandidates n ∧
      decide (mbqcGFlowCheck G I O lam (mbqcGFromBits x.1) x.2) = true := by
    unfold mbqcGFlowSearch at h
    rw [List.find?_isSome] at h
    obtain ⟨x, hx, hp⟩ := h
    refine ⟨x, ?_, ?_⟩
    · exact mbqcGFlowCandidates_complete x.1 x.2
    · exact hp
  obtain ⟨p, _, hcheck⟩ := hex
  exact mbqcHasGFlow_of_check G I O lam (mbqcGFromBits p.1) p.2 (of_decide_eq_true hcheck)

/-- Expresses existence of generalized-flow correction sets with a decidable strict total order
satisfying the input, causality, odd-neighbourhood, and measurement-plane conditions. -/
def MbqcHasGFlowTotal {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (lam : Fin n → MbqcPlane) : Prop :=
  ∃ (g : Fin n → Finset (Fin n)) (prec : Fin n → Fin n → Prop),
    ∃ _dp : DecidableRel prec,
      (∀ v : Fin n, v ∉ O → ∀ u : Fin n, u ∈ g v → u ∉ I) ∧
      IsStrictOrder (Fin n) prec ∧
      (∀ u v : Fin n, u ≠ v → prec u v ∨ prec v u) ∧
      (∀ v : Fin n, v ∉ O → ∀ u : Fin n, u ∈ g v → u ≠ v → prec v u) ∧
      (∀ v : Fin n, v ∉ O → ∀ u : Fin n, prec u v → u ∉ mbqcOdd G (g v)) ∧
      (∀ v : Fin n, v ∉ O →
        mbqcGFlowPlaneCond (lam v) (v ∈ g v) (v ∈ mbqcOdd G (g v)))

/-- For correction sets satisfying the generalized-flow conditions with a strict total order,
predecessor-count ranks satisfy `mbqcGFlowCheck`. -/
theorem mbqcHasGFlowTotal_of_check {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (lam : Fin n → MbqcPlane) (g : Fin n → Finset (Fin n)) (prec : Fin n → Fin n → Prop)
    [DecidableRel prec] (hirr : ∀ x : Fin n, ¬ prec x x)
    (htrans : ∀ (a b c : Fin n), prec a b → prec b c → prec a c)
    (htot : ∀ u v : Fin n, u ≠ v → prec u v ∨ prec v u)
    (hG0 : ∀ v : Fin n, v ∉ O → ∀ u : Fin n, u ∈ g v → u ∉ I)
    (hG1 : ∀ v : Fin n, v ∉ O → ∀ u : Fin n, u ∈ g v → u ≠ v → prec v u)
    (hG2 : ∀ v : Fin n, v ∉ O → ∀ u : Fin n, prec u v → u ∉ mbqcOdd G (g v))
    (hC : ∀ v : Fin n, v ∉ O →
      mbqcGFlowPlaneCond (lam v) (v ∈ g v) (v ∈ mbqcOdd G (g v))) :
    mbqcGFlowCheck G I O lam g (mbqcStrictOrderRank prec (mbqcIsStrictOrder hirr htrans)) := by
  intro v hv
  refine ⟨hG0 v hv, ?_, ?_, ?_⟩
  · intro u hu hne
    exact mbqcStrictOrderRank_lt (mbqcIsStrictOrder hirr htrans) (hG1 v hv u hu hne)
  · intro u hprec hu
    by_cases heq : u = v
    · subst heq
      simp only [mbqcRankPrec] at hprec
      exact absurd hprec (Nat.lt_irrefl _)
    · rcases htot u v heq with hdown | hup
      · exact absurd hu (hG2 v hv u hdown)
      · have hup' := mbqcStrictOrderRank_lt (mbqcIsStrictOrder hirr htrans) hup
        simp only [mbqcRankPrec] at hprec hup'
        omega
  · have hplane := hC v hv
    rw [mbqcGFlowPlaneCondB_iff]
    simpa only [decide_eq_true_eq] using hplane

/-- Existence of a generalized flow with a decidable strict total order implies successful
generalized-flow search. -/
theorem mbqcHasGFlowTotal_implies_search {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (lam : Fin n → MbqcPlane) :
    MbqcHasGFlowTotal G I O lam → (mbqcGFlowSearch G I O lam).isSome := by
  rintro ⟨g, prec, dp, hG0, hprec, htot, hG1, hG2, hC⟩
  letI := dp
  have hirr : ∀ x : Fin n, ¬ prec x x := fun x => hprec.irrefl x
  have htrans : ∀ (a b c : Fin n), prec a b → prec b c → prec a c :=
    fun a b c h1 h2 => @IsTrans.trans _ _ hprec.toIsTrans a b c h1 h2
  have hrank : mbqcStrictOrderRank prec (mbqcIsStrictOrder hirr htrans)
      ∈ mbqcFuncSpace n (List.finRange n) := by
    refine mbqcFuncSpace_complete n (List.finRange n) ?_ _
    intro c
    exact List.mem_finRange c
  have hbits : (fun v u => decide (u ∈ g v)) ∈ mbqcFuncSpace n (mbqcFuncSpace n [false, true]) := by
    refine mbqcFuncSpace_complete n (mbqcFuncSpace n [false, true]) ?_ _
    intro y
    refine mbqcFuncSpace_complete n [false, true] ?_ y
    intro c
    cases c <;> simp
  have hmem : ((fun v u => decide (u ∈ g v)),
      mbqcStrictOrderRank prec (mbqcIsStrictOrder hirr htrans)) ∈ mbqcGFlowCandidates n :=
    List.mem_flatMap.mpr ⟨fun v u => decide (u ∈ g v), hbits,
      List.mem_map.mpr ⟨mbqcStrictOrderRank prec (mbqcIsStrictOrder hirr htrans), hrank, rfl⟩⟩
  have hcheck : mbqcGFlowCheck G I O lam g
      (mbqcStrictOrderRank prec (mbqcIsStrictOrder hirr htrans)) :=
    mbqcHasGFlowTotal_of_check G I O lam g prec hirr htrans htot hG0 hG1 hG2 hC
  have hdec : decide (mbqcGFlowCheck G I O lam
      (mbqcGFromBits (fun v u => decide (u ∈ g v)))
      (mbqcStrictOrderRank prec (mbqcIsStrictOrder hirr htrans))) = true := by
    have hgf : mbqcGFromBits (fun v u => decide (u ∈ g v)) = g := mbqcGFromBits_of g
    rw [hgf]
    exact decide_eq_true hcheck
  have hsome : (mbqcGFlowCandidates n).find?
      (fun p => decide (mbqcGFlowCheck G I O lam (mbqcGFromBits p.1) p.2)) |>.isSome := by
    rw [List.find?_isSome]
    exact ⟨((fun v u => decide (u ∈ g v)),
        mbqcStrictOrderRank prec (mbqcIsStrictOrder hirr htrans)), hmem, hdec⟩
  obtain ⟨p, hp⟩ : ∃ p, (mbqcGFlowCandidates n).find?
      (fun q => decide (mbqcGFlowCheck G I O lam (mbqcGFromBits q.1) q.2)) = some p := by
    cases h1 : (mbqcGFlowCandidates n).find?
      (fun q => decide (mbqcGFlowCheck G I O lam (mbqcGFromBits q.1) q.2)) with
    | none => exact absurd hsome (by simp [h1])
    | some v => exact ⟨v, rfl⟩
  have : (mbqcGFlowSearch G I O lam).isSome = true := by
    unfold mbqcGFlowSearch
    rw [hp]
    rfl
  exact this

/-- There is no universal implication from `MbqcHasGFlow` to success of `mbqcGFlowSearch`. -/
theorem mbqcGFlowSearch_not_complete :
    ¬ (∀ (n : ℕ) (G : MbqcGraph n) (I O : Finset (Fin n)) (lam : Fin n → MbqcPlane),
        MbqcHasGFlow G I O lam → (mbqcGFlowSearch G I O lam).isSome) := by
  intro h
  have hsome := h 4 clause6Aux_counterGraph clause6Aux_counterI clause6Aux_counterO clause6Aux_counterLam
    clause6_clause3b_counter_witness
  have hex : ∃ x, x ∈ mbqcGFlowCandidates 4 ∧
      decide (mbqcGFlowCheck clause6Aux_counterGraph clause6Aux_counterI clause6Aux_counterO clause6Aux_counterLam
        (mbqcGFromBits x.1) x.2) = true := by
    unfold mbqcGFlowSearch at hsome
    rw [List.find?_isSome] at hsome
    obtain ⟨x, hx, hp⟩ := hsome
    refine ⟨x, ?_, ?_⟩
    · exact mbqcGFlowCandidates_complete x.1 x.2
    · exact hp
  obtain ⟨p, _, hcheck⟩ := hex
  exact clause6Aux_counter_noCheck (mbqcGFromBits p.1) p.2 (of_decide_eq_true hcheck)

/-- Stores charges for fresh gates, pre-entanglement controlled-Z gates, measurements, feedback
gates, and messages. -/
structure Clause13Charge where

  freshGates : ℕ

  preEntanglementCz : ℕ

  measurementGates : ℕ

  feedbackGates : ℕ

  messages : ℕ
  deriving DecidableEq, Repr

/-- Sums the fresh, pre-entanglement, measurement, and feedback gate charges. -/
def Clause13Charge.totalGates (c : Clause13Charge) : ℕ :=
  c.freshGates + c.preEntanglementCz + c.measurementGates + c.feedbackGates

/-- Encodes two Boolean values as the index `2 * b0.toNat + b1.toNat` in `Fin 4`. -/
def clause12Index (b0 b1 : Bool) : Fin 4 :=
  ⟨(b0.toNat) * 2 + b1.toNat, by
    rcases b0 with _ | _ <;> rcases b1 with _ | _ <;> decide⟩

/-- Defines the identity operator on a two-dimensional system. -/
def clause12Identity : Operator 2 :=
  fun i j => if i = j then 1 else 0

/-- Defines the Pauli X matrix by its entries. -/
def clause12PauliX : Operator 2 :=
  fun i j => if i = j then 0 else 1

/-- Defines the diagonal Pauli Z matrix with entries 1 and -1. -/
def clause12PauliZ : Operator 2 :=
  fun i j => if i = j then (if i.val = 0 then 1 else -1) else 0

/-- Defines the product of Pauli X and Pauli Z, with off-diagonal entries -1 and 1. -/
def clause12PauliXZ : Operator 2 :=
  fun i j => if i = j then 0 else (if i.val = 0 then -1 else 1)

/-- Defines the unnormalized two-qubit vector supported on basis indices 0 and 3. -/
def clause12XTypeVector : Fin 4 → ℂ :=
  fun r => if r = 0 ∨ r = 3 then 1 else 0

/-- Defines the two-qubit operator obtained by scaling the outer product of
`clause12XTypeVector` by one half. -/
noncomputable def clause12XTypeEigenstate : Operator 4 :=
  fun r r' => (2 : ℂ)⁻¹ * (clause12XTypeVector r * clause12XTypeVector r')

/-- Defines the two X-basis projectors, with the off-diagonal sign determined by the Boolean
outcome. -/
noncomputable def clause12XyProjector (s : Bool) : Operator 2 :=
  fun i j => if i = j then (2 : ℂ)⁻¹ else (if s then -(2 : ℂ)⁻¹ else (2 : ℂ)⁻¹)

/-- Defines the computational-basis projector selected by the Boolean outcome. -/
noncomputable def clause12ZProjector (s : Bool) : Operator 2 :=
  fun i j =>
    if i = j then (if (i.val = 1) == s then 1 else 0) else 0

/-- Selects the X-basis projector for the XY and YZ planes and the computational-basis projector
for the XZ plane. -/
noncomputable def clause12PlaneProjector (lam : MbqcPlane) (s : Bool) : Operator 2 :=
  match lam with
  | .XY => clause12XyProjector s
  | .XZ => clause12ZProjector s
  | .YZ => clause12XyProjector s

/-- Lifts a two-dimensional operator to the first tensor factor of a two-qubit system. -/
noncomputable def clause12Lift0 (P : Operator 2) : Operator 4 :=
  fun r r' =>
    P ⟨r.val / 2, by omega⟩ ⟨r'.val / 2, by omega⟩ *
      (if r.val % 2 = r'.val % 2 then 1 else 0)

/-- Traces out the first qubit of a two-qubit operator, leaving an operator on the second qubit. -/
noncomputable def clause12Reduce1 (M : Operator 4) : Operator 2 :=
  fun i j => M ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
    + M ⟨2 + i.val, by omega⟩ ⟨2 + j.val, by omega⟩

/-- Selects Pauli X for the XZ plane and the product XZ for the XY and YZ planes. -/
noncomputable def clause12CorrectionType : MbqcPlane → Operator 2
  | .XY => clause12PauliXZ
  | .XZ => clause12PauliX
  | .YZ => clause12PauliXZ

/-- Applies the plane-dependent correction for outcome `true` and the identity for outcome
`false`. -/
noncomputable def clause12PlaneCorrection (lam : MbqcPlane) (s : Bool) : Operator 2 :=
  if s then clause12CorrectionType lam else clause12Identity

/-- Defines the identity matrix used as the adjoint of the trivial correction. -/
noncomputable def clause12AdjIdentity : Operator 2 :=
  fun i j => if i = j then 1 else 0

/-- Defines the Pauli X matrix used as its own correction adjoint. -/
noncomputable def clause12AdjX : Operator 2 :=
  fun i j => if i = j then 0 else 1

/-- Defines the adjoint of the XZ correction, with off-diagonal entries 1 and -1. -/
noncomputable def clause12AdjXZ : Operator 2 :=
  fun i j => if i = j then 0 else (if i.val = 0 then 1 else -1)

/-- Selects the adjoint of the plane-dependent correction according to the measurement outcome. -/
noncomputable def clause12PlaneCorrectionAdj (lam : MbqcPlane) (s : Bool) : Operator 2 :=
  match lam with
  | .XY => if s then clause12AdjXZ else clause12AdjIdentity
  | .XZ => if s then clause12AdjX else clause12AdjIdentity
  | .YZ => if s then clause12AdjXZ else clause12AdjIdentity

/-- Conjugates `clause12XTypeEigenstate` by the lifted plane-dependent measurement projector. -/
noncomputable def clause12Branch (lam : MbqcPlane) (s : Bool) : Operator 4 :=
  let P := clause12Lift0 (clause12PlaneProjector lam s)
  P * clause12XTypeEigenstate * P

/-- Traces out the measured first qubit from `clause12Branch`. -/
noncomputable def clause12Output (lam : MbqcPlane) (s : Bool) : Operator 2 :=
  clause12Reduce1 (clause12Branch lam s)

/-- Conjugates the reduced measurement output by the outcome-dependent plane correction. -/
noncomputable def clause12CorrectedOutput (lam : MbqcPlane) (s : Bool) : Operator 2 :=
  let C := clause12PlaneCorrection lam s
  C * clause12Output lam s * clause12PlaneCorrectionAdj lam s

end Qatlib.Concepts.FiniteLocc.LOCCProgram
