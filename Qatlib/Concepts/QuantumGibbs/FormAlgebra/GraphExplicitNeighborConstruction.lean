/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.GraphSpectralConstructionDefs
public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.GraphNormalizedChainConstruction
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
open Qatlib.Foundations.PureStateMath Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.GraphNormalizedChainConstruction

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra

open Qatlib
open Qatlib.Concepts.GraphEnergy.ZeroEnergy
open Qatlib.Concepts.GraphStationary.StationaryLaw
open scoped BigOperators Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

abbrev PairVertex (N : ℕ) : Type := {S : Finset (Fin N) // S.card = 2}

instance (N : ℕ) : Finite (PairVertex N) := by
  unfold PairVertex
  infer_instance

instance (N : ℕ) : Fintype (PairVertex N) := Fintype.ofFinite _

/-- Intersecting a finite set with a pair containing one member and one nonmember gives the
singleton member. -/
lemma inter_pair {α : Type*} [DecidableEq α] {s : Finset α} {a b : α}
    (ha : a ∈ s) (hb : b ∉ s) : s ∩ insert a {b} = {a} := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  aesop

def pairGraph (N : ℕ) : SimpleGraph (PairVertex N) where
  Adj S S' := (S.1 ∩ S'.1).card = 1
  symm := ⟨fun S S' h => by
    rw [Finset.inter_comm]
    exact h⟩
  loopless := ⟨fun S h => by
    have hcard : (S.1 ∩ S.1).card = 2 := by rw [Finset.inter_self]; exact S.2
    rw [hcard] at h
    norm_num at h⟩

instance (N : ℕ) : DecidableRel (pairGraph N).Adj := fun _ _ => by
  unfold pairGraph SimpleGraph.Adj
  infer_instance

def pairNeighbours (N : ℕ) (S : PairVertex N) : Finset (PairVertex N) :=
  (Finset.univ : Finset (PairVertex N)).filter (fun S' => (S.1 ∩ S'.1).card = 1)

/-- The complement of a pair vertex contains `N` minus two elements. -/
lemma pairVertex_outside_card {N : ℕ} (S : PairVertex N) :
    ((Finset.univ : Finset (Fin N)) \ S.1).card = N - 2 := by
  have hsub : S.1 ⊆ (Finset.univ : Finset (Fin N)) := Finset.subset_univ _
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ]
  simp only [Fintype.card_fin]
  omega

def pairNeighbourOf {N : ℕ} (S : PairVertex N) (x c : Fin N)
    (hx : x ∈ S.1) (hc : c ∉ S.1) : PairVertex N :=
  ⟨insert x {c}, by
    have hne : x ≠ c := by
      intro h
      subst h
      exact hc hx
    rw [Finset.card_insert_of_notMem (by simpa using! hne)]
    simp⟩

/-- The underlying set of `pairNeighbourOf` is the pair formed by the retained and new elements. -/
lemma pairNeighbourOf_val {N : ℕ} (S : PairVertex N) (x c : Fin N)
    (hx : x ∈ S.1) (hc : c ∉ S.1) :
    (pairNeighbourOf S x c hx hc).1 = insert x {c} := rfl

/-- Replacing one element of a pair vertex with an outside element produces an adjacent vertex. -/
lemma pairNeighbourOf_adj {N : ℕ} (S : PairVertex N) (x c : Fin N)
    (hx : x ∈ S.1) (hc : c ∉ S.1) :
    (pairGraph N).Adj S (pairNeighbourOf S x c hx hc) := by
  have hkey : S.1 ∩ insert x {c} = {x} := by
    ext y
    constructor
    · intro hy
      have hy2 : y = x ∨ y = c := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using! (Finset.mem_inter.mp hy).2
      rcases hy2 with hxy | hyc
      · rw [hxy]
        exact Finset.mem_singleton.mpr rfl
      · exact False.elim (hc (hyc ▸ (Finset.mem_inter.mp hy).1))
    · intro hy
      have hxy : y = x := by simpa only [Finset.mem_singleton] using! hy
      rw [hxy]
      exact Finset.mem_inter.mpr ⟨hx, Finset.mem_insert_self x {c}⟩
  show (S.1 ∩ (pairNeighbourOf S x c hx hc).1).card = 1
  rw [pairNeighbourOf_val, hkey]
  simp

/-- The number of pair neighbors is the pair cardinality times its complement cardinality. -/
lemma pairNeighbours_card {N : ℕ} (S : PairVertex N) :
    (pairNeighbours N S).card
      = S.1.card * ((Finset.univ : Finset (Fin N)) \ S.1).card := by
  unfold pairNeighbours
  set src : Finset (Fin N × Fin N) :=
    Finset.product S.1 ((Finset.univ : Finset (Fin N)) \ S.1) with hsrc
  set tgt : Finset (PairVertex N) :=
    (Finset.univ : Finset (PairVertex N)).filter (fun z => (S.1 ∩ z.1).card = 1) with htgt
  have hsplitOf : ∀ (p : Fin N × Fin N), p ∈ src → p.1 ∈ S.1 ∧ p.2 ∉ S.1 := by
    intro p hp
    rw [hsrc] at hp
    have hmem : p.1 ∈ S.1 ∧ p.2 ∈ (Finset.univ : Finset (Fin N)) \ S.1 :=
      Finset.mem_product.mp hp
    exact ⟨hmem.1, (Finset.mem_sdiff.mp hmem.2).2⟩
  have hneOf : ∀ (p : Fin N × Fin N), p ∈ src → p.2 ∉ S.1 := fun p hp => (hsplitOf p hp).2
  have hcard : src.card = tgt.card := by
    apply Finset.card_bij (fun (p : Fin N × Fin N) (hp : p ∈ src) => pairNeighbourOf S p.1 p.2
      (hsplitOf p hp).1 (hneOf p hp))
    · intro p hp
      rw [htgt]
      simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, pairNeighbourOf_adj S p.1 p.2 (hsplitOf p hp).1
        (hneOf p hp)⟩
    · intro p hp q hq hxy
      have hxmem : p.1 ∈ S.1 := (hsplitOf p hp).1
      have hcmem : p.2 ∉ S.1 := (hsplitOf p hp).2
      have hymem : q.1 ∈ S.1 := (hsplitOf q hq).1
      have hcmem' : q.2 ∉ S.1 := (hsplitOf q hq).2
      have hset : (insert p.1 {p.2} : Finset (Fin N)) = (insert q.1 {q.2} : Finset (Fin N)) := by
        have h1 : (pairNeighbourOf S p.1 p.2 hxmem hcmem).1
            = (insert p.1 {p.2} : Finset (Fin N)) := rfl
        have h2 : (pairNeighbourOf S q.1 q.2 hymem hcmem').1
            = (insert q.1 {q.2} : Finset (Fin N)) := rfl
        have hxy' := congrArg Subtype.val hxy
        rw [h1, h2] at hxy'
        exact hxy'
      have hx1 : p.1 = q.1 ∨ p.1 = q.2 := by
        have hxmem' : p.1 ∈ (insert q.1 {q.2} : Finset (Fin N)) := by
          rw [← hset]
          exact Finset.mem_insert_self (p.1 : Fin N) ({p.2} : Finset (Fin N))
        rcases Finset.mem_insert.mp hxmem' with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_singleton.mp h)
      rcases hx1 with hxy | hxy
      · have hymem' : q.1 ∈ (insert p.1 {p.2} : Finset (Fin N)) := by
          rw [hset]
          exact Finset.mem_insert_self (q.1 : Fin N) ({q.2} : Finset (Fin N))
        have hy1 : q.1 = p.1 ∨ q.1 = p.2 := by
          rcases Finset.mem_insert.mp hymem' with h | h
          · exact Or.inl h
          · exact Or.inr (Finset.mem_singleton.mp h)
        rcases hy1 with hyx | hyx
        · have hp2mem' : p.2 ∈ (insert q.1 {q.2} : Finset (Fin N)) := by
            rw [← hset]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self (p.2 : Fin N))
          have hp2 : p.2 = q.1 ∨ p.2 = q.2 := by
            rcases Finset.mem_insert.mp hp2mem' with h | h
            · exact Or.inl h
            · exact Or.inr (Finset.mem_singleton.mp h)
          rcases hp2 with h | h
          · exact False.elim (hcmem (show p.2 ∈ S.1 from by rw [h]; exact hymem))
          · exact Prod.ext hxy h
        · exact False.elim (hcmem (show p.2 ∈ S.1 from by rw [← hyx]; exact hymem))
      · exact False.elim (hcmem' (show q.2 ∈ S.1 from by rw [← hxy]; exact hxmem))
    · intro z hz
      rw [htgt] at hz
      have hzcard : (S.1 ∩ z.1).card = 1 := (Finset.mem_filter.mp hz).2
      obtain ⟨shared, hshared⟩ := Finset.card_eq_one.mp hzcard
      have hsharedin : shared ∈ S.1 ∩ z.1 := by
        rw [hshared]
        simp
      have hsharedS : shared ∈ S.1 := (Finset.mem_inter.mp hsharedin).1
      have hsharedz : shared ∈ z.1 := (Finset.mem_inter.mp hsharedin).2
      have hzcard2 : (z.1 \ (S.1 ∩ z.1)).card = 1 := by
        rw [Finset.card_sdiff]
        have hinter : (S.1 ∩ z.1) ∩ z.1 = S.1 ∩ z.1 := by
          rw [Finset.inter_assoc, Finset.inter_self]
        rw [hinter]
        rw [show z.1.card = 2 from z.2]
        omega
      obtain ⟨other, hother⟩ := Finset.card_eq_one.mp hzcard2
      have hotherin : other ∈ z.1 \ (S.1 ∩ z.1) := by
        rw [hother]
        simp
      have hotherz : other ∈ z.1 := (Finset.mem_sdiff.mp hotherin).1
      have hothermem : other ∉ S.1 := by
        intro h
        exact (Finset.mem_sdiff.mp hotherin).2 (Finset.mem_inter.mpr ⟨h, hotherz⟩)
      have hne : shared ≠ other := by
        intro h
        exact hothermem (h ▸ hsharedS)
      have hzset : z.1 = {shared, other} := by
        have h1 : ({shared, other} : Finset (Fin N)) ⊆ z.1 := by
          intro y hy
          have hy' : y = shared ∨ y = other := by
            simpa only [Finset.mem_insert, Finset.mem_singleton] using! hy
          rcases hy' with h | h
          · rw [h]; exact hsharedz
          · rw [h]; exact hotherz
        have h2 : z.1.card ≤ ({shared, other} : Finset (Fin N)).card := by
          rw [Finset.card_insert_of_notMem (by simp [hne])]
          simp only [Finset.card_singleton]
          rw [show z.1.card = 2 from z.2]
        exact (Finset.eq_of_subset_of_card_le h1 h2).symm
      refine ⟨(shared, other),
        Finset.mem_product.mpr ⟨hsharedS, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hothermem⟩⟩, ?_⟩
      apply Subtype.ext
      rw [pairNeighbourOf_val, hzset]
  rw [← hcard, hsrc, Finset.product_eq_sprod, Finset.card_product]

/-- Every pair graph vertex has degree twice the natural difference of `N` and two. -/
lemma pairGraph_degree {N : ℕ} (S : PairVertex N) :
    degree (pairGraph N) S = ((2 * (N - 2) : ℕ) : ℝ) := by
  rw [degree_eq_sum_adj]
  have hsum : (∑ z : PairVertex N, (if (pairGraph N).Adj S z then (1 : ℝ) else 0))
      = (pairNeighbours N S).card := by
    have h1 : (∑ z : PairVertex N, (if (pairGraph N).Adj S z then (1 : ℝ) else 0))
        = ∑ z ∈ (Finset.univ : Finset (PairVertex N)).filter
            (fun z => (pairGraph N).Adj S z), (1 : ℝ) := by
      rw [Finset.sum_filter]
    have h2 : (∑ z ∈ (Finset.univ : Finset (PairVertex N)).filter
            (fun z => (pairGraph N).Adj S z), (1 : ℝ))
        = ((Finset.univ : Finset (PairVertex N)).filter
            (fun z => (pairGraph N).Adj S z)).card := by
      have h := Finset.card_eq_sum_ones
        (s := (Finset.univ : Finset (PairVertex N)).filter
          (fun z => (pairGraph N).Adj S z))
      exact_mod_cast h.symm
    have h3 : ((Finset.univ : Finset (PairVertex N)).filter
            (fun z => (pairGraph N).Adj S z)) = pairNeighbours N S := by
      unfold pairNeighbours
      rfl
    rw [h1, h2, h3]
  rw [hsum, pairNeighbours_card, S.2, pairVertex_outside_card]

/-- The pair graph is regular of degree twice the natural difference of `N` and two. -/
lemma pairGraph_isDegreeRegular (N : ℕ) :
    IsDegreeRegular (pairGraph N) ((2 * (N - 2) : ℕ) : ℝ) := by
  intro x
  exact pairGraph_degree x

/-- The complement of a pair vertex has cardinality `N` minus two. -/
lemma pairVertex_outside_card' {N : ℕ} (S : PairVertex N) :
    ((Finset.univ : Finset (Fin N)) \ S.1).card = N - 2 :=
  pairVertex_outside_card S

variable {N : ℕ}

def pairAtTotal (hN : 2 ≤ N) (c w : Fin N) : PairVertex N :=
  if h : c ≠ w then
    ⟨insert c {w}, by
      rw [Finset.card_insert_of_notMem (by simp [h])]
      simp⟩
  else
    ⟨insert (⟨0, by omega⟩ : Fin N) {(⟨1, by omega⟩ : Fin N)}, by
      have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by
        intro hh
        have := congrArg Fin.val hh
        simp at this
      rw [Finset.card_insert_of_notMem (by simp [h01])]
      simp⟩

/-- For distinct inputs, `pairAtTotal` has the underlying set consisting of those two inputs. -/
lemma pairAtTotal_val (hN : 2 ≤ N) (c w : Fin N) (hcw : c ≠ w) :
    (pairAtTotal hN c w).1 = insert c {w} := by
  simp [pairAtTotal, hcw]

/-- For distinct inputs, `pairAtTotal` is unchanged by swapping them. -/
lemma pairAtTotal_symm (hN : 2 ≤ N) (c w : Fin N) (hcw : c ≠ w) :
    pairAtTotal hN c w = pairAtTotal hN w c := by
  have hset : (insert c {w} : Finset (Fin N)) = insert w {c} := by
    ext x
    simp [or_comm]
  exact Subtype.ext
      (by rw [pairAtTotal_val hN c w hcw, pairAtTotal_val hN w c hcw.symm]; exact hset)

def pairStar (hN : 2 ≤ N) (f : PairVertex N → ℝ) (c : Fin N) : ℝ :=
  ∑ w ∈ (Finset.univ : Finset (Fin N)).erase c, f (pairAtTotal hN c w)

/-- Equality of pairs formed from an inside element and an outside element determines both
elements uniquely. -/
lemma pairAtTotal_inj {S : PairVertex N} (hN : 2 ≤ N) {c c' w w' : Fin N}
    (hcw : c ≠ w) (hc'w' : c' ≠ w')
    (hcS : c ∈ S.1) (hc'S : c' ∈ S.1)
    (hwS : w ∉ S.1) (hw'S : w' ∉ S.1)
    (h : pairAtTotal hN c w = pairAtTotal hN w' c') :
    c = c' ∧ w = w' := by
  have h' : (pairAtTotal hN c w).1 = (pairAtTotal hN w' c').1 := congrArg Subtype.val h
  rw [pairAtTotal_val hN c w hcw] at h'
  rw [pairAtTotal_val hN w' c' hc'w'.symm] at h'
  have hmem : c ∈ insert w' ({c'} : Finset (Fin N)) := by rw [← h']; simp
  rcases Finset.mem_insert.mp hmem with hcc | hcc
  · exact (hw'S (hcc ▸ hcS)).elim
  · have hcc' : c = c' := Finset.mem_singleton.mp hcc
    refine ⟨hcc', ?_⟩
    have hnotw : c ∉ ({w} : Finset (Fin N)) := fun h => hcw (Finset.mem_singleton.mp h)
    have hnotw' : c ∉ ({w'} : Finset (Fin N)) :=
      fun h => hc'w' (hcc' ▸ Finset.mem_singleton.mp h)
    have h''' : (insert c {w} : Finset (Fin N)) = insert w' {c} := by simpa [hcc'] using! h'
    have hsym : (insert w' {c} : Finset (Fin N)) = insert c {w'} := by
      ext x
      simp [or_comm]
    have h'' : (insert c {w} : Finset (Fin N)) = insert c {w'} := by rw [h''', hsym]
    have hset : ({w} : Finset (Fin N)) = {w'} := by
      have h1 : (insert c {w} : Finset (Fin N)).erase c = {w} := Finset.erase_insert hnotw
      have h2 : (insert c {w'} : Finset (Fin N)).erase c = {w'} := Finset.erase_insert hnotw'
      rw [← h1, ← h2, h'']
    refine Finset.mem_singleton.mp ?_
    rw [← hset]
    exact Finset.mem_singleton_self (w : Fin N)

/-- Every neighbor of a pair vertex consists of one element from that vertex and one element
outside it. -/
lemma pair_neighbour_split {S z : PairVertex N} (h : (pairGraph N).Adj S z) :
    ∃ c w : Fin N, c ∈ S.1 ∧ w ∉ S.1 ∧ c ≠ w ∧ z.1 = insert c {w} := by
  have hcard : (S.1 ∩ z.1).card = 1 := h
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
  have hcin : c ∈ S.1 ∩ z.1 := by rw [hc]; simp
  have hcin' : c ∈ S.1 ∧ c ∈ z.1 := Finset.mem_inter.mp hcin
  have hcinS : c ∈ S.1 := hcin'.1
  have hcinZ : c ∈ z.1 := hcin'.2
  obtain ⟨x, y, hxy, hz⟩ := Finset.card_eq_two.mp z.2
  have hcmem : c ∈ insert x ({y} : Finset (Fin N)) := by rw [← hz]; exact hcinZ
  rcases Finset.mem_insert.mp hcmem with hcx | hcy'
  · have hcxS : x ∈ S.1 := hcx ▸ hcinS
    refine ⟨x, y, hcxS, ?_, hxy, ?_⟩
    · intro hy
      have hyin : y ∈ S.1 ∩ z.1 := Finset.mem_inter.mpr ⟨hy, by rw [hz]; simp⟩
      rw [hc] at hyin
      simp only [Finset.mem_singleton] at hyin
      exact hxy (hyin.trans hcx).symm
    · rw [hz]
  · have hcy : c = y := Finset.mem_singleton.mp hcy'
    have hcyS : y ∈ S.1 := hcy ▸ hcinS
    refine ⟨y, x, hcyS, ?_, hxy.symm, ?_⟩
    · intro hx
      have hxin : x ∈ S.1 ∩ z.1 := Finset.mem_inter.mpr ⟨hx, by rw [hz]; simp⟩
      rw [hc] at hxin
      simp only [Finset.mem_singleton] at hxin
      exact hxy (hxin.trans hcy)
    · rw [hz]
      have hsym : ({x, y} : Finset (Fin N)) = {y, x} := by
        ext q
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl)
          · exact Or.inr rfl
          · exact Or.inl rfl
        · rintro (rfl | rfl)
          · exact Or.inr rfl
          · exact Or.inl rfl
      exact hsym

/-- A finite set of cardinality two containing `c` consists of `c` and one distinct element. -/
lemma exists_insert_of_card_two {α : Type} [DecidableEq α] {s : Finset α} (hcard : s.card = 2)
    {c : α} (hcm : c ∈ s) : ∃ w : α, w ≠ c ∧ s = insert c {w} := by
  obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.mp hcard
  have hcmem : c ∈ insert x ({y} : Finset α) := by rw [← hs]; exact hcm
  rcases Finset.mem_insert.mp hcmem with hcx | hcy'
  · refine ⟨y, fun h => hxy.symm (h.trans hcx), ?_⟩
    rw [hs]
    simp [hcx]
  · have hcy : c = y := Finset.mem_singleton.mp hcy'
    refine ⟨x, fun h => hxy (h.trans hcy), ?_⟩
    rw [hs]
    have hsym : ({x, y} : Finset α) = {y, x} := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (rfl | rfl)
        · exact Or.inr rfl
        · exact Or.inl rfl
      · rintro (rfl | rfl)
        · exact Or.inr rfl
        · exact Or.inl rfl
    rw [hsym]
    simp [hcy]

/-- The sum over pair vertices containing `c` equals the star sum at `c`. -/
lemma pairStar_eq_vertexSum (hN : 2 ≤ N) (f : PairVertex N → ℝ) (c : Fin N) :
    (∑ S : PairVertex N, if c ∈ S.1 then f S else 0) = pairStar hN f c := by
  have hset : (Finset.univ : Finset (PairVertex N)).filter (fun S => c ∈ S.1)
      = Finset.image (fun w : Fin N => pairAtTotal hN c w)
          ((Finset.univ : Finset (Fin N)).erase c) := by
    ext z
    constructor
    · intro hz
      rw [Finset.mem_filter] at hz
      obtain ⟨w, hw1, hw2⟩ := exists_insert_of_card_two z.2 hz.2
      rw [Finset.mem_image]
      refine ⟨w, Finset.mem_erase.mpr ⟨hw1, Finset.mem_univ (w : Fin N)⟩, ?_⟩
      have hv : (pairAtTotal hN c w).1 = z.1 := by
        rw [pairAtTotal_val hN c w hw1.symm]
        exact hw2.symm
      exact Subtype.ext hv
    · intro hz
      rw [Finset.mem_image] at hz
      obtain ⟨w, hw1, hw2⟩ := hz
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ z, ?_⟩
      have hne : w ≠ c := Finset.mem_erase.mp hw1 |>.1
      rw [← hw2, pairAtTotal_val hN c w hne.symm]
      simp
  rw [← Finset.sum_filter, hset]
  have hinj : Set.InjOn (fun w : Fin N => pairAtTotal hN c w)
      ((Finset.univ : Finset (Fin N)).erase c) := by
    intro w hw1 w' hw2 h
    have hne1 : w ≠ c := Finset.mem_erase.mp hw1 |>.1
    have hne2 : w' ≠ c := Finset.mem_erase.mp hw2 |>.1
    have h' := congrArg Subtype.val h
    rw [pairAtTotal_val hN c w hne1.symm] at h'
    rw [pairAtTotal_val hN c w' hne2.symm] at h'
    have hnotw : c ∉ ({w} : Finset (Fin N)) := by
      intro h
      have hc' : c = w := by simpa only [Finset.mem_singleton] using! h
      exact hne1 hc'.symm
    have hnotw' : c ∉ ({w'} : Finset (Fin N)) := by
      intro h
      have hc' : c = w' := by simpa only [Finset.mem_singleton] using! h
      exact hne2 hc'.symm
    have h1 : (insert c {w} : Finset (Fin N)).erase c = {w} := Finset.erase_insert hnotw
    have h2 : (insert c {w'} : Finset (Fin N)).erase c = {w'} := Finset.erase_insert hnotw'
    have hset' : ({w} : Finset (Fin N)) = {w'} := by rw [← h1, ← h2, h']
    refine Finset.mem_singleton.mp ?_
    rw [← hset']
    exact Finset.mem_singleton_self (w : Fin N)
  rw [Finset.sum_image (f := fun z => f z) (g := fun w : Fin N => pairAtTotal hN c w)
    (s := (Finset.univ : Finset (Fin N)).erase c) hinj]
  rfl

/-- A sum over pair neighbors can be indexed by a retained element and an outside element. -/
lemma pairNeighbours_sum (hN : 2 ≤ N) (S : PairVertex N) (f : PairVertex N → ℝ) :
    (∑ z ∈ pairNeighbours N S, f z)
      = ∑ c ∈ S.1, ∑ w ∈ (Finset.univ : Finset (Fin N)) \ S.1, f (pairAtTotal hN c w) := by
  let T : Finset (Fin N) := (Finset.univ : Finset (Fin N)) \ S.1
  have hmem : ∀ p : Fin N × Fin N, p ∈ S.1 ×ˢ T → p.1 ∈ S.1 ∧ p.2 ∉ S.1 := by
    intro p hp
    rw [Finset.mem_product] at hp
    exact ⟨hp.1, (Finset.mem_sdiff.mp hp.2).2⟩
  have hne : ∀ p : Fin N × Fin N, p ∈ S.1 ×ˢ T → p.1 ≠ p.2 := by
    intro p hp
    obtain ⟨h1, h2⟩ := hmem p hp
    exact fun hh => h2 (hh.symm ▸ h1)
  have hinject : ∀ p q : Fin N × Fin N, p ∈ S.1 ×ˢ T → q ∈ S.1 ×ˢ T →
      pairAtTotal hN p.1 p.2 = pairAtTotal hN q.1 q.2 → p = q := by
    intro p q hp hq h
    obtain ⟨hp1, hp2⟩ := hmem p hp
    obtain ⟨hq1, hq2⟩ := hmem q hq
    have hsym : pairAtTotal hN q.1 q.2 = pairAtTotal hN q.2 q.1 :=
      pairAtTotal_symm hN q.1 q.2 (hne q hq)
    have hres := pairAtTotal_inj hN (hne p hp) (hne q hq) hp1 hq1 hp2 hq2 (h.trans hsym)
    exact Prod.ext hres.1 hres.2
  have hmain : (∑ p ∈ S.1 ×ˢ T, f (pairAtTotal hN p.1 p.2))
      = ∑ z ∈ pairNeighbours N S, f z := by
    refine Finset.sum_bij (s := S.1 ×ˢ T) (t := pairNeighbours N S)
      (f := fun p : Fin N × Fin N => f (pairAtTotal hN p.1 p.2))
      (g := fun z : PairVertex N => f z)
      (fun p _ => pairAtTotal hN p.1 p.2) ?_ ?_ ?_ ?_
    · intro p hp
      rw [pairNeighbours, Finset.mem_filter]
      refine ⟨Finset.mem_univ (pairAtTotal hN p.1 p.2), ?_⟩
      obtain ⟨hp1, hp2⟩ := hmem p hp
      have hne' : p.1 ≠ p.2 := hne p hp
      have hset : S.1 ∩ insert p.1 {p.2} = ({p.1} : Finset (Fin N)) := by
        ext q
        constructor
        · intro hq
          have hq1 : q ∈ S.1 := (Finset.mem_inter.mp hq).1
          have hq2 : q ∈ insert p.1 {p.2} := (Finset.mem_inter.mp hq).2
          rcases Finset.mem_insert.mp hq2 with h1 | h2
          · exact Finset.mem_singleton.mpr h1
          · exact False.elim (hp2 (by rw [← Finset.mem_singleton.mp h2]; exact hq1))
        · intro hq
          refine Finset.mem_inter.mpr ⟨?_, ?_⟩
          · rw [Finset.mem_singleton.mp hq]
            exact hp1
          · exact (by rw [Finset.mem_singleton.mp hq]; exact Finset.mem_insert_self p.1 {p.2})
      have hcard : (S.1 ∩ (pairAtTotal hN p.1 p.2).1).card = 1 := by
        rw [pairAtTotal_val hN p.1 p.2 hne']
        rw [hset]
        simp
      exact hcard
    · intro p hp q hq heq
      exact hinject p q hp hq heq
    · intro z hz
      rw [pairNeighbours, Finset.mem_filter] at hz
      obtain ⟨c, w, hcS, hwS, hcw, hzset⟩ := pair_neighbour_split hz.2
      refine ⟨(c, w), ?_, ?_⟩
      · rw [Finset.mem_product]
        exact ⟨hcS, Finset.mem_sdiff.mpr ⟨Finset.mem_univ (w : Fin N), hwS⟩⟩
      · have hv : pairAtTotal hN c w = z := by
          have : (pairAtTotal hN c w).1 = z.1 := by
            rw [pairAtTotal_val hN c w hcw]
            exact hzset.symm
          exact Subtype.ext this
        exact hv
    · intro p hp
      rfl
  calc
    (∑ z ∈ pairNeighbours N S, f z)
        = ∑ p ∈ S.1 ×ˢ T, f (pairAtTotal hN p.1 p.2) := by
          symm
          exact hmain
    _ = ∑ c ∈ S.1, ∑ w ∈ T, f (pairAtTotal hN c w) :=
          Finset.sum_product S.1 T (fun p => f (pairAtTotal hN p.1 p.2))

def pairStarIndicator (c : Fin N) (S : PairVertex N) : ℝ :=
  if c ∈ S.1 then 1 else 0

/-- The real sum of a finite set's indicator is its cardinality. -/
lemma sum_indicator_card {α : Type} [Fintype α] [DecidableEq α] (s : Finset α) :
    (∑ x : α, (if x ∈ s then (1 : ℝ) else 0)) = s.card := by
  have hfilter : ((Finset.univ : Finset α).filter (fun x => x ∈ s)) = s := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).2
    · intro hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
  have h1 : (∑ x : α, (if x ∈ s then (1 : ℝ) else 0))
      = ∑ x ∈ ((Finset.univ : Finset α).filter (fun x => x ∈ s)), (1 : ℝ) := by
    symm
    exact Finset.sum_filter (p := fun x => x ∈ s) (f := fun _ => (1 : ℝ))
  have hcard : (∑ x ∈ s, (1 : ℝ)) = (s.card : ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_ones s).symm
  rw [h1, hfilter, hcard]

/-- For `N` at least two, the sum of a star indicator is `N` minus one. -/
lemma pairStarIndicator_sum (hN : 2 ≤ N) (c : Fin N) :
    (∑ S : PairVertex N, pairStarIndicator c S) = (N - 1 : ℝ) := by
  have h := pairStar_eq_vertexSum hN (fun _ => (1 : ℝ)) c
  unfold pairStarIndicator
  rw [h]
  unfold pairStar
  have hcard : ((Finset.univ : Finset (Fin N)).erase c).card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ]
    simp
  have h1 : (∑ w ∈ (Finset.univ : Finset (Fin N)).erase c,
      (fun _ => (1 : ℝ)) (pairAtTotal hN c w))
      = ∑ w ∈ (Finset.univ : Finset (Fin N)).erase c, (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro w _
    rfl
  have hcard' : (∑ w ∈ (Finset.univ : Finset (Fin N)).erase c, (1 : ℝ))
      = (N - 1 : ℝ) := by
    have h'' : ((Finset.univ : Finset (Fin N)).erase c).card = N - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ]
      simp
    have h1' : (∑ w ∈ (Finset.univ : Finset (Fin N)).erase c, (1 : ℝ))
        = (((Finset.univ : Finset (Fin N)).erase c).card : ℝ) := by
      exact_mod_cast (Finset.card_eq_sum_ones _).symm
    have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    rw [h1', h'', hcast]
  rw [h1, hcard']

/-- The inner product of two star indicators is `N` minus one for equal centers and one
otherwise. -/
lemma pairStarIndicator_gram (hN : 2 ≤ N) (c d : Fin N) :
    (∑ S : PairVertex N, pairStarIndicator c S * pairStarIndicator d S)
      = if c = d then (N - 1 : ℝ) else 1 := by
  by_cases hcd : c = d
  · subst hcd
    have hsq : ∀ S : PairVertex N,
        pairStarIndicator c S * pairStarIndicator c S = pairStarIndicator c S := by
      intro S
      unfold pairStarIndicator
      split <;> ring
    rw [Finset.sum_congr rfl (fun S _ => hsq S)]
    rw [pairStarIndicator_sum hN c]
    simp
  · have hconv : ∀ S : PairVertex N,
        pairStarIndicator c S * pairStarIndicator d S
          = (if c ∈ S.1 then (if d ∈ S.1 then (1 : ℝ) else 0) else 0) := by
      intro S
      unfold pairStarIndicator
      split <;> split <;> ring
    rw [Finset.sum_congr rfl (fun S _ => hconv S)]
    have hgr := pairStar_eq_vertexSum hN (fun S => if d ∈ S.1 then (1 : ℝ) else 0) c
    rw [hgr]
    unfold pairStar
    have hval : ∀ w ∈ (Finset.univ : Finset (Fin N)).erase c,
        (if d ∈ (pairAtTotal hN c w).1 then (1 : ℝ) else 0)
          = (if d = w then (1 : ℝ) else 0) := by
      intro w hw
      have hne : c ≠ w := Ne.symm (Finset.mem_erase.mp hw).1
      rw [pairAtTotal_val hN c w hne]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hdw : d = w
      · simp [hdw]
      · have hdc : d ≠ c := fun h => hcd h.symm
        simp [hdw, hdc]
    rw [Finset.sum_congr rfl (fun w hw => hval w hw)]
    have hmem : d ∈ (Finset.univ : Finset (Fin N)).erase c :=
      Finset.mem_erase.mpr ⟨fun h => hcd h.symm, Finset.mem_univ d⟩
    have hsum : (∑ w ∈ (Finset.univ : Finset (Fin N)).erase c,
        (if d = w then (1 : ℝ) else 0)) = 1 := by
      rw [Finset.sum_eq_single d]
      · simp
      · intro b hb hne
        have hdb : d ≠ b := fun h => hne h.symm
        simp [hdb]
      · intro h
        exact (h hmem).elim
    rw [hsum]
    simp [hcd]

/-- Summing all pair star sums counts every pair vertex twice. -/
lemma sum_pairStar_eq_two_mul_sum (hN : 2 ≤ N) (f : PairVertex N → ℝ) :
    (∑ c : Fin N, pairStar hN f c) = 2 * (∑ S : PairVertex N, f S) := by
  have hconv : ∀ c : Fin N, pairStar hN f c
      = ∑ S : PairVertex N, (if c ∈ S.1 then f S else 0) :=
    fun c => (pairStar_eq_vertexSum hN f c).symm
  rw [Finset.sum_congr rfl (fun c _ => hconv c)]
  have hswap : (∑ c : Fin N, ∑ S : PairVertex N, (if c ∈ S.1 then f S else 0))
      = ∑ S : PairVertex N, ∑ c : Fin N, (if c ∈ S.1 then f S else 0) := by
    exact Finset.sum_comm' (s := (Finset.univ : Finset (Fin N)))
      (t := fun _ => (Finset.univ : Finset (PairVertex N)))
      (t' := (Finset.univ : Finset (PairVertex N)))
      (s' := fun _ => (Finset.univ : Finset (Fin N))) (fun _ _ => by simp)
  rw [hswap]
  have hinner (S : PairVertex N) :
      (∑ c : Fin N, (if c ∈ S.1 then f S else 0))
        = f S * (∑ c : Fin N, (if c ∈ S.1 then (1 : ℝ) else 0)) := by
    have h1 : (∑ c : Fin N, (if c ∈ S.1 then f S else 0))
        = ∑ c : Fin N, (f S * (if c ∈ S.1 then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases h : c ∈ S.1 <;> simp [h]
    rw [h1, Finset.mul_sum]
  calc
    (∑ S : PairVertex N, ∑ c : Fin N, (if c ∈ S.1 then f S else 0))
        = ∑ S : PairVertex N, f S * (∑ c : Fin N, (if c ∈ S.1 then (1 : ℝ) else 0)) := by
          apply Finset.sum_congr rfl
          intro S _
          rw [hinner, Finset.mul_sum]
    _ = ∑ S : PairVertex N, f S * (2 : ℝ) := by
          apply Finset.sum_congr rfl
          intro S _
          rw [sum_indicator_card S.1]
          have h2 : (S.1.card : ℝ) = 2 := by exact_mod_cast S.2
          rw [h2]
    _ = 2 * (∑ S : PairVertex N, f S) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S _
          ring

def pairGroundSum (s : Fin N → ℝ) : ℝ :=
  ∑ c : Fin N, s c

def pairPotentialRaw (s : Fin N → ℝ) (S : PairVertex N) : ℝ :=
  ∑ c : Fin N, s c * pairStarIndicator c S

def pairPotentialPart (s : Fin N → ℝ) (S : PairVertex N) : ℝ :=
  pairPotentialRaw s S / ((N - 2 : ℝ))

/-- The star Gram matrix applied to `s` gives its total sum plus the product of its value at the
chosen center with the difference between `N` and two. -/
lemma sum_potential_gram (s : Fin N → ℝ) (c : Fin N) :
    (∑ d : Fin N, s d * (if c = d then (N - 1 : ℝ) else 1))
      = (∑ d : Fin N, s d) + ((N - 2 : ℝ)) * s c := by
  have hsplit : ∀ d : Fin N,
      s d * (if c = d then (N - 1 : ℝ) else 1)
        = s d * (1 + ((N - 2 : ℝ)) * (if c = d then (1 : ℝ) else 0)) := by
    intro d
    by_cases h : c = d
    · rw [ite_eq_left h, ite_eq_left h]
      ring
    · rw [ite_eq_right h, ite_eq_right h]
      ring
  have hdiag : Finset.univ.sum (fun d => s d * (if c = d then (1 : ℝ) else 0)) = s c := by
    rw [Finset.sum_eq_single c]
    · simp
    · intro b hb hne
      have hcb : c ≠ b := fun h => hne h.symm
      simp [hcb]
    · intro h
      exact (h (Finset.mem_univ c)).elim
  calc
    (∑ d : Fin N, s d * (if c = d then (N - 1 : ℝ) else 1))
        = ∑ d : Fin N, s d * (1 + ((N - 2 : ℝ)) * (if c = d then (1 : ℝ) else 0)) := by
          apply Finset.sum_congr rfl
          intro d _
          exact hsplit d
    _ = (∑ d : Fin N, s d)
        + ((N - 2 : ℝ)) * (∑ d : Fin N, s d * (if c = d then (1 : ℝ) else 0)) := by
          have h1 : ∀ d : Fin N,
              s d * (1 + ((N - 2 : ℝ)) * (if c = d then (1 : ℝ) else 0))
                = s d + ((N - 2 : ℝ)) * (s d * (if c = d then (1 : ℝ) else 0)) := by
            intro d
            by_cases h : c = d
            · simp [h]
              ring
            · simp [h]
          calc
            (∑ d : Fin N, s d * (1 + ((N - 2 : ℝ)) * (if c = d then (1 : ℝ) else 0)))
                = ∑ d : Fin N,
                    (s d + ((N - 2 : ℝ)) * (s d * (if c = d then (1 : ℝ) else 0))) := by
                  apply Finset.sum_congr rfl
                  intro d _
                  exact h1 d
            _ = (∑ d : Fin N, s d)
                + ∑ d : Fin N, ((N - 2 : ℝ)) * (s d * (if c = d then (1 : ℝ) else 0)) := by
                  rw [Finset.sum_add_distrib]
            _ = (∑ d : Fin N, s d)
                + ((N - 2 : ℝ)) * (∑ d : Fin N, s d * (if c = d then (1 : ℝ) else 0)) := by
                  rw [Finset.mul_sum]
    _ = (∑ d : Fin N, s d) + ((N - 2 : ℝ)) * s c := by rw [hdiag]

/-- For a zero-sum ground potential and `N` at least three, its lifted squared norm is its
original squared norm times the difference between `N` and two. -/
lemma pairPotentialRaw_sq (hN : 3 ≤ N) (s : Fin N → ℝ) (hzero : pairGroundSum s = 0) :
    (∑ S : PairVertex N, (pairPotentialRaw s S)^2)
      = ((N - 2 : ℝ)) * (∑ c : Fin N, (s c)^2) := by
  have h2 : 2 ≤ N := by omega
  have hzerop : Finset.univ.sum s = 0 := hzero
  have hinner (c : Fin N) :
      Finset.univ.sum (fun S => pairStarIndicator c S * pairPotentialRaw s S)
        = Finset.univ.sum (fun d => s d
          * Finset.univ.sum (fun S => pairStarIndicator c S * pairStarIndicator d S)) := by
    unfold pairPotentialRaw
    calc
      (∑ S : PairVertex N,
          pairStarIndicator c S * Finset.univ.sum (fun d => s d * pairStarIndicator d S))
          = ∑ S : PairVertex N, Finset.univ.sum (fun d =>
              pairStarIndicator c S * (s d * pairStarIndicator d S)) := by
            apply Finset.sum_congr rfl
            intro S _
            rw [Finset.mul_sum]
      _ = Finset.univ.sum (fun d => Finset.univ.sum (fun S =>
              pairStarIndicator c S * (s d * pairStarIndicator d S))) := by
            exact Finset.sum_comm' (s := (Finset.univ : Finset (PairVertex N)))
              (t := fun _ => (Finset.univ : Finset (Fin N)))
              (t' := (Finset.univ : Finset (Fin N)))
              (s' := fun _ => (Finset.univ : Finset (PairVertex N))) (fun _ _ => by simp)
      _ = Finset.univ.sum (fun d => s d
          * Finset.univ.sum (fun S => pairStarIndicator c S * pairStarIndicator d S)) := by
            apply Finset.sum_congr rfl
            intro d _
            calc
              Finset.univ.sum (fun S =>
                  pairStarIndicator c S * (s d * pairStarIndicator d S))
                  = Finset.univ.sum (fun S =>
                      s d * (pairStarIndicator c S * pairStarIndicator d S)) := by
                    apply Finset.sum_congr rfl
                    intro S _
                    ring
              _ = s d * Finset.univ.sum (fun S =>
                  pairStarIndicator c S * pairStarIndicator d S) := by
                    rw [Finset.mul_sum]
  calc
    (∑ S : PairVertex N, (pairPotentialRaw s S)^2)
        = ∑ S : PairVertex N, Finset.univ.sum (fun c => s c * pairStarIndicator c S)
            * pairPotentialRaw s S := by
          apply Finset.sum_congr rfl
          intro S _
          have hsq : (pairPotentialRaw s S)^2
              = Finset.univ.sum (fun c => s c * pairStarIndicator c S) * pairPotentialRaw s S := by
            unfold pairPotentialRaw
            ring
          exact hsq
    _ = Finset.univ.sum (fun c => s c
          * Finset.univ.sum (fun S => pairStarIndicator c S * pairPotentialRaw s S)) := by
        calc
          (∑ S : PairVertex N, Finset.univ.sum (fun c => s c * pairStarIndicator c S)
              * pairPotentialRaw s S)
              = ∑ S : PairVertex N, Finset.univ.sum (fun c =>
                  (s c * pairStarIndicator c S) * pairPotentialRaw s S) := by
                apply Finset.sum_congr rfl
                intro S _
                rw [Finset.sum_mul]
          _ = Finset.univ.sum (fun c => Finset.univ.sum (fun S =>
                  (s c * pairStarIndicator c S) * pairPotentialRaw s S)) := by
                exact Finset.sum_comm' (s := (Finset.univ : Finset (PairVertex N)))
                  (t := fun _ => (Finset.univ : Finset (Fin N)))
                  (t' := (Finset.univ : Finset (Fin N)))
                  (s' := fun _ => (Finset.univ : Finset (PairVertex N))) (fun _ _ => by simp)
          _ = Finset.univ.sum (fun c => s c
                * Finset.univ.sum (fun S => pairStarIndicator c S * pairPotentialRaw s S)) := by
            apply Finset.sum_congr rfl
            intro c _
            calc
              Finset.univ.sum (fun S => (s c * pairStarIndicator c S) * pairPotentialRaw s S)
                  = Finset.univ.sum (fun S =>
                      s c * (pairStarIndicator c S * pairPotentialRaw s S)) := by
                    apply Finset.sum_congr rfl
                    intro S _
                    ring
              _ = s c * Finset.univ.sum (fun S =>
                  pairStarIndicator c S * pairPotentialRaw s S) := by
                    rw [Finset.mul_sum]
    _ = Finset.univ.sum (fun c => s c * Finset.univ.sum (fun d => s d
          * Finset.univ.sum (fun S => pairStarIndicator c S * pairStarIndicator d S))) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [hinner c]
    _ = Finset.univ.sum (fun c => s c * Finset.univ.sum (fun d => s d
          * (if c = d then (N - 1 : ℝ) else 1))) := by
        apply Finset.sum_congr rfl
        intro c _
        have hgram : Finset.univ.sum (fun d => s d
              * Finset.univ.sum (fun S => pairStarIndicator c S * pairStarIndicator d S))
            = Finset.univ.sum (fun d => s d * (if c = d then (N - 1 : ℝ) else 1)) := by
          apply Finset.sum_congr rfl
          intro d _
          rw [pairStarIndicator_gram h2 c d]
        rw [hgram]
    _ = Finset.univ.sum (fun c => s c
          * (Finset.univ.sum (fun d => s d) + ((N - 2 : ℝ)) * s c)) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [sum_potential_gram]
    _ = pairGroundSum s * pairGroundSum s
        + ((N - 2 : ℝ)) * (∑ c : Fin N, (s c)^2) := by
        calc
          Finset.univ.sum (fun c => s c
              * (Finset.univ.sum (fun d => s d) + ((N - 2 : ℝ)) * s c))
              = Finset.univ.sum (fun c => s c * Finset.univ.sum (fun d => s d))
                + Finset.univ.sum (fun c => s c * (((N - 2 : ℝ)) * s c)) := by
                  have hdist : Finset.univ.sum (fun c => s c
                      * (Finset.univ.sum (fun d => s d) + ((N - 2 : ℝ)) * s c))
                      = Finset.univ.sum (fun c => s c * Finset.univ.sum (fun d => s d))
                        + Finset.univ.sum (fun c => s c * (((N - 2 : ℝ)) * s c)) := by
                    have hstep : ∀ c : Fin N,
                        s c * (Finset.univ.sum (fun d => s d) + ((N - 2 : ℝ)) * s c)
                          = s c * Finset.univ.sum (fun d => s d)
                            + s c * (((N - 2 : ℝ)) * s c) := by
                      intro c
                      ring
                    have hsum : Finset.univ.sum (fun c => s c
                          * (Finset.univ.sum (fun d => s d) + ((N - 2 : ℝ)) * s c))
                        = Finset.univ.sum (fun c => (s c * Finset.univ.sum (fun d => s d)
                          + s c * (((N - 2 : ℝ)) * s c))) := by
                      apply Finset.sum_congr rfl
                      intro c _
                      exact hstep c
                    rw [hsum, Finset.sum_add_distrib]
                  exact hdist
          _ = pairGroundSum s * pairGroundSum s
                + ((N - 2 : ℝ)) * (∑ c : Fin N, (s c)^2) := by
                  have h1 : Finset.univ.sum (fun c => s c * Finset.univ.sum (fun d => s d))
                      = pairGroundSum s * pairGroundSum s := by
                    calc
                      Finset.univ.sum (fun c => s c * Finset.univ.sum (fun d => s d))
                          = Finset.univ.sum (fun c => Finset.univ.sum (fun d => s d) * s c) := by
                            apply Finset.sum_congr rfl
                            intro c _
                            ring
                      _ = Finset.univ.sum (fun d => s d) * Finset.univ.sum (fun c => s c) := by
                            rw [Finset.mul_sum]
                      _ = pairGroundSum s * pairGroundSum s := by
                            simp only [pairGroundSum]
                  have h2' : Finset.univ.sum (fun c => s c * (((N - 2 : ℝ)) * s c))
                      = ((N - 2 : ℝ)) * (∑ c : Fin N, (s c)^2) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro c _
                    ring
                  rw [h1, h2']
    _ = ((N - 2 : ℝ)) * (∑ c : Fin N, (s c)^2) := by
        simp only [pairGroundSum, hzerop]
        ring

/-- The inner product with a raw pair potential equals the ground potential paired with the
corresponding star sums. -/
lemma pairPotentialRaw_inner (f : PairVertex N → ℝ) (s : Fin N → ℝ) :
    (∑ S : PairVertex N, f S * pairPotentialRaw s S)
      = ∑ c : Fin N, s c * (∑ S : PairVertex N, (if c ∈ S.1 then f S else 0)) := by
  unfold pairPotentialRaw
  calc
    (∑ S : PairVertex N, f S * Finset.univ.sum (fun c => s c * pairStarIndicator c S))
        = ∑ S : PairVertex N, Finset.univ.sum (fun c => f S * (s c * pairStarIndicator c S)) := by
          apply Finset.sum_congr rfl
          intro S _
          rw [Finset.mul_sum]
    _ = Finset.univ.sum (fun c => Finset.univ.sum (fun S =>
            f S * (s c * pairStarIndicator c S))) := by
          exact Finset.sum_comm' (s := (Finset.univ : Finset (PairVertex N)))
            (t := fun _ => (Finset.univ : Finset (Fin N)))
            (t' := (Finset.univ : Finset (Fin N)))
            (s' := fun _ => (Finset.univ : Finset (PairVertex N))) (fun _ _ => by simp)
    _ = Finset.univ.sum (fun c => s c
          * Finset.univ.sum (fun S => f S * pairStarIndicator c S)) := by
          apply Finset.sum_congr rfl
          intro c _
          calc
            Finset.univ.sum (fun S => f S * (s c * pairStarIndicator c S))
                = Finset.univ.sum (fun S => s c * (f S * pairStarIndicator c S)) := by
                  apply Finset.sum_congr rfl
                  intro S _
                  ring
            _ = s c * Finset.univ.sum (fun S => f S * pairStarIndicator c S) := by
                  rw [Finset.mul_sum]
    _ = ∑ c : Fin N, s c * (∑ S : PairVertex N, (if c ∈ S.1 then f S else 0)) := by
          apply Finset.sum_congr rfl
          intro c _
          have hconv : Finset.univ.sum (fun S => f S * pairStarIndicator c S)
              = Finset.univ.sum (fun S => (if c ∈ S.1 then f S else 0)) := by
            apply Finset.sum_congr rfl
            intro S _
            unfold pairStarIndicator
            split <;> ring
          rw [hconv]

/-- Summing a function over a pair equals summing its product with the pair's star indicators
over all ground vertices. -/
lemma pairStar_sum_eq_indicator (hN : 2 ≤ N) (S : PairVertex N) (s : Fin N → ℝ) :
    Finset.sum S.1 (fun c => s c)
      = Finset.univ.sum (fun c => s c * pairStarIndicator c S) := by
  have hfilter : ((Finset.univ : Finset (Fin N)).filter (fun c => c ∈ S.1)) = S.1 := by
    ext c
    constructor
    · intro h
      exact (Finset.mem_filter.mp h).2
    · intro h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, h⟩
  calc
    Finset.sum S.1 (fun c => s c)
        = ∑ c ∈ ((Finset.univ : Finset (Fin N)).filter (fun c => c ∈ S.1)), s c := by
          rw [hfilter]
    _ = ∑ c ∈ (Finset.univ : Finset (Fin N)), (if c ∈ S.1 then s c else 0) := by
          rw [Finset.sum_filter]
    _ = Finset.univ.sum (fun c => s c * pairStarIndicator c S) := by
          apply Finset.sum_congr rfl
          intro c _
          unfold pairStarIndicator
          by_cases hc : c ∈ S.1 <;> simp [hc]

/-- The outside-element part of a star sum is the full star sum minus the original pair value. -/
lemma pairStar_split (hN : 2 ≤ N) (S : PairVertex N) (f : PairVertex N → ℝ)
    (c : Fin N) (hc : c ∈ S.1) :
    (∑ w ∈ (Finset.univ : Finset (Fin N)) \ S.1, f (pairAtTotal hN c w))
      = pairStar hN f c - f S := by
  obtain ⟨c', hc', hS⟩ := exists_insert_of_card_two S.2 hc
  have hspan : pairAtTotal hN c c' = S := by
    apply Subtype.ext
    rw [pairAtTotal_val hN c c' (Ne.symm hc')]
    rw [hS]
  have hwhole : (∑ w ∈ (Finset.univ : Finset (Fin N)), f (pairAtTotal hN c w))
      = pairStar hN f c + f (pairAtTotal hN c c) := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin N))
      (fun w => f (pairAtTotal hN c w)) (Finset.mem_univ c)
    rw [← h]
    unfold pairStar
    rfl
  have htwo : (∑ w ∈ S.1, f (pairAtTotal hN c w))
      = f S + f (pairAtTotal hN c c) := by
    rw [hS]
    calc
      (∑ w ∈ insert c ({c'} : Finset (Fin N)), f (pairAtTotal hN c w))
          = f (pairAtTotal hN c c)
            + (∑ w ∈ ({c'} : Finset (Fin N)), f (pairAtTotal hN c w)) := by
              rw [Finset.sum_insert (by rw [Finset.mem_singleton]; exact Ne.symm hc')]
      _ = f (pairAtTotal hN c c) + f (pairAtTotal hN c c') := by
              simp
      _ = f S + f (pairAtTotal hN c c) := by
              rw [hspan]
              ring
  have hsdiff : (∑ w ∈ (Finset.univ : Finset (Fin N)) \ S.1, f (pairAtTotal hN c w))
      + (∑ w ∈ S.1, f (pairAtTotal hN c w))
      = ∑ w ∈ (Finset.univ : Finset (Fin N)), f (pairAtTotal hN c w) :=
    Finset.sum_sdiff (Finset.subset_univ _)
  have hfinal : (∑ w ∈ (Finset.univ : Finset (Fin N)) \ S.1, f (pairAtTotal hN c w))
      = pairStar hN f c - f S := by
    have hstep : (∑ w ∈ (Finset.univ : Finset (Fin N)) \ S.1, f (pairAtTotal hN c w))
        + (∑ w ∈ S.1, f (pairAtTotal hN c w))
        = pairStar hN f c + f (pairAtTotal hN c c) := by
      rw [hsdiff, hwhole]
    calc
      (∑ w ∈ (Finset.univ : Finset (Fin N)) \ S.1, f (pairAtTotal hN c w))
          = (pairStar hN f c + f (pairAtTotal hN c c))
            - (∑ w ∈ S.1, f (pairAtTotal hN c w)) := by
              linarith
      _ = (pairStar hN f c + f (pairAtTotal hN c c))
            - (f S + f (pairAtTotal hN c c)) := by
              rw [htwo]
      _ = pairStar hN f c - f S := by
              ring
  exact hfinal

/-- The sum of a function over pair graph neighbors equals the incident star sums minus twice
the original value. -/
lemma pairNeighbours_sum_star (hN : 2 ≤ N) (S : PairVertex N) (f : PairVertex N → ℝ) :
    (∑ y, (if (pairGraph N).Adj S y then f y else 0))
      = Finset.univ.sum (fun c => pairStar hN f c * pairStarIndicator c S) - 2 * f S := by
  have hfilter : (∑ y : PairVertex N, (if (pairGraph N).Adj S y then f y else 0))
      = (∑ y ∈ pairNeighbours N S, f y) := by
    have h0 : (∑ y : PairVertex N, (if (pairGraph N).Adj S y then f y else 0))
        = ∑ y ∈ (Finset.univ : Finset (PairVertex N)),
            (if (pairGraph N).Adj S y then f y else 0) := by rfl
    have h1 : ∑ y ∈ (Finset.univ : Finset (PairVertex N)),
            (if (pairGraph N).Adj S y then f y else 0)
        = (∑ y ∈ pairNeighbours N S, f y) := by
      rw [← Finset.sum_filter]
      rfl
    rw [h0, h1]
  rw [hfilter, pairNeighbours_sum hN S f]
  calc
    Finset.sum S.1 (fun c => Finset.sum ((Finset.univ : Finset (Fin N)) \ S.1)
        (fun w => f (pairAtTotal hN c w)))
        = Finset.sum S.1 (fun c => pairStar hN f c - f S) := by
          apply Finset.sum_congr rfl
          intro c hc
          exact pairStar_split hN S f c hc
    _ = Finset.univ.sum (fun c => pairStar hN f c * pairStarIndicator c S)
        - Finset.sum S.1 (fun _ => f S) := by
          have hid : Finset.sum S.1 (fun c => pairStar hN f c)
              = Finset.univ.sum (fun c => pairStar hN f c * pairStarIndicator c S) :=
            pairStar_sum_eq_indicator hN S (pairStar hN f)
          calc
            (∑ c ∈ S.1, (pairStar hN f c - f S))
                = Finset.sum S.1 (fun c => pairStar hN f c)
                    - Finset.sum S.1 (fun _ => f S) := by
                      rw [Finset.sum_sub_distrib]
            _ = Finset.univ.sum (fun c => pairStar hN f c * pairStarIndicator c S)
                    - Finset.sum S.1 (fun _ => f S) := by
                      rw [hid]
    _ = Finset.univ.sum (fun c => pairStar hN f c * pairStarIndicator c S)
        - 2 * f S := by
          have hcard' : (S.1.card : ℝ) = 2 := by exact_mod_cast S.2
          have hsum : Finset.sum S.1 (fun _ => f S) = (S.1.card : ℝ) * f S := by
            have hone : Finset.sum S.1 (fun _ => (1 : ℝ)) = (S.1.card : ℝ) := by
              exact_mod_cast (Finset.card_eq_sum_ones S.1).symm
            calc
              Finset.sum S.1 (fun _ => f S)
                  = Finset.sum S.1 (fun _ => (1 : ℝ) * f S) := by
                      apply Finset.sum_congr rfl
                      intro c _
                      ring
              _ = Finset.sum S.1 (fun _ => (1 : ℝ)) * f S := by
                      rw [Finset.sum_mul]
              _ = (S.1.card : ℝ) * f S := by
                      rw [hone]
          rw [hsum, hcard']

/-- For `N` at least two, casting twice the natural difference of `N` and two agrees with real
subtraction. -/
lemma pairCast_degree (hN : 2 ≤ N) :
    ((2 * (N - 2) : ℕ) : ℝ) = 2 * ((N : ℝ) - 2) := by
  rw [Nat.cast_mul]
  have h1 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have h2 : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [h1, h2]

/-- The pair graph adjacency quadratic form is the sum of squared star sums minus twice the sum
of squared values. -/
lemma pairGraph_adj_form (hN : 2 ≤ N) (f : PairVertex N → ℝ) :
    (∑ x, ∑ y, (if (pairGraph N).Adj x y then f x * f y else 0))
      = (∑ c : Fin N, (pairStar hN f c)^2) - 2 * (∑ S : PairVertex N, (f S)^2) := by
  have hsplit : ∀ x : PairVertex N,
      (∑ y, (if (pairGraph N).Adj x y then f x * f y else 0))
        = f x * (∑ y, (if (pairGraph N).Adj x y then f y else 0)) := by
    intro x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> ring
  have hsplit2 : ∀ x : PairVertex N,
      f x * (∑ y, (if (pairGraph N).Adj x y then f y else 0))
        = f x * (∑ c : Fin N, pairStar hN f c * pairStarIndicator c x) - 2 * (f x)^2 := by
    intro x
    have h := pairNeighbours_sum_star hN x f
    rw [h]
    ring
  have hind : ∀ c : Fin N,
      (∑ x : PairVertex N, pairStarIndicator c x * f x)
        = (∑ x : PairVertex N, (if c ∈ x.1 then f x else 0)) := by
    intro c
    apply Finset.sum_congr rfl
    intro x _
    unfold pairStarIndicator
    split <;> ring
  have hstar2 : (∑ x : PairVertex N,
        f x * (∑ c : Fin N, pairStar hN f c * pairStarIndicator c x))
      = ∑ c : Fin N, pairStar hN f c * (∑ x : PairVertex N, pairStarIndicator c x * f x) := by
    calc
      (∑ x, f x * (∑ c : Fin N, pairStar hN f c * pairStarIndicator c x))
          = ∑ x, ∑ c : Fin N, (pairStar hN f c * pairStarIndicator c x) * f x := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c _
            ring
      _ = ∑ c : Fin N, ∑ x : PairVertex N, (pairStar hN f c * pairStarIndicator c x) * f x := by
            exact Finset.sum_comm' (s := (Finset.univ : Finset (PairVertex N)))
              (t := fun _ => (Finset.univ : Finset (Fin N)))
              (t' := (Finset.univ : Finset (Fin N)))
              (s' := fun _ => (Finset.univ : Finset (PairVertex N))) (fun _ _ => by simp)
      _ = ∑ c : Fin N, ∑ x : PairVertex N,
            pairStar hN f c * (pairStarIndicator c x * f x) := by
            apply Finset.sum_congr rfl
            intro c _
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = ∑ c : Fin N, pairStar hN f c * (∑ x : PairVertex N, pairStarIndicator c x * f x) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [← Finset.mul_sum]
  have hstar3 : (∑ c : Fin N, pairStar hN f c * (∑ x : PairVertex N, pairStarIndicator c x * f x))
      = (∑ c : Fin N, (pairStar hN f c)^2) := by
    calc
      (∑ c, pairStar hN f c * (∑ x, pairStarIndicator c x * f x))
          = ∑ c, pairStar hN f c * (∑ x, (if c ∈ x.1 then f x else 0)) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [hind c]
      _ = ∑ c, (pairStar hN f c)^2 := by
            apply Finset.sum_congr rfl
            intro c _
            rw [pairStar_eq_vertexSum hN f c]
            ring
  have hstar : (∑ x : PairVertex N,
        f x * (∑ c : Fin N, pairStar hN f c * pairStarIndicator c x))
      = (∑ c : Fin N, (pairStar hN f c)^2) := hstar2.trans hstar3
  have hnorm : (∑ x : PairVertex N, 2 * (f x)^2) = 2 * (∑ S : PairVertex N, (f S)^2) := by
    calc
      (∑ x, 2 * (f x)^2) = 2 * (∑ x, (f x)^2) := by
        rw [Finset.mul_sum]
      _ = 2 * (∑ S : PairVertex N, (f S)^2) := rfl
  calc
    (∑ x, ∑ y, (if (pairGraph N).Adj x y then f x * f y else 0))
        = ∑ x, (f x * (∑ y, (if (pairGraph N).Adj x y then f y else 0))) := by
          apply Finset.sum_congr rfl
          intro x _
          exact hsplit x
    _ = ∑ x, (f x * (∑ c : Fin N, pairStar hN f c * pairStarIndicator c x)
        - 2 * (f x)^2) := by
          apply Finset.sum_congr rfl
          intro x _
          exact hsplit2 x
    _ = (∑ x, f x * (∑ c : Fin N, pairStar hN f c * pairStarIndicator c x))
        - ∑ x, 2 * (f x)^2 := by rw [Finset.sum_sub_distrib]
    _ = (∑ c : Fin N, (pairStar hN f c)^2) - ∑ x, 2 * (f x)^2 := by rw [hstar]
    _ = (∑ c : Fin N, (pairStar hN f c)^2) - 2 * (∑ S : PairVertex N, (f S)^2) := by
      rw [hnorm]

/-- Half the pair graph edge quadratic form is twice the product of the squared norm with the
difference between `N` and one, minus the squared star norm. -/
lemma pairGraph_edgeForm_half (hN : 2 ≤ N) (f : PairVertex N → ℝ) :
    (1 / 2 : ℝ) * (∑ x, ∑ y, (if (pairGraph N).Adj x y then (f x - f y)^2 else 0))
      = 2 * ((N : ℝ) - 1) * (∑ S : PairVertex N, (f S)^2)
        - (∑ c : Fin N, (pairStar hN f c)^2) := by
  have hform := normalizedLaplacian_quadratic_form (pairGraph N) f
  have hform2 := normalizedLaplacian_form_eq (pairGraph N) f
  have hDA : (1 / 2 : ℝ) * (∑ x, ∑ y, (if (pairGraph N).Adj x y then (f x - f y)^2 else 0))
      = (∑ x, degree (pairGraph N) x * (f x)^2)
        - (∑ x, ∑ y, (if (pairGraph N).Adj x y then f x * f y else 0)) := by
    calc
      (1 / 2 : ℝ) * (∑ x, ∑ y, (if (pairGraph N).Adj x y then (f x - f y)^2 else 0))
          = (∑ x, ∑ y, degreeScaled (pairGraph N) f x * normalizedLaplacian (pairGraph N) x y
              * degreeScaled (pairGraph N) f y) := by rw [hform]
      _ = (∑ x, degree (pairGraph N) x * (f x)^2)
          - (∑ x, ∑ y, (if (pairGraph N).Adj x y then f x * f y else 0)) := hform2
  have hdeg : (∑ x, degree (pairGraph N) x * (f x)^2)
      = 2 * ((N : ℝ) - 2) * (∑ S : PairVertex N, (f S)^2) := by
    calc
      (∑ x, degree (pairGraph N) x * (f x)^2)
          = ∑ x, ((2 * (N - 2) : ℕ) : ℝ) * (f x)^2 := by
            apply Finset.sum_congr rfl
            intro x _
            rw [pairGraph_degree x]
      _ = ((2 * (N - 2) : ℕ) : ℝ) * (∑ S : PairVertex N, (f S)^2) := by rw [Finset.mul_sum]
      _ = 2 * ((N : ℝ) - 2) * (∑ S : PairVertex N, (f S)^2) := by rw [pairCast_degree hN]
  have hadj := pairGraph_adj_form hN f
  rw [hDA, hdeg, hadj]
  ring

/-- The pair graph edge quadratic form is four times the product of the squared norm with the
difference between `N` and one, minus twice the squared star norm. -/
lemma pairGraph_edgeForm (hN : 2 ≤ N) (f : PairVertex N → ℝ) :
    (∑ x, ∑ y, (if (pairGraph N).Adj x y then (f x - f y)^2 else 0))
      = 4 * ((N : ℝ) - 1) * (∑ S : PairVertex N, (f S)^2)
        - 2 * (∑ c : Fin N, (pairStar hN f c)^2) := by
  have h := pairGraph_edgeForm_half hN f
  have h2 : (∑ x, ∑ y, (if (pairGraph N).Adj x y then (f x - f y)^2 else 0))
      = 2 * ((1 / 2 : ℝ)
        * (∑ x, ∑ y, (if (pairGraph N).Adj x y then (f x - f y)^2 else 0))) := by
    ring
  rw [h2, h]
  ring

/-- For a zero-sum function and `N` at least three, the squared star norm is at most the squared
norm times the difference between `N` and two. -/
lemma pairStar_sq_le (hN2 : 2 ≤ N) (hN3 : 3 ≤ N) (f : PairVertex N → ℝ)
    (hf : (∑ S : PairVertex N, f S) = 0) :
    (∑ c : Fin N, (pairStar hN2 f c)^2) ≤ ((N : ℝ) - 2) * (∑ S : PairVertex N, (f S)^2) := by
  have hground : pairGroundSum (pairStar hN2 f) = 0 := by
    unfold pairGroundSum
    rw [sum_pairStar_eq_two_mul_sum hN2 f, hf, mul_zero]
  have hinner : (∑ S : PairVertex N, f S * pairPotentialRaw (pairStar hN2 f) S)
      = (∑ c : Fin N, (pairStar hN2 f c)^2) := by
    rw [pairPotentialRaw_inner f (pairStar hN2 f)]
    apply Finset.sum_congr rfl
    intro c _
    rw [pairStar_eq_vertexSum hN2 f c]
    ring
  have hsqψ : (∑ S : PairVertex N, (pairPotentialRaw (pairStar hN2 f) S)^2)
      = ((N : ℝ) - 2) * (∑ c : Fin N, (pairStar hN2 f c)^2) :=
    pairPotentialRaw_sq hN3 (pairStar hN2 f) hground
  have e1 : ∀ S : PairVertex N,
      (((N : ℝ) - 2) * f S - pairPotentialRaw (pairStar hN2 f) S)^2
        = ((N : ℝ) - 2)
            * ((((N : ℝ) - 2) * f S - pairPotentialRaw (pairStar hN2 f) S) * f S)
          - ((((N : ℝ) - 2) * f S - pairPotentialRaw (pairStar hN2 f) S)
              * pairPotentialRaw (pairStar hN2 f) S) := by
    intro S
    ring
  have e2 : ∀ S : PairVertex N,
      ((((N : ℝ) - 2) * f S - pairPotentialRaw (pairStar hN2 f) S) * f S)
        = ((N : ℝ) - 2) * (f S)^2 - (f S * pairPotentialRaw (pairStar hN2 f) S) := by
    intro S
    ring
  have e3 : ∀ S : PairVertex N,
      ((((N : ℝ) - 2) * f S - pairPotentialRaw (pairStar hN2 f) S)
          * pairPotentialRaw (pairStar hN2 f) S)
        = ((N : ℝ) - 2) * (f S * pairPotentialRaw (pairStar hN2 f) S)
          - (pairPotentialRaw (pairStar hN2 f) S)^2 := by
    intro S
    ring
  have e4 : (∑ S : PairVertex N,
        (((N : ℝ) - 2) * f S - pairPotentialRaw (pairStar hN2 f) S)^2)
      = ((N : ℝ) - 2) * (∑ S : PairVertex N,
          ((((N : ℝ) - 2) * f S - pairPotentialRaw (pairStar hN2 f) S) * f S))
        - (∑ S : PairVertex N,
          ((((N : ℝ) - 2) * f S - pairPotentialRaw (pairStar hN2 f) S)
            * pairPotentialRaw (pairStar hN2 f) S)) := by
    rw [Finset.sum_congr rfl (fun S _ => e1 S)]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
  have e5 : (∑ S : PairVertex N,
        ((((N : ℝ) - 2) * f S - pairPotentialRaw (pairStar hN2 f) S) * f S))
      = ((N : ℝ) - 2) * (∑ S : PairVertex N, (f S)^2)
        - (∑ S : PairVertex N, (f S * pairPotentialRaw (pairStar hN2 f) S)) := by
    rw [Finset.sum_congr rfl (fun S _ => e2 S)]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
  have e6 : (∑ S : PairVertex N,
        ((((N : ℝ) - 2) * f S - pairPotentialRaw (pairStar hN2 f) S)
          * pairPotentialRaw (pairStar hN2 f) S))
      = ((N : ℝ) - 2) * (∑ S : PairVertex N,
          (f S * pairPotentialRaw (pairStar hN2 f) S))
        - (∑ S : PairVertex N, (pairPotentialRaw (pairStar hN2 f) S)^2) := by
    rw [Finset.sum_congr rfl (fun S _ => e3 S)]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
  have hmain : (∑ S : PairVertex N,
        (((N : ℝ) - 2) * f S - pairPotentialRaw (pairStar hN2 f) S)^2)
      = ((N : ℝ) - 2) * (((N : ℝ) - 2) * (∑ S : PairVertex N, (f S)^2)
        - (∑ c : Fin N, (pairStar hN2 f c)^2)) := by
    rw [e4, e5, e6, hinner, hsqψ]
    ring
  have hsqle : 0 ≤ ((N : ℝ) - 2) * (((N : ℝ) - 2) * (∑ S : PairVertex N, (f S)^2)
      - (∑ c : Fin N, (pairStar hN2 f c)^2)) := by
    rw [← hmain]
    exact Finset.sum_nonneg fun S _ => sq_nonneg _
  have hpos : 0 < ((N : ℝ) - 2) := by
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  have h1 : (∑ c : Fin N, (pairStar hN2 f c)^2) * ((N : ℝ) - 2)
      ≤ ((N : ℝ) - 2) * ((N : ℝ) - 2) * (∑ S : PairVertex N, (f S)^2) := by
    nlinarith [hsqle]
  exact le_of_mul_le_mul_left (by convert! h1 using 1 <;> ring) hpos

/-- For a zero-sum function and `N` at least three, the pair graph edge quadratic form is at
least twice `N` times the squared norm. -/
lemma pairGraph_edgeForm_lower (hN : 3 ≤ N) (f : PairVertex N → ℝ)
    (hf : (∑ S : PairVertex N, f S) = 0) :
    2 * (N : ℝ) * (∑ S : PairVertex N, (f S)^2)
      ≤ (∑ x, ∑ y, (if (pairGraph N).Adj x y then (f x - f y)^2 else 0)) := by
  have hform := pairGraph_edgeForm (show 2 ≤ N from by omega) f
  have hsq := pairStar_sq_le (show 2 ≤ N from by omega) hN f hf
  rw [hform]
  have hnonnegA : 0 ≤ (∑ c : Fin N, (pairStar (show 2 ≤ N from by omega) f c)^2) :=
    Finset.sum_nonneg fun c _ => sq_nonneg _
  have hnonnegB : 0 ≤ (∑ S : PairVertex N, (f S)^2) :=
    Finset.sum_nonneg fun S _ => sq_nonneg _
  nlinarith [hsq]

/-- The pair graph has positive volume when `N` is at least three. -/
lemma pairGraph_volume_pos (hN : 3 ≤ N) : 0 < volume (pairGraph N) := by
  have h2N : 2 ≤ N := by omega
  have hv : PairVertex N := pairAtTotal h2N (⟨0, by omega⟩) (⟨1, by omega⟩)
  have hge : degree (pairGraph N) hv ≤ ∑ x, degree (pairGraph N) x :=
    Finset.single_le_sum (s := (Finset.univ : Finset (PairVertex N)))
      (f := fun x => degree (pairGraph N) x)
      (fun x _ => degree_nonneg (pairGraph N) x) (Finset.mem_univ hv)
  calc
    0 < 2 * ((N : ℝ) - 2) := by
      have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    _ = degree (pairGraph N) hv := by rw [pairGraph_degree hv, pairCast_degree h2N]
    _ ≤ ∑ x, degree (pairGraph N) x := hge

/-- For `N` at least three, the pair graph satisfies `LazyChainGap` with parameter `N` divided
by four times the difference between `N` and two. -/
lemma pairGraph_lazyChainGap (hN : 3 ≤ N) :
    LazyChainGap (pairGraph N) ((N : ℝ) / (4 * ((N : ℝ) - 2))) := by
  have h2N : 2 ≤ N := by omega
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hdegpos : 0 < 2 * ((N : ℝ) - 2) := by linarith
  have hv : PairVertex N := pairAtTotal h2N (⟨0, by omega⟩) (⟨1, by omega⟩)
  have hvolpos : 0 < volume (pairGraph N) := by
    have hge : degree (pairGraph N) hv ≤ ∑ x, degree (pairGraph N) x :=
      Finset.single_le_sum (s := (Finset.univ : Finset (PairVertex N)))
        (f := fun x => degree (pairGraph N) x)
        (fun x _ => degree_nonneg (pairGraph N) x) (Finset.mem_univ hv)
    calc
      0 < 2 * ((N : ℝ) - 2) := hdegpos
      _ = degree (pairGraph N) hv := by
        rw [pairGraph_degree hv, pairCast_degree h2N]
      _ ≤ ∑ x, degree (pairGraph N) x := hge
  have hvolne : volume (pairGraph N) ≠ 0 := ne_of_gt hvolpos
  have hreg : IsDegreeRegular (pairGraph N) (2 * ((N : ℝ) - 2)) := by
    intro x
    rw [pairGraph_degree x, pairCast_degree h2N]
  have hmean0 : ∀ f : PairVertex N → ℝ, mean (pairGraph N) f = 0 →
      (∑ S : PairVertex N, f S) = 0 := by
    intro f hmean
    have hdmz : degreeMeanZero (pairGraph N) f :=
      (mean_zero_iff_degree_mean_zero (pairGraph N) hvolne f).mp hmean
    unfold degreeMeanZero at hdmz
    have hsum : (∑ x, degree (pairGraph N) x * f x)
        = 2 * ((N : ℝ) - 2) * (∑ S : PairVertex N, f S) := by
      calc
        (∑ x, degree (pairGraph N) x * f x) = ∑ x, 2 * ((N : ℝ) - 2) * f x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hreg x]
        _ = 2 * ((N : ℝ) - 2) * (∑ S : PairVertex N, f S) := by rw [Finset.mul_sum]
    rw [hsum] at hdmz
    have hne : 2 * ((N : ℝ) - 2) ≠ 0 := by positivity
    rcases mul_eq_zero.mp hdmz with h | h
    · exact absurd h hne
    · exact h
  refine lazyChainGap_of_edgeForm (pairGraph N) (d := 2 * ((N : ℝ) - 2))
    (δ := (N : ℝ) / (4 * ((N : ℝ) - 2))) hreg hdegpos hvolne ?_ ?_
  · have hposden : 0 < 4 * ((N : ℝ) - 2) := by
      have hN3' : (3 : ℝ) ≤ N := by exact_mod_cast hN
      have : 0 < ((N : ℝ) - 2) := by linarith
      positivity
    rw [div_le_iff₀ hposden]
    linarith
  · intro f hmean
    have hf0 : (∑ S : PairVertex N, f S) = 0 := hmean0 f hmean
    have hlow := pairGraph_edgeForm_lower hN f hf0
    have hform : 4 * ((N : ℝ) / (4 * ((N : ℝ) - 2))) * (2 * ((N : ℝ) - 2))
        = 2 * (N : ℝ) := by
      have hne : ((N : ℝ) - 2) ≠ 0 := by linarith
      field_simp
    calc
      4 * ((N : ℝ) / (4 * ((N : ℝ) - 2))) * (2 * ((N : ℝ) - 2))
          * (∑ S : PairVertex N, (f S)^2)
          = 2 * (N : ℝ) * (∑ S : PairVertex N, (f S)^2) := by rw [hform]
      _ ≤ (∑ x, ∑ y, (if (pairGraph N).Adj x y then (f x - f y)^2 else 0)) := hlow

/-- The stated pair graph gap parameter is at least one quarter when `N` is at least three. -/
lemma pairGraph_gap_ge_quarter (hN : 3 ≤ N) :
    (1 / 4 : ℝ) ≤ (N : ℝ) / (4 * ((N : ℝ) - 2)) := by
  have hposden : 0 < 4 * ((N : ℝ) - 2) := by
    have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have : 0 < ((N : ℝ) - 2) := by linarith
    positivity
  rw [le_div_iff₀ hposden]
  linarith

section PairNeighbourProgram

variable {N : ℕ}

def pairRowIndexSet (S : PairVertex N) : Finset (Fin N × Fin N) :=
  Finset.product S.1 ((Finset.univ : Finset (Fin N)) \ S.1)

abbrev PairRowIndex (S : PairVertex N) : Type :=
  {x : Fin N × Fin N // x ∈ pairRowIndexSet S}

/-- The row index type has cardinality equal to the pair size times its complement size. -/
lemma pairRowIndex_card (S : PairVertex N) :
    Fintype.card (PairRowIndex S)
      = S.1.card * ((Finset.univ : Finset (Fin N)) \ S.1).card := by
  show Fintype.card (↥(pairRowIndexSet S)) = _
  rw [Fintype.card_coe]
  exact Finset.card_product _ _

def pairRowOracle (S : PairVertex N) (p : PairRowIndex S) : PairVertex N :=
  pairNeighbourOf S p.val.1 p.val.2
    (Finset.mem_product.mp p.property).1
    (Finset.mem_sdiff.mp (Finset.mem_product.mp p.property).2).2

/-- Every output of `pairRowOracle` is adjacent to its input vertex. -/
lemma pairRowOracle_adj (S : PairVertex N) (p : PairRowIndex S) :
    (pairGraph N).Adj S (pairRowOracle S p) :=
  pairNeighbourOf_adj S p.val.1 p.val.2 (Finset.mem_product.mp p.property).1
    (Finset.mem_sdiff.mp (Finset.mem_product.mp p.property).2).2

/-- The pair row oracle never returns its input vertex. -/
lemma pairRowOracle_ne (S : PairVertex N) (p : PairRowIndex S) :
    pairRowOracle S p ≠ S := by
  intro h
  have hadj := pairRowOracle_adj S p
  rw [h] at hadj
  exact (pairGraph N).loopless.irrefl S hadj

/-- The pair row oracle is injective in its row index. -/
lemma pairRowOracle_injective (S : PairVertex N) :
    Function.Injective (pairRowOracle S) := by
  intro p q h
  have hvalp : (pairRowOracle S p).1 = insert (α := Fin N) p.val.1 ({p.val.2} : Finset (Fin N)) :=
    pairNeighbourOf_val S p.val.1 p.val.2 (Finset.mem_product.mp p.property).1
      (Finset.mem_sdiff.mp (Finset.mem_product.mp p.property).2).2
  have hvalq : (pairRowOracle S q).1 = insert (α := Fin N) q.val.1 ({q.val.2} : Finset (Fin N)) :=
    pairNeighbourOf_val S q.val.1 q.val.2 (Finset.mem_product.mp q.property).1
      (Finset.mem_sdiff.mp (Finset.mem_product.mp q.property).2).2
  have hset : (insert (α := Fin N) p.val.1 ({p.val.2} : Finset (Fin N))) = insert (α := Fin N) q.val.1 ({q.val.2} : Finset (Fin N)) := by
    have h1 := congrArg Subtype.val h
    rw [hvalp, hvalq] at h1
    exact h1
  have hp1in : p.val.1 ∈ S.1 := (Finset.mem_product.mp p.property).1
  have hp2out : p.val.2 ∉ S.1 := (Finset.mem_sdiff.mp (Finset.mem_product.mp p.property).2).2
  have hq1in : q.val.1 ∈ S.1 := (Finset.mem_product.mp q.property).1
  have hq2out : q.val.2 ∉ S.1 := (Finset.mem_sdiff.mp (Finset.mem_product.mp q.property).2).2
  have hp1 : p.val.1 ∈ insert (α := Fin N) q.val.1 ({q.val.2} : Finset (Fin N)) := by
    have hmem : p.val.1 ∈ insert (α := Fin N) p.val.1 ({p.val.2} : Finset (Fin N)) := by
      rw [Finset.mem_insert]
      exact Or.inl rfl
    rw [hset] at hmem
    exact hmem
  have hp1' : p.val.1 = q.val.1 ∨ p.val.1 = q.val.2 := by
    rcases Finset.mem_insert.mp hp1 with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  have hp1'' : p.val.1 = q.val.1 := by
    rcases hp1' with h | h
    · exact h
    · exact False.elim (hq2out (h ▸ hp1in))
  have hp2 : p.val.2 ∈ insert (α := Fin N) q.val.1 ({q.val.2} : Finset (Fin N)) := by
    have hmem : p.val.2 ∈ insert (α := Fin N) p.val.1 ({p.val.2} : Finset (Fin N)) := by
      rw [Finset.mem_insert]
      exact Or.inr (Finset.mem_singleton.mpr rfl)
    rw [hset] at hmem
    exact hmem
  have hp2' : p.val.2 = q.val.1 ∨ p.val.2 = q.val.2 := by
    rcases Finset.mem_insert.mp hp2 with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  have hp2'' : p.val.2 = q.val.2 := by
    rcases hp2' with h | h
    · exact False.elim (hp2out (h ▸ hq1in))
    · exact h
  have hprod : p.val = q.val := Prod.ext hp1'' hp2''
  exact Subtype.ext hprod

/-- Every pair row oracle output belongs to the input vertex's neighbor set. -/
lemma pairRowOracle_mem_neighbours (S : PairVertex N) (p : PairRowIndex S) :
    pairRowOracle S p ∈ pairNeighbours N S := by
  unfold pairNeighbours
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact pairRowOracle_adj S p

/-- Every pair neighbor is produced by some row index of `pairRowOracle`. -/
lemma pairRowOracle_surj (S : PairVertex N) (z : PairVertex N)
    (hz : z ∈ pairNeighbours N S) :
    ∃ p : PairRowIndex S, pairRowOracle S p = z := by
  have hadj : (pairGraph N).Adj S z := by
    unfold pairNeighbours at hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact hz
  obtain ⟨c, w, hc, hw, hcw, hzval⟩ := pair_neighbour_split hadj
  have hwout : w ∈ (Finset.univ : Finset (Fin N)) \ S.1 :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩
  let p : PairRowIndex S :=
    ⟨(c, w), Finset.mem_product.mpr ⟨hc, hwout⟩⟩
  refine ⟨p, ?_⟩
  have h1 : (pairRowOracle S p).1 = insert c {w} := pairNeighbourOf_val S c w hc hw
  have h2 : (pairRowOracle S p).val = z.val := by
    rw [hzval]
    exact h1
  exact Subtype.ext h2

/-- Establishes the pair family's degree and neighbor counts, injective and surjective row
enumeration, a gap parameter of at least one quarter, and positive volume. -/
theorem pair_family_neighbour_program (hN : 3 ≤ N) :
    (∀ S : PairVertex N, degree (pairGraph N) S = ((2 * (N - 2) : ℕ) : ℝ)) ∧
    (∀ S : PairVertex N, (pairNeighbours N S).card = ((2 * (N - 2) : ℕ) : ℝ)) ∧
    (∀ S : PairVertex N, Function.Injective (pairRowOracle S)) ∧
    (∀ S z : PairVertex N, z ∈ pairNeighbours N S →
        ∃ p : PairRowIndex S, pairRowOracle S p = z) ∧
    (1 / 4 : ℝ) ≤ (N : ℝ) / (4 * ((N : ℝ) - 2)) ∧
    0 < volume (pairGraph N) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S
    exact pairGraph_degree S
  · intro S
    have h := pairNeighbours_card S
    rw [S.2, pairVertex_outside_card] at h
    exact_mod_cast h
  · intro S
    exact pairRowOracle_injective S
  · intro S z hz
    exact pairRowOracle_surj S z hz
  · exact pairGraph_gap_ge_quarter hN
  · exact pairGraph_volume_pos hN

end PairNeighbourProgram
end Qatlib.Concepts.QuantumGibbs.FormAlgebra
