/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCoreDefs
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteGatePhaseBoundary

/-!
# Correctness of finite MBQC flow search

This module proves that `mbqcFlowDecide` succeeds exactly when `MbqcHasFlow` holds, using
predecessor cardinalities to turn a finite strict order into finite ranks. The causal flow
conditions are those used for deterministic one-way computation [DanosKashefi2006].

It also proves soundness of `mbqcGFlowDecide`, supplies rank witnesses under additional forward
or total-order hypotheses, and constructs causal local Pauli corrections.
`clause6Aux_clause4_branchObligation` names the separate branch-equality proposition; the
correction theorem establishes Pauli membership and causality.

## Main statements

* `clause6_clause3a`: soundness and completeness of the causal flow search.
* `clause6_clause3b_sound`: soundness of the generalized-flow search.
* `clause6Aux_check_of_totalPrec`: a rank witness under the stated total-order hypotheses.
* `clause6_clause4_pauli_causal`: causal local Pauli corrections for a returned flow witness.

## References

* [Danos and Kashefi, 2006][DanosKashefi2006]
* [Browne et al., 2007][BrowneEtAl2007]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false

open Qatlib
open Qatlib
open Matrix
open scoped Classical ComplexOrder

set_option autoImplicit false

open Qatlib.Concepts.ChannelTheory.Stinespring

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

/-- The local correction whose `X` factor is triggered by a true outcome mapped to `u` and whose
`Z` factor is triggered by a true outcome mapped to a neighbor of `u` other than its source. -/
noncomputable def flowCorrection {n : ℕ} (G : MbqcGraph n) (f : Fin n → Option (Fin n))
    (s : Fin n → Bool) (u : Fin n) : Operator 2 :=
  (if ∃ v : Fin n, s v = true ∧ f v = some u then pauliX else (1 : Operator 2)) *
    (if ∃ v w : Fin n, s v = true ∧ f v = some w ∧ u ≠ v ∧ mbqcAdj G w u then pauliZ
      else (1 : Operator 2))

/-- Every `flowCorrection` is one of the four operators specified by `MbqcPauliWire`. -/
theorem flowCorrection_pauliWire {n : ℕ} (G : MbqcGraph n) (f : Fin n → Option (Fin n))
    (s : Fin n → Bool) (u : Fin n) :
    MbqcPauliWire (flowCorrection G f s u) := by
  unfold flowCorrection
  by_cases hx : ∃ v : Fin n, s v = true ∧ f v = some u
  · rw [if_pos hx]
    by_cases hz : ∃ v w : Fin n, s v = true ∧ f v = some w ∧ u ≠ v ∧ mbqcAdj G w u
    · rw [if_pos hz]
      exact Or.inr (Or.inr (Or.inr rfl))
    · rw [if_neg hz, mul_one]
      exact Or.inr (Or.inl rfl)
  · rw [if_neg hx]
    by_cases hz : ∃ v w : Fin n, s v = true ∧ f v = some w ∧ u ≠ v ∧ mbqcAdj G w u
    · rw [if_pos hz, one_mul]
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [if_neg hz, one_mul]
      exact Or.inl rfl

/-- If all correction dependencies satisfy the stated F2 and F3 order conditions,
`flowCorrection` depends only on preceding outcomes. -/
theorem flowCorrection_causal {n : ℕ} (G : MbqcGraph n)
    (f : Fin n → Option (Fin n)) (prec : Fin n → Fin n → Prop)
    (hF2 : ∀ v u : Fin n, f v = some u → prec v u)
    (hF3 : ∀ v w u : Fin n, f v = some w → u ≠ v → mbqcAdj G w u → prec v u) :
    MbqcCausalCorrection prec (flowCorrection G f) := by
  intro s s' u hagree
  unfold flowCorrection
  have hx : (∃ v : Fin n, s v = true ∧ f v = some u) ↔
      (∃ v : Fin n, s' v = true ∧ f v = some u) := by
    constructor
    · intro ⟨v, hv, hf⟩
      refine ⟨v, ?_, hf⟩
      have hprec : prec v u := hF2 v u hf
      rw [← hagree v hprec]
      exact hv
    · intro ⟨v, hv, hf⟩
      refine ⟨v, ?_, hf⟩
      have hprec : prec v u := hF2 v u hf
      rw [hagree v hprec]
      exact hv
  have hz : (∃ v w : Fin n, s v = true ∧ f v = some w ∧ u ≠ v ∧ mbqcAdj G w u) ↔
      (∃ v w : Fin n, s' v = true ∧ f v = some w ∧ u ≠ v ∧ mbqcAdj G w u) := by
    constructor
    · intro ⟨v, w, hv, hf, hne, hadj⟩
      refine ⟨v, w, ?_, hf, hne, hadj⟩
      have hprec : prec v u := hF3 v w u hf hne hadj
      rw [← hagree v hprec]
      exact hv
    · intro ⟨v, w, hv, hf, hne, hadj⟩
      refine ⟨v, w, ?_, hf, hne, hadj⟩
      have hprec : prec v u := hF3 v w u hf hne hadj
      rw [hagree v hprec]
      exact hv
  rw [if_congr hx (by rfl) (by rfl), if_congr hz (by rfl) (by rfl)]

/-- A successful flow check places each non-output vertex strictly before its selected image in
the rank order. -/
theorem flow_F2_of_check {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (f : Fin n → Option (Fin n)) (r : Fin n → Fin n)
    (h : mbqcFlowCheck G I O f r) (v u : Fin n) (hv : v ∉ O) (hf : f v = some u) :
    mbqcRankPrec r v u := by
  obtain ⟨w, hfw, _, _, hprec, _⟩ := h v hv
  rw [hf] at hfw
  cases hfw
  exact hprec

/-- A successful flow check places each non-output vertex strictly before every other neighbor
of its selected image. -/
theorem flow_F3_of_check {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (f : Fin n → Option (Fin n)) (r : Fin n → Fin n)
    (h : mbqcFlowCheck G I O f r) (v w u : Fin n) (hv : v ∉ O) (hf : f v = some w)
    (hne : u ≠ v) (hadj : mbqcAdj G w u) : mbqcRankPrec r v u := by
  obtain ⟨w', hfw, _, _, _, hF3⟩ := h v hv
  rw [hf] at hfw
  cases hfw
  exact hF3 u hadj hne
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Strict comparison of finite ranks defines a strict order on the vertices. -/
private theorem rankPrec_isStrictOrder {n : ℕ} (r : Fin n → Fin n) :
    IsStrictOrder (Fin n) (mbqcRankPrec r) where
  irrefl x h := by
    simp only [mbqcRankPrec] at h
    exact Nat.lt_irrefl _ h
  trans {a b c} h1 h2 := by
    simp only [mbqcRankPrec] at h1 h2
    exact Nat.lt_trans h1 h2

/-- For an irreflexive relation on `Fin n`, every vertex has fewer than `n` predecessors. -/
private theorem predCard_lt {n : ℕ} (prec : Fin n → Fin n → Prop)
    (hirr : ∀ x : Fin n, ¬ prec x x) (v : Fin n) :
    (Finset.univ.filter (fun u => prec u v)).card < n := by
  have hnot : v ∉ Finset.univ.filter (fun u => prec u v) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hirr v
  have hss : (Finset.univ.filter (fun u => prec u v)) ⊂ (Finset.univ : Finset (Fin n)) :=
    Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.filter_subset _ _, fun he => hnot (by rw [he]; exact Finset.mem_univ v)⟩
  have := Finset.card_lt_card hss
  rwa [Finset.card_univ, Fintype.card_fin] at this

/-- The finite rank of a vertex given by the number of its predecessors in an irreflexive
relation. -/
private noncomputable def predRank {n : ℕ} (prec : Fin n → Fin n → Prop)
    (hirr : ∀ x : Fin n, ¬ prec x x) (v : Fin n) : Fin n :=
  ⟨(Finset.univ.filter (fun u => prec u v)).card, predCard_lt prec hirr v⟩

/-- For an irreflexive transitive relation, the predecessor-count rank strictly increases along
every related pair. -/
private theorem predRank_lt {n : ℕ} (prec : Fin n → Fin n → Prop)
    (hirr : ∀ x : Fin n, ¬ prec x x)
    (htrans : ∀ (a b c : Fin n), prec a b → prec b c → prec a c)
    {u v : Fin n} (h : prec u v) :
    mbqcRankPrec (predRank prec hirr) u v := by
  have hsub : (Finset.univ.filter (fun w => prec w u))
      ⊆ (Finset.univ.filter (fun w => prec w v)) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact htrans w u v hw h
  have hmem : u ∈ Finset.univ.filter (fun w => prec w v) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  have hnot : u ∉ Finset.univ.filter (fun w => prec w u) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hirr u
  have hne : (Finset.univ.filter (fun w => prec w u))
      ≠ (Finset.univ.filter (fun w => prec w v)) := by
    intro he
    have := hmem
    rw [← he] at this
    exact hnot this
  have hlt : (Finset.univ.filter (fun w => prec w u)).card
      < (Finset.univ.filter (fun w => prec w v)).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  show (predRank prec hirr u : ℕ) < (predRank prec hirr v)
  simp only [predRank]
  exact hlt

/-- A Boolean list search returns a value exactly when some element of the list satisfies its
predicate. -/
private theorem find_isSome_iff_exists {α : Type} (p : α → Bool) (l : List α) :
    (List.find? p l).isSome = true ↔ ∃ x ∈ l, p x = true := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
    exact ⟨a, List.mem_of_find?_eq_some ha, List.find?_some ha⟩
  · rintro ⟨x, hx, hp⟩
    cases hfind : List.find? p l with
    | none => exact absurd hp (List.find?_eq_none.mp hfind x hx)
    | some a => simp

/-- The finite flow search succeeds exactly when the open graph possesses a causal flow in the
sense of `MbqcHasFlow`. The flow conditions follow [DanosKashefi2006]. -/
theorem clause6_clause3a :
    ∀ (n : ℕ) (G : MbqcGraph n) (I O : Finset (Fin n)),
      (mbqcFlowDecide G I O).isSome = true ↔ MbqcHasFlow G I O := by
  intro n G I O
  have hform :
      mbqcFlowDecide G I O =
        (Fintype.elems (α := (Fin n → Option (Fin n)) × (Fin n → Fin n))).toList.find?
          (fun p => decide (mbqcFlowCheck G I O p.1 p.2)) := rfl
  constructor
  · intro h
    rw [hform, find_isSome_iff_exists] at h
    obtain ⟨p, _, hcheck⟩ := h
    have hflow : mbqcFlowCheck G I O p.1 p.2 := of_decide_eq_true hcheck
    refine ⟨p.1, mbqcRankPrec p.2, (fun u v => mbqcRankPrecDec p.2 u v),
      rankPrec_isStrictOrder p.2, ?_⟩
    intro v hv
    exact hflow v hv
  · intro h
    obtain ⟨f, prec, _, hstrict, hcond⟩ := h
    have hirr : ∀ x : Fin n, ¬ prec x x := fun x => hstrict.irrefl x
    have htrans : ∀ (a b c : Fin n), prec a b → prec b c → prec a c :=
      fun a b c h1 h2 => @IsTrans.trans _ _ hstrict.toIsTrans a b c h1 h2
    have hcheck : mbqcFlowCheck G I O f (predRank prec hirr) := by
      intro v hv
      obtain ⟨w, hfw, hadj, hnI, hprec, hfuture⟩ := hcond v hv
      refine ⟨w, hfw, hadj, hnI, ?_, ?_⟩
      · exact predRank_lt prec hirr htrans hprec
      · intro k hk hkv
        exact predRank_lt prec hirr htrans (hfuture k hk hkv)
    have hdec : decide (mbqcFlowCheck G I O f (predRank prec hirr)) = true :=
      decide_eq_true hcheck
    have hp : ((f, predRank prec hirr) :
        (Fin n → Option (Fin n)) × (Fin n → Fin n)) ∈
          (Fintype.elems (α := (Fin n → Option (Fin n)) × (Fin n → Fin n))).toList :=
      Finset.mem_toList.mpr (Fintype.complete _)
    rw [hform, find_isSome_iff_exists]
    exact ⟨(f, predRank prec hirr), hp, hdec⟩

/-- The propositional plane condition holds exactly when its Boolean form evaluates to true on
the decisions of the two propositions. -/
private theorem gflow_plane_iff_gen (p : MbqcPlane) {mem odd : Prop}
    [Decidable mem] [Decidable odd] :
    mbqcGFlowPlaneCond p mem odd ↔ mbqcGFlowPlaneCondB p (decide mem) (decide odd) = true := by
  cases p <;> simp [mbqcGFlowPlaneCond, mbqcGFlowPlaneCondB]

/-- At a vertex, the propositional generalized-flow plane condition agrees with its Boolean test
for correction-set and odd-neighborhood membership. -/
private theorem gflow_plane_iff {n : ℕ} (lam : Fin n → MbqcPlane)
    (g : Fin n → Finset (Fin n)) (G : MbqcGraph n) (v : Fin n) :
    mbqcGFlowPlaneCond (lam v) (v ∈ g v) (v ∈ mbqcOdd G (g v))
      ↔ mbqcGFlowPlaneCondB (lam v) (decide (v ∈ g v)) (decide (v ∈ mbqcOdd G (g v)))
        = true :=
  gflow_plane_iff_gen (lam v)

/-- If the finite generalized-flow search succeeds, the graph satisfies `MbqcHasGFlow` for the
given input set, output set, and plane assignment; compare [BrowneEtAl2007]. -/
theorem clause6_clause3b_sound :
    ∀ (n : ℕ) (G : MbqcGraph n) (I O : Finset (Fin n)) (lam : Fin n → MbqcPlane),
      (mbqcGFlowDecide G I O lam).isSome = true → MbqcHasGFlow G I O lam := by
  intro n G I O lam
  have hform :
      mbqcGFlowDecide G I O lam =
        (Fintype.elems (α := (Fin n → Finset (Fin n)) × (Fin n → Fin n))).toList.find?
          (fun p => decide (mbqcGFlowCheck G I O lam p.1 p.2)) := rfl
  intro h
  rw [hform, find_isSome_iff_exists] at h
  obtain ⟨p, _, hcheck⟩ := h
  have hgf : mbqcGFlowCheck G I O lam p.1 p.2 := of_decide_eq_true hcheck
  refine ⟨p.1, mbqcRankPrec p.2, (fun u v => mbqcRankPrecDec p.2 u v), ?_, rankPrec_isStrictOrder p.2,
    ?_, ?_, ?_⟩
  · intro v hv u hu
    exact (hgf v hv).1 u hu
  · intro v hv u hu hne
    exact (hgf v hv).2.1 u hu hne
  · intro v hv u hprec
    exact (hgf v hv).2.2.1 u hprec
  · intro v hv
    exact (gflow_plane_iff lam p.1 G v).mpr (hgf v hv).2.2.2

set_option autoImplicit false
set_option maxHeartbeats 800000
open Qatlib
open scoped Classical
set_option maxHeartbeats 400000

/-- For an irreflexive relation on `Fin n`, the predecessor set of any vertex has cardinality
less than `n`. -/
theorem clause6Aux_predCard_lt {n : ℕ} (prec : Fin n → Fin n → Prop)
    (hirr : ∀ x : Fin n, ¬ prec x x) (v : Fin n) :
    (Finset.univ.filter (fun u => prec u v)).card < n := by
  have hnot : v ∉ Finset.univ.filter (fun u => prec u v) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hirr v
  have hss : (Finset.univ.filter (fun u => prec u v)) ⊂ (Finset.univ : Finset (Fin n)) :=
    Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.filter_subset _ _, fun he => hnot (by rw [he]; exact Finset.mem_univ v)⟩
  have := Finset.card_lt_card hss
  rwa [Finset.card_univ, Fintype.card_fin] at this

/-- The finite predecessor-count rank associated with an irreflexive vertex relation. -/
noncomputable def clause6Aux_predRank {n : ℕ} (prec : Fin n → Fin n → Prop)
    (hirr : ∀ x : Fin n, ¬ prec x x) (v : Fin n) : Fin n :=
  ⟨(Finset.univ.filter (fun u => prec u v)).card, clause6Aux_predCard_lt prec hirr v⟩

/-- For an irreflexive transitive relation, `clause6Aux_predRank` strictly increases along every
related pair. -/
theorem clause6Aux_predRank_lt {n : ℕ} (prec : Fin n → Fin n → Prop)
    (hirr : ∀ x : Fin n, ¬ prec x x)
    (htrans : ∀ (a b c : Fin n), prec a b → prec b c → prec a c)
    {u v : Fin n} (h : prec u v) :
    mbqcRankPrec (clause6Aux_predRank prec hirr) u v := by
  have hsub : (Finset.univ.filter (fun w => prec w u))
      ⊆ (Finset.univ.filter (fun w => prec w v)) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact htrans w u v hw h
  have hmem : u ∈ Finset.univ.filter (fun w => prec w v) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  have hnot : u ∉ Finset.univ.filter (fun w => prec w u) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hirr u
  have hne : (Finset.univ.filter (fun w => prec w u))
      ≠ (Finset.univ.filter (fun w => prec w v)) := by
    intro he
    have := hmem
    rw [← he] at this
    exact hnot this
  have hlt : (Finset.univ.filter (fun w => prec w u)).card
      < (Finset.univ.filter (fun w => prec w v)).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  show (clause6Aux_predRank prec hirr u : ℕ) < (clause6Aux_predRank prec hirr v)
  simp only [clause6Aux_predRank]
  exact hlt

/-- A propositional generalized-flow plane condition implies that its Boolean test evaluates to
true. -/
theorem clause6Aux_planeCond_to_planeCondB {p : MbqcPlane} {mem odd : Prop} [Decidable mem]
    [Decidable odd] (h : mbqcGFlowPlaneCond p mem odd) :
    mbqcGFlowPlaneCondB p (decide mem) (decide odd) = true := by
  cases p <;> simp only [mbqcGFlowPlaneCond, mbqcGFlowPlaneCondB] at h ⊢
  · obtain ⟨h1, h2⟩ := h
    rw [decide_eq_false h1, decide_eq_true h2]
    decide
  · obtain ⟨h1, h2⟩ := h
    rw [decide_eq_true h1, decide_eq_true h2]
    decide
  · obtain ⟨h1, h2⟩ := h
    rw [decide_eq_true h1, decide_eq_false h2]
    decide

/-- Correction sets and an irreflexive transitive relation satisfying input exclusion, forward
correction dependencies, forward odd-neighborhood dependencies, and plane conditions pass
the generalized-flow check with predecessor-count ranks. -/
theorem clause6Aux_check_predRank_of_forwardOdd {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (lam : Fin n → MbqcPlane) (g : Fin n → Finset (Fin n)) (prec : Fin n → Fin n → Prop)
    (hirr : ∀ x : Fin n, ¬ prec x x)
    (htrans : ∀ (a b c : Fin n), prec a b → prec b c → prec a c)
    (hG0 : ∀ v : Fin n, v ∉ O → ∀ u : Fin n, u ∈ g v → u ∉ I)
    (hG1 : ∀ v : Fin n, v ∉ O → ∀ u : Fin n, u ∈ g v → u ≠ v → prec v u)
    (hFwd : ∀ v : Fin n, v ∉ O → ∀ u : Fin n, u ∈ mbqcOdd G (g v) → u = v ∨ prec v u)
    (hC : ∀ v : Fin n, v ∉ O →
      mbqcGFlowPlaneCond (lam v) (v ∈ g v) (v ∈ mbqcOdd G (g v))) :
    mbqcGFlowCheck G I O lam g (clause6Aux_predRank prec hirr) := by
  intro v hv
  refine ⟨hG0 v hv, ?_, ?_, ?_⟩
  · intro u hu hne
    exact clause6Aux_predRank_lt prec hirr htrans (hG1 v hv u hu hne)
  · intro u hprec hu
    rcases hFwd v hv u hu with heq | hup
    · subst heq
      simp only [mbqcRankPrec] at hprec
      exact absurd hprec (Nat.lt_irrefl _)
    · have hup' := clause6Aux_predRank_lt prec hirr htrans hup
      simp only [mbqcRankPrec] at hprec hup'
      omega
  · exact clause6Aux_planeCond_to_planeCondB (hC v hv)

/-- If distinct vertices are comparable and earlier vertices are excluded from the odd
neighborhood, each odd-neighborhood vertex is either the measured vertex itself or a later
vertex. -/
theorem clause6Aux_forwardOdd_of_totalPrec {n : ℕ} (G : MbqcGraph n) (O : Finset (Fin n))
    (g : Fin n → Finset (Fin n)) (prec : Fin n → Fin n → Prop)
    (htot : ∀ u v : Fin n, u ≠ v → prec u v ∨ prec v u)
    (hG2 : ∀ v : Fin n, v ∉ O → ∀ u : Fin n, prec u v → u ∉ mbqcOdd G (g v))
    {v : Fin n} (hv : v ∉ O) {u : Fin n} (hu : u ∈ mbqcOdd G (g v)) :
    u = v ∨ prec v u := by
  by_cases heq : u = v
  · exact Or.inl heq
  · rcases htot u v heq with hdown | hup
    · exact (hG2 v hv u hdown hu).elim
    · exact Or.inr hup

/-- Under an irreflexive transitive relation comparing distinct vertices, the stated input,
correction, odd-neighborhood, and plane conditions yield a rank assignment passing the
generalized-flow check. -/
theorem clause6Aux_check_of_totalPrec {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (lam : Fin n → MbqcPlane) (g : Fin n → Finset (Fin n)) (prec : Fin n → Fin n → Prop)
    (hirr : ∀ x : Fin n, ¬ prec x x)
    (htrans : ∀ (a b c : Fin n), prec a b → prec b c → prec a c)
    (htot : ∀ u v : Fin n, u ≠ v → prec u v ∨ prec v u)
    (hG0 : ∀ v : Fin n, v ∉ O → ∀ u : Fin n, u ∈ g v → u ∉ I)
    (hG1 : ∀ v : Fin n, v ∉ O → ∀ u : Fin n, u ∈ g v → u ≠ v → prec v u)
    (hG2 : ∀ v : Fin n, v ∉ O → ∀ u : Fin n, prec u v → u ∉ mbqcOdd G (g v))
    (hC : ∀ v : Fin n, v ∉ O →
      mbqcGFlowPlaneCond (lam v) (v ∈ g v) (v ∈ mbqcOdd G (g v))) :
    ∃ r : Fin n → Fin n, mbqcGFlowCheck G I O lam g r :=
  ⟨clause6Aux_predRank prec hirr, clause6Aux_check_predRank_of_forwardOdd G I O lam g prec hirr htrans
    hG0 hG1 (fun _ hv _ hu => clause6Aux_forwardOdd_of_totalPrec G O g prec htot hG2 hv hu) hC⟩

/-- Replaces the flow map by `none` on output vertices and preserves it on every other vertex. -/
def clause6Aux_outMaskedFlow {n : ℕ} (f : Fin n → Option (Fin n)) (O : Finset (Fin n)) :
    Fin n → Option (Fin n) :=
  fun v => if v ∈ O then none else f v

/-- Whenever the finite flow search returns a witness, there exists a correction family
consisting of local Pauli operators and depending only on outcomes earlier in the returned
rank order. -/
theorem clause6_clause4_pauli_causal :
    ∀ (n : ℕ) (G : MbqcGraph n) (I O : Finset (Fin n)) (_a : Fin n → ℝ),
      match mbqcFlowDecide G I O with
      | some p =>
          ∃ corr : (Fin n → Bool) → Fin n → Operator 2,
            (∀ s : Fin n → Bool, ∀ v : Fin n, MbqcPauliWire (corr s v)) ∧
            MbqcCausalCorrection (mbqcRankPrec p.2) corr
      | none => True := by
  intro n G I O _
  cases hdec : mbqcFlowDecide G I O with
  | none => trivial
  | some p =>
    obtain ⟨f, r⟩ := p
    have hcheck : mbqcFlowCheck G I O f r := by
      have hform :
          mbqcFlowDecide G I O =
            (Fintype.elems (α := (Fin n → Option (Fin n)) × (Fin n → Fin n))).toList.find?
              (fun q => decide (mbqcFlowCheck G I O q.1 q.2)) := rfl
      rw [hform] at hdec
      have hsome : decide (mbqcFlowCheck G I O f r) = true :=
        List.find?_some
          (p := fun q : (Fin n → Option (Fin n)) × (Fin n → Fin n) =>
            decide (mbqcFlowCheck G I O q.1 q.2)) hdec
      exact of_decide_eq_true hsome
    refine ⟨flowCorrection G (clause6Aux_outMaskedFlow f O), ?_, ?_⟩
    · intro s v
      exact flowCorrection_pauliWire G (clause6Aux_outMaskedFlow f O) s v
    · refine flowCorrection_causal G (clause6Aux_outMaskedFlow f O) (mbqcRankPrec r) ?_ ?_
      · intro v u hf
        by_cases hv : v ∈ O
        · simp [clause6Aux_outMaskedFlow, hv] at hf
        · have hf' : f v = some u := by simpa [clause6Aux_outMaskedFlow, hv] using hf
          exact flow_F2_of_check G I O f r hcheck v u hv hf'
      · intro v w u hf hne hadj
        by_cases hv : v ∈ O
        · simp [clause6Aux_outMaskedFlow, hv] at hf
        · have hf' : f v = some w := by simpa [clause6Aux_outMaskedFlow, hv] using hf
          exact flow_F3_of_check G I O f r hcheck v w u hv hf' hne hadj

/-- The proposition that a successful flow search gives equal XY-pattern branches on all density
inputs when using the output-masked flow corrections. -/
def clause6Aux_clause4_branchObligation : Prop :=
  ∀ (n : ℕ) (G : MbqcGraph n) (I O : Finset (Fin n)) (a : Fin n → ℝ),
    match mbqcFlowDecide G I O with
    | some p =>
        ∀ ρ : Operator (2 ^ I.card), IsDensityOperator ρ →
          ∀ s s' : Fin n → Bool,
            mbqcPatternBranch G I O p.2 (fun _ => MbqcPlane.XY) a
              (flowCorrection G (clause6Aux_outMaskedFlow p.1 O)) s ρ
            = mbqcPatternBranch G I O p.2 (fun _ => MbqcPlane.XY) a
              (flowCorrection G (clause6Aux_outMaskedFlow p.1 O)) s' ρ
    | none => True
end Qatlib.Concepts.MbqcFlow.FlowDecision
