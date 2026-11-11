/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Path-containment problems and the color-coding reduction

Source: A. Cornelissen, A. S. Gilani, S. Patro, *Quantum algorithms for path and cycle
containment problems*, arXiv:2605.09017v2 (fixed version read for this file).

The paper works with graph problems presented as boolean functions on the adjacency
matrix (Definition 3.1, Definition 3.7).  We model an input graph by its arc relation
`A : V → V → Prop` and define the directed path-containment problems
`DirPath^{=k}_{s,t}` and `DirPath^{≤k}_{s,t}` exactly as "there is an injective
(vertex-simple) directed path of the prescribed length".

The results formalized here are the deterministic, combinatorial cores of the
color-coding reductions:

* `colorCoded` builds the filtered graph of Lemma 4.1 / Proposition 3.13, keeping only
  the arcs that increase a colouring by exactly one;
* `colorCoded_iff` proves that filtering by a well-chosen colouring neither creates nor
  destroys directed paths (soundness and completeness for a single colouring), which is
  the deterministic content of "the colour-coded instance is positive with positive
  probability" in Lemma 4.1;
* `layeredPath_colorCoded_iff` specialises this to a layered partition of the vertices,
  which is the graph `G'` of Lemma 4.1.

What stays outside this file is recorded in the PR discussion: the probabilistic
statement over the random colouring (probability `Ω(1)`), the multiplicative query-cost
transfer of Lemma 2.5, and every statement about quantum query complexity.
-/

set_option autoImplicit false

namespace Qatlib.Papers.PathCycle26.MainResults

universe u

/-- A directed walk of exactly `k` arcs from `s` to `t` in the graph with arc relation
`A`.  This is the walk underlying the path-containment problems of Definition 3.7: the
vertices need not be distinct yet, simplicity is imposed by `DirWalk.IsSimple`. -/
inductive DirWalk {V : Type u} (A : V → V → Prop) : V → V → ℕ → Type u
  | nil (v : V) : DirWalk A v v 0
  | cons {u v : V} {t : V} {k : ℕ} (h : A u v) (p : DirWalk A v t k) :
      DirWalk A u t (k + 1)

namespace DirWalk

variable {V : Type*} {A : V → V → Prop}

/-- The vertices visited by a directed walk, in order, starting with the source. -/
def verts {s t : V} {k : ℕ} (p : DirWalk A s t k) : List V :=
  match p with
  | .nil _ => [t]
  | .cons _ q => s :: verts q

/-- A directed walk is *simple*, i.e. a path, when no vertex is visited twice. -/
def IsSimple {s t : V} {k : ℕ} (p : DirWalk A s t k) : Prop := p.verts.Nodup

/-- The vertex list of the empty walk is the single source vertex. -/
@[simp]
theorem verts_nil (v : V) : (DirWalk.nil (A := A) v).verts = [v] := rfl

/-- The vertex list of a walk prepended by an arc starts with that arc's source. -/
@[simp]
theorem verts_cons {u v t : V} {k : ℕ} (h : A u v) (q : DirWalk A v t k) :
    (DirWalk.cons h q).verts = u :: q.verts := rfl

/-- Reinterpret a directed walk in a sub- or super-relation. -/
def map {B : V → V → Prop} (f : ∀ u v, A u v → B u v) {s t : V} {k : ℕ}
    (p : DirWalk A s t k) : DirWalk B s t k :=
  match p with
  | .nil v => .nil v
  | .cons h q => .cons (f _ _ h) (map f q)

/-- The source of a walk is the first vertex of its vertex list. -/
theorem head?_verts {s t : V} {k : ℕ} (p : DirWalk A s t k) :
    p.verts.head? = some s := by
  induction p with
  | nil => rfl
  | cons _ _ _ => rfl

/-- The target of a walk is the last vertex of its vertex list. -/
theorem getLast?_verts {s t : V} {k : ℕ} (p : DirWalk A s t k) :
    p.verts.getLast? = some t := by
  induction p with
  | nil => rfl
  | cons h q ih =>
      rw [verts, List.getLast?_cons, ih, Option.getD_some]

/-- The vertex list of a walk has one more entry than its length. -/
theorem length_verts {s t : V} {k : ℕ} (p : DirWalk A s t k) :
    p.verts.length = k + 1 := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [verts, ih]

/-- `map` does not change the vertex list. -/
theorem verts_map {B : V → V → Prop} (f : ∀ u v, A u v → B u v) :
    ∀ {s t : V} {k : ℕ} (p : DirWalk A s t k), (p.map f).verts = p.verts
  | _, _, _, p => by
      induction p with
      | nil => rfl
      | cons h q ih => simp only [map, verts, ih]

/-- The source of a walk occurs in its vertex list. -/
theorem mem_verts_head {s t : V} {k : ℕ} (p : DirWalk A s t k) : s ∈ p.verts := by
  cases p with
  | nil => simp
  | cons _ _ => simp

/-- Mapping a simple walk keeps it simple. -/
theorem map_isSimple {B : V → V → Prop} (f : ∀ u v, A u v → B u v) :
    ∀ {s t : V} {k : ℕ} (p : DirWalk A s t k), p.IsSimple → (p.map f).IsSimple
  | _, _, _, _, hp => by
      simp only [IsSimple, verts_map] at *
      exact hp

/-- Append a single arc at the *end* of a directed walk.  This is the operation
needed to reverse a walk: the last arc of a walk from `s` to `t` points into `s` in
the reversed relation. -/
def snoc {V : Type*} {A : V → V → Prop} {s t : V} :
    ∀ {k : ℕ}, DirWalk A s t k → ∀ {u : V}, A t u → DirWalk A s u (k + 1)
  | 0, .nil _, _, e => .cons e (.nil _)
  | _ + 1, .cons h q, _, e => .cons h (q.snoc e)

/-- The vertex list of a walk with an arc appended at the end. -/
theorem verts_snoc {V : Type*} {A : V → V → Prop} {s t : V} :
    ∀ {k : ℕ} (p : DirWalk A s t k) {u : V} (e : A t u),
      (p.snoc e).verts = p.verts ++ [u]
  | 0, .nil _, _, _ => rfl
  | _ + 1, .cons _ _, _, _ => by
      simp only [snoc, verts, verts_snoc, List.cons_append]

/-- Reverse a directed walk, provided the arc relation is symmetric.  This is the
bookkeeping behind the undirected/directed identifications of Proposition 3.6 and
Proposition 3.11: in an undirected graph a path can be traversed in either direction. -/
def reverse {V : Type*} {A : V → V → Prop} {s t : V} (hsym : ∀ u v, A u v → A v u) :
    ∀ {k : ℕ}, DirWalk A s t k → DirWalk A t s k
  | 0, .nil v => .nil v
  | _ + 1, .cons h q => (reverse hsym q).snoc (hsym _ _ h)

/-- Reversing a walk reverses its vertex list. -/
theorem verts_reverse {V : Type*} {A : V → V → Prop} {s t : V}
    (hsym : ∀ u v, A u v → A v u) :
    ∀ {k : ℕ} (p : DirWalk A s t k), (p.reverse hsym).verts = p.verts.reverse
  | 0, .nil _ => rfl
  | _ + 1, .cons _ _ => by
      simp only [reverse, verts_snoc, verts, List.reverse_cons, verts_reverse]

end DirWalk

/-- `DirPathExact A s t k` is the problem `DirPath^{=k}_{s,t}` of Definition 3.7(2):
the graph contains an injective directed path of exactly `k` arcs from `s` to `t`. -/
def DirPathExact {V : Type*} (A : V → V → Prop) (s t : V) (k : ℕ) : Prop :=
  ∃ p : DirWalk A s t k, p.IsSimple

/-- `DirPathAtMost A s t k` is the problem `DirPath^{≤k}_{s,t}` of Definition 3.7. -/
def DirPathAtMost {V : Type*} (A : V → V → Prop) (s t : V) (k : ℕ) : Prop :=
  ∃ ℓ ≤ k, DirPathExact A s t ℓ

/-- An exact-length path is in particular a path of at most that length. -/
theorem DirPathExact.toAtMost {V : Type*} {A : V → V → Prop} {s t : V} {k : ℕ}
    (h : DirPathExact A s t k) : DirPathAtMost A s t k :=
  ⟨k, le_rfl, h⟩

/-- In a symmetric graph (an undirected graph read as a directed relation), a simple
directed path from `s` to `t` can be traversed backwards, giving a simple directed
path from `t` to `s`.  This is the deterministic core of the undirected-to-directed
identification in Proposition 3.6 / Proposition 3.11. -/
theorem DirPathExact.symm {V : Type*} {A : V → V → Prop} (hsym : ∀ u v, A u v → A v u)
    {s t : V} {k : ℕ} (h : DirPathExact A s t k) : DirPathExact A t s k := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse hsym, by
    show (p.reverse hsym).verts.Nodup
    rw [DirWalk.verts_reverse, List.nodup_reverse]
    exact hp⟩

/-- A directed path survives in any super-relation. -/
theorem DirPathExact.mono {V : Type*} {A B : V → V → Prop} (hAB : ∀ u v, A u v → B u v)
    {s t : V} {k : ℕ} (h : DirPathExact A s t k) : DirPathExact B s t k := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.map (fun u v h => hAB u v h), p.map_isSimple _ hp⟩

/-! ### The colour-coded subgraph

Lemma 4.1 and Proposition 3.13 both replace the input graph by the subgraph that keeps
only the arcs `(v, w)` with `c w = c v + 1` for a colouring `c : V → ℕ`.  The lemmas
below show that this operation is sound for every colouring and complete for a
suitable one. -/

/-- The colour-coded arc relation: keep only the arcs that raise the colouring by
exactly one.  With `c` the layer map this is the graph `G'` of Lemma 4.1, viz.
`A_j = {(v, w) ∈ A : v ∈ V_{j-1}, w ∈ V_j}`. -/
def colorCoded {V : Type*} (A : V → V → Prop) (c : V → ℕ) : V → V → Prop :=
  fun u v => A u v ∧ c v = c u + 1

/-- Along a walk in the colour-coded graph the colouring increases by exactly one per
step, so the colour difference of the endpoints is the length of the walk. -/
theorem colorCoded_color {V : Type*} {A : V → V → Prop} {c : V → ℕ} {s t : V} {k : ℕ}
    (p : DirWalk (colorCoded A c) s t k) : c t = c s + k := by
  induction p with
  | nil => simp
  | cons h _ ih =>
      simp only [colorCoded] at h
      omega

/-- A path in a colour-coded graph is a path in the original graph: colour-coding only
removes arcs, so it cannot create new paths. -/
theorem DirPathExact.colorCoded_lift {V : Type*} {A : V → V → Prop} {c : V → ℕ} {s t : V}
    {k : ℕ} (h : DirPathExact (colorCoded A c) s t k) : DirPathExact A s t k :=
  h.mono fun _ _ h => h.1

/-- Two colourings that agree on the vertices of a walk support the same colour-coded
walk.  This is the bookkeeping that lets us colour the vertices of a path one at a
time. -/
def colorCoded_congr {V : Type*} {A : V → V → Prop} {c d : V → ℕ} :
    ∀ {s t : V} {k : ℕ} (p : DirWalk (colorCoded A c) s t k),
      (∀ w ∈ p.verts, c w = d w) → DirWalk (colorCoded A d) s t k
  | _, _, 0, .nil v, _ => .nil v
  | _, _, _ + 1, @DirWalk.cons _ _ u v t j h q, hcd =>
      .cons ⟨h.1, by
          have hu := hcd u (by simp)
          have hv := hcd v (by simp [DirWalk.mem_verts_head q])
          simp only [colorCoded] at h ⊢
          omega⟩
        (colorCoded_congr q fun w hw => hcd w (by simp [hw]))

/-- `colorCoded_congr` keeps the vertex list, so the walk it returns visits exactly the
vertices of the original walk. -/
theorem verts_colorCoded_congr {V : Type*} {A : V → V → Prop} {c d : V → ℕ} :
    ∀ {s t : V} {k : ℕ} (p : DirWalk (colorCoded A c) s t k)
      (h : ∀ w ∈ p.verts, c w = d w), (colorCoded_congr p h).verts = p.verts
  | _, _, 0, .nil v, _ => rfl
  | _, _, _ + 1, @DirWalk.cons _ _ u v t j h q, hcd => by
      change u :: (colorCoded_congr q _).verts = u :: q.verts
      exact congrArg (List.cons u) (verts_colorCoded_congr q _)

/-- Every simple directed walk can be turned into a walk of a colour-coded graph by
colouring its vertices in order: the `i`-th vertex of the walk receives colour `n + i`
and all other vertices are coloured as prescribed by the induction hypothesis.  This is
the deterministic content of the positive case of Lemma 4.1: some colouring always
succeeds, hence a random one succeeds with positive probability. -/
theorem exists_colorCoded_walk {V : Type*} [DecidableEq V] {A : V → V → Prop} :
    ∀ {s t : V} {k : ℕ} (p : DirWalk A s t k), p.IsSimple → ∀ n : ℕ,
      ∃ c : V → ℕ, c s = n ∧ ∃ p' : DirWalk (colorCoded A c) s t k, p'.verts = p.verts
  | _, _, 0, .nil v, _, n => ⟨fun _ => n, rfl, ⟨.nil v, rfl⟩⟩
  | _, _, _ + 1, @DirWalk.cons _ _ u v t j h q, hp, n => by
      have hp' : q.IsSimple := (List.nodup_cons.mp hp).2
      have huq : u ∉ q.verts := (List.nodup_cons.mp hp).1
      have hvq : v ∈ q.verts := DirWalk.mem_verts_head q
      obtain ⟨c', hc', q', hq'⟩ := exists_colorCoded_walk q hp' (n + 1)
      have hvu : v ≠ u := by
        intro hvu
        exact huq (hvu ▸ hvq)
      refine ⟨Function.update c' u n, by simp, ?_⟩
      have hcol : c' v = Function.update c' u n u + 1 := by
        rw [Function.update_self, hc']
      refine ⟨.cons ⟨h, ?_⟩ (colorCoded_congr q' ?_), ?_⟩
      · rw [Function.update_of_ne hvu, hcol]
      · intro w hw
        rw [hq'] at hw
        have hwu : w ≠ u := fun hwu => huq (hwu ▸ hw)
        exact (Function.update_of_ne hwu n c').symm
      · change u :: (colorCoded_congr q' _).verts = u :: q.verts
        rw [verts_colorCoded_congr, hq']

/-- Colour-coding is exact for a suitable colouring: the input graph contains a simple
directed path of length `k` from `s` to `t` if and only if some colouring exposes such a
path in the colour-coded graph.  The forward direction colours the path vertices in
order, the backward direction only uses that colour-coding removes arcs. -/
theorem dirPathExact_colorCoded_iff {V : Type*} [DecidableEq V] (A : V → V → Prop)
    (s t : V) (k : ℕ) :
    DirPathExact A s t k ↔ ∃ c : V → ℕ, DirPathExact (colorCoded A c) s t k := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨c, -, p', hp'⟩ := exists_colorCoded_walk p hp 0
    refine ⟨c, p', ?_⟩
    show p'.verts.Nodup
    rw [hp']
    exact hp
  · rintro ⟨c, hp⟩
    exact hp.colorCoded_lift

/-- Lemma 4.1, negative case: the filtered graph keeps only a subset of the arcs of the
input graph, hence a negative instance stays negative under every layered colouring. -/
theorem lemma41_negative {V : Type*} (A : V → V → Prop) (s t : V) (k : ℕ)
    (c : V → ℕ) : ¬ DirPathExact A s t k → ¬ DirPathExact (colorCoded A c) s t k :=
  fun hneg hpos => hneg hpos.colorCoded_lift

/-- In a layered colour-coded graph every directed walk from layer `0` to layer `k` has
length exactly `k`: the layers, not the walk, fix the length.  This is the "no false
positive" side of the layered path problem of §4. -/
theorem colorCoded_length_eq {V : Type*} {A : V → V → Prop} {c : V → ℕ} {s t : V} {k n : ℕ}
    (hcs : c s = 0) (hct : c t = k) (p : DirWalk (colorCoded A c) s t n) : n = k := by
  have h := colorCoded_color p
  omega

/-- The `≤ k` version of the colour-coding soundness: if the layered graph has a path of
length at most `k`, then the original graph has a path of length exactly `k`.  Together
with `lemma41_positive` this is the deterministic core of Proposition 3.11. -/
theorem dirPathAtMost_colorCoded_to_exact {V : Type*} {A : V → V → Prop} {s t : V} {k : ℕ}
    {c : V → ℕ} (hcs : c s = 0) (hct : c t = k)
    (h : DirPathAtMost (colorCoded A c) s t k) : DirPathExact A s t k := by
  obtain ⟨ℓ, -, p, hp⟩ := h
  have hℓ : ℓ = k := colorCoded_length_eq hcs hct p
  have h' : DirPathExact A s t ℓ :=
    DirPathExact.colorCoded_lift (⟨p, hp⟩ : DirPathExact (colorCoded A c) s t ℓ)
  rwa [hℓ] at h'

/-- Lemma 4.1, positive case in deterministic form: if the input graph contains a simple
directed path of length `k`, then some layered colouring exposes it in the filtered
graph.  The paper's probabilistic statement, that a uniformly random layering does so
with probability `Ω(1)`, together with the query-cost transfer of Lemma 2.5, is not
part of this theorem. -/
theorem lemma41_positive {V : Type*} [DecidableEq V] (A : V → V → Prop) (s t : V) (k : ℕ)
    (h : DirPathExact A s t k) : ∃ c : V → ℕ, DirPathExact (colorCoded A c) s t k :=
  (dirPathExact_colorCoded_iff A s t k).1 h

/-- In a layered colour-coded graph whose source sits in layer `0` and whose target sits
in layer `k`, the `≤ k` and `= k` versions of the directed path problem coincide: any
walk of length at most `k` in the layered graph has length exactly `k`.  This is the
"no false positive" step that lets Proposition 3.11 replace `DirPath^{≤k}` by
`DirPath^{=k}` inside the colour-coded instance. -/
theorem dirPathAtMost_colorCoded_iff {V : Type*} {A : V → V → Prop} {c : V → ℕ} {s t : V}
    {k : ℕ} (hcs : c s = 0) (hct : c t = k) :
    DirPathAtMost (colorCoded A c) s t k ↔ DirPathExact (colorCoded A c) s t k := by
  constructor
  · rintro ⟨ℓ, -, p, hp⟩
    have hlen : ℓ = k := colorCoded_length_eq hcs hct p
    rw [← hlen]
    exact ⟨p, hp⟩
  · exact DirPathExact.toAtMost

/-! ### The probability that a random colouring exposes a fixed path

Lemma 4.1 colours every vertex independently and uniformly with one of `k + 1` colours,
and observes that a fixed simple path of length `k` receives its `k + 1` prescribed,
pairwise distinct colours with probability `(k + 1)^{-(k+1)}`.  The lemmas below make
this counting statement precise:

* `pathColor` is the prescribed colouring of a walk's vertices (`i`-th vertex ↦ colour
  `i`);
* `exists_colorCoded_of_colorMatches` turns any colouring that agrees with `pathColor`
  on the walk's vertices into a colour-coded copy of the walk;
* `card_fun_agree_on` counts the colourings that agree with a fixed colouring on a set
  of prescribed vertices. -/

/-- A colouring of a finite type that agrees with a fixed colouring `g` on a finite set
`S` is determined freely on the complement, so there are `|β| ^ (|α| - |S|)` of them.
This is the elementary counting step behind Lemma 4.1's probability `(k+1)^{-(k+1)}`. -/
theorem card_fun_agree_on {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Nonempty β] (S : Finset α) (g : α → β) :
    (Finset.univ.filter (fun f : α → β => ∀ a ∈ S, f a = g a)).card =
      (Fintype.card β) ^ (Fintype.card α - S.card) := by
  classical
  have h1 : (Finset.univ.filter (fun f : α → β => ∀ a ∈ S, f a = g a)).card =
      Fintype.card {f : α → β // ∀ a ∈ S, f a = g a} := by
    rw [Fintype.card_subtype]
  have e : {f : α → β // ∀ a ∈ S, f a = g a} ≃ ({a : α // a ∉ S} → β) := by
    refine ⟨fun f a => f.1 a.1,
      fun h => ⟨fun a => if ha : a ∈ S then g a else h ⟨a, ha⟩, ?_⟩, ?_, ?_⟩
    · intro a ha
      dsimp only
      rw [dif_pos ha]
    · intro f; apply Subtype.ext; funext a; by_cases ha : a ∈ S
      · dsimp only; rw [dif_pos ha]; exact (f.2 a ha).symm
      · dsimp only; rw [dif_neg ha]
    · intro f; funext x; by_cases hx : x.1 ∈ S
      · exact absurd hx x.2
      · dsimp only; rw [dif_neg hx]
  have h2 : Fintype.card {a : α // a ∉ S} = Fintype.card α - S.card := by
    rw [Fintype.card_subtype]
    rw [show (Finset.univ.filter (fun a => a ∉ S)) = Sᶜ from by ext a; simp]
    rw [Finset.card_compl]
  rw [h1, Fintype.card_congr e, Fintype.card_fun, h2]

/-- `ColorMatches f n l` says the colouring `f` sends the `i`-th vertex of `l` to the
colour `n + i`.  It is stated through `l[i]?` so that it behaves well under `cons`. -/
def ColorMatches {V : Type*} (f : V → ℕ) (n : ℕ) (l : List V) : Prop :=
  ∀ (i : ℕ) (v : V), l[i]? = some v → f v = n + i

/-- The prescribed colouring of a walk's vertices: the `i`-th vertex receives colour
`i`, and all other vertices receive colour `0`. -/
def pathColor {V : Type*} [DecidableEq V] {A : V → V → Prop} {s t : V} {k : ℕ}
    (p : DirWalk A s t k) : V → Fin (k + 1) :=
  fun v => if h : v ∈ p.verts then
      ⟨p.verts.idxOf v, by
        have hv := List.idxOf_lt_length_iff.mpr h
        rw [DirWalk.length_verts] at hv
        exact hv⟩
    else ⟨0, Nat.succ_pos k⟩

/-- The prescribed colouring gives the `i`-th vertex of a simple walk colour `i`. -/
theorem pathColor_get {V : Type*} [DecidableEq V] {A : V → V → Prop} {s t : V} {k : ℕ}
    (p : DirWalk A s t k) (hp : p.IsSimple) (i : Fin (k + 1)) :
    pathColor p (p.verts.get ⟨i.1, by rw [DirWalk.length_verts]; exact i.2⟩) = i := by
  unfold pathColor
  rw [dif_pos (List.get_mem _ _)]
  apply Fin.ext
  exact List.get_idxOf hp ⟨i.1, by rw [DirWalk.length_verts]; exact i.2⟩

/-- If the colouring `f` matches the increasing pattern `n, n+1, …` along a walk's
vertices, then the walk can be lifted to the colour-coded graph: every arc of the walk
raises the colour by exactly one. -/
theorem exists_colorCoded_of_colorMatches {V : Type*} [DecidableEq V] {A : V → V → Prop}
    (f : V → ℕ) :
    ∀ {s t : V} {k : ℕ} (p : DirWalk A s t k) (n : ℕ), ColorMatches f n p.verts →
      ∃ p' : DirWalk (colorCoded A f) s t k, p'.verts = p.verts
  | _, _, 0, .nil v, _, _ => ⟨.nil v, rfl⟩
  | _, _, _ + 1, @DirWalk.cons _ _ u v t j h q, n, hc => by
      have hcu : f u = n := by
        have h0 : (DirWalk.cons h q).verts[0]? = some u := by
          simp [DirWalk.verts_cons]
        have := hc 0 u h0
        simpa using this
      have hvq : q.verts[0]? = some v := by
        have := DirWalk.head?_verts q
        rwa [List.head?_eq_getElem?] at this
      have hcv : f v = n + 1 := by
        have h1 : (DirWalk.cons h q).verts[1]? = some v := by
          simp [DirWalk.verts_cons, hvq]
        have := hc 1 v h1
        simpa using this
      have harc : colorCoded A f u v := ⟨h, by rw [hcu, hcv]⟩
      have htail : ColorMatches f (n + 1) q.verts := by
        intro i w hw
        have h1 : (DirWalk.cons h q).verts[i + 1]? = some w := by
          simp [DirWalk.verts_cons, hw]
        have := hc (i + 1) w h1
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      obtain ⟨q', hq'⟩ := exists_colorCoded_of_colorMatches f q (n + 1) htail
      exact ⟨.cons harc q', by simp [DirWalk.verts_cons, hq']⟩

/-- If a colouring agrees with the prescribed colouring on the vertices of a simple walk,
then it matches the increasing colour pattern along that walk. -/
theorem colorMatches_of_agrees {V : Type*} [DecidableEq V] {A : V → V → Prop}
    {s t : V} {k : ℕ} (p : DirWalk A s t k) (hp : p.IsSimple) (c : V → ℕ)
    (hagree : ∀ v ∈ p.verts, c v = (pathColor p v : ℕ)) :
    ColorMatches c 0 p.verts := by
  intro i v hiv
  obtain ⟨hlen, hge⟩ := List.getElem?_eq_some_iff.mp hiv
  have hmem : v ∈ p.verts := by rw [← hge]; exact List.get_mem _ _
  have hidx : p.verts.idxOf v = i := by
    have h1 : p.verts.idxOf (p.verts.get ⟨i, hlen⟩) = i := by
      simpa using List.get_idxOf hp ⟨i, hlen⟩
    have hget : p.verts.get ⟨i, hlen⟩ = v := hge
    rw [hget] at h1
    exact h1
  rw [hagree v hmem]
  have hval : (pathColor p v : ℕ) = p.verts.idxOf v := by
    unfold pathColor
    rw [dif_pos hmem]
  rw [hval, hidx]
  omega

/-- Lemma 4.1, positive case as a finite counting statement: on a finite vertex set there
are exactly `(k+1)^(|V| - (k+1))` colourings `V → Fin (k+1)` agreeing with the prescribed
colouring on the vertices of a simple walk of length `k`.  This is the numerator of the
paper's positive-probability bound `(k+1)^{-(k+1)}`. -/
theorem card_colorings_exposing_walk {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → V → Prop} {s t : V} {k : ℕ} (p : DirWalk A s t k) (hp : p.IsSimple) :
    (Finset.univ.filter (fun f : V → Fin (k + 1) =>
        ∀ v ∈ p.verts.toFinset, f v = pathColor p v)).card
      = (k + 1) ^ (Fintype.card V - (k + 1)) := by
  rw [card_fun_agree_on p.verts.toFinset (pathColor p)]
  simp [List.toFinset_card_of_nodup hp, DirWalk.length_verts, Fintype.card_fin]

/-- Every colouring counted in `card_colorings_exposing_walk` actually exposes the walk in
the colour-coded graph: the walk lifts arc by arc because consecutive colours increase by
one.  Together with the count this is the positive case of Lemma 4.1. -/
theorem exposing_of_agrees {V : Type*} [DecidableEq V] {A : V → V → Prop}
    {s t : V} {k : ℕ} (p : DirWalk A s t k) (hp : p.IsSimple)
    (f : V → Fin (k + 1)) (hf : ∀ v ∈ p.verts.toFinset, f v = pathColor p v) :
    ∃ p' : DirWalk (colorCoded A (fun v => (f v : ℕ))) s t k, p'.verts = p.verts := by
  apply exists_colorCoded_of_colorMatches (fun v => (f v : ℕ)) p 0
  apply colorMatches_of_agrees p hp
  intro v hv
  exact congrArg Fin.val (hf v (List.mem_toFinset.mpr hv))

end Qatlib.Papers.PathCycle26.MainResults
