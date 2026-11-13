/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.QueryWordCore.Circuit
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.BitIndices

set_option backward.isDefEq.respectTransparency false

/-!
# SubHypergraph13 source model

Fixed source: Guerreschi--Magniez--Santha, "Quantum Algorithms for Finding
Constant-sized Sub-hypergraphs", arXiv:1310.4127 (2013), PDF pages 4--15.
All definitions below are the paper's own objects, transcribed in the paper's
notation (`Σ₁,Σ₂,Σ₃`, `rᵢ,fᵢⱼ,eᵢⱼₖ`, `Mᵢⱼₖ`, `Γᵢⱼₖ`, `Υ(R,Γ)`).

Model boundary. A 3-uniform hypergraph on `Fin n` is a finite set of
3-element vertex sets (the paper's `(V,E)` with `E ⊆ {unordered triples}`).
A quantum query algorithm is a finite list-based circuit
(`Qatlib.Foundations.QueryWordCore.Circuit`) over a
finite computational basis, initialised in one displayed computational basis
state, with the paper's oracle
`|{u,v,w},b⟩ ↦ |{u,v,w}, b ⊕ χ({u,v,w})⟩` as the only query step. Fixed gates
are unrestricted (query complexity, not gate complexity, is the source
measure). The final answer is a function of the measured basis state. This is
exactly the source's query model; it does not assert gate synthesis or running
time.

The probability of an event is the normalised counting measure on the relevant
finite family (uniform `r`-subsets for the hypergeometric walks). Where the
paper writes `exp` we use `Real.exp`, and where it writes `(1/2)^x` with real
`x` we use `Real.rpow (1/2) x`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Papers.SubHypergraph13.MainResults

/-! ## Hypergraphs and copies -/

/-- The paper's `V × V × V` when `V = Fin n`. -/
abbrev Triple (n : ℕ) := Fin n × Fin n × Fin n

/-- A 3-uniform hypergraph on `Fin n`: a finite set of edges, each a
3-element vertex set (paper p.3, "Preliminaries"). -/
structure Hypergraph3 (n : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ e ∈ edges, e.card = 3

/-- The unordered vertex set of an ordered triple. -/
def tripleEdge {n : ℕ} (p : Triple n) : Finset (Fin n) := {p.1, p.2.1, p.2.2}

/-- The complete 3-uniform hypergraph on `κ` vertices (the paper's 4-clique is
`completeHypergraph 4`, p.15 Theorem 11). -/
def completeHypergraph (κ : ℕ) : Hypergraph3 κ where
  edges := Finset.univ.filter (fun e : Finset (Fin κ) => e.card = 3)
  uniform := by
    intro e he
    exact (Finset.mem_filter.mp he).2

/-- `φ` embeds `H` into `G` as a (not necessarily induced) sub-hypergraph. -/
def IsCopy {κ n : ℕ} (H : Hypergraph3 κ) (G : Hypergraph3 n)
    (φ : Fin κ → Fin n) : Prop :=
  Function.Injective φ ∧ ∀ e ∈ H.edges, e.image φ ∈ G.edges

/-- `G` contains a copy of `H` (paper p.15, "4-clique detection"). -/
def HasCopy {κ n : ℕ} (H : Hypergraph3 κ) (G : Hypergraph3 n) : Prop :=
  ∃ φ : Fin κ → Fin n, IsCopy H G φ

/-! ## Loading schedules and parameters (paper §3, Definitions 3 and 4) -/

/-- One element `sₜ` of a loading schedule: a vertex, a pair, or a triple of
vertices of `H` (identified with `Σ₁, Σ₂, Σ₃`). -/
inductive ScheduleItem (κ : ℕ) where
  | vertex (i : Fin κ) : ScheduleItem κ
  | pair (i j : Fin κ) : ScheduleItem κ
  | triple (i j k : Fin κ) : ScheduleItem κ
deriving DecidableEq, Repr

/-- The unordered pair `{i,j}`. -/
def pairSet {κ : ℕ} (i j : Fin κ) : Finset (Fin κ) := {i, j}

/-- The unordered triple `{i,j,k}`. -/
def tripleSet {κ : ℕ} (i j k : Fin κ) : Finset (Fin κ) := {i, j, k}

/-- Some earlier entry of the schedule is the vertex `i`. -/
def earlierVertex {κ m : ℕ} (σ : Fin m → ScheduleItem κ) (t : Fin m) (i : Fin κ) : Prop :=
  ∃ t' : Fin m, t' < t ∧ σ t' = ScheduleItem.vertex i

/-- Some earlier entry of the schedule is the (unordered) pair `{i,j}`. -/
def earlierPair {κ m : ℕ} (σ : Fin m → ScheduleItem κ) (t : Fin m) (i j : Fin κ) : Prop :=
  ∃ t' : Fin m, t' < t ∧
    (σ t' = ScheduleItem.pair i j ∨ σ t' = ScheduleItem.pair j i)

/-- Definition 3: a valid loading schedule. The order conditions are exactly
`(i)--(iii)`; validity also demands that no element of `Σ₁ ∪ Σ₂ ∪ Σ₃` repeats
and that every hyperedge of `H` occurs as a triple. -/
def ValidSchedule {κ m : ℕ} (H : Hypergraph3 κ) (σ : Fin m → ScheduleItem κ) : Prop :=
  (∀ t : Fin m,
      match σ t with
      | ScheduleItem.vertex _ => True
      | ScheduleItem.pair i j =>
          i ≠ j ∧ earlierVertex σ t i ∧ earlierVertex σ t j
      | ScheduleItem.triple i j k =>
          i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
            earlierPair σ t i j ∧ earlierPair σ t i k ∧ earlierPair σ t j k) ∧
  (∀ t₁ t₂ : Fin m, σ t₁ = σ t₂ → t₁ = t₂) ∧
  (∀ i j k : Fin κ, tripleSet i j k ∈ H.edges →
      ∃ t : Fin m, σ t = ScheduleItem.triple i j k)

/-- Definition 4: the integer parameters attached to a schedule. -/
structure Parameters (κ : ℕ) where
  r : Fin κ → ℕ
  f : Fin κ → Fin κ → ℕ
  e : Fin κ → Fin κ → Fin κ → ℕ

/-- The admissibility conditions of Definition 4 (paper p.5): the range
conditions and the polynomial-scale conditions `n/rᵢ`, `fᵢⱼ/rᵢ`,
`fᵢⱼfᵢₖfⱼₖ/(rᵢrⱼrₖ)` all exceeding `n^γ` for some `γ > 0`. -/
def Parameters.Admissible {κ : ℕ} (P : Parameters κ) (_H : Hypergraph3 κ) (n : ℕ) : Prop :=
  (∀ i : Fin κ, 1 ≤ P.r i) ∧
  (∀ i j k : Fin κ, 1 ≤ P.e i j k) ∧
  (∀ i j : Fin κ, (P.r i : ℝ) ≤ P.f i j) ∧
  (∀ i j : Fin κ, P.f i j ≤ P.r i * P.r j) ∧
  (∀ i j k : Fin κ, P.e i j k ≤ P.r i * P.r j * P.r k) ∧
  (∀ i j k : Fin κ,
      1 ≤ ((P.f i j : ℝ) * (P.f i k : ℝ) * (P.f j k : ℝ)) /
        ((P.r i : ℝ) * (P.r j : ℝ) * (P.r k : ℝ)) / (P.e i j k : ℝ)) ∧
  (∃ γ : ℝ, 0 < γ ∧
    (∀ i : Fin κ, (n : ℝ) ^ γ ≤ (n : ℝ) / (P.r i : ℝ)) ∧
    (∀ i j : Fin κ, (n : ℝ) ^ γ ≤ (P.f i j : ℝ) / (P.r i : ℝ)) ∧
    (∀ i j k : Fin κ,
        (n : ℝ) ^ γ ≤ ((P.f i j : ℝ) * (P.f i k : ℝ) * (P.f j k : ℝ)) /
          ((P.r i : ℝ) * (P.r j : ℝ) * (P.r k : ℝ))))

/-- `Mᵢⱼₖ = 11 fᵢⱼ fᵢₖ fⱼₖ / (rᵢ rⱼ rₖ)` (paper §4, p.11). -/
def Mijk {κ : ℕ} (P : Parameters κ) (i j k : Fin κ) : ℝ :=
  11 * (P.f i j : ℝ) * (P.f i k : ℝ) * (P.f j k : ℝ) /
    ((P.r i : ℝ) * (P.r j : ℝ) * (P.r k : ℝ))

/-! ## The cost expression of Theorem 5 -/

/-- The setup cost `S = Σ_{{i,j,k}∈Σ₃} eᵢⱼₖ`, read off the schedule
(each hyperedge appears exactly once in a valid schedule). -/
def setupCost {κ m : ℕ} (σ : Fin m → ScheduleItem κ) (P : Parameters κ) : ℝ :=
  ∑ t : Fin m,
    match σ t with
    | ScheduleItem.triple i j k => (P.e i j k : ℝ)
    | _ => 0

/-- `δₜ`, with the paper's case values `1/rᵢ`, `1/fᵢⱼ`, `1/eᵢⱼₖ` (p.5). -/
def deltaAt {κ m : ℕ} (σ : Fin m → ScheduleItem κ) (P : Parameters κ) (t : ℕ) : ℝ :=
  if ht : t < m then
    match σ ⟨t, ht⟩ with
    | ScheduleItem.vertex i => 1 / (P.r i : ℝ)
    | ScheduleItem.pair i j => 1 / (P.f i j : ℝ)
    | ScheduleItem.triple i j k => 1 / (P.e i j k : ℝ)
  else 0

/-- `εₜ`, with the paper's case values `rᵢ/n`, `fᵢⱼ/(rᵢrⱼ)`,
`eᵢⱼₖ rᵢrⱼrₖ/(fᵢⱼfᵢₖfⱼₖ)` (p.5). -/
def epsAt {κ m : ℕ} (σ : Fin m → ScheduleItem κ) (P : Parameters κ) (n t : ℕ) : ℝ :=
  if ht : t < m then
    match σ ⟨t, ht⟩ with
    | ScheduleItem.vertex i => (P.r i : ℝ) / (n : ℝ)
    | ScheduleItem.pair i j => (P.f i j : ℝ) / ((P.r i : ℝ) * (P.r j : ℝ))
    | ScheduleItem.triple i j k =>
        ((P.e i j k : ℝ) * (P.r i : ℝ) * (P.r j : ℝ) * (P.r k : ℝ)) /
          ((P.f i j : ℝ) * (P.f i k : ℝ) * (P.f j k : ℝ))
  else 0

/-- `Uₜ` with the paper's case values `1 + Σ_{∋i} eᵢⱼₖ/rᵢ`,
`1 + Σ_{∋{i,j}} eᵢⱼₖ/fᵢⱼ`, and `1` for a triple step (p.5). -/
def updateAt {κ m : ℕ} (H : Hypergraph3 κ) (σ : Fin m → ScheduleItem κ)
    (P : Parameters κ) (t : ℕ) : ℝ :=
  if ht : t < m then
    match σ ⟨t, ht⟩ with
    | ScheduleItem.vertex i =>
        1 + ∑ j : Fin κ, ∑ k ∈ (Finset.univ.filter (fun k : Fin κ => j < k)),
          if tripleSet i j k ∈ H.edges then (P.e i j k : ℝ) / (P.r i : ℝ) else 0
    | ScheduleItem.pair i j =>
        1 + ∑ k : Fin κ,
          if tripleSet i j k ∈ H.edges then (P.e i j k : ℝ) / (P.f i j : ℝ) else 0
    | ScheduleItem.triple _ _ _ => 1
  else 0

/-- The nested-walk query cost `S + Σₜ (Π_{r≤t} 1/√ε_r)·(1/√δ_t)·U_t`
(paper p.4, p.5). -/
def nestedWalkCost {κ m : ℕ} (H : Hypergraph3 κ) (σ : Fin m → ScheduleItem κ)
    (P : Parameters κ) (n : ℕ) : ℝ :=
  setupCost σ P +
    ∑ t ∈ Finset.Icc 1 m,
      ((∏ r ∈ Finset.Icc 1 t, (1 / Real.sqrt (epsAt σ P n r))) *
        (1 / Real.sqrt (deltaAt σ P t)) * updateAt H σ P t)

/-- `g̃ = Õ(f)`: `f ≤ C·(log n)^k·g` eventually, with an absolute constant and
an absolute polylog exponent. -/
def TildeBigO (f g : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    f n ≤ C * (Real.log (n + 2)) ^ k * g n

/-! ## Uniform probabilities over finite subset families -/

/-- Uniform counting probability of `P` over the finite set `S`. -/
def uniformEventProb {α : Type*} (S : Finset α) (P : α → Prop) : ℝ := by
  classical
  exact (S.filter P).card / S.card

/-! ## Hypergeometric distribution (paper p.4) -/

/-- `Pr[X = j]` for `X ~ HG(N,K,r)`. -/
def hypergeomMass (N K r j : ℕ) : ℝ :=
  (Nat.choose K j : ℝ) * (Nat.choose (N - K) (r - j) : ℝ) / (Nat.choose N r : ℝ)

/-- The expectation `µ = rK/N` of `HG(N,K,r)`. -/
def hypergeomMean (N K r : ℕ) : ℝ := (r : ℝ) * (K : ℝ) / (N : ℝ)

/-- `Pr[X ≥ (1+δ)µ]`. -/
def hypergeomTailGE (N K r : ℕ) (δ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1),
    if (1 + δ) * hypergeomMean N K r ≤ (j : ℝ) then hypergeomMass N K r j else 0

/-- `Pr[X ≤ (1-δ)µ]`. -/
def hypergeomTailLE (N K r : ℕ) (δ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1),
    if (j : ℝ) ≤ (1 - δ) * hypergeomMean N K r then hypergeomMass N K r j else 0

/-- `Pr[X > (1+δ)µ]`. -/
def hypergeomTailGT (N K r : ℕ) (δ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1),
    if (1 + δ) * hypergeomMean N K r < (j : ℝ) then hypergeomMass N K r j else 0

/-! ## The map `Υ(R,Γ)` (paper §4.2, p.6) -/

/-- The list `Λ` of all triples: first all triples of `Γ`, then all triples of
its complement (the paper's "first `Γ`, then the rest").  We use `Finset.toList`
rather than a sorted enumeration; the exact traversal order is irrelevant to
`Υ` since the paper's Lemma 6 supplies a compensating permutation `π`. -/
def upsilonList (V : Type*) [Fintype V] [DecidableEq V] (Γ : Finset (V × V × V)) :
    List (V × V × V) :=
  Γ.toList ++ (Finset.univ \ Γ).toList

/-- `Υ(R,Γ) = {Λ[a] | a ∈ R} ∩ Γ`, with `R ⊆ {1,…,p}` represented by
zero-based `Fin` indices into `Λ` (`a.val` is the paper's index minus one). -/
def upsilon {V : Type*} [Fintype V] [DecidableEq V] {p : ℕ}
    (Γ : Finset (V × V × V)) (R : Finset (Fin p)) : Finset (V × V × V) :=
  Γ.filter (fun x => ∃ a : Fin p, a ∈ R ∧ (upsilonList V Γ)[a.val]? = some x)

/-- `Υ(R,Γ) ⊆ Γ`. -/
theorem upsilon_subset {V : Type*} [Fintype V] [DecidableEq V] {p : ℕ}
    (Γ : Finset (V × V × V)) (R : Finset (Fin p)) : upsilon Γ R ⊆ Γ := by
  intro x hx
  simp only [upsilon, Finset.mem_filter] at hx
  exact hx.1

/-! ## The inner set `Γᵢⱼₖ` and the regular-set conditions of Lemma 8 -/

/-- `Γᵢⱼₖ = {(u,v,w) ∈ Vᵢ×Vⱼ×Vₖ | (u,v)∈Fᵢⱼ, (u,w)∈Fᵢₖ, (v,w)∈Fⱼₖ}`
(paper §4.2, p.8). The vertex sets are `Fin ri`, `Fin rj`, `Fin rk`. -/
def gammaSet (ri rj rk : ℕ) (Fij : Finset (Fin ri × Fin rj))
    (Fik : Finset (Fin ri × Fin rk)) (Fjk : Finset (Fin rj × Fin rk)) :
    Finset (Fin ri × Fin rj × Fin rk) :=
  Finset.univ.filter (fun p => (p.1, p.2.1) ∈ Fij ∧ (p.1, p.2.2) ∈ Fik ∧
    (p.2.1, p.2.2) ∈ Fjk)

/-- Left degree of `Fᵢⱼ` at `u ∈ Vᵢ`. -/
def leftDegree {ri rj : ℕ} (Fij : Finset (Fin ri × Fin rj)) (u : Fin ri) : ℕ :=
  (Fij.filter (fun p => p.1 = u)).card

/-- Right degree of `Fᵢⱼ` at `v ∈ Vⱼ`. -/
def rightDegree {ri rj : ℕ} (Fij : Finset (Fin ri × Fin rj)) (v : Fin rj) : ℕ :=
  (Fij.filter (fun p => p.2 = v)).card

/-- Lemma 8 conditions (b) and (c): all degrees lie in
`[fᵢⱼ/(2rᵢ), 2fᵢⱼ/rᵢ]` (resp. `[fᵢⱼ/(2rⱼ), 2fᵢⱼ/rⱼ]`). -/
def degreeRegular {ri rj : ℕ} (fij : ℕ) (Fij : Finset (Fin ri × Fin rj)) : Prop :=
  (∀ u : Fin ri, (fij : ℝ) / (2 * (ri : ℝ)) ≤ (leftDegree Fij u : ℝ) ∧
    (leftDegree Fij u : ℝ) ≤ 2 * (fij : ℝ) / (ri : ℝ)) ∧
  (∀ v : Fin rj, (fij : ℝ) / (2 * (rj : ℝ)) ≤ (rightDegree Fij v : ℝ) ∧
    (rightDegree Fij v : ℝ) ≤ 2 * (fij : ℝ) / (rj : ℝ))

/-- Lemma 8 condition (d): for every `(v,w) ∈ Vⱼ×Vₖ`,
`|{u∈Vᵢ | (u,v)∈Fᵢⱼ, (u,w)∈Fᵢₖ}| ≤ 11 fᵢⱼfᵢₖ/(rᵢrⱼrₖ)`. -/
def pairTripleBound {ri rj rk : ℕ} (fij fik : ℕ)
    (Fij : Finset (Fin ri × Fin rj)) (Fik : Finset (Fin ri × Fin rk))
    (Fjk : Finset (Fin rj × Fin rk)) : Prop :=
  ∀ v : Fin rj, ∀ w : Fin rk,
    (((Fij.filter (fun p => p.2 = v)).filter (fun p => (p.1, w) ∈ Fik)).card : ℝ) ≤
      11 * (fij : ℝ) * (fik : ℝ) / ((ri : ℝ) * (rj : ℝ) * (rk : ℝ))

/-- The number of triples in `Γᵢⱼₖ` is at most `|Fⱼₖ|·11 fᵢⱼfᵢₖ/(rᵢrⱼrₖ)`
(paper §4.4, case 3, the `Mᵢⱼₖ` bound). -/
theorem gammaSet_card_le {ri rj rk : ℕ} {fij fik fjk : ℕ}
    {Fij : Finset (Fin ri × Fin rj)} {Fik : Finset (Fin ri × Fin rk)}
    {Fjk : Finset (Fin rj × Fin rk)}
    (hFjk : Fjk.card = fjk) (hd : pairTripleBound fij fik Fij Fik Fjk) :
    (gammaSet ri rj rk Fij Fik Fjk).card ≤
      (fjk : ℝ) * (11 * (fij : ℝ) * (fik : ℝ) / ((ri : ℝ) * (rj : ℝ) * (rk : ℝ))) := by
  classical
  set B : ℝ := 11 * (fij : ℝ) * (fik : ℝ) / ((ri : ℝ) * (rj : ℝ) * (rk : ℝ)) with hB
  let fib : Fin rj × Fin rk → Finset (Fin ri × Fin rj × Fin rk) := fun q =>
    ((Fij.filter (fun p => p.2 = q.1)).filter (fun p => (p.1, q.2) ∈ Fik)).image
      (fun u => (u.1, q.1, q.2))
  have hsubset : gammaSet ri rj rk Fij Fik Fjk ⊆ Fjk.biUnion fib := by
    intro p hp
    simp only [gammaSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hij, hik, hjk⟩ := hp
    refine Finset.mem_biUnion.mpr ⟨(p.2.1, p.2.2), hjk, ?_⟩
    refine Finset.mem_image.mpr ⟨(p.1, p.2.1), ?_, rfl⟩
    simp only [Finset.mem_filter, and_true]
    exact ⟨hij, hik⟩
  have hfiber : ∀ q ∈ Fjk, (fib q).card ≤ B := by
    intro q _
    have h1 : (fib q).card ≤
        ((Fij.filter (fun p => p.2 = q.1)).filter (fun p => (p.1, q.2) ∈ Fik)).card :=
      Finset.card_image_le
    have h2 : (((Fij.filter (fun p => p.2 = q.1)).filter
        (fun p => (p.1, q.2) ∈ Fik)).card : ℝ) ≤ B := by
      simpa [B] using hd q.1 q.2
    exact le_trans (by exact_mod_cast h1) h2
  have h1 : ((gammaSet ri rj rk Fij Fik Fjk).card : ℝ) ≤ ((Fjk.biUnion fib).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have h2 : ((Fjk.biUnion fib).card : ℝ) ≤ ∑ q ∈ Fjk, B := by
    have hb := Finset.card_biUnion_le (s := Fjk) (t := fib)
    calc ((Fjk.biUnion fib).card : ℝ) ≤ ((∑ q ∈ Fjk, (fib q).card : ℕ) : ℝ) := by
          exact_mod_cast hb
      _ = ∑ q ∈ Fjk, ((fib q).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ q ∈ Fjk, B := Finset.sum_le_sum (fun q hq => hfiber q hq)
  have h3 : ∑ q ∈ Fjk, B = (fjk : ℝ) * B := by
    rw [Finset.sum_const, nsmul_eq_mul, hFjk]
  exact le_trans h1 (le_trans h2 (le_of_eq h3))

/-! ## Quantum query algorithms for 3-uniform hypergraphs -/

/-- Indices of the quantum register: a candidate embedding `Fin κ → Fin n`,
a success flag, and the triple being queried. -/
abbrev HypergraphIndex (n κ : ℕ) := (Fin κ → Fin n) × Bool × Triple n

/-- Computational basis of the algorithm: an index together with one answer bit
(the paper's query register `{u,v,w},b`). -/
abbrev HypergraphState (n κ : ℕ) := HypergraphIndex n κ × Bool

/-- The oracle answer `χ({u,v,w})`. -/
def oracleAnswer {n : ℕ} (G : Hypergraph3 n) (p : Triple n) : Bool :=
  decide (tripleEdge p ∈ G.edges)

/-- The paper's oracle `|q,b⟩ ↦ |q, b ⊕ f(q)⟩` as a permutation matrix. -/
def boolOracleMatrix {σ : Type*} [DecidableEq σ] (f : σ → Bool) : Matrix (σ × Bool) (σ × Bool) ℂ :=
  Matrix.of (fun p q => if q = (p.1, Bool.xor p.2 (f p.1)) then 1 else 0)

/-- The hypergraph oracle on the algorithm register (the oracle ignores the
embedding and flag components). -/
def hypergraphOracleMatrix {n κ : ℕ} (G : Hypergraph3 n) :
    Matrix (HypergraphState n κ) (HypergraphState n κ) ℂ :=
  boolOracleMatrix (fun p : HypergraphIndex n κ => oracleAnswer G p.2.2)

/-- Any fixed computational basis state of the algorithm register. -/
def hypergraphInitialState {n κ : ℕ} (p₀ : HypergraphIndex n κ) :
    QState (HypergraphState n κ) :=
  Ket (p₀, false)

/-- Measurement success set: a claimed copy must really be one; a "no" answer is
accepted exactly when no copy exists. -/
def hypergraphSuccessSet {n κ : ℕ} (H : Hypergraph3 κ) (G : Hypergraph3 n) :
    Finset (HypergraphState n κ) := by
  classical
  exact Finset.univ.filter (fun q =>
    if q.1.2.1 then IsCopy H G q.1.1 else ¬ HasCopy H G)

/-- The oracle matrix is a permutation matrix, hence unitary: one query is one
unitary `b ↦ b ⊕ χ(q)` on the answer bit. -/
theorem boolOracleMatrix_mem_unitaryGroup {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → Bool) :
    boolOracleMatrix f ∈ Matrix.unitaryGroup (σ × Bool) ℂ := by
  classical
  -- the answer-bit flip `z ↦ (z.1, z.2 ⊕ f z.1)` is injective
  have hinj : Function.Injective
      (fun z : σ × Bool => (z.1, Bool.xor z.2 (f z.1))) := by
    rintro ⟨x, b⟩ ⟨y, c⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hxy, hbc⟩ := h
    subst hxy
    have hbc' : b = c := by
      have key : Bool.xor (Bool.xor b (f x)) (f x) =
          Bool.xor (Bool.xor c (f x)) (f x) := by rw [hbc]
      simpa using key
    rw [hbc']
  rw [Matrix.mem_unitaryGroup_iff]
  ext p q
  rw [Matrix.mul_apply]
  simp only [boolOracleMatrix, Matrix.of_apply, Matrix.star_apply, Matrix.one_apply]
  -- each row of the permutation matrix has a single `1`, at `Φ p`
  rw [Finset.sum_eq_single (p.1, Bool.xor p.2 (f p.1))]
  · by_cases hpq : p = q
    · simp [hpq]
    · have hne : (p.1, Bool.xor p.2 (f p.1)) ≠ (q.1, Bool.xor q.2 (f q.1)) :=
        fun h => hpq (hinj h)
      simp [hpq, hne]
  · intro b _ hb
    rw [if_neg hb, zero_mul]
  · intro hmem
    simp at hmem

/-! ## Ternary associativity (paper §5, p.15) -/

/-- A ternary operator on `X = Fin n`. -/
abbrev TernaryOp (n : ℕ) := Fin n × Fin n × Fin n → Fin n

/-- The paper's associativity law (p.15): both bracketings agree on every
5-tuple. -/
def IsAssociative {n : ℕ} (F : TernaryOp n) : Prop :=
  ∀ (a b c d e : Fin n),
    F (F (a, b, c), d, e) = F (a, F (b, c, d), e) ∧
    F (a, F (b, c, d), e) = F (a, b, F (c, d, e))

/-- A 5-tuple exhibiting a failure of associativity (cases (i) or (ii) of the
paper's proof of Theorem 12). -/
structure Witness5 (n : ℕ) where
  a1 : Fin n
  a2 : Fin n
  a3 : Fin n
  a4 : Fin n
  a5 : Fin n
deriving DecidableEq, Fintype

/-- The witness violates one of the two associativity equations. -/
def Witness5.violates {n : ℕ} (F : TernaryOp n) (w : Witness5 n) : Prop :=
  F (F (w.a1, w.a2, w.a3), w.a4, w.a5) ≠
      F (w.a1, F (w.a2, w.a3, w.a4), w.a5) ∨
  F (w.a1, F (w.a2, w.a3, w.a4), w.a5) ≠
      F (w.a1, w.a2, F (w.a3, w.a4, w.a5))

/-- Basis of the associativity-testing algorithm: candidate witness, flag,
queried triple, and the answer register (bit encoding of `F(a,b,c)`). -/
abbrev AssocIndex (n : ℕ) := Witness5 n × Bool × (Fin n × Fin n × Fin n)

/-- Computational basis including answer bits. -/
abbrev AssocState (n : ℕ) := AssocIndex n × (Fin n → Bool)

/-- Xor the bit encoding of `F(a,b,c)` into the answer register. -/
def assocOracleUpdate {n : ℕ} (F : TernaryOp n) (p : AssocState n) : AssocState n :=
  (p.1, fun i => Bool.xor (p.2 i) (Nat.testBit (F p.1.2.2).val i))

/-- The oracle `|a,b,c,y⟩ ↦ |a,b,c, y ⊕ F(a,b,c)⟩`. -/
def assocOracleMatrix {n : ℕ} (F : TernaryOp n) :
    Matrix (AssocState n) (AssocState n) ℂ :=
  Matrix.of (fun p q => if q = assocOracleUpdate F p then 1 else 0)

/-- Any fixed computational basis state of the associativity algorithm. -/
def assocInitialState {n : ℕ} (p₀ : AssocIndex n) : QState (AssocState n) :=
  Ket (p₀, fun _ => false)

/-- Measurement success set: a positive answer must carry a genuine violating
5-tuple; a negative answer is accepted exactly when `F` is associative. -/
def assocSuccessSet {n : ℕ} (F : TernaryOp n) : Finset (AssocState n) := by
  classical
  exact Finset.univ.filter (fun q => if q.1.2.1 then q.1.1.violates F else IsAssociative F)

end Qatlib.Papers.SubHypergraph13.MainResults
