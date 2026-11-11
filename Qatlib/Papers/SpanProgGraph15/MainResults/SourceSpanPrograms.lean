/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Span-program-based quantum algorithms for graph bipartiteness and connectivity

Fixed source: arXiv:1510.07825v1 (27 Oct 2015), A. Āriņš,
*Span-program-based quantum algorithms for graph bipartiteness and connectivity*.

This module fixes the two concrete span programs of the paper together with the
vocabulary used by the paper's witness-size definitions (Definition 1 and
Definition 2, §2.1, p. 2):

* `BipBasis n`, the `2n²+1`-dimensional space `{|0⟩} ∪ {|v_{k,b}⟩ : v,k ∈ [1..n], b ∈ {0,1}}`
  of span program `P₁` (§3, p. 3);
* `ConnBasis n`, the `n²−1`-dimensional space `{|v_k⟩ : v ∈ [0..n], k ∈ [2..n]}`
  of span program `P₂` (§4, p. 5);
* their free vectors, edge vectors, target vectors, availability predicates and
  generator families `BipGen`/`ConnGen` that index every declared program vector
  (so that the negative witness size of Definition 2(2) can be summed over all
  program vectors, as the paper does in Eqs. (2) and (5));
* input-independent interfaces `PosWitnessData`, `NegWitnessData`, `posNorm`,
  `negNorm` encoding Definition 2.

The graph input is a `SimpleGraph (Fin n)`; the paper's adjacency-matrix query
model is the `GraphQuery.EdgeQuery` block (`G.Adj u v` is the query answer
`x_{u,v}`).  All statements here are for `n ≥ 1` vertices, matching the paper's
`n = |G|`.

The main declarations are in `BipartiteProgram`, `ConnectivityProgram`,
`SpaceCost` and `MainResults`.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators
open Finset

namespace Qatlib.Papers.SpanProgGraph15.MainResults

/-! ## Generic span-program witness vocabulary (Definition 2, p. 2)

`vec : ι → H → ℂ` is an indexed family of program vectors (`ι` ranges over every
declared vector, including the free ones), `avail : ι → Prop` marks the vectors
available on the current input, and `t : H → ℂ` is the target vector.

For a positive witness, Definition 2(1) asks for coefficients `c` supported on
available vectors with `Σ c_v • v = t`; the positive witness size is `Σ ‖c_v‖²`.

For a negative witness, Definition 2(2) asks for a dual vector `u` with
`⟨u|t⟩ = 1` and `⟨u|v⟩ = 0` for every available `v`; the negative witness size is
`Σ ‖⟨u|v⟩‖²` summed over *all* declared program vectors `v ∈ V` (the vectors not
available on the input are exactly the ones contributing). -/

/-- The coefficient pairing `⟨u|x⟩ = Σ_y conj(u y) · x y` used for negative witnesses. -/
def pair {H : Type} [Fintype H] (u x : H → ℂ) : ℂ := ∑ y, star (u y) * x y

/-- The pairing against the zero vector vanishes (`⟨u|0⟩ = 0`). -/
@[simp] theorem pair_zero {H : Type} [Fintype H] (u : H → ℂ) : pair u 0 = 0 := by
  simp [pair]

/-- The pairing `⟨u|·⟩` is additive in its second argument, as required of a
witness pairing (Definition 2, p. 2). -/
theorem pair_add {H : Type} [Fintype H] (u x y : H → ℂ) :
    pair u (x + y) = pair u x + pair u y := by
  simp [pair, mul_add, Finset.sum_add_distrib]

/-- The pairing `⟨u|·⟩` is complex-linear in its second argument (Definition 2,
p. 2). -/
theorem pair_smul {H : Type} [Fintype H] (u x : H → ℂ) (c : ℂ) :
    pair u (c • x) = c * pair u x := by
  simp only [pair, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Positive witness with coefficients `c` (Definition 2(1)): coefficients are
supported on available vectors and `Σ c_v • v = t`. -/
def PosWitnessData {ι H : Type} [Fintype ι]
    (vec : ι → H → ℂ) (avail : ι → Prop) (t : H → ℂ) (c : ι → ℂ) : Prop :=
  (∀ i, c i ≠ 0 → avail i) ∧ (∑ i, c i • vec i) = t

/-- Squared norm `Σ ‖c_v‖²` of a positive witness, Definition 2(1). -/
def posNorm {ι : Type} [Fintype ι] (c : ι → ℂ) : ℝ := ∑ i, ‖c i‖ ^ 2

/-- Negative witness (Definition 2(2)): `⟨u|t⟩ = 1` and `⟨u|v⟩ = 0` for all
available program vectors `v`. -/
def NegWitnessData {ι H : Type} [Fintype ι] [Fintype H]
    (vec : ι → H → ℂ) (avail : ι → Prop) (t : H → ℂ) (u : H → ℂ) : Prop :=
  pair u t = 1 ∧ ∀ i, avail i → pair u (vec i) = 0

/-- Negative witness size, Definition 2(2): the squared pairing summed over all
declared program vectors (the unavailable ones are the only ones that can
contribute for a negative witness). -/
def negNorm {ι H : Type} [Fintype ι] [Fintype H] (vec : ι → H → ℂ) (u : H → ℂ) : ℝ :=
  ∑ i, ‖pair u (vec i)‖ ^ 2

/-! ## §3 — span program `P₁` for graph bipartiteness (p. 3)

Basis type `Unit ⊕ (Fin n × Bool × Fin n)` with `Sum.inl ()` the special vector
`|0⟩` and `Sum.inr (v,b,k)` the vector `|v_{k,b}⟩`.  Thus the dimension is
`1 + 2n² = 2n²+1`, as printed. -/

/-- The `2n²+1` dimensional basis `{|0⟩} ∪ {|v_{k,b}⟩}` of `P₁` (§3, p. 3). -/
abbrev BipBasis (n : ℕ) : Type := Unit ⊕ (Fin n × Bool × Fin n)

/-- The special basis vector `|0⟩`. -/
def bipZero (n : ℕ) : BipBasis n → ℂ := Pi.single (Sum.inl ()) 1

/-- The basis vector `|v_{k,b}⟩`. -/
def bipBasisVec (n : ℕ) (v : Fin n) (b : Bool) (k : Fin n) : BipBasis n → ℂ :=
  Pi.single (Sum.inr (v, b, k)) 1

/-- The free vector `|0⟩ + |k_{k,0}⟩ + |k_{k,1}⟩` available for every `k` (§3, p. 3). -/
def bipFree (n : ℕ) (k : Fin n) : BipBasis n → ℂ :=
  bipZero n + bipBasisVec n k false k + bipBasisVec n k true k

/-- The edge vector `|u_{k,0}⟩ + |v_{k,1}⟩` (§3, p. 3). -/
def bipEdge0 (n : ℕ) (k : Fin n) (u v : Fin n) : BipBasis n → ℂ :=
  bipBasisVec n u false k + bipBasisVec n v true k

/-- The edge vector `|u_{k,1}⟩ + |v_{k,0}⟩` (§3, p. 3). -/
def bipEdge1 (n : ℕ) (k : Fin n) (u v : Fin n) : BipBasis n → ℂ :=
  bipBasisVec n u true k + bipBasisVec n v false k

/-- The target vector `|0⟩` of `P₁`. -/
def bipTarget (n : ℕ) : BipBasis n → ℂ := bipZero n

/-- Generator index of `P₁`: `Sum.inl k` is the free vector of block `k`;
`Sum.inr (k,b,(u,v))` is the `b`-parity edge vector of block `k` for the ordered
pair `(u,v)` (the two orientations of an undirected edge give the same two
vectors, so ordered pairs faithfully index the paper's edge vectors). -/
abbrev BipGen (n : ℕ) : Type := Fin n ⊕ (Fin n × Bool × (Fin n × Fin n))

/-- The program vector indexed by a `BipGen` generator. -/
def bipGenVec (n : ℕ) : BipGen n → (BipBasis n → ℂ)
  | Sum.inl k => bipFree n k
  | Sum.inr (k, b, p) => if b then bipEdge1 n k p.1 p.2 else bipEdge0 n k p.1 p.2

/-- Availability of the `P₁` generators on the graph `G`: free vectors are always
available; an edge vector is available iff `G.Adj u v` (the paper's `x_{u,v}=1`). -/
def bipGenAvail (n : ℕ) (G : SimpleGraph (Fin n)) : BipGen n → Prop
  | Sum.inl _ => True
  | Sum.inr (_, _, p) => G.Adj p.1 p.2

/-- The span of the available `P₁` generators, i.e. `span(V(x))` of Definition 1. -/
def bipSpan (n : ℕ) (G : SimpleGraph (Fin n)) : Submodule ℂ (BipBasis n → ℂ) :=
  Submodule.span ℂ (Set.range (fun i : {i : BipGen n // bipGenAvail n G i} => bipGenVec n i.1))

/-- Every available `P₁` generator belongs to `bipSpan` (§3, p. 3). -/
theorem bipGenVec_mem_span {n : ℕ} {G : SimpleGraph (Fin n)} {i : BipGen n}
    (h : bipGenAvail n G i) : bipGenVec n i ∈ bipSpan n G :=
  Submodule.subset_span ⟨⟨i, h⟩, rfl⟩

/-- A positive witness for `P₁` makes the target lie in the span of the available
vectors (Definition 1). -/
theorem mem_span_of_posWitness {n : ℕ} {G : SimpleGraph (Fin n)} {c : BipGen n → ℂ}
    (h : PosWitnessData (bipGenVec n) (bipGenAvail n G) (bipTarget n) c) :
    bipTarget n ∈ bipSpan n G := by
  rw [← h.2]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hc : c i = 0
  · simp [hc]
  · exact Submodule.smul_mem _ _ (bipGenVec_mem_span (h.1 i hc))

/-- A negative witness certifies that the target is outside the span of the
available vectors: the pairing functional vanishes on every generator but takes
value one on the target. -/
theorem not_mem_span_of_negWitness {n : ℕ} {G : SimpleGraph (Fin n)} {u : BipBasis n → ℂ}
    (h : NegWitnessData (bipGenVec n) (bipGenAvail n G) (bipTarget n) u) :
    bipTarget n ∉ bipSpan n G := by
  intro hmem
  have hker : bipSpan n G ≤ LinearMap.ker
      ({ toFun := fun x => pair u x
         map_add' := by intro x y; exact pair_add u x y
         map_smul' := by intro c x; exact pair_smul u x c } :
        (BipBasis n → ℂ) →ₗ[ℂ] ℂ) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact h.2 j j.2
  have hzero := hker hmem
  change pair u (bipTarget n) = 0 at hzero
  rw [h.1] at hzero
  exact one_ne_zero hzero

/-! ### Dimensions and generator counts -/

/-- The `P₁` space has dimension `2n²+1` (§3, p. 3). -/
theorem card_bipBasis (n : ℕ) : Fintype.card (BipBasis n) = 2 * n ^ 2 + 1 := by
  simp [BipBasis]
  ring

/-- `P₁` declares `n` free vectors and `2 n³` edge vectors, i.e. `n + 2n³` in the
ordered-pair indexing used here (the paper counts the `n³` undirected edge
vectors and adds the `n` free ones, Eq. (2), p. 4). -/
theorem card_bipGen (n : ℕ) : Fintype.card (BipGen n) = n + 2 * n ^ 3 := by
  simp [BipGen]
  ring

/-! ## §4 — span program `P₂` for graph connectivity (p. 5)

Basis type `Fin (n+1) × Fin (n-1)`: the first coordinate is the paper's vertex
index `v ∈ [0..n]`, the second the subroutine index `k ∈ [2..n]` (encoded as
`k = i+2`).  The dimension is `(n+1)(n−1) = n²−1`, matching the paper.  The
graph's vertices `Fin n` are embedded as paper vertices `1..n` by `Fin.succ`. -/

/-- The `n²−1` dimensional basis `{|v_k⟩ : v ∈ [0..n], k ∈ [2..n]}` of `P₂`
(§4, p. 5). -/
abbrev ConnBasis (n : ℕ) : Type := Fin (n + 1) × Fin (n - 1)

/-- The paper's vertex `1` inside `Fin (n+1)` (requires `n ≥ 1`). -/
def connOne (n : ℕ) (hn : 1 ≤ n) : Fin (n + 1) := ⟨1, by omega⟩

/-- The graph vertex `k.val+1 : Fin n` corresponding to the paper's subroutine
index `k.val+2 ∈ [2..n]`. -/
def connKIdx (n : ℕ) (k : Fin (n - 1)) : Fin n := ⟨k.val + 1, by omega⟩

/-- The paper's vertex `k.val+2` inside `Fin (n+1)`. -/
def connK (n : ℕ) (k : Fin (n - 1)) : Fin (n + 1) := Fin.succ (connKIdx n k)

/-- The basis vector `|v_k⟩`. -/
def connBasisVec (n : ℕ) (v : Fin (n + 1)) (k : Fin (n - 1)) : ConnBasis n → ℂ :=
  Pi.single (v, k) 1

/-- The target vector `|t⟩ = |0_2⟩ + |0_3⟩ + ⋯ + |0_n⟩` (§4, p. 5). -/
def connTarget (n : ℕ) : ConnBasis n → ℂ := fun x => if x.1 = 0 then 1 else 0

/-- The free vector `|0_k⟩ + |1_k⟩ − |k_k⟩` (§4, p. 5). -/
def connFree (n : ℕ) (hn : 1 ≤ n) (k : Fin (n - 1)) : ConnBasis n → ℂ :=
  connBasisVec n 0 k + connBasisVec n (connOne n hn) k - connBasisVec n (connK n k) k

/-- The edge vector `|u_k⟩ − |v_k⟩` (§4, p. 5). -/
def connEdge (n : ℕ) (k : Fin (n - 1)) (u v : Fin n) : ConnBasis n → ℂ :=
  connBasisVec n (Fin.succ u) k - connBasisVec n (Fin.succ v) k

/-- Generator index of `P₂`: free vectors and oriented edge vectors. -/
abbrev ConnGen (n : ℕ) : Type := Fin (n - 1) ⊕ (Fin (n - 1) × Fin n × Fin n)

/-- The program vector indexed by a `ConnGen` generator. -/
def connGenVec (n : ℕ) (hn : 1 ≤ n) : ConnGen n → (ConnBasis n → ℂ)
  | Sum.inl k => connFree n hn k
  | Sum.inr (k, u, v) => connEdge n k u v

/-- Availability of the `P₂` generators: free vectors always, edge vectors iff
`G.Adj u v`. -/
def connGenAvail (n : ℕ) (G : SimpleGraph (Fin n)) : ConnGen n → Prop
  | Sum.inl _ => True
  | Sum.inr (_, u, v) => G.Adj u v

/-- The span of the available `P₂` generators. -/
def connSpan (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) :
    Submodule ℂ (ConnBasis n → ℂ) :=
  Submodule.span ℂ (Set.range (fun i : {i : ConnGen n // connGenAvail n G i} =>
    connGenVec n hn i.1))

/-- Every available `P₂` generator belongs to `connSpan` (§4, p. 5). -/
theorem connGenVec_mem_span {n : ℕ} {hn : 1 ≤ n} {G : SimpleGraph (Fin n)} {i : ConnGen n}
    (h : connGenAvail n G i) : connGenVec n hn i ∈ connSpan n hn G :=
  Submodule.subset_span ⟨⟨i, h⟩, rfl⟩

/-- A positive witness for `P₂` puts the target in the span of the available
vectors. -/
theorem mem_connSpan_of_posWitness {n : ℕ} {hn : 1 ≤ n} {G : SimpleGraph (Fin n)}
    {c : ConnGen n → ℂ}
    (h : PosWitnessData (connGenVec n hn) (connGenAvail n G) (connTarget n) c) :
    connTarget n ∈ connSpan n hn G := by
  rw [← h.2]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hc : c i = 0
  · simp [hc]
  · exact Submodule.smul_mem _ _ (connGenVec_mem_span (h.1 i hc))

/-- A negative witness for `P₂` certifies that the target is outside the span of
the available vectors. -/
theorem not_mem_connSpan_of_negWitness {n : ℕ} {hn : 1 ≤ n} {G : SimpleGraph (Fin n)}
    {u : ConnBasis n → ℂ}
    (h : NegWitnessData (connGenVec n hn) (connGenAvail n G) (connTarget n) u) :
    connTarget n ∉ connSpan n hn G := by
  intro hmem
  have hker : connSpan n hn G ≤ LinearMap.ker
      ({ toFun := fun x => pair u x
         map_add' := by intro x y; exact pair_add u x y
         map_smul' := by intro c x; exact pair_smul u x c } :
        (ConnBasis n → ℂ) →ₗ[ℂ] ℂ) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact h.2 j j.2
  have hzero := hker hmem
  change pair u (connTarget n) = 0 at hzero
  rw [h.1] at hzero
  exact one_ne_zero hzero

/-- The `P₂` space has dimension `n²−1` (§4, p. 5). -/
theorem card_connBasis (n : ℕ) (hn : 1 ≤ n) : Fintype.card (ConnBasis n) = n ^ 2 - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [ConnBasis, Fintype.card_prod, Fintype.card_fin]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  ring_nf
  omega

/-- `P₂` declares `n−1` free vectors plus `(n−1)·n²` edge vectors. -/
theorem card_connGen (n : ℕ) : Fintype.card (ConnGen n) = (n - 1) + (n - 1) * n ^ 2 := by
  simp only [ConnGen, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

end Qatlib.Papers.SpanProgGraph15.MainResults
