/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Shared source model for Babai, *Graph Isomorphism in Quasipolynomial Time*

Fixed source: László Babai, arXiv:1512.03547v2 (author-revised v2.5, 2018-11-02),
verbatim from `assets/1512.03547v2.pdf`; page numbers in docstrings are the printed
page numbers of that PDF.

This file fixes the paper's *mathematical objects* once, so that every claim file can
state its theorem against the same definitions: k-ary relational structures, binary
coherent configurations (Definition 2.5.1), twins and symmetry defect (Definitions
2.4.2/2.4.7/2.4.8), uniform hypergraphs and their t-skeletons (Definition 2.3.2),
Johnson schemes, colored partitions (Definition 5.1.1), and String/Coset-Intersection
instances (Definition 3.1.2 and §1.1.1).

## Boundary / honesty note on running time

The paper works with *multiplicative cost* — the number of group operations as a
function of the instance size `n` — rather than with a Turing-machine model (see §1.1.2,
p. 4). We therefore record an algorithm together with its cost function as one datum
(`Algorithm`) and state the paper's complexity claims as existence of such a datum with
a bound. This is a statement-level interface: it does not pretend to model a machine
encoding, and it does not weaken the mathematical side of the theorem (which is the
existence of the reductions and constructions with the stated cost). Statements that
depend on such a cost model are marked accordingly in their docstrings.
-/

set_option autoImplicit false
noncomputable section

open Classical
open scoped Pointwise BigOperators

universe u

namespace Qatlib.Papers.GraphIsoBabai15.MainResults

/-! ## Abstract cost model -/

/-- An algorithm together with a cost function on instances. For the paper's purposes
the cost is the worst-case number of group operations ("multiplicative cost", §1.1.2). -/
structure Algorithm (I : Type u) (O : Type u) where
  run : I → O
  cost : I → ℕ

/-- `SolvesWithin P A t`: `A` answers every instance `i` correctly (`P i (A.run i)`)
and its cost never exceeds `t i`. -/
def SolvesWithin {I O : Type u} (P : I → O → Prop) (A : Algorithm I O) (t : I → ℕ) : Prop :=
  (∀ i, P i (A.run i)) ∧ ∀ i, A.cost i ≤ t i

/-- `SolvableWithin P t`: some algorithm solves `P` within cost `t`. -/
def SolvableWithin {I O : Type u} (P : I → O → Prop) (t : I → ℕ) : Prop :=
  ∃ A : Algorithm I O, SolvesWithin P A t

/-- Quasipolynomially bounded: `0 < f n ≤ C · exp(c · (log n)^c)` for all `n ≥ 2`
(§1.1.1, p. 4). -/
def Quasipolynomial (f : ℕ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ n : ℕ, 2 ≤ n → f n ≤ C * Real.exp (c * Real.rpow (Real.log (n : ℝ)) c)

/-- A function is bounded by a polynomial in `n` times a quasipolynomial in `n₀`
(Theorem 1.1.3, p. 4). -/
def PolyInNQuasipolyInN0 (f : ℕ → ℕ → ℝ) : Prop :=
  ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ n n0 : ℕ, 2 ≤ n → 2 ≤ n0 →
      f n n0 ≤ A * (n : ℝ) ^ a * (C * Real.exp (c * Real.rpow (Real.log (n0 : ℝ)) c))

/-! ## k-ary relational structures (Definition 2.3) -/

/-- A k-ary relational structure on a vertex set `V` with relation index type `ι`:
`rel i` is a `k`-ary relation. -/
structure RelStructure (ι : Type u) (k : ℕ) (V : Type u) where
  rel : ι → Set (Fin k → V)

variable {ι : Type u} {k : ℕ} {V W : Type u}

/-- `f : V ≃ W` is an isomorphism `X → Y` when it carries every relation of `X` to the
corresponding relation of `Y` (Definition 2.3, p. 13). -/
def RelIso (X : RelStructure ι k V) (Y : RelStructure ι k W) : Set (V ≃ W) :=
  {f | ∀ (i : ι) (x : Fin k → V), x ∈ X.rel i ↔ (fun j => f (x j)) ∈ Y.rel i}

/-- The automorphism group `Aut(X)`. -/
def RelAut (X : RelStructure ι k V) : Subgroup (Equiv.Perm V) where
  carrier := RelIso X X
  one_mem' := by
    intro i x
    simp [RelIso]
  mul_mem' := by
    intro f g hf hg i x
    show x ∈ X.rel i ↔ (fun j => (f * g) (x j)) ∈ X.rel i
    have h1 : (fun j => (f * g) (x j)) = (fun j => f (g (x j))) := rfl
    rw [h1]
    exact (hg i x).trans (hf i (fun j => g (x j)))
  inv_mem' := by
    intro f hf i x
    show x ∈ X.rel i ↔ (fun j => f⁻¹ (x j)) ∈ X.rel i
    have h := hf i (fun j => f⁻¹ (x j))
    have hx : (fun j => f (f⁻¹ (x j))) = x := by
      funext j
      simp
    rw [hx] at h
    exact h.symm

/-- Induced substructure on `Δ ⊆ V` (Definition 2.3.1, p. 13). -/
def RelStructure.induce (X : RelStructure ι k V) (Δ : Set V) : RelStructure ι k Δ where
  rel i := {x | (fun j => (x j : V)) ∈ X.rel i}

/-! ## Twins and symmetry defect (Definitions 2.4.2, 2.4.5, 2.4.7, 2.4.8) -/

/-- A 3-cycle moving `x ↦ y ↦ z ↦ x` (written as a product of two transpositions; any
conjugation of this product by the fixed points is the same 3-cycle up to orientation). -/
def threeCycle {Ω : Type u} [DecidableEq Ω] (x y z : Ω) : Equiv.Perm Ω :=
  Equiv.swap x y * Equiv.swap y z

/-- Strong twins for a permutation group: `x ≠ y` and the transposition `(x y)` lies
in `G` (Definition 2.4.2, p. 14). -/
def StrongTwin {Ω : Type u} [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω)) (x y : Ω) : Prop :=
  x ≠ y ∧ Equiv.swap x y ∈ G

/-- Weak twins: strong twins, or a 3-cycle on `x, y` and a third point lies in `G`
(Definition 2.4.2, p. 14). -/
def WeakTwin {Ω : Type u} [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω)) (x y : Ω) : Prop :=
  x ≠ y ∧ (Equiv.swap x y ∈ G ∨ ∃ z : Ω, z ≠ x ∧ z ≠ y ∧ threeCycle x y z ∈ G)

/-- `Ψ` is a strongly symmetrical set for `G`: `|Ψ| ≥ 2` and every pair of distinct
points of `Ψ` are strong twins (Definition 2.4.5, p. 14). -/
def StronglySymmetricSet {Ω : Type u} [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω))
    (Ψ : Finset Ω) : Prop :=
  2 ≤ Ψ.card ∧ ∀ x ∈ Ψ, ∀ y ∈ Ψ, x ≠ y → Equiv.swap x y ∈ G

/-- `Ψ` is a weakly symmetrical set for `G` (Definition 2.4.5, p. 14). -/
def WeaklySymmetricSet {Ω : Type u} [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω))
    (Ψ : Finset Ω) : Prop :=
  2 ≤ Ψ.card ∧ ∀ x ∈ Ψ, ∀ y ∈ Ψ, x ≠ y →
    (Equiv.swap x y ∈ G ∨ ∃ z : Ω, z ≠ x ∧ z ≠ y ∧ threeCycle x y z ∈ G)

/-- `G` has relative symmetry defect ≥ `α`: every complement of a weakly symmetrical
set has at least `α·n` points (`defect = min{|T| : Ω \ T weakly symmetrical}`,
Definition 2.4.7, p. 14; phrased without the `min`). -/
def RelativeDefectAtLeast {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    (G : Subgroup (Equiv.Perm Ω)) (α : ℝ) : Prop :=
  ∀ T : Finset Ω, WeaklySymmetricSet G (Finset.univ \ T) →
    α * (Fintype.card Ω : ℝ) ≤ (T.card : ℝ)

/-! ## Binary coherent configurations (Definition 2.5.1, pp. 16–17) -/

/-- A (classical, binary) coherent configuration on `V`: a partition of `V × V` into
nonempty *cells* indexed by `ι`, closed under transposition, with intersection numbers
`p(i,j,k)` (Definition 2.3.5/2.5.1: defining conditions (i)–(iv), p. 16). `cell x y` is the color of
the ordered pair `(x,y)`. -/
structure CoherentConfig (V : Type u) [Fintype V] [DecidableEq V] where
  ι : Type u
  [fintypeι : Fintype ι]
  [decι : DecidableEq ι]
  cell : V → V → ι
  /-- (i) every cell is nonempty. -/
  nonempty : ∀ i : ι, ∃ x y : V, cell x y = i
  /-- (ii) each cell lies inside or outside the diagonal. -/
  diag_or_off : ∀ i : ι,
    (∀ x y : V, cell x y = i → x = y) ∨ (∀ x y : V, cell x y = i → x ≠ y)
  /-- (iii) transposes: `cell y x = trans (cell x y)`. -/
  trans : ι → ι
  trans_spec : ∀ x y : V, cell y x = trans (cell x y)
  /-- (iv) intersection numbers. -/
  p : ι → ι → ι → ℕ
  p_spec : ∀ (x y : V) (i j kk : ι), cell x y = kk →
    (Finset.univ.filter (fun z : V => cell x z = i ∧ cell z y = j)).card = p i j kk

namespace CoherentConfig

variable {V : Type u} [Fintype V] [DecidableEq V] (X : CoherentConfig V)

/-- Vertex color `c(x) = c(x,x)` (p. 16). -/
def color (x : V) : X.ι := X.cell x x

/-- Two vertices have the same vertex color. -/
def SameColor (x y : V) : Prop := X.cell x x = X.cell y y

/-- Vertex-color class of `x`. -/
def colorClass (x : V) : Set V := {y | X.cell y y = X.cell x x}

/-- The constituent digraph `X_i` as a relation. -/
def constituent (i : X.ι) : Set (V × V) := {(a, b) | X.cell a b = i}

/-- Out-degree of `x` in the constituent `X_i`. -/
def outDeg (i : X.ι) (x : V) : ℕ := (Finset.univ.filter (fun y : V => X.cell x y = i)).card

/-- In-degree of `x` in the constituent `X_i`. -/
def inDeg (i : X.ι) (x : V) : ℕ := (Finset.univ.filter (fun y : V => X.cell y x = i)).card

/-- The underlying binary relational structure (relations indexed by cells). -/
def toRelStructure : RelStructure X.ι 2 V where
  rel i := {p | X.cell (p 0) (p 1) = i}

/-- Strong twins in a coherent configuration, via its automorphism group
(Definition 2.4.8, p. 15). -/
def StrongTwinCC (x y : V) : Prop := StrongTwin (RelAut X.toRelStructure) x y

/-- Weak twins in a coherent configuration. -/
def WeakTwinCC (x y : V) : Prop := WeakTwin (RelAut X.toRelStructure) x y

/-- A constituent is *homogeneous* when it is contained in a single vertex-color class
(i.e. it is an edge set inside one color class). -/
def HomogeneousConstituent (i : X.ι) : Prop :=
  ∀ x y : V, X.cell x y = i → X.cell x x = X.cell y y

/-- A constituent is *bipartite* between color classes `j` and `l` when it relates
only points of color `j` to points of color `l` with `j ≠ l`. -/
def BipartiteConstituent (i j l : X.ι) : Prop :=
  j ≠ l ∧ ∀ x y : V, X.cell x y = i → (X.cell x x = j ∧ X.cell y y = l)

end CoherentConfig

/-! ## Uniform hypergraphs and skeletons (Definitions 2.3.2, 2.6) -/

/-- A `d`-uniform hypergraph on `V` given by its (finite) set of edges. -/
structure Hypergraph (V : Type u) [Fintype V] [DecidableEq V] where
  d : ℕ
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = d

namespace Hypergraph

variable {V : Type u} [Fintype V] [DecidableEq V] (H : Hypergraph V)

/-- The number of edges containing `v`. -/
def degree (v : V) : ℕ := (H.edges.filter (fun e => v ∈ e)).card

/-- Regular: all degrees are equal. -/
def Regular : Prop := ∃ r : ℕ, ∀ v : V, H.degree v = r

/-- The t-skeleton: the `t`-uniform hypergraph whose edges are the `t`-subsets of the
edges of `H` (Definition 2.3.2, p. 13, unordered form). -/
def skeleton (t : ℕ) : Finset (Finset V) :=
  H.edges.biUnion (fun e => e.powersetCard t)

/-- The automorphism group of the hypergraph: permutations of `V` that preserve the
edge set. -/
def aut : Subgroup (Equiv.Perm V) where
  carrier := {f | ∀ e : Finset V, e ∈ H.edges ↔ e.image f ∈ H.edges}
  one_mem' := by
    intro e
    simp
  mul_mem' := by
    intro f g hf hg e
    show e ∈ H.edges ↔ Finset.image (⇑(f * g)) e ∈ H.edges
    have hmul : (⇑(f * g) : V → V) = ⇑f ∘ ⇑g := rfl
    rw [hmul, ← Finset.image_image]
    exact (hg e).trans (hf (e.image ⇑g))
  inv_mem' := by
    intro f hf e
    show e ∈ H.edges ↔ Finset.image (⇑f⁻¹) e ∈ H.edges
    have h := hf (Finset.image (⇑f⁻¹) e)
    rw [Finset.image_image] at h
    have hcomp : (⇑f ∘ ⇑f⁻¹ : V → V) = id := by
      funext x
      simp
    simp only [hcomp, Finset.image_id] at h
    exact h.symm

end Hypergraph

/-! ## Johnson schemes -/

/-- The vertex set of the Johnson scheme `J(m,t)`: the `t`-subsets of `Fin m`. -/
abbrev JohnsonVertex (m t : ℕ) := {s : Finset (Fin m) // s.card = t}

/-- The Johnson graph adjacency relation: `|s ∩ s'| = t - 1`. -/
def JohnsonAdj {m : ℕ} (t : ℕ) (s s' : Finset (Fin m)) : Prop := (s ∩ s').card + 1 = t

/-- The Johnson scheme viewed as a binary relational structure on `t`-subsets of
`Fin m`. -/
def JohnsonStructure (m t : ℕ) : RelStructure (Fin 2) 2 (JohnsonVertex m t) where
  rel i :=
    if i = 0 then
      {p | (p 0).1 = (p 1).1}
    else
      {p | JohnsonAdj t (p 0).1 (p 1).1}

/-! ## Colored partitions (Definition 5.1.1, p. 35) -/

/-- A colored partition of a finite set: a coloring together with, in each color class,
a partition (a block label). -/
structure ColoredPartition (Ω : Type u) [Fintype Ω] [DecidableEq Ω] where
  color : Ω → ℕ
  block : Ω → ℕ
  block_respects_color : ∀ x y : Ω, block x = block y → color x = color y

namespace ColoredPartition

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

/-- Size of the color class of `c`. -/
def colorClassSize (P : ColoredPartition Ω) (c : ℕ) : ℕ :=
  (Finset.univ.filter (fun x => P.color x = c)).card

/-- Size of the block labelled `b`. -/
def blockSize (P : ColoredPartition Ω) (b : ℕ) : ℕ :=
  (Finset.univ.filter (fun x => P.block x = b)).card

/-- `P` is admissible: in every color class of size ≥ 2, all blocks have size ≥ 2
(a block may equal the whole color class; Definition 5.1.1, p. 35). -/
def Admissible (P : ColoredPartition Ω) : Prop :=
  ∀ c : ℕ, 2 ≤ P.colorClassSize c →
    ∀ b : ℕ, (∃ x : Ω, P.color x = c ∧ P.block x = b) → 2 ≤ P.blockSize b

/-- `P` is a colored α-partition: admissible with every block of size `≤ α|Ω|`
(Definition 5.1.1, p. 35). -/
def IsAlphaPartition (P : ColoredPartition Ω) (α : ℝ) : Prop :=
  P.Admissible ∧ ∀ b : ℕ, (P.blockSize b : ℝ) ≤ α * (Fintype.card Ω : ℝ)

/-- A color class that contains all but at most `α|Ω|` points, i.e. `ρ(P) ≤ α|Ω|`
phrased with the largest color-class size. -/
def IsAlphaColoring (P : ColoredPartition Ω) (α : ℝ) : Prop :=
  ∀ c : ℕ, (P.colorClassSize c : ℝ) ≤ α * (Fintype.card Ω : ℝ)

end ColoredPartition

/-! ## String Isomorphism and related instances (§1.1.1, Definition 3.1.2) -/

/-- A String Isomorphism instance with domain `Ω`, alphabet `Σ`, permutation group
given by a generator list, and strings `x, y`. -/
structure SIInstance (Ω Alph : Type u) [Fintype Ω] [DecidableEq Ω]
    [Fintype Alph] [DecidableEq Alph] where
  gens : List (Equiv.Perm Ω)
  x : Ω → Alph
  y : Ω → Alph

/-- The subgroup generated by `inst.gens`. -/
def SIInstance.group {Ω Alph : Type u} [Fintype Ω] [DecidableEq Ω] [Fintype Alph] [DecidableEq Alph]
    (inst : SIInstance Ω Alph) : Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure (inst.gens.toFinset : Set (Equiv.Perm Ω))

/-- `σ` transforms `x` into `y`: `y = x ∘ σ⁻¹` (paper convention `x^σ`). -/
def Transforms {Ω Alph : Type u} [Fintype Ω] [DecidableEq Ω] [Fintype Alph] [DecidableEq Alph]
    (inst : SIInstance Ω Alph) (σ : Equiv.Perm Ω) : Prop :=
  ∀ a : Ω, inst.y a = inst.x (σ.symm a)

/-- `StringIsoSolution inst out`: `out` is a valid SI output — `none` when no element
of `G` transforms `x` into `y`, `some σ` with `σ ∈ G` transforming `x` into `y`
otherwise. -/
def StringIsoSolution {Ω Alph : Type u} [Fintype Ω] [DecidableEq Ω] [Fintype Alph] [DecidableEq Alph]
    (inst : SIInstance Ω Alph) (out : Option (Equiv.Perm Ω)) : Prop :=
  match out with
  | none => ¬ ∃ σ : Equiv.Perm Ω, σ ∈ inst.group ∧ Transforms inst σ
  | some σ => σ ∈ inst.group ∧ Transforms inst σ

/-- A graph isomorphism instance: two Boolean adjacency matrices on the same vertex
set. -/
structure GIInstance (V : Type u) [Fintype V] [DecidableEq V] where
  A : V → V → Bool
  B : V → V → Bool

/-- `p` is an isomorphism `A ≅ B`. -/
def GraphIso {V : Type u} [Fintype V] [DecidableEq V] (i : GIInstance V)
    (p : Equiv.Perm V) : Prop :=
  ∀ a b : V, i.B (p a) (p b) = i.A a b

/-- A coset-intersection instance: two cosets of permutation subgroups over `V`. -/
structure CIInstance (V : Type u) [Fintype V] [DecidableEq V] where
  G : Subgroup (Equiv.Perm V)
  H : Subgroup (Equiv.Perm V)
  a : Equiv.Perm V
  b : Equiv.Perm V

/-- The two cosets intersect (Definition 2.4.11-style `CI`). -/
def CIInstance.Intersects {V : Type u} [Fintype V] [DecidableEq V]
    (i : CIInstance V) : Prop :=
  ((i.a • (i.G : Set (Equiv.Perm V))) ∩ (i.b • (i.H : Set (Equiv.Perm V)))).Nonempty

/-- The largest orbit length `n₀(G)` of a permutation group (Theorem 1.1.3, p. 4). -/
def largestOrbit {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    (G : Subgroup (Equiv.Perm Ω)) : ℕ :=
  Finset.univ.sup (fun x : Ω =>
    (Finset.univ.filter (fun y : Ω => ∃ g : G, (g : Equiv.Perm Ω) • x = y)).card)

/-- `G` is a permutation group on `Ω` but we only need its action; this records a
representative group for statements about `S(Ω)`. -/
abbrev fullSymmetric (Ω : Type u) [Fintype Ω] [DecidableEq Ω] : Subgroup (Equiv.Perm Ω) := ⊤

/-! ## Index bounds -/

/-- The index `[Aut(X) : Aut(X) ∩ Aut(Y)]` is quasipolynomially bounded in `|V|`
(Theorem 1.3.3, p. 9). -/
def QuasipolyIndexBound {V : Type u} [Fintype V] [DecidableEq V]
    (G H : Subgroup (Equiv.Perm V)) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ((G ⊓ H).index : ℝ) ≤ C * Real.exp (c * Real.rpow (Real.log (Fintype.card V : ℝ)) c)

end Qatlib.Papers.GraphIsoBabai15.MainResults
