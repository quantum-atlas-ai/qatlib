/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphIsoBabai15.MainResults.SourceModel
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.GroupTheory.SpecificGroups.Alternating

set_option backward.isDefEq.respectTransparency false

/-!
# Shared interface for the paper-layer statements of Babai's paper

Fixed source: Babai, *Graph Isomorphism in Quasipolynomial Time*, arXiv:1512.03547v2.
This file collects the cost bounds, canonicity notions, primitivity notions and defect
notions used by the claims of §§4–10, so that every claim file states its result through
the same vocabulary.

Conventions (paper Definition 4.0.4): a reduction "at multiplicative cost `s`" is a
family of structures produced per instance; the multiplicative cost is the number of
smaller isomorphism problems queried, and `Algorithm.cost` (from `SourceModel`) counts
them. Polynomial additive overhead is recorded by `PolyCostBound`.

Boundary note. The algorithm interface is the abstract `Algorithm (I O)` of
`SourceModel`: it records an input-to-output map together with an integer cost, not a
Turing machine. "Canonical" means invariant under the relevant automorphism group
(Definition 4.0.1/5.1.2, pp. 33–35); for objects with individualized vertices we use the
automorphism group of the individualized structure, which fixes the individualized
points.
-/

set_option autoImplicit false
noncomputable section

open Classical
open scoped Pointwise BigOperators

universe u

namespace Qatlib.Papers.GraphIsoBabai15.MainResults.SectionCore

/-! ## Cost bounds -/

/-- A polynomial upper bound `C·(n+2)^c` on the cost of `A`. -/
def PolyCostBound {I O : Type u} (size : I → ℕ) (A : Algorithm I O) : Prop :=
  ∃ c C : ℕ, ∀ i : I, A.cost i ≤ C * (size i + 2) ^ c

/-- A quasipolynomial upper bound `q(n)` on the cost of `A`. -/
def QuasipolyCostBound {I O : Type u} (size : I → ℕ) (A : Algorithm I O) : Prop :=
  ∃ q : ℕ → ℕ, Quasipolynomial (fun n => (q n : ℝ)) ∧ ∀ i : I, A.cost i ≤ q (size i)

/-- A multiplicative cost bound `c·n` on the cost of `A`. -/
def MulCostBound {I O : Type u} (size : I → ℕ) (A : Algorithm I O) (c : ℕ) : Prop :=
  ∀ i : I, A.cost i ≤ c * size i

/-- A cost bound of the form `n^{O(k)}` with `k` an instance parameter
(Theorem 6.1.1: "in time `n^{O(k)}`"). -/
def NKCostBound {I O : Type u} (size k : I → ℕ) (A : Algorithm I O) : Prop :=
  ∃ c : ℕ, ∀ i : I, A.cost i ≤ (size i + 2) ^ (c * (k i + 1))

/-- A cost bound of the form `q(n)·n^{O(k)}` (Theorem 7.3.3). -/
def QuasipolyNKCostBound {I O : Type u} (size k : I → ℕ) (A : Algorithm I O) : Prop :=
  ∃ q : ℕ → ℕ, Quasipolynomial (fun n => (q n : ℝ)) ∧
    ∃ c : ℕ, ∀ i : I, A.cost i ≤ q (size i) * (size i + 2) ^ (c * (k i + 1))

/-! ## Canonicity -/

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

/-- A finset is `G`-invariant. -/
def InvariantFinset (G : Subgroup (Equiv.Perm Ω)) (W : Finset Ω) : Prop :=
  ∀ γ : Equiv.Perm Ω, γ ∈ G → W.image γ = W

/-- A canonical colored `α`-partition (Definitions 4.0.1/5.1.2, pp. 33–35): an admissible
colored partition with all blocks of size `≤ α|Ω|`, invariant under `G`. -/
def CanonicalColoredPartition (G : Subgroup (Equiv.Perm Ω)) (α : ℝ) : Prop :=
  ∃ P : ColoredPartition Ω, P.IsAlphaPartition α ∧
    ∀ γ : Equiv.Perm Ω, γ ∈ G →
      ∀ x : Ω, P.color (γ x) = P.color x ∧ P.block (γ x) = P.block x

/-- `G`-canonically embedded nontrivial Johnson scheme on `W ⊆ Ω` of relative size `≥ β`
(Theorem 7.3.1 (b)): `W` has `≥ βn` points, is `G`-invariant, and its points are in
bijection with the `t`-subsets of `[m]` for a nontrivial Johnson scheme (`2 ≤ t`,
`2t+1 ≤ m`). -/
def HasEmbeddedJohnson (G : Subgroup (Equiv.Perm Ω)) (W : Finset Ω) (β : ℝ) : Prop :=
  β * (Fintype.card Ω : ℝ) ≤ (W.card : ℝ) ∧ InvariantFinset G W ∧
    ∃ m t : ℕ, 2 ≤ t ∧ 2 * t + 1 ≤ m ∧ Nonempty ({x // x ∈ W} ≃ JohnsonVertex m t)

/-- A colored equipartition (Definition 5.1.1, p. 35): all blocks within the same color
class have equal size. -/
def IsEquipartition (P : ColoredPartition Ω) : Prop :=
  ∀ c b₁ b₂ : ℕ, (∃ x : Ω, P.color x = c ∧ P.block x = b₁) →
    (∃ y : Ω, P.color y = c ∧ P.block y = b₂) → P.blockSize b₁ = P.blockSize b₂

/-! ## Primitivity -/

/-- `B` is a block of imprimitivity for `G` (Definition 3.1? : a nonempty proper subset
whose translates are pairwise disjoint or equal). -/
def IsBlock (G : Subgroup (Equiv.Perm Ω)) (B : Finset Ω) : Prop :=
  B.Nonempty ∧ B.card < Fintype.card Ω ∧
    ∀ γ : Equiv.Perm Ω, γ ∈ G → B.image γ = B ∨ Disjoint (B.image γ) B

/-- `G` is primitive: its only blocks of imprimitivity are singletons. -/
def IsPrimitiveGroup (G : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ B : Finset Ω, IsBlock G B → B.card = 1

/-- A system of imprimitivity (a `G`-invariant partition of `Ω` into nonempty blocks). -/
def IsSystemOfImprimitivity (G : Subgroup (Equiv.Perm Ω)) (B : Finset (Finset Ω)) : Prop :=
  (∀ b ∈ B, b.Nonempty) ∧
  (∀ x : Ω, ∃ b ∈ B, x ∈ b) ∧
  (∀ x : Ω, ∀ b₁ ∈ B, ∀ b₂ ∈ B, x ∈ b₁ → x ∈ b₂ → b₁ = b₂) ∧
  (∀ γ : Equiv.Perm Ω, γ ∈ G → ∀ b ∈ B, b.image γ ∈ B)

/-- `G` acts on the block system `B` as the Johnson group `A_k^{(t)}`
(Theorem 3.2.1): there is a bijection of `B` with the `t`-subsets of `[k]` such that every
element of `G` acts on blocks as a permutation induced by an even permutation of `[k]`. -/
def ActsAsJohnsonGroup (G : Subgroup (Equiv.Perm Ω)) (B : Finset (Finset Ω))
    (k t : ℕ) : Prop :=
  IsSystemOfImprimitivity G B ∧
    ∃ e : {b // b ∈ B} ≃ JohnsonVertex k t,
      ∀ γ : Equiv.Perm Ω, γ ∈ G → ∃ σ ∈ alternatingGroup (Fin k),
        ∀ b : {b // b ∈ B},
          ∃ hb : b.1.image γ ∈ B,
            e ⟨b.1.image γ, hb⟩ =
              ⟨(e b).1.image (σ : Equiv.Perm (Fin k)),
                by rw [Finset.card_image_of_injective _ σ.injective]; exact (e b).2⟩

/-! ## Symmetry defect -/

/-- The strong relative symmetry defect of `G` is `≥ α`: every complement of a strongly
symmetrical set has at least `αn` points (Definition 2.4.7, p. 14, with "weakly" replaced
by "strongly", as in Theorem 6.1.1). -/
def StrongRelativeDefectAtLeast (G : Subgroup (Equiv.Perm Ω)) (α : ℝ) : Prop :=
  ∀ T : Finset Ω, StronglySymmetricSet G (Finset.univ \ T) →
    α * (Fintype.card Ω : ℝ) ≤ (T.card : ℝ)

/-- Individualization of a finite set `S` of vertices: each `s ∈ S` becomes a constant
relation (`x ∈ S` iff exactly one point, Definition 4.0.8 example, p. 35). -/
def RelStructure.individualize {ι : Type u} {k : ℕ} {V : Type u}
    (X : RelStructure ι k V) (S : Finset V) : RelStructure (ι ⊕ {v // v ∈ S}) k V where
  rel i :=
    match i with
    | Sum.inl j => X.rel j
    | Sum.inr s => {p | ∀ j : Fin k, p j = (s : V)}

/-- The induced substructure on `W` (as a `Finset`). -/
def RelStructure.onFinset {ι : Type u} {k : ℕ} {V : Type u}
    (X : RelStructure ι k V) (W : Finset V) : RelStructure ι k {x // x ∈ W} :=
  X.induce {x | x ∈ W}

namespace RelStructure

variable {ι : Type u} {k : ℕ} {V : Type u}

/-- A relational structure has strong relative symmetry defect `≥ α`. -/
def StrongRelativeDefectAtLeast [Fintype V] [DecidableEq V]
    (X : RelStructure ι k V) (α : ℝ) : Prop :=
  SectionCore.StrongRelativeDefectAtLeast (RelAut X) α

end RelStructure

/-! ## Bipartite graphs (§7.2, §7.3, §7.5) -/

/-- A bipartite graph between two finite vertex sets, given by its adjacency relation.
Vertex colours on `V₂` (as in Theorem 7.3.2) are recorded separately when needed. -/
structure BipartiteGraph (V₁ V₂ : Type u) where
  /-- The adjacency relation between the two parts. -/
  adj : V₁ → V₂ → Prop

namespace BipartiteGraph

variable {V₁ V₂ : Type u} (X : BipartiteGraph V₁ V₂)

/-- The subgroup of `S(V₁)` induced by `Aut(X)`: the left components of the
automorphisms of `X` (a permutation `σ` of `V₁` lies here iff it extends to an
automorphism of `X`). -/
def leftGroup : Subgroup (Equiv.Perm V₁) where
  carrier := {σ | ∃ τ : Equiv.Perm V₂, ∀ a b, X.adj (σ a) (τ b) ↔ X.adj a b}
  one_mem' := ⟨1, by intro a b; simp⟩
  mul_mem' := by
    rintro σ₁ σ₂ ⟨τ₁, h₁⟩ ⟨τ₂, h₂⟩
    refine ⟨τ₁ * τ₂, ?_⟩
    intro a b
    show X.adj (σ₁ (σ₂ a)) (τ₁ (τ₂ b)) ↔ X.adj a b
    exact (h₁ (σ₂ a) (τ₂ b)).trans (h₂ a b)
  inv_mem' := by
    rintro σ ⟨τ, h⟩
    refine ⟨τ⁻¹, ?_⟩
    intro a b
    have h' := h (σ⁻¹ a) (τ⁻¹ b)
    simpa using h'.symm

/-- `X` is semiregular (Definition 7.2.1): all vertices on each side have the same
degree. -/
def Semiregular [Fintype V₁] [Fintype V₂] [DecidableRel X.adj] : Prop :=
  (∃ r : ℕ, ∀ a : V₁, (Finset.univ.filter (fun b => X.adj a b)).card = r) ∧
    ∃ r : ℕ, ∀ b : V₂, (Finset.univ.filter (fun a => X.adj a b)).card = r

/-- `X` has at least one edge ("not empty" in the sense of §7.2). -/
def HasEdge : Prop := ∃ a b, X.adj a b

/-- `X` is not the complete bipartite graph ("not complete" in the sense of §7.2). -/
def NotComplete : Prop := ∃ a b, ¬ X.adj a b

/-- The subgraph induced on a set `C` of right vertices. -/
def restrictRight (C : Finset V₂) : BipartiteGraph V₁ {b // b ∈ C} where
  adj a b := X.adj a b.1

end BipartiteGraph

/-! ## Symmetry defect on a subset -/

/-- The relative symmetry defect of `G` restricted to a subset `W` is `≥ α`: every
`T ⊆ W` whose complement in `W` is weakly symmetrical satisfies `|T| ≥ α|W|`
(Definition 2.4.7 applied to the action on `W`; used for "the symmetry defect of `V₁`
in `X`" in §7.2–7.5). -/
def DefectOnSet {Ω : Type u} [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω))
    (W : Finset Ω) (α : ℝ) : Prop :=
  ∀ T : Finset Ω, T ⊆ W → WeaklySymmetricSet G (W \ T) → α * (W.card : ℝ) ≤ (T.card : ℝ)

/-- The absolute symmetry defect of `G` is at most `s`: some residual set of size `≤ s`
has a weakly symmetrical complement (Definition 2.4.7 with `min` unfolded). -/
def AbsoluteDefectAtMost {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    (G : Subgroup (Equiv.Perm Ω)) (s : ℕ) : Prop :=
  ∃ T : Finset Ω, T.card ≤ s ∧ WeaklySymmetricSet G (Finset.univ \ T)

/-! ## Permutation-group vocabulary of §8 -/

/-- The stabilizer of a point `x` inside a subgroup `G ≤ S(Ω)`. -/
def stabilizerIn {Ω : Type u} (G : Subgroup (Equiv.Perm Ω)) (x : Ω) : Subgroup G where
  carrier := {g | (g : Equiv.Perm Ω) x = x}
  one_mem' := rfl
  mul_mem' := by
    intro g h hg hh
    show ((g * h : G) : Equiv.Perm Ω) x = x
    have hmul : ((g * h : G) : Equiv.Perm Ω) = (g : Equiv.Perm Ω) * (h : Equiv.Perm Ω) := rfl
    rw [hmul, Equiv.Perm.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    show ((g⁻¹ : G) : Equiv.Perm Ω) x = x
    have hinv : ((g⁻¹ : G) : Equiv.Perm Ω) = (g : Equiv.Perm Ω)⁻¹ := rfl
    rw [hinv]
    have h2 : (g : Equiv.Perm Ω)⁻¹ ((g : Equiv.Perm Ω) x) = (g : Equiv.Perm Ω)⁻¹ x := by
      rw [hg]
    simpa using h2.symm

/-- The pointwise stabilizer of a finite set `T`: permutations fixing every element of
`T` (the paper's `S_{T}` in the "pointwise" reading used for `(A_k)^{(T)}`). -/
def pointwiseStabilizer {Γ : Type u} [Fintype Γ] [DecidableEq Γ]
    (T : Finset Γ) : Subgroup (Equiv.Perm Γ) where
  carrier := {σ | ∀ x ∈ T, σ x = x}
  one_mem' := by intro x _; rfl
  mul_mem' := by
    intro f g hf hg x hx
    show (f * g) x = x
    rw [Equiv.Perm.mul_apply, hg x hx, hf x hx]
  inv_mem' := by
    intro f hf x hx
    show f⁻¹ x = x
    have h2 := congrArg (⇑f⁻¹) (hf x hx)
    simpa using h2.symm

/-- The setwise stabilizer of a finite set `T`: permutations mapping `T` onto itself
(the paper's `(S_k)_{T}`). -/
def setwiseStabilizer {Γ : Type u} [Fintype Γ] [DecidableEq Γ]
    (T : Finset Γ) : Subgroup (Equiv.Perm Γ) where
  carrier := {σ | T.image σ = T}
  one_mem' := by simp
  mul_mem' := by
    intro f g hf hg
    show T.image ⇑(f * g) = T
    have hcomp : (⇑(f * g) : Γ → Γ) = ⇑f ∘ ⇑g := rfl
    rw [hcomp, ← Finset.image_image, hg, hf]
  inv_mem' := by
    intro f hf
    show T.image ⇑f⁻¹ = T
    have h := congrArg (fun S : Finset Γ => S.image ⇑f⁻¹) hf
    simpa [Finset.image_image] using h.symm

/-- A subgroup of `S(Γ)` is a giant if it contains the alternating group
(§1.2.1: "giants" are `S(Γ)` and `A(Γ)`). -/
def IsGiant {Γ : Type u} [Fintype Γ] [DecidableEq Γ] (H : Subgroup (Equiv.Perm Γ)) : Prop :=
  alternatingGroup Γ ≤ H

/-- `φ : G → S(Γ)` is a giant representation (§1.2.1, p. 9): its image is a giant. -/
def IsGiantRep {Ω Γ : Type u} [Fintype Γ] [DecidableEq Γ]
    (G : Subgroup (Equiv.Perm Ω)) (φ : G →* Equiv.Perm Γ) : Prop :=
  IsGiant φ.range

/-- `x` is affected by the giant representation `φ` (§1.3.1, p. 8): the image of the
stabilizer `G_x` under `φ` does not contain `A(Γ)`. -/
def Affected {Ω Γ : Type u} [Fintype Γ] [DecidableEq Γ]
    (G : Subgroup (Equiv.Perm Ω)) (φ : G →* Equiv.Perm Γ) (x : Ω) : Prop :=
  ¬ IsGiant ((stabilizerIn G x).map φ)

/-- The symmetric group on `A`, viewed as a subgroup of `S(Ω)`: permutations supported
on `A` (the paper's `S(A)`). -/
def symmetricGroupOn {Ω : Type u} (A : Finset Ω) : Subgroup (Equiv.Perm Ω) where
  carrier := {σ | ∀ x : Ω, x ∉ A → σ x = x}
  one_mem' := by intro x _; rfl
  mul_mem' := by
    intro f g hf hg x hx
    show (f * g) x = x
    rw [Equiv.Perm.mul_apply, hg x hx, hf x hx]
  inv_mem' := by
    intro f hf x hx
    show f⁻¹ x = x
    have h2 := congrArg (⇑f⁻¹) (hf x hx)
    simpa using h2.symm

namespace CoherentConfig

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A uniprimitive coherent configuration (UPCC, §6.1): at least two vertices, every
constituent is homogeneous, and the configuration is primitive. Primitivity of the
configuration is encoded as primitivity of the action of its automorphism group; for a
homogeneous configuration the two notions coincide on the Weisfeiler–Leman closure
(boundary note: the configuration-level block system is not separately formalized). -/
def IsUPCC (X : CoherentConfig V) : Prop :=
  2 ≤ Fintype.card V ∧ IsPrimitiveGroup (RelAut X.toRelStructure) ∧
    ∀ i : X.ι, X.HomogeneousConstituent i

/-- A coherent configuration with strong relative symmetry defect `≥ α`. -/
def StrongDefectAtLeast (X : CoherentConfig V) (α : ℝ) : Prop :=
  SectionCore.StrongRelativeDefectAtLeast (RelAut X.toRelStructure) α

end CoherentConfig

end Qatlib.Papers.GraphIsoBabai15.MainResults.SectionCore
