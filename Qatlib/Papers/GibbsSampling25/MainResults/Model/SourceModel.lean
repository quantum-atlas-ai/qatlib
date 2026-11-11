/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Dist
import Qatlib.Concepts.QuantumEntropy.EntropyCalculus
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCoreDefs

set_option backward.isDefEq.respectTransparency false

/-!
# Source model for arXiv:2412.01732v1 (GibbsSampling25)

This file fixes the vocabulary shared by all claims of *Quasi-optimal sampling
from Gibbs states via non-commutative optimal transport metrics*
(Capel–Gondolf–Kochanowski–Rouzé, arXiv:2412.01732v1).

The density-matrix relative entropy, the Gibbs state, the trace distance and the
mixing time are taken from the shared Frozen foundations
(`QuantumEntropy.EntropyCalculus` and `GkslSemigroup.LindbladSemigroupModel`).
On top of them we add:

* `relEnt` — the real-valued Umegaki relative entropy of two densities
  (paper notation `D(ρ‖σ)`, Appendix A.1);
* `condRelEnt` — the conditional relative entropy of Definition 2.4, eq. (4);
* `Site`, `latticeDist`, `setDist` — the lattice `Λ_L = {-L,…,L}^D ⊂ ℤ^D`
  of Section 2 with its sup-metric and the induced set distance
  `dist(A,C)`;
* `CoarseGraining` — the data of a suitable coarse-graining, whose four
  defining properties are exactly the items of Lemma 2.6 / Lemma B.2;
* `McmiNorm` — the operator norm `‖H_σ(A:C|D)‖∞` of the matrix-valued
  conditional mutual information of Definition 2.2, eq. (2), exposed as a
  function of the three regions.

The matrix-level construction of `McmiNorm` (partial traces of `log σ` padded
with identities via Kronecker products) is *not* formalised here; every result
that mentions it takes it as an explicit datum whose intended meaning is fixed
by the docstring of `McmiNorm`. This is recorded as a modelling gap in the
placeholder comments of the individual results.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Kronecker

namespace Qatlib.Papers.GibbsSampling25.MainResults.Model

open Qatlib.Concepts.QuantumEntropy.EntropyCalculus

/-! ## Relative entropy of density matrices -/

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The real-valued relative entropy `D(ρ‖σ)` of two density matrices, i.e. the
Umegaki relative entropy `tr[ρ(log ρ − log σ)]` of Appendix A.1. It is the
`toReal` cast of the Frozen `relative` (an `ℝ≥0∞` which is `⊤` on disjoint
supports). -/
def relEnt (ρ σ : Density I) : ℝ := (relative ρ σ).toReal

/-- Relative entropy is non-negative (the `toReal` of an `ℝ≥0∞`). -/
theorem relEnt_nonneg (ρ σ : Density I) : 0 ≤ relEnt ρ σ := ENNReal.toReal_nonneg

/-- Relative entropy of a state with itself vanishes:
`D(ρ‖ρ) = 0` (Frozen `relative_entropy_density_bridge`). -/
theorem relEnt_self (ρ : Density I) : relEnt ρ ρ = 0 := by
  have h : relative ρ ρ = 0 :=
    ((relative_entropy_density_bridge.1 I ρ ρ).2.2.2).mpr rfl
  simp [relEnt, h]

/-- Reindexing a square matrix along an equivalence does not change its trace. -/
theorem trace_submatrix_equiv {R : Type*} [AddCommMonoid R] (e : I ≃ J)
    (M : Matrix I I R) : (M.submatrix e.symm e.symm).trace = M.trace := by
  simp only [Matrix.trace, Matrix.submatrix]
  exact Equiv.sum_comp e.symm (fun i => M i i)

/-- Transport a density along an equivalence of index sets. -/
def reindexDensity (e : I ≃ J) (ρ : Density I) : Density J :=
  ⟨ρ.val.submatrix e.symm e.symm, ρ.property.1.submatrix e.symm, by
    rw [trace_submatrix_equiv]
    exact ρ.property.2⟩

/-- Partial trace of a density on `I × J` over the second factor. -/
def ptraceD (ρ : Density (I × J)) : Density I :=
  ⟨ρ.val.traceRight, ρ.property.1.traceRight, by
    rw [Matrix.traceRight_trace]
    exact ρ.property.2⟩

/-- Partial trace of a density on `I × J` over the first factor. -/
def ptraceL (ρ : Density (I × J)) : Density J :=
  ⟨ρ.val.traceLeft, ρ.property.1.traceLeft, by
    rw [Matrix.traceLeft_trace]
    exact ρ.property.2⟩

/-- Conditional relative entropy `D_A(ρ‖σ)` of Definition 2.4, eq. (4):
`D(ρ‖σ) − D(ρ_Ā‖σ_Ā)`, where `marg` is the partial trace onto the complement
of `A` (kept as an explicit datum; the intended instance is a partial trace of
density matrices). -/
def condRelEnt (marg : Density I → Density J) (ρ σ : Density I) : ℝ :=
  relEnt ρ σ - relEnt (marg ρ) (marg σ)

/-! ## The lattice `Λ_L` and its geometry -/

/-- The lattice `Λ_L = {-L, …, L}^D ⊂ ℤ^D` of Section 2, with `|Λ_L| = (2L+1)^D`. -/
abbrev Site (D L : ℕ) : Type := Fin D → Fin (2 * L + 1)

/-- The finite lattice has finitely many sites. -/
instance (D L : ℕ) : Fintype (Site D L) := inferInstanceAs (Fintype (Fin D → Fin (2 * L + 1)))
/-- Equality of finite lattice sites is decidable. -/
instance (D L : ℕ) : DecidableEq (Site D L) :=
  inferInstanceAs (DecidableEq (Fin D → Fin (2 * L + 1)))

/-- The lattice distance `d(x,y) = max_i |x_i − y_i|` (sup-metric on `ℤ^D`). -/
def latticeDist {D L : ℕ} (x y : Site D L) : ℝ :=
  ((Finset.univ.sup fun i => Nat.dist (x i) (y i) : ℕ) : ℝ)

/-- The lattice distance is symmetric. -/
theorem latticeDist_comm {D L : ℕ} (x y : Site D L) : latticeDist x y = latticeDist y x := by
  have h : (fun i => Nat.dist (x i) (y i)) = (fun i => Nat.dist (y i) (x i)) := by
    funext i
    exact Nat.dist_comm (x i) (y i)
  simp only [latticeDist, h]

/-- The lattice distance is non-negative. -/
theorem latticeDist_nonneg {D L : ℕ} (x y : Site D L) : 0 ≤ latticeDist x y := by
  simp only [latticeDist]
  positivity

/-- The set distance `dist(A,C) = min_{x∈A, y∈C} d(x,y)` induced by a metric
`δ` (with the convention that the infimum of the empty set is `0`). -/
def setDistOf {α : Type*} (δ : α → α → ℝ) (A C : Finset α) : ℝ :=
  sInf {d : ℝ | ∃ x ∈ A, ∃ y ∈ C, d = δ x y}

/-- The set distance on the lattice `Λ_L`. -/
def setDist {D L : ℕ} (A C : Finset (Site D L)) : ℝ :=
  setDistOf latticeDist A C

/-- The set distance induced by a symmetric metric is symmetric. -/
theorem setDistOf_comm {α : Type*} (δ : α → α → ℝ) (hδ : ∀ x y : α, δ x y = δ y x)
    (A C : Finset α) : setDistOf δ A C = setDistOf δ C A := by
  unfold setDistOf
  congr 1
  ext d
  constructor
  · rintro ⟨x, hx, y, hy, hd⟩
    exact ⟨y, hy, x, hx, by rw [hd, hδ x y]⟩
  · rintro ⟨y, hy, x, hx, hd⟩
    exact ⟨x, hx, y, hy, by rw [hd, hδ y x]⟩

/-- The set distance on `Λ_L` is symmetric. -/
theorem setDist_comm {D L : ℕ} (A C : Finset (Site D L)) :
    setDist A C = setDist C A :=
  setDistOf_comm latticeDist (fun _ _ => latticeDist_comm _ _) A C

/-! ## Coarse-grainings -/

/-- A suitable coarse-graining of `Λ_L` in the sense of Lemma 2.6 and
Lemma B.2: `D+1` levels of cells `C_{a,i}`, with cores `C̊_{a,i}` and
shells `C^∂_{a,i}`, satisfying

1. the cells cover `Λ_L` and every site belongs to at most `D+1` cells;
2. the cells of each fixed level are mutually disjoint;
3. every cell has at most `ℓ^D` sites;
4. cores are contained in cells and adjacent-level core/shell distances are
   at least `c` (the "suitable overlap `c`"). -/
structure CoarseGraining (D L k c ℓ : ℕ) where
  /-- Cells `C_{a,i}` of level `a`. -/
  cell : Fin (D + 1) → Finset (Finset (Site D L))
  /-- Cores `C̊_{a,i}` of level `a`. -/
  core : Fin (D + 1) → Finset (Site D L) → Finset (Site D L)
  /-- Shells `C^∂_{a,i}` of level `a`. -/
  shell : Fin (D + 1) → Finset (Site D L) → Finset (Site D L)
  /-- Cores sit inside their cells. -/
  core_subset : ∀ (a : Fin (D + 1)) (C : Finset (Site D L)), C ∈ cell a → core a C ⊆ C
  /-- Shells sit inside their cells. -/
  shell_subset : ∀ (a : Fin (D + 1)) (C : Finset (Site D L)), C ∈ cell a → shell a C ⊆ C
  /-- Property 1 (cover): the cells cover the lattice. -/
  cover : ∀ x : Site D L, ∃ (a : Fin (D + 1)) (C : Finset (Site D L)), C ∈ cell a ∧ x ∈ C
  /-- Property 1 (overlap bound): each site lies in at most `D+1` cells. -/
  mem_le : ∀ x : Site D L,
    (Finset.univ.filter (fun a : Fin (D + 1) =>
      ∃ C : Finset (Site D L), C ∈ cell a ∧ x ∈ C)).card ≤ D + 1
  /-- Property 2: cells of a fixed level are pairwise disjoint. -/
  disjoint : ∀ (a : Fin (D + 1)) (C₁ : Finset (Site D L)), C₁ ∈ cell a →
    ∀ (C₂ : Finset (Site D L)), C₂ ∈ cell a → C₁ ≠ C₂ → Disjoint C₁ C₂
  /-- Property 3: every cell has at most `ℓ^D` sites. -/
  size : ∀ (a : Fin (D + 1)) (C : Finset (Site D L)), C ∈ cell a → C.card ≤ ℓ ^ D
  /-- Property 4: adjacent levels have core/shell distance at least `c`. -/
  overlap : ∀ (a : Fin (D + 1)) (h : a.val + 1 < D + 1) (C : Finset (Site D L)),
    C ∈ cell a → ∀ C' : Finset (Site D L), C' ∈ cell ⟨a.val + 1, h⟩ →
    (c : ℝ) ≤ setDist (core a C) (shell ⟨a.val + 1, h⟩ C')
  /-- Lemma B.2: cells of the same level are at distance at least `2k`. -/
  same_level_sep : ∀ (a : Fin (D + 1)) (C₁ : Finset (Site D L)), C₁ ∈ cell a →
    ∀ (C₂ : Finset (Site D L)), C₂ ∈ cell a → C₁ ≠ C₂ → (2 * k : ℝ) ≤ setDist C₁ C₂
  /-- Lemma B.2: level-`0` cells have diameter at most `2D(k+c)`. -/
  level0_diam : ∀ C : Finset (Site D L), C ∈ cell 0 → ∀ x ∈ C, ∀ y ∈ C,
    latticeDist x y ≤ (2 * D * (k + c) : ℝ)
  /-- Lemma B.2: distinct level-`0` cells are at distance at least `ℓ − 2D(k+c)`. -/
  level0_sep : ∀ (C₁ : Finset (Site D L)), C₁ ∈ cell 0 → ∀ C₂ : Finset (Site D L),
    C₂ ∈ cell 0 → C₁ ≠ C₂ → ((ℓ : ℝ) - (2 * D * (k + c) : ℝ)) ≤ setDist C₁ C₂

/-- The operator norm `‖H_σ(A:C|D)‖∞` of the MCMI of Definition 2.2, eq. (2):
for a fixed Gibbs state `σ`, `McmiNorm Λ` maps the three regions `A`, `C`, `D`
to the operator norm of `log σ_ACD + log σ_D − log σ_AD − log σ_CD` (with each
marginal padded by identities on the complementary systems). -/
abbrev McmiNorm (Λ : Type) := Finset Λ → Finset Λ → Finset Λ → ℝ

/-- A strong local effective Hamiltonian in the sense of Appendix A.4.3 /
[BCPH24, Definition 3.1], specialised to the data needed by Lemma D.1: region
dependent local terms with operator norms `hterm A X` satisfying

* locality: `hterm A X` only depends on `A ∩ X`;
* the uniform interaction-norm bound (72): for every region `A` and every
  `x ∈ A`, `∑_{X ∋ x} hterm A X · e^{μ diam X} ≤ Δ`;
* the reconstruction of the MCMI (Definition A.4.3, item 3):
  `H_σ(A:C|D) = ∑_X (h̃^{ACD}_X + h̃^D_X − h̃^{AD}_X − h̃^{CD}_X)`. -/
def IsStrongLocalEffectiveHamiltonian {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (mcmi : McmiNorm Λ) (hterm : Finset Λ → Finset Λ → ℝ) (Δ μ : ℝ) : Prop :=
  (∀ (A X : Finset Λ), hterm A X = hterm (A ∩ X) X) ∧
  (∀ (A : Finset Λ) (x : Λ), x ∈ A →
    ∑ X ∈ Finset.univ.filter (fun X : Finset Λ => x ∈ X),
      hterm A X * Real.exp (μ * (X.card : ℝ)) ≤ Δ) ∧
  (∀ A C Dd : Finset Λ,
    mcmi A C Dd = ∑ X ∈ Finset.univ,
      (hterm (A ∪ C ∪ Dd) X + hterm Dd X - hterm (A ∪ Dd) X - hterm (C ∪ Dd) X))

/-- The normalized Wasserstein-1 distance `‖ρ − σ‖_{W¹}` of Definition 2.8,
eqs. (9)–(10), left as an explicit interface datum (a function of two
densities with its intended meaning fixed by the docstring). -/
abbrev WOneDist (I : Type) [Fintype I] [DecidableEq I] := Density I → Density I → ℝ

end Qatlib.Papers.GibbsSampling25.MainResults.Model
