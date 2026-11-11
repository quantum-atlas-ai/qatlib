/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option backward.isDefEq.respectTransparency false

/-!
# Paper vocabulary for AdiabNoSign20

This module fixes the vocabulary of M. B. Hastings, *The Power of Adiabatic
Quantum Computation with No Sign Problem*, arXiv:2005.03791v2 (2021), at the
level of abstraction of Sections 1.1, 2, 3 and 6.  No theorem of the paper is
assumed here; the module only defines the paper's objects so that the claim
files can state its lemmas over them.

* Computational basis: a finite type `ι`; a Hamiltonian is a real matrix
  `ι → ι → ℝ`, its entries being `⟨i|H|j⟩` in the computational basis.  The
  paper's Hamiltonians are real symmetric there.
* The six admissibility conditions of Section 1.1 (p. 2) are collected in
  `IsAdmissiblePath`; the endpoint condition is `SatisfiesEndpoint`.
* `AdNSPInstance` is Definition 1 (Section 1.1, p. 3-4).
* `Rayleigh`-quotient formulations of "ground state" and "spectral gap" avoid
  an eigenbasis and are exactly the finite Hermitian-matrix conditions.
* `lambda0` is the largest eigenvalue of a graph's adjacency matrix, written
  as the Perron root (supremum of the quadratic form over the probability
  simplex); for a nonnegative symmetric adjacency matrix this is the largest
  eigenvalue by Perron--Frobenius, and it makes `lambda0_mono` elementary.
* `spectralGap` is the gap between the two largest adjacency eigenvalues,
  taken from the spectral theorem for Hermitian matrices.
* `Pcoin` and `ReachHard` are the coin-tail and hardness notions of
  Section 6 (p. 17-18).
-/

namespace Qatlib.Papers.AdiabNoSign20.MainResults.SourceModel

open scoped BigOperators
open Finset

set_option autoImplicit false

/-! ## Computational basis states and Hamiltonians -/

/-- A computational basis. -/
abbrev Basis (ι : Type) := ι

/-- A Hamiltonian on the real computational basis `ι`. -/
abbrev Hamiltonian (ι : Type) := ι → ι → ℝ

/-- Symmetry of a Hamiltonian matrix. -/
def IsSymmetricHamiltonian {ι : Type} (H : Hamiltonian ι) : Prop :=
  ∀ i j, H i j = H j i

/-- **No sign problem** (Section 1.1, p. 2): every off-diagonal entry is
nonpositive in the computational basis ("stoquastic"). -/
def NoSignProblem {ι : Type} (H : Hamiltonian ι) : Prop :=
  ∀ i j, i ≠ j → H i j ≤ 0

/-- Polynomial sparsity (second admissibility condition, Section 1.1, p. 2):
each row has at most `B` nonzero entries. -/
def IsRowSparse {ι : Type} [Fintype ι] (H : Hamiltonian ι) (B : ℕ) : Prop :=
  ∀ i, (univ.filter (fun j => H i j ≠ 0)).card ≤ B

/-- Bounded matrix elements (third admissibility condition, Section 1.1,
p. 2). -/
def HasBoundedEntries {ι : Type} (H : Hamiltonian ι) (B : ℝ) : Prop :=
  ∀ i j, |H i j| ≤ B

/-! ## Rayleigh quotients, ground states and gaps -/

/-- The Rayleigh quotient `⟨v|H|v⟩ / ⟨v|v⟩`. -/
noncomputable def rayleigh {ι : Type} [Fintype ι] (H : Hamiltonian ι)
    (v : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, v i * H i j * v j) / (∑ i, v i * v i)

/-- `ψ` is a ground-state vector of `H`: it is nonzero and minimises the
Rayleigh quotient. -/
def IsGroundState {ι : Type} [Fintype ι] (H : Hamiltonian ι)
    (ψ : ι → ℝ) : Prop :=
  (∑ i, ψ i * ψ i) ≠ 0 ∧ ∀ φ, (∑ i, φ i * φ i) ≠ 0 → rayleigh H ψ ≤ rayleigh H φ

/-- The ground state is unique and separated from the rest of the spectrum by
a gap at least `δ` (fifth admissibility condition, Section 1.1, p. 2).  Since
`rayleigh` is scale invariant, the orthogonal complement is stated with the
un-normalised inner product `∑ i, ψ i * φ i`. -/
def UniqueGappedGroundState {ι : Type} [Fintype ι] (H : Hamiltonian ι)
    (δ : ℝ) : Prop :=
  ∃ ψ, IsGroundState H ψ ∧
    ∀ φ, (∑ i, ψ i * φ i) = 0 → (∑ i, φ i * φ i) ≠ 0 →
      rayleigh H ψ + δ ≤ rayleigh H φ

/-- The computational basis vector at `i`. -/
def basisVector {ι : Type} [DecidableEq ι] (i : ι) : ι → ℝ :=
  fun j => if j = i then 1 else 0

/-! ## Parameters, admissible paths and `AdNSP` -/

/-- The polynomial data on which the definition of admissible paths and of
`AdNSP` implicitly depends (Section 1.1, p. 2-3). -/
structure AdNSPParameters where
  /-- exponent of the number of computational basis states -/
  p : ℕ → ℕ
  /-- sparsity bound -/
  sparseBound : ℕ → ℕ
  /-- matrix-element bound -/
  entryBound : ℕ → ℝ
  /-- derivative bound -/
  derivBound : ℕ → ℝ
  /-- spectral-gap lower bound -/
  gapBound : ℕ → ℝ
  /-- length of the `s` interval -/
  lengthBound : ℕ → ℝ
  /-- `p` is polynomially bounded -/
  pPoly : ∃ d : ℕ, ∀ N : ℕ, p N ≤ N ^ d + 1
  /-- the gap bound is inverse polynomial -/
  gapInversePoly : ∃ c : ℝ, 0 < c ∧ ∃ d : ℕ, ∀ N : ℕ, 1 ≤ N → c / (N : ℝ) ^ d ≤ gapBound N

/-- **Admissible path** (Section 1.1, p. 2): the Hamiltonian family
`H : ℝ → Hamiltonian ι` on the interval `[a,b]` satisfies the six conditions:
symmetry, no sign problem, polynomial sparsity, bounded entries, bounded
`s`-derivative, and a unique ground state with gap at least
`params.gapBound N`; together with a polynomially long interval. -/
def IsAdmissiblePath {ι : Type} [Fintype ι] (params : AdNSPParameters)
    (N : ℕ) (H : ℝ → Hamiltonian ι) (a b : ℝ) : Prop :=
  a ≤ b ∧
  b - a ≤ params.lengthBound N ∧
  (∀ s, IsSymmetricHamiltonian (H s)) ∧
  (∀ s, NoSignProblem (H s)) ∧
  (∀ s, IsRowSparse (H s) (params.sparseBound N)) ∧
  (∀ s, HasBoundedEntries (H s) (params.entryBound N)) ∧
  (∀ s i j, DifferentiableAt ℝ (fun t => H t i j) s) ∧
  (∀ s i j, |deriv (fun t => H t i j) s| ≤ params.derivBound N) ∧
  (∀ s, UniqueGappedGroundState (H s) (params.gapBound N))

/-- The **endpoint condition** (Section 1.1, p. 3): the ground state at both
ends of the path is a computational basis state. -/
def SatisfiesEndpoint {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : ℝ → Hamiltonian ι) (a b : ℝ) : Prop :=
  (∃ i₀ : ι, IsGroundState (H a) (basisVector i₀)) ∧
    (∃ i₁ : ι, IsGroundState (H b) (basisVector i₁))

/-- An instance of the oracle problem `AdNSP` (Definition 1, Section 1.1,
p. 3-4): an admissible path satisfying the endpoint condition. -/
structure AdNSPInstance (ι : Type) [Fintype ι] [DecidableEq ι]
    (params : AdNSPParameters) (N : ℕ) where
  H : ℝ → Hamiltonian ι
  a : ℝ
  b : ℝ
  admissible : IsAdmissiblePath params N H a b
  endpoint : SatisfiesEndpoint H a b

/-- The basis state at the end of the path, i.e. the "answer" of Definition 1
(p. 4), chosen from the endpoint condition. -/
noncomputable def AdNSPInstance.finalBasis {ι : Type} [Fintype ι] [DecidableEq ι]
    {params : AdNSPParameters} {N : ℕ} (inst : AdNSPInstance ι params N) : ι :=
  Classical.choose inst.endpoint.2

/-- The chosen `finalBasis` is the ground state at the end of the path. -/
theorem AdNSPInstance.finalBasis_ground {ι : Type} [Fintype ι] [DecidableEq ι]
    {params : AdNSPParameters} {N : ℕ} (inst : AdNSPInstance ι params N) :
    IsGroundState (inst.H inst.b) (basisVector inst.finalBasis) :=
  Classical.choose_spec inst.endpoint.2

/-! ## Query models and classical algorithms -/

/-- The two query models of Section 2. -/
inductive QueryModelKind where
  /-- original oracle model of Definition 1 -/
  | original
  /-- modified query model of Section 2.2 -/
  | modified
  deriving DecidableEq, Repr

/-- A classical algorithm with finite randomness `R` (the paper allows
randomised algorithms, Section 1.1, p. 4).  `out r inst` is the basis state
returned on randomness `r`; `queryCount` is the number of oracle queries. -/
structure ClassicalAlgorithm (ι R : Type) [Fintype ι] [DecidableEq ι]
    (params : AdNSPParameters) (N : ℕ) [Fintype R] [Nonempty R] where
  /-- the query model in which the algorithm operates (Section 2) -/
  model : QueryModelKind
  queryCount : ℕ
  out : R → AdNSPInstance ι params N → ι
  /-- the algorithm only ever queries "related" states, i.e. states reached
  from the start state along the query tree (§2.1, used in Lemma 1); this is a
  paper-layer abstraction of the algorithm's query trace -/
  relatedOnly : Prop

/-- Success probability of a randomised algorithm on one instance. -/
noncomputable def ClassicalAlgorithm.successProb {ι R : Type} [Fintype ι]
    [DecidableEq ι] {params : AdNSPParameters} {N : ℕ} [Fintype R] [Nonempty R]
    (alg : ClassicalAlgorithm ι R params N) (inst : AdNSPInstance ι params N) : ℝ :=
  ((univ.filter (fun r => alg.out r inst = inst.finalBasis)).card : ℝ) /
    (Fintype.card R : ℝ)

/-- Quasi-polynomially many queries (Section 1.1, p. 4): the query count is
bounded by `exp(O(log(N)^d))` for some `d`. -/
def QuasiPolynomialQueryCount {ι R : Type} [Fintype ι] [DecidableEq ι]
    {params : AdNSPParameters} {N : ℕ} [Fintype R] [Nonempty R]
    (alg : ClassicalAlgorithm ι R params N) : Prop :=
  ∃ C d : ℕ, 0 < C ∧ (alg.queryCount : ℝ) ≤ (C : ℝ) * Real.exp ((C : ℝ) * (Real.log N) ^ d)

/-- `alg` solves every instance of `AdNSP` with probability at least `pr`
(Definition 1, p. 4). -/
def SolvesEveryInstance {ι R : Type} [Fintype ι] [DecidableEq ι]
    {params : AdNSPParameters} {N : ℕ} [Fintype R] [Nonempty R]
    (alg : ClassicalAlgorithm ι R params N) (pr : ℝ) : Prop :=
  ∀ inst, pr ≤ alg.successProb inst

/-- The algorithm only queries related states (§2.1, p. 5): the paper-layer
abstraction recorded in `ClassicalAlgorithm.relatedOnly`. -/
def QueriesOnlyRelatedStates {ι R : Type} [Fintype ι] [DecidableEq ι]
    {params : AdNSPParameters} {N : ℕ} [Fintype R] [Nonempty R]
    (alg : ClassicalAlgorithm ι R params N) : Prop :=
  alg.relatedOnly

/-- **Theorem 1 of the paper at a fixed query model** (§1.1 p. 4): there are a
constant `c > 0`, a constant `K > 0` and a specific choice of polynomials
defining `AdNSP` (an `AdNSPParameters`) such that for every `N ≥ 2`, no
algorithm operating in `model` with at most `exp (K (log N)^2)` classical
queries solves every instance with probability at least `exp (-cN)`. -/
def NoAlgorithmBeatsInModel (model : QueryModelKind) : Prop :=
  ∃ (params : AdNSPParameters) (c K : ℝ), 0 < c ∧ 0 < K ∧
    ∀ (N : ℕ), 2 ≤ N → ∀ (ι R : Type) [Fintype ι] [DecidableEq ι]
      [Fintype R] [Nonempty R] (alg : ClassicalAlgorithm ι R params N),
      alg.model = model →
      (alg.queryCount : ℝ) ≤ Real.exp (K * (Real.log (N : ℝ)) ^ 2) →
      ¬ SolvesEveryInstance alg (Real.exp (-(c * (N : ℝ))))

/-! ## Graphs, spectra and Table 1 -/

/-- The Hamiltonian of a graph: minus its adjacency matrix (Section 3,
p. 10). -/
noncomputable def graphHamiltonian {V : Type} (G : SimpleGraph V) : Hamiltonian V := by
  classical
  exact fun i j => -(G.adjMatrix ℝ) i j

/-- **The largest eigenvalue of the adjacency matrix** of a finite graph,
written as the Perron root: the supremum of the quadratic form `v ↦ vᵀ A v`
over the probability simplex (nonnegative vectors summing to one).  For a
nonnegative symmetric adjacency matrix this equals the largest eigenvalue
(Perron--Frobenius); the simplex formulation makes `lambda0_mono` elementary.
-/
noncomputable def lambda0 {V : Type} [Fintype V] (G : SimpleGraph V) : ℝ := by
  classical
  exact ⨆ v : {v : V → ℝ // (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1},
    ∑ i, ∑ j, v.1 i * (G.adjMatrix ℝ) i j * v.1 j

/-- The uniform vector lies in the probability simplex of a nonempty finite
type. -/
theorem exists_simplex_vector {V : Type} [Fintype V] [Nonempty V] :
    Nonempty {v : V → ℝ // (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1} := by
  classical
  refine ⟨⟨fun _ => (Fintype.card V : ℝ)⁻¹, ?_, ?_⟩⟩
  · intro i
    positivity
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Every coordinate of a simplex vector is at most one. -/
theorem simplex_coord_le_one {V : Type} [Fintype V] {v : V → ℝ}
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∑ i, v i = 1) (i : V) : v i ≤ 1 := by
  have hsingle : v i ≤ ∑ j, v j :=
    Finset.single_le_sum (f := v) (fun j _ => hv0 j) (Finset.mem_univ i)
  rw [hv1] at hsingle
  exact hsingle

/-- The adjacency quadratic form of a probability-simplex vector is at most
`1`: an adjacency entry is `0` or `1`, so the form is at most
`∑ i ∑ j v i * v j = (∑ i, v i)^2 = 1`. -/
theorem simplex_quadform_le_one {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {v : V → ℝ} (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∑ i, v i = 1) :
    (∑ i, ∑ j, v i * (G.adjMatrix ℝ) i j * v j) ≤ 1 := by
  classical
  have step : ∀ i j, v i * (G.adjMatrix ℝ) i j * v j ≤ v i * v j := by
    intro i j
    simp only [SimpleGraph.adjMatrix_apply]
    split_ifs with h
    · simp
    · have hnn : 0 ≤ v i * v j := mul_nonneg (hv0 i) (hv0 j)
      simp only [mul_zero]
      linarith
  calc (∑ i, ∑ j, v i * (G.adjMatrix ℝ) i j * v j)
      ≤ ∑ i, ∑ j, v i * v j :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => step i j
    _ = (∑ i, v i) * (∑ j, v j) := by rw [Finset.sum_mul_sum]
    _ = 1 := by rw [hv1]; norm_num

/-- The adjacency quadratic form over the probability simplex is bounded
above (by `1`). -/
theorem bddAbove_simplex_quadform {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    BddAbove (Set.range fun v : {v : V → ℝ // (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1} =>
      ∑ i, ∑ j, v.1 i * (G.adjMatrix ℝ) i j * v.1 j) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact simplex_quadform_le_one v.2.1 v.2.2

/-- **Adding edges cannot decrease `lambda0`.**  If every edge of `G` is an
edge of `G'`, then `lambda0 G ≤ lambda0 G'`; used in Lemma 4 (§5.3, p. 16)
for `λ₀(G) ≤ λ₀(G_l)`. -/
theorem lambda0_mono {V : Type} [Fintype V] [Nonempty V] {G G' : SimpleGraph V}
    (h : ∀ a b, G.Adj a b → G'.Adj a b) : lambda0 G ≤ lambda0 G' := by
  classical
  haveI : Nonempty {v : V → ℝ // (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1} :=
    exists_simplex_vector
  unfold lambda0
  apply ciSup_le
  intro v
  have hsum :
      (∑ i, ∑ j, v.1 i * (G.adjMatrix ℝ) i j * v.1 j) ≤
        ∑ i, ∑ j, v.1 i * (G'.adjMatrix ℝ) i j * v.1 j := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hi0 : 0 ≤ v.1 i := v.2.1 i
    have hj0 : 0 ≤ v.1 j := v.2.1 j
    have hi1 : v.1 i ≤ 1 := simplex_coord_le_one v.2.1 v.2.2 i
    have hj1 : v.1 j ≤ 1 := simplex_coord_le_one v.2.1 v.2.2 j
    rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
    by_cases hadj : G.Adj i j
    · have hadj' : G'.Adj i j := h i j hadj
      simp only [hadj, hadj', if_true]
      nlinarith [mul_le_mul hi1 hj1 hj0 (zero_le_one : (0 : ℝ) ≤ 1)]
    · simp only [hadj, if_false]
      have : 0 ≤ (if G'.Adj i j then (1 : ℝ) else 0) := by split <;> norm_num
      nlinarith [mul_nonneg hi0 hj0]
  exact le_trans hsum (le_ciSup (bddAbove_simplex_quadform G') v)

/-- The `k`-th largest adjacency eigenvalue, from the spectral theorem for
Hermitian matrices (`Matrix.IsHermitian.eigenvalues₀` is antitone). -/
noncomputable def adjEigenvalue {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (hk : k < Fintype.card V) : ℝ := by
  classical
  exact (G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨k, hk⟩

/-- The spectral gap of the graph Hamiltonian `H(C) = -A(C)` (item 2 of
Table 1): the gap between the two largest adjacency eigenvalues. -/
noncomputable def spectralGap {V : Type} [Fintype V] [DecidableEq V]
    [Nontrivial V] (G : SimpleGraph V) : ℝ :=
  adjEigenvalue G 0 (by have h := Fintype.one_lt_card (α := V); omega) -
    adjEigenvalue G 1 (by have h := Fintype.one_lt_card (α := V); omega)

/-- The squared overlap of the ground state of `H(C) = -A(C)` with the start
vertex (item 3 of Table 1): the supremum over all ground-state vectors of the
normalised weight at `start`.  All ground-state vectors are proportional, so
this is the "probability" of the remark in Section 5.3 (p. 16). -/
noncomputable def groundOverlap {V : Type} [Fintype V] (G : SimpleGraph V)
    (start : V) : ℝ :=
  ⨆ ψ : {ψ : V → ℝ // IsGroundState (graphHamiltonian G) ψ},
    (ψ.1 start) ^ 2 / (∑ i, ψ.1 i * ψ.1 i)

/-- `f = Ω(1/poly N)` at a fixed problem size `N`: `f ≥ c / N^d`. -/
def IsOmegaInversePolyAt (f : ℝ) (N : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ d : ℕ, c / (N : ℝ) ^ d ≤ f

/-- `f = Ω(1/poly N)` as a sequence. -/
def IsOmegaInversePoly (f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ d : ℕ, ∀ N : ℕ, 1 ≤ N → c / (N : ℝ) ^ d ≤ f N

/-! ## Coin tails and reach-hardness (Section 6) -/

/-- `P_coin(n, N)` (Section 6, p. 18): the probability that a fair coin tossed
`N` times comes up heads at least `n` times. -/
noncomputable def Pcoin (n N : ℕ) : ℝ :=
  ∑ m ∈ Icc n N, (N.choose m : ℝ) * ((2 : ℝ) ^ N)⁻¹

/-- `P_coin` is monotone decreasing in the threshold `n`. -/
theorem Pcoin_antitone {n n' N : ℕ} (h : n ≤ n') : Pcoin n' N ≤ Pcoin n N := by
  classical
  unfold Pcoin
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro m hm
    simp only [Finset.mem_Icc] at hm ⊢
    exact ⟨le_trans h hm.1, hm.2⟩
  · intro m _ hm
    exact mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- A classical algorithm probing a graph in the modified query model.  The
record keeps the query budget and the probability of reaching a vertex set
starting from a start vertex (Section 6, p. 17). -/
structure GraphQueryAlgorithm (V : Type) where
  /-- number of queries -/
  queryCount : ℕ
  /-- probability of reaching the set `S` in `G`, starting from `start` -/
  reachProb : SimpleGraph V → V → Set V → ℝ

/-- **`(p,q)`-hardness to reach a vertex set** (Section 6, p. 17): no
classical algorithm in the modified query model, starting from `start`, can
reach `S` with at most `q` queries with probability greater than `p`. -/
def ReachHard {V : Type} (G : SimpleGraph V) (start : V) (S : Set V)
    (p : ℝ) (q : ℕ) : Prop :=
  ∀ alg : GraphQueryAlgorithm V, alg.queryCount ≤ q → alg.reachProb G start S ≤ p

/-- **Table 1** of Section 3 (p. 10), items 1-5, at a fixed problem size `N`.
`C` and `D` are the two graphs, `startC` is the start vertex of `C`.
1. the ground-state energies of `H(C)` and `H(D)` differ by `Ω(1/poly N)`;
2. the spectral gap of `H(C)` is `Ω(1/poly N)`;
3. the ground-state amplitude of `C` on the start vertex is `Ω(1/poly N)`;
4. with fewer than `q` classical queries in the modified query model the
   mutual information between the query responses and the choice of graph is
   bounded by `S < 1`, for a superpolynomial `q`;
5. the number of vertices is `O(2^{poly N})`.
(The mutual-information bound of item 4 is represented by the `distinguishHard`
field, which is the only place Lemma 5 uses it.) -/
structure Table1 (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    [Nontrivial V] (C D : SimpleGraph V) (startC : V) (N : ℕ) : Prop where
  energySeparation : IsOmegaInversePolyAt (lambda0 C - lambda0 D) N
  gapC : IsOmegaInversePolyAt (spectralGap C) N
  startAmplitude : IsOmegaInversePolyAt (groundOverlap C startC) N
  distinguishHard :
    ∃ (S : ℝ) (q : ℕ), S < 1 ∧ 0 ≤ S ∧ ReachHard C startC (Set.univ : Set V) S q
  vertices : ∃ d : ℕ, Fintype.card V ≤ 2 ^ (d * (N + 1))

end Qatlib.Papers.AdiabNoSign20.MainResults.SourceModel
