/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Card
public import Qatlib.Concepts.QmaCompleteness.HistoryHam.QmaCompletenessVerifier

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# `RAMSEY ∈ QMA` (Gaitan--Clark, arXiv:1103.1345v3)

Fixed source: Frank Gaitan and Lane Clark, *Ramsey numbers and adiabatic quantum
computing*, arXiv:1103.1345v3 (8 Jan 2012), pages 3--4 and Appendix
("the Ramsey problem is in QMA because it reduces to the `k`-Local Hamiltonian
problem, which is in QMA").

The paper's problem Hamiltonian `H_P^{Nmn}` (Eq. (3)--(6)) is a sum of
projectors, one per `m`-vertex set (`H_α`) and one per `n`-vertex set (`H^α`).
Each projector acts on the `C(m,2)` (resp. `C(n,2)`) edge qubits of its vertex
set, so `H_P^{Nmn}` is `t`-local with `t = max{C(m,2), C(n,2)}` and has
`C(N,m) + C(N,n)` terms.  Its ground-state energy is `0` below the Ramsey
threshold and `≥ 1` above it , giving the constant promise gap used
by the `k`-Local Hamiltonian reduction.

This module formalises:
* the cost `h(G) = C(G) + I(G)` (Eq. (2)) and the ground-state energy `E_gs`
  (Eq. (4)), together with the energy/threshold dichotomy;
* `edgeSupport`, the edge qubits a projector term acts on, and `edgeSupport_card`;
* the two term families and `termCount_eq = C(N,m) + C(N,n)`;
* `ramseyHamiltonian_is_t_local`, the `t`-locality bound (paper page 3);
* the promise predicates `ramseyYes` / `ramseyNo`, their disjointness, and the
  energy sides of the gap;
* `ramsey_in_qma : InPromiseQMA (ramseyYes ...) (ramseyNo ...)`.

The final theorem constructs an actual finite gate verifier of a graph witness.
Its parameters are fixed outside the input language: the finite truth-table
compiler is not asserted to be polynomial uniformly in `N`.

The cost/threshold model is repeated here (rather than imported) so that this
module elaborates on its own; it mirrors `MainResults/Threshold/SourceThreshold.lean`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.RamseyAdiab11.MainResults.QMA

open Finset
open Qatlib.Concepts.QmaCompleteness.HistoryHam

/-! ## The cost `h(G) = C(G) + I(G)` (paper Eq. (2)) -/

variable {V : Type*}

/-- `C(G)`: the number of `m`-cliques in `G` (paper page 2, Eq. (2)). -/
noncomputable def cliqueCount [Fintype V] (G : SimpleGraph V) (m : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun S : Finset V => G.IsNClique m S)).card

/-- `I(G)`: the number of `n`-independent sets in `G` (paper page 2, Eq. (2)). -/
noncomputable def indepCount [Fintype V] (G : SimpleGraph V) (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun T : Finset V => G.IsNIndepSet n T)).card

/-- Paper Eq. (2), page 2: `h(G) = C(G) + I(G)`. -/
noncomputable def h [Fintype V] (G : SimpleGraph V) (m n : ℕ) : ℕ :=
  cliqueCount G m + indepCount G n

/-- `C(G) = 0` iff `G` has no `m`-clique. -/
theorem cliqueCount_eq_zero_iff [Fintype V] (G : SimpleGraph V) (m : ℕ) :
    cliqueCount G m = 0 ↔ ∀ S : Finset V, ¬ G.IsNClique m S := by
  classical
  simp [cliqueCount]

/-- `I(G) = 0` iff `G` has no `n`-independent set. -/
theorem indepCount_eq_zero_iff [Fintype V] (G : SimpleGraph V) (n : ℕ) :
    indepCount G n = 0 ↔ ∀ T : Finset V, ¬ G.IsNIndepSet n T := by
  classical
  simp [indepCount]

/-- Paper page 2: `h(G) = 0` iff `G` contains neither an `m`-clique nor an
`n`-independent set. -/
theorem h_eq_zero_iff [Fintype V] (G : SimpleGraph V) (m n : ℕ) :
    h G m n = 0 ↔
      (∀ S : Finset V, ¬ G.IsNClique m S) ∧
        (∀ T : Finset V, ¬ G.IsNIndepSet n T) := by
  rw [h, Nat.add_eq_zero_iff, cliqueCount_eq_zero_iff, indepCount_eq_zero_iff]

/-- Paper page 2: `0 < h(G)` iff `G` contains an `m`-clique or an
`n`-independent set. -/
theorem h_pos_iff [Fintype V] (G : SimpleGraph V) (m n : ℕ) :
    0 < h G m n ↔
      (∃ S : Finset V, G.IsNClique m S) ∨ (∃ T : Finset V, G.IsNIndepSet n T) := by
  constructor
  · intro hp
    by_contra hcon
    push Not at hcon
    exact absurd ((h_eq_zero_iff G m n).mpr hcon) (Nat.pos_iff_ne_zero.mp hp)
  · rintro (⟨S, hS⟩ | ⟨T, hT⟩)
    · exact Nat.pos_of_ne_zero fun hz => ((h_eq_zero_iff G m n).mp hz).1 S hS
    · exact Nat.pos_of_ne_zero fun hz => ((h_eq_zero_iff G m n).mp hz).2 T hT

/-! ## Ground-state energy (Eq. (4)) and the Ramsey predicate -/

/-- The ground-state energy `E_gs` of the Ramsey problem Hamiltonian: the
minimum of `h(G)` over all `N`-vertex graphs (Eq. (4), page 2). -/
noncomputable def groundStateEnergy [Fintype V] (m n : ℕ) : ℕ := by
  classical
  have : Nonempty (SimpleGraph V) := ⟨⊥⟩
  exact (Finset.univ.image (fun G : SimpleGraph V => h G m n)).min'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- `0 < E_gs` iff every graph has positive cost (paper page 2). -/
theorem groundStateEnergy_pos_iff [Fintype V] (m n : ℕ) :
    0 < groundStateEnergy (V := V) m n ↔ ∀ G : SimpleGraph V, 0 < h G m n := by
  classical
  have : Nonempty (SimpleGraph V) := ⟨⊥⟩
  unfold groundStateEnergy
  rw [Finset.lt_min'_iff]
  constructor
  · intro H G
    exact H (h G m n) (Finset.mem_image.mpr ⟨G, Finset.mem_univ G, rfl⟩)
  · intro H b hb
    obtain ⟨G, -, rfl⟩ := Finset.mem_image.1 hb
    exact H G

/-- Paper page 2: `R(m,n)` is the least `N` such that every `N`-vertex graph
contains an `m`-clique or an `n`-independent set. -/
def RamseyProp (m n N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    (∃ S : Finset (Fin N), G.IsNClique m S) ∨
      (∃ T : Finset (Fin N), G.IsNIndepSet n T)

/-- Paper core dichotomy: `N` is Ramsey for `(m,n)` iff the ground-state
energy of `H_P^{Nmn}` is strictly positive. -/
theorem ramseyProp_iff_groundStateEnergy_pos (m n N : ℕ) :
    RamseyProp m n N ↔ 0 < groundStateEnergy (V := Fin N) m n := by
  rw [groundStateEnergy_pos_iff]
  unfold RamseyProp
  constructor
  · intro hh G
    rcases hh G with ⟨S, hS⟩ | ⟨T, hT⟩
    · exact (h_pos_iff G m n).mpr (Or.inl ⟨S, hS⟩)
    · exact (h_pos_iff G m n).mpr (Or.inr ⟨T, hT⟩)
  · intro hh G
    rcases (h_pos_iff G m n).mp (hh G) with ⟨S, hS⟩ | ⟨T, hT⟩
    · exact Or.inl ⟨S, hS⟩
    · exact Or.inr ⟨T, hT⟩

/-! ## Edge support and terms of the Ramsey Hamiltonian -/

variable {W : Type*}

/-- The set of qubits associated with the vertex set `S`, i.e. the unordered
pairs of distinct vertices of `S`.  These are the `C(|S|,2)` edge positions on
which the paper's projector `H_α` / `H^α` depends (paper page 3). -/
noncomputable def edgeSupport [DecidableEq W] (S : Finset W) : Finset (Sym2 W) :=
  S.offDiag.image Sym2.mk.uncurry

/-- The edge support of a `|S|`-vertex set has `C(|S|,2)` qubits. -/
theorem edgeSupport_card [DecidableEq W] (S : Finset W) :
    (edgeSupport S).card = S.card.choose 2 :=
  Sym2.card_image_offDiag S

variable [Fintype W]

/-- The `m`-vertex sets indexing the clique terms `H_α` (paper pages 2--3). -/
noncomputable def cliqueTermSets (m : ℕ) : Finset (Finset W) :=
  Finset.univ.powersetCard m

/-- The `n`-vertex sets indexing the independent-set terms `H^α` (paper page 3). -/
noncomputable def indepTermSets (n : ℕ) : Finset (Finset W) :=
  Finset.univ.powersetCard n

/-- There are `C(N,m)` clique terms. -/
theorem cliqueTermSets_card (m : ℕ) :
    (cliqueTermSets (W := W) m).card = (Fintype.card W).choose m := by
  classical
  simp [cliqueTermSets]

/-- There are `C(N,n)` independent-set terms. -/
theorem indepTermSets_card (n : ℕ) :
    (indepTermSets (W := W) n).card = (Fintype.card W).choose n := by
  classical
  simp [indepTermSets]

/-- Total number of terms of `H_P^{Nmn}`: `C(N,m) + C(N,n)` (paper page 3). -/
noncomputable def termCount (m n : ℕ) : ℕ :=
  (cliqueTermSets (W := W) m).card + (indepTermSets (W := W) n).card

/-- Paper page 3: `H_P^{Nmn}` contains `C(N,m)+C(N,n)` terms. -/
theorem termCount_eq (m n : ℕ) :
    termCount (W := W) m n =
      (Fintype.card W).choose m + (Fintype.card W).choose n := by
  classical
  simp [termCount, cliqueTermSets_card, indepTermSets_card]

/-- Each clique term `H_α` acts on at most `C(m,2)` qubits (paper page 3). -/
theorem cliqueTerm_edgeSupport_card_le [DecidableEq W] (m n : ℕ) {S : Finset W}
    (hS : S ∈ cliqueTermSets (W := W) m) :
    (edgeSupport S).card ≤ max (m.choose 2) (n.choose 2) := by
  rw [edgeSupport_card]
  rw [(Finset.mem_powersetCard.mp hS).2]
  exact le_max_left _ _

/-- Each independent-set term `H^α` acts on at most `C(n,2)` qubits (paper page 3). -/
theorem indepTerm_edgeSupport_card_le [DecidableEq W] (m n : ℕ) {T : Finset W}
    (hT : T ∈ indepTermSets (W := W) n) :
    (edgeSupport T).card ≤ max (m.choose 2) (n.choose 2) := by
  rw [edgeSupport_card]
  rw [(Finset.mem_powersetCard.mp hT).2]
  exact le_max_right _ _

/-- Paper page 3: `H_P^{Nmn}` is `t`-local with `t = max{C(m,2), C(n,2)}`. -/
theorem ramseyHamiltonian_is_t_local [DecidableEq W] (m n : ℕ) :
    (∀ S ∈ cliqueTermSets (W := W) m,
        (edgeSupport S).card ≤ max (m.choose 2) (n.choose 2)) ∧
      (∀ T ∈ indepTermSets (W := W) n,
        (edgeSupport T).card ≤ max (m.choose 2) (n.choose 2)) :=
  ⟨fun _ hS => cliqueTerm_edgeSupport_card_le m n hS,
    fun _ hT => indepTerm_edgeSupport_card_le m n hT⟩

/-! ## The `RAMSEY` promise problem -/

/-- Paper pages 3--4: the yes side of the `RAMSEY` promise problem.  Inputs are
bit strings of length `C(N,2)` (an `N`-vertex graph, Eq. (1)); they are yes
instances when `N` is below the Ramsey threshold, i.e. `¬ RamseyProp m n N`,
equivalently `E_gs = 0` . -/
def ramseyYes (m n N : ℕ) (x : List Bool) : Prop :=
  x.length = N.choose 2 ∧ ¬ RamseyProp m n N

/-- Paper pages 3--4: the no side of the `RAMSEY` promise problem: `N` is at or
above the Ramsey threshold, i.e. `RamseyProp m n N`, equivalently `E_gs ≥ 1`. -/
def ramseyNo (m n N : ℕ) (x : List Bool) : Prop :=
  x.length = N.choose 2 ∧ RamseyProp m n N

/-- The yes and no sets of the `RAMSEY` promise problem are disjoint. -/
theorem ramseyYes_disjoint_ramseyNo (m n N : ℕ) :
    ∀ x : List Bool, ¬ (ramseyYes m n N x ∧ ramseyNo m n N x) := by
  intro x hx
  exact hx.1.2 hx.2.2

/-- Below threshold: the ground-state energy of `H_P^{Nmn}` vanishes. -/
theorem ramseyYes_energy_zero (m n N : ℕ) (hh : ¬ RamseyProp m n N) :
    groundStateEnergy (V := Fin N) m n = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  exact hh ((ramseyProp_iff_groundStateEnergy_pos m n N).mpr hpos)

/-- At or above threshold: the ground-state energy is at least `1`. -/
theorem ramseyNo_energy_pos (m n N : ℕ) (hh : RamseyProp m n N) :
    1 ≤ groundStateEnergy (V := Fin N) m n :=
  Nat.succ_le_of_lt ((ramseyProp_iff_groundStateEnergy_pos m n N).mp hh)

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

/-- Decode an adjacency-bit witness to an undirected loopless graph. -/
def witnessGraph (N : ℕ) (w : Reg (N * N)) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun i j => w (finProdFinEquiv (i, j)) = true

/-- Encode every graph by its adjacency matrix bits. -/
noncomputable def graphWitness {N : ℕ} (G : SimpleGraph (Fin N)) : Reg (N * N) := by
  classical
  exact fun z => decide (G.Adj (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2)

/-- The adjacency witness decodes to the original graph. -/
theorem witnessGraph_encode {N : ℕ} (G : SimpleGraph (Fin N)) :
    witnessGraph N (graphWitness G) = G := by
  classical
  ext i j
  simp only [witnessGraph, SimpleGraph.fromRel_adj, graphWitness,
    Equiv.symm_apply_apply, decide_eq_true_eq, G.adj_comm, or_self]
  exact ⟨fun hh => hh.2, fun hh => ⟨G.ne_of_adj hh, hh⟩⟩

/-- The finite graph-witness test checks the absence of both forbidden subgraphs. -/
noncomputable def graphCheck (m n N : ℕ) (w : Reg (N * N)) : Bool := by
  classical
  exact decide (h (witnessGraph N w) m n = 0)

/-- The all-true characteristic projector is the identity. -/
private theorem char_true (b : ℕ) :
    charProjector b (fun _ => true) = 1 := by
  ext i j
  simp [charProjector, Matrix.diagonal, Matrix.one_apply]

/-- A passing basis witness has unit acceptance mass after the Hadamard transform. -/
private theorem passing_mass {b : ℕ} (S : Reg b → Bool) (w : Reg b)
    (hw : S w = true) :
    forrWitnessMass b S (fun _ => true) (Qatlib.Foundations.PureStateMath.Ket w) = 1 := by
  have hp : (charProjector b S).mulVec (Qatlib.Foundations.PureStateMath.Ket w) =
      Qatlib.Foundations.PureStateMath.Ket w := by
    ext z
    rw [cnotAux_char_mulVec]
    by_cases hz : z = w
    · subst z
      simp [Qatlib.Foundations.PureStateMath.Ket, hw]
    · simp [Qatlib.Foundations.PureStateMath.Ket, hz]
  unfold forrWitnessMass
  rw [char_true, Matrix.one_mul, ← Matrix.mulVec_mulVec, hp]
  have hn := normalized_applyGate (hadamardN_unitary b) (normalized_ket w)
  have hh := (normalized_iff_norm_toEuclidean_fromVec _).mp hn
  change ‖toEuclidean_fromVec ((HadamardN b).mulVec
    (Qatlib.Foundations.PureStateMath.Ket w))‖ = 1 at hh
  rw [hh]
  norm_num

/-- A checker false on every witness has zero acceptance mass for every state. -/
private theorem rejecting_mass {b : ℕ} (S : Reg b → Bool)
    (hS : ∀ w, S w = false) (ψ : QState (Reg b)) :
    forrWitnessMass b S (fun _ => true) ψ = 0 := by
  have hp : charProjector b S = 0 := by
    ext i j
    simp [charProjector, hS]
  simp [forrWitnessMass, hp, toEuclidean_fromVec]

/-- The fixed-parameter Ramsey language has a finite gate graph-witness verifier.
The program evaluates the actual adjacency-witness predicate using reversible
truth-table compilation, then uses the proved acceptance semantics of that
program. Since `m,n,N` are fixed outside the language input, its gate bound is
constant in input length. This does not assert a polynomial bound uniform in
`N`, nor a uniform Ramsey problem with parameters encoded in the input. -/
theorem ramsey_in_qma (m n N : ℕ) :
    InPromiseQMA (ramseyYes m n N) (ramseyNo m n N) := by
  classical
  let S := graphCheck m n N
  refine ⟨cnotAuxVf (N * N) S (fun _ => true), ?_, ?_⟩
  · intro x hx
    have hex : ∃ G : SimpleGraph (Fin N), h G m n = 0 := by
      by_contra hnone
      have hg : ∀ G : SimpleGraph (Fin N), 0 < h G m n := by
        intro G
        exact Nat.pos_of_ne_zero fun hz => hnone ⟨G, hz⟩
      exact hx.2 ((ramseyProp_iff_groundStateEnergy_pos m n N).mpr
        ((groundStateEnergy_pos_iff m n).mpr hg))
    obtain ⟨G, hG⟩ := hex
    let w := graphWitness G
    have hw : S w = true := by
      simp [S, graphCheck, w, witnessGraph_encode, hG]
    refine ⟨Ket w, normalized_ket w, ?_⟩
    change 2 / 3 ≤ qmaAcceptProb (cnotAuxVf (N * N) S (fun _ => true)) x (Ket w)
    rw [show qmaAcceptProb (cnotAuxVf (N * N) S (fun _ => true)) x (Ket w) =
      forrWitnessMass (N * N) S (fun _ => true) (Ket w) from
        cnotAux_accept_eq_forr (N * N) S (fun _ => true) (Ket w)]
    rw [passing_mass S w hw]
    norm_num
  · intro x hx ψ _hψ
    have hS : ∀ w, S w = false := by
      intro w
      have hp := (h_pos_iff (witnessGraph N w) m n).mpr (hx.2 _)
      simp [S, graphCheck, Nat.ne_of_gt hp]
    change qmaAcceptProb (cnotAuxVf (N * N) S (fun _ => true)) x ψ ≤ 1 / 3
    rw [show qmaAcceptProb (cnotAuxVf (N * N) S (fun _ => true)) x ψ =
      forrWitnessMass (N * N) S (fun _ => true) ψ from
        cnotAux_accept_eq_forr (N * N) S (fun _ => true) ψ]
    rw [rejecting_mass S hS ψ]
    norm_num

end Qatlib.Papers.RamseyAdiab11.MainResults.QMA
