/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.RingTheory.Polynomial.Chebyshev
import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

set_option backward.isDefEq.respectTransparency false

/-!
# Model layer for arXiv:1801.03922v4 (LatticeHam18)

Fixed paper version: Haah--Hastings--Kothari--Low, *Quantum algorithm for
simulating real time evolution of lattice Hamiltonians*, arXiv:1801.03922v4.

This module introduces the objects used by the paper-layer statements:

* a finite lattice of sites with a metric `d`, site-set distances `dist` and
  diameters `diam` (paper p.8, just after Lemma 4);
* the local-Hamiltonian data of Theorem 1 (paper p.4): Hermitian terms
  `h_X(t)`, `h_X = 0` when `diam X > 1`, `‖h_X(t)‖ ≤ 1`, `O(1)` qubits per unit
  ball and entrywise piecewise-slow variation;
* the time-ordered propagator `U_t` for `i ∂_t U = H(t) U`;
* legacy matrix records with resource metadata and a separate layer-realization
  predicate tying those records to explicit operations;
* the Bernstein ellipse `E_ρ` of Appendix D.

Nothing here asserts any paper result; the claim files import this module.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Kronecker

namespace Qatlib.Papers.LatticeHam18.MainResults.Model

/-! ## Site geometry -/

variable {Site : Type} [Fintype Site] [DecidableEq Site]

/-- A metric on the lattice sites (the Euclidean metric of `ℝ^D` in the paper). -/
abbrev SiteMetric := Site → Site → ℝ

/-- Paper p.8: `dist(x, Y)` for a site and a finite set.  For the empty set we
return `0`; every statement that needs the paper's `∞` convention assumes the
set is nonempty (the paper only uses nonempty distance targets). -/
def distTo (d : SiteMetric (Site := Site)) (x : Site) (Y : Finset Site) : ℝ :=
  if h : Y.Nonempty then Y.inf' h (fun y => d x y) else 0

/-- Paper p.8: `dist(X, Y) = min_{x∈X,y∈Y} dist(x,y)`. -/
def setDist (d : SiteMetric (Site := Site)) (X Y : Finset Site) : ℝ :=
  if h : X.Nonempty then X.inf' h (fun x => distTo d x Y) else 0

/-- Paper p.8: `diam(X) = max_{x,x'∈X} dist(x,x')`. -/
def diam (d : SiteMetric (Site := Site)) (X : Finset Site) : ℝ :=
  if h : X.Nonempty then X.sup' h (fun x => X.sup' h (fun y => d x y)) else 0

/-- The open unit ball around a site. -/
def unitBall (d : SiteMetric (Site := Site)) (x : Site) : Finset Site :=
  Finset.univ.filter (fun y => d x y ≤ 1)

/-! ## Series of sites and local Hamiltonians -/

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- Entrywise piecewise-slow variation on `[0,T]` (paper p.4): there are
`M = O(T)` intervals `[t_{j-1}, t_j]` with `0 = t_0 < … < t_M = T` on which
every matrix entry has derivative of norm at most `1/(t_j - t_{j-1})`. -/
def PiecewiseSlowlyVaryingMatrix (f : ℝ → Matrix Q Q ℂ) (T : ℝ) : Prop :=
  ∃ (M : ℕ) (t : Fin (M + 1) → ℝ) (g : ℝ → Q → Q → ℂ),
    (M : ℝ) ≤ T + 1 ∧
    t 0 = 0 ∧ t (Fin.last M) = T ∧
    (∀ i j : Fin (M + 1), i < j → t i < t j) ∧
    ∀ j : Fin M, ∀ s ∈ Set.Ioo (t j.castSucc) (t j.succ), ∀ a b : Q,
      HasDerivAt (fun u => f u a b) (g s a b) s ∧
        ‖g s a b‖ ≤ 1 / (t j.succ - t j.castSucc)

/-- Data of a time-dependent geometrically local Hamiltonian, exactly the
hypotheses of Theorem 1 (paper p.4).  The sum `H(t) = ∑_X h_X(t)` ranges over
all subsets of the finite lattice; the structure keeps the term family and the
hypotheses, and `totalHam` forms the sum. -/
structure TimeDependentLocalHam (Site Q : Type) [Fintype Site] [DecidableEq Site]
    [Fintype Q] [DecidableEq Q] (d : SiteMetric (Site := Site)) (T : ℝ) where
  /-- The local term `h_X(t)` indexed by the support `X`. -/
  term : ℝ → Finset Site → Matrix Q Q ℂ
  /-- Every local term is Hermitian at every time. -/
  herm : ∀ (t : ℝ) (X : Finset Site), (term t X).IsHermitian
  /-- `h_X = 0` if `diam(X) > 1` (strict geometric locality). -/
  strictly_local : ∀ (t : ℝ) (X : Finset Site), term t X = 0 ∨ diam d X ≤ 1
  /-- `‖h_X(t)‖ ≤ 1` for all `X` and `t`. -/
  norm_bound : ∀ (t : ℝ) (X : Finset Site), ‖term t X‖ ≤ 1
  /-- Every unit ball contains `O(1)` qubits: one uniform cardinality bound. -/
  ball_count : ∃ κ : ℕ, ∀ x : Site, (unitBall d x).card ≤ κ
  /-- Every entry of every local term is piecewise slowly varying on `[0,T]`. -/
  slowly_varying : ∀ X : Finset Site, PiecewiseSlowlyVaryingMatrix (fun t => term t X) T

/-- The full Hamiltonian `H(t) = ∑_{X⊆Λ} h_X(t)`. -/
def totalHam (d : SiteMetric (Site := Site)) (T : ℝ) (H : TimeDependentLocalHam Site Q d T)
    (t : ℝ) : Matrix Q Q ℂ :=
  ∑ X : Finset Site, H.term t X

/-- The subsystem Hamiltonian `H_Ω = ∑_{X⊆Ω} h_X` used in Lemma 6. -/
def subHam (d : SiteMetric (Site := Site)) (T : ℝ) (H : TimeDependentLocalHam Site Q d T)
    (Ω : Finset Site) (t : ℝ) : Matrix Q Q ℂ :=
  ∑ X ∈ Finset.univ.filter (fun X : Finset Site => X ⊆ Ω), H.term t X

/-- Data of a time-independent geometrically local Hamiltonian (used by Lemma 6,
Lemma 12 and Proposition 13, paper pp.8--24).  Same hypotheses as Theorem 1
minus the time dependence. -/
structure LocalHam (Site Q : Type) [Fintype Site] [DecidableEq Site]
    [Fintype Q] [DecidableEq Q] (d : SiteMetric (Site := Site)) where
  /-- The local term `h_X` indexed by its support `X`. -/
  term : Finset Site → Matrix Q Q ℂ
  /-- Every local term is Hermitian. -/
  herm : ∀ X : Finset Site, (term X).IsHermitian
  /-- `h_X = 0` if `diam(X) > 1`. -/
  strictly_local : ∀ X : Finset Site, term X = 0 ∨ diam d X ≤ 1
  /-- `‖h_X‖ ≤ 1` for all `X`. -/
  norm_bound : ∀ X : Finset Site, ‖term X‖ ≤ 1
  /-- Every unit ball contains `O(1)` qubits. -/
  ball_count : ∃ κ : ℕ, ∀ x : Site, (unitBall d x).card ≤ κ

/-- The full Hamiltonian `∑_X h_X`. -/
def LocalHam.total {d : SiteMetric (Site := Site)} (h : LocalHam Site Q d) : Matrix Q Q ℂ :=
  ∑ X : Finset Site, h.term X

/-- The subsystem Hamiltonian `H_Ω = ∑_{X⊆Ω} h_X` (paper p.8). -/
def LocalHam.subHam {d : SiteMetric (Site := Site)} (h : LocalHam Site Q d)
    (Ω : Finset Site) : Matrix Q Q ℂ :=
  ∑ X ∈ Finset.univ.filter (fun X : Finset Site => X ⊆ Ω), h.term X

/-- Commutator `[A,B] = AB - BA`. -/
def commutator (A B : Matrix Q Q ℂ) : Matrix Q Q ℂ := A * B - B * A

/-- Heisenberg-picture evolution `A(t) = e^{iHt} A e^{-iHt}` (paper p.21). -/
def heisenbergEvolve (H : Matrix Q Q ℂ) (t : ℝ) (A : Matrix Q Q ℂ) : Matrix Q Q ℂ :=
  NormedSpace.exp ((Complex.I * (t : ℂ)) • H) * A *
    NormedSpace.exp (-((Complex.I * (t : ℂ)) • H))

/-! ## Time-ordered evolution -/

/-- The time-ordered propagator `U_t` of `i ∂_t U = H(t) U`, i.e.
`U_t = 𝒯 exp(-i ∫_0^t H)`, built from the Dyson series in
`Qatlib.Papers.QLinearODE17.TaylorAnalysis.orderedEvolution`
(generator `i • H`). -/
def evolution (H : ℝ → Matrix Q Q ℂ) (t : ℝ) : Matrix Q Q ℂ :=
  Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution
    (fun s => Complex.I • H s) 0 t

/-- The Schrödinger evolution of a time-independent Hermitian `H`. -/
def staticEvolution (H : Matrix Q Q ℂ) (t : ℝ) : Matrix Q Q ℂ :=
  evolution (fun _ => H) t

/-! ## Circuits used by the lower bounds -/

/-- Legacy unitary matrix with independent resource metadata. Only `Realized`
relates these fields to operations; this record alone is not a counted circuit. -/
structure GateCircuit (W : Type) [Fintype W] [DecidableEq W] where
  /-- Number of two-qubit gates. -/
  gates : ℕ
  /-- Circuit depth. -/
  depth : ℕ
  /-- Implemented unitary matrix. -/
  matrix : Matrix W W ℂ
  /-- The matrix is unitary. -/
  mem_unitary : matrix ∈ Matrix.unitaryGroup W ℂ

/-- A counted implementation of a legacy matrix record, relative to an explicit
elementary gate library and admissible parallel layers. These predicates must
encode the desired locality and disjointness restrictions. Counts and matrix are
determined by the same layers; the legacy record alone has no such guarantee. -/
def GateCircuit.Realized {W : Type} [Fintype W] [DecidableEq W]
    (C : GateCircuit W) (elementary : Matrix W W ℂ → Prop)
    (parallel : List (Matrix W W ℂ) → Prop) : Prop :=
  ∃ layers : List (List (Matrix W W ℂ)),
    (∀ layer ∈ layers, parallel layer ∧ ∀ g ∈ layer, elementary g) ∧
    C.gates = (layers.map List.length).sum ∧
    C.depth = layers.length ∧
    C.matrix = layers.foldr (fun layer acc => layer.prod * acc) 1

/-- A realized zero-gate record must implement the identity matrix. -/
theorem GateCircuit.matrix_eq_one_of_realized_zero {W : Type}
    [Fintype W] [DecidableEq W] (C : GateCircuit W)
    (elementary : Matrix W W ℂ → Prop) (parallel : List (Matrix W W ℂ) → Prop)
    (h : C.Realized elementary parallel) (hz : C.gates = 0) : C.matrix = 1 := by
  obtain ⟨layers, hallowed, hg, hd, hm⟩ := h
  rw [hm]
  have hcount : (layers.map List.length).sum = 0 := hg.symm.trans hz
  clear hm hg hz hallowed hd
  induction layers with
  | nil => simp
  | cons layer layers ih =>
    have hc : layer.length = 0 ∧ (layers.map List.length).sum = 0 :=
      Nat.add_eq_zero_iff.mp (by simpa using hcount)
    have hl : layer = [] := List.length_eq_zero_iff.mp hc.1
    simpa [hl] using ih hc.2

/-- `n` qubits together with an arbitrary finite ancilla register `A`
(the lower bounds allow unlimited ancillas, paper p.5). -/
abbrev WithAncilla (n : ℕ) (A : Type) := (Fin n → Bool) × A

/-- The operator `U ⊗ 1_A` on `n` qubits plus ancillas. -/
def extendByAncilla {n : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    Matrix (WithAncilla n A) (WithAncilla n A) ℂ :=
  U ⊗ₖ (1 : Matrix A A ℂ)

/-- Spectral matrix comparison on the enlarged register. This predicate alone
imposes no implementation or resource constraints on `C`. -/
def ApproximatesWithAncillas {n : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (ε : ℝ)
    (C : GateCircuit (WithAncilla n A)) : Prop :=
  ‖C.matrix - extendByAncilla (A := A) U‖ ≤ ε

/-- Basis state `|x⟩|a₀⟩` on `n` qubits plus ancillas. -/
def basisState {n : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (a₀ : A) (x : Fin n → Bool) : WithAncilla n A → ℂ :=
  fun p => if p.1 = x ∧ p.2 = a₀ then 1 else 0

/-- Probability that measuring qubit `i₀` of the circuit output on input `x`
(ancillas initialised in `a₀`) yields `b`. -/
def outputProbability {n : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (C : GateCircuit (WithAncilla n A)) (a₀ : A) (i₀ : Fin n) (x : Fin n → Bool)
    (b : Bool) : ℝ :=
  ∑ p : WithAncilla n A,
    if p.1 i₀ = b then ‖(C.matrix *ᵥ basisState a₀ x) p‖ ^ 2 else 0

/-- Probability that measuring qubit `i₀` of the unitary `V` applied to `|x⟩`
yields `b`. -/
def unitaryFirstQubitProbability {n : ℕ}
    (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (i₀ : Fin n) (x : Fin n → Bool)
    (b : Bool) : ℝ :=
  ∑ p : Fin n → Bool,
    if p i₀ = b then ‖(V *ᵥ (fun q => if q = x then 1 else 0)) p‖ ^ 2 else 0

/-- The circuit `C` reproduces, to error `ε`, every computational-basis
measurement of every output qubit performed after the ideal evolution `U`
(paper Theorem 3, p.5: the lower bound even holds when the only permitted local
measurement is a computational-basis measurement on one output qubit). -/
def ApproximatesLocalFirstQubit {n : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (ε : ℝ) (a₀ : A)
    (C : GateCircuit (WithAncilla n A)) : Prop :=
  ∀ (i₀ : Fin n) (x : Fin n → Bool) (b : Bool),
    |outputProbability C a₀ i₀ x b - unitaryFirstQubitProbability U i₀ x b| ≤ ε

/-- A circuit computes the Boolean function `f` with high probability
(success at least `2/3`, paper p.12). -/
def ComputesBooleanFunction {n : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (C : GateCircuit (WithAncilla n A)) (a₀ : A) (i₀ : Fin n)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool, (2 / 3 : ℝ) ≤ outputProbability C a₀ i₀ x (f x)

/-- Embedding of a two-qubit gate on qubits `i, j` into the `n`-qubit register
(local 2-qubit gate, paper p.5). -/
def localEmbedding (n : ℕ) (i j : Fin n) (g : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  fun x y =>
    if ∀ k : Fin n, k ≠ i → k ≠ j → x k = y k then
      g ((if x i then (1 : Fin 2) else 0), (if x j then (1 : Fin 2) else 0))
        ((if y i then (1 : Fin 2) else 0), (if y j then (1 : Fin 2) else 0))
    else 0

/-- Matrix of one layer of (not necessarily disjoint) two-qubit gates. -/
def layerMatrix (n : ℕ)
    (gates : List (Fin n × Fin n × Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  gates.foldr (fun g acc => localEmbedding n g.1 g.2.1 g.2.2 * acc) 1

/-- A depth-`T` circuit on `n` qubits built from layers of local two-qubit
gates drawn from a gate set `G`.  Ancillas are absent, as in Lemmas 8 and 10. -/
structure LocalCircuit (G : Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) (n : ℕ) where
  /-- The layers, each a list of (qubit pair, gate) entries. -/
  layers : List (List (Fin n × Fin n × Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  /-- Every gate belongs to the gate set. -/
  gate_mem : ∀ l ∈ layers, ∀ g ∈ l, g.2.2 ∈ G
  /-- Total number of gates. -/
  gates : ℕ
  /-- Number of layers (the depth). -/
  depth : ℕ
  /-- Consistency of the counted data. -/
  gates_eq : gates = (layers.map List.length).sum
  /-- Depth is the number of layers. -/
  depth_eq : depth = layers.length

/-- The unitary implemented by a `LocalCircuit`. -/
def LocalCircuit.matrix {G : Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)} {n : ℕ}
    (C : LocalCircuit G n) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  C.layers.foldr (fun l acc => layerMatrix n l * acc) 1

/-- The Boolean function computed with high probability by a local circuit,
measuring the first qubit. -/
def LocalCircuit.Computes {G : Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)} {n : ℕ}
    (C : LocalCircuit G n) (i₀ : Fin n) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool,
    (2 / 3 : ℝ) ≤
      ∑ p : Fin n → Bool,
        if p i₀ = f x then
          ‖((C.matrix) *ᵥ (fun q => if q = x then 1 else 0)) p‖ ^ 2
        else 0

/-- A circuit with an arbitrary gate set and unlimited ancillas, using `G`
non-local two-qubit gates (paper p.12, Lemma 9). -/
structure NonLocalCircuit (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] where
  /-- Number of non-local two-qubit gates. -/
  gates : ℕ
  /-- Implemented unitary. -/
  matrix : Matrix (WithAncilla n A) (WithAncilla n A) ℂ
  /-- The matrix is unitary. -/
  mem_unitary : matrix ∈ Matrix.unitaryGroup (WithAncilla n A) ℂ

/-- A non-local circuit (with ancillas) computes the Boolean function `f` with
high probability by measuring one output qubit (paper p.12). -/
def NonLocalCircuit.Computes {n : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (C : NonLocalCircuit n A) (a₀ : A) (i₀ : Fin n) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool,
    (2 / 3 : ℝ) ≤
      ∑ p : WithAncilla n A,
        if p.1 i₀ = f x then ‖(C.matrix *ᵥ basisState a₀ x) p‖ ^ 2 else 0

/-- An operator on the qubit lattice `Site → Bool` is supported on `X` when it
acts as the identity on the complement of `X` (paper p.21: `A` supported on
`X`, `B` supported on `Y`). -/
def SupportedOn {Site : Type} [Fintype Site] [DecidableEq Site]
    (X : Finset Site) (A : Matrix (Site → Bool) (Site → Bool) ℂ) : Prop :=
  ∃ A_X : Matrix (↥X → Bool) (↥X → Bool) ℂ,
    ∀ f g : Site → Bool, A f g = A_X (fun i : ↥X => f i.1) (fun i : ↥X => g i.1)

/-- Two unitaries are distinguishable when they are separated in spectral norm
by a constant; for unitaries this is equivalent (up to constants) to
distinguishability by a measurement, which is the paper's notion (p.13). -/
def Distinguishable {W : Type} [Fintype W] [DecidableEq W]
    (U V : Matrix W W ℂ) : Prop :=
  (1 / 2 : ℝ) ≤ ‖U - V‖

/-! ## Bernstein ellipse (Appendix D) -/

/-- The Bernstein ellipse `E_ρ`, image of `{z : ℂ | ‖z‖ = ρ}` under
`z ↦ (z + z⁻¹)/2` (paper p.30, Eq. (59) discussion). -/
def bernsteinEllipse (ρ : ℝ) : Set ℂ :=
  {z : ℂ | ∃ w : ℂ, ‖w‖ = ρ ∧ z = (w + w⁻¹) / 2}

end Qatlib.Papers.LatticeHam18.MainResults.Model
