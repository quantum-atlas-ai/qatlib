/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabEquiv04.MainResults.Model.HistoryConstruction

/-!
# Computation and locality predicates

This module packages output states, acceptance probabilities, and polynomial size bounds for the
circuit and adiabatic models associated with [AharonovEtAl2007Adiabatic]. It defines finite grid
bases with six states per site, support and neighbor predicates, and the proposition
`TwoLocalGridSimulatesCircuits`.

## Main statements

* `AdiabaticComputation`: endpoint Hamiltonians, an output density matrix, and a locality
  parameter.
* `CircuitDecider`, `AdiabaticDecider`, and `SparseAdiabaticDecider`: size and acceptance
  predicates.
* `TwoLocalGridSimulatesCircuits`: the stated grid simulation conditions.

## References

* [Aharonov et al., 2007][AharonovEtAl2007Adiabatic]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Classical
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.AdiabEquiv04.MainResults.Model

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The complex inner product `(star a) ⬝ᵥ b` of two coordinate vectors. -/
def innerVec (a b : Vector ι) : ℂ := (star a) ⬝ᵥ b

/-- The existence of a complex scalar of squared norm one for which `c • ψ` is within Euclidean
distance `ε` of `φ`. -/
def PhaseClose (ψ φ : Vector ι) (ε : ℝ) : Prop :=
  ∃ c : ℂ, Complex.normSq c = 1 ∧ l2Dist (c • ψ) φ ≤ ε

/-- The condition that `ρ - ketDensity φ` is Hermitian and its trace distance is at most `ε`. -/
def StateClose (ρ : Matrix ι ι ℂ) (φ : Vector ι) (ε : ℝ) : Prop :=
  ∃ h : (ρ - ketDensity φ).IsHermitian, traceDistance ρ (ketDensity φ) h ≤ ε

/-- The sum of the absolute values of the eigenvalues of a Hamiltonian. -/
def hamNorm (H : Hamiltonian ι) : ℝ := ∑ i : Fin (Fintype.card ι), |eigvals H i|

/-- Data consisting of initial and final Hamiltonians, an output density matrix, and a
natural-valued locality parameter. -/
structure AdiabaticComputation (ι : Type) [Fintype ι] [DecidableEq ι] where

  Hinit : Hamiltonian ι

  Hfinal : Hamiltonian ι

  output : Matrix ι ι ℂ

  output_density : IsDensityMatrix output

  locality : ℕ

/-- The condition that `ψ` is a ground vector of the final Hamiltonian and the output state is
`StateClose` to `ψ` with tolerance `ε`. -/
def AdiabaticRunsTo (ε : ℝ) (A : AdiabaticComputation ι) (ψ : Vector ι) : Prop :=
  IsGroundVector A.Hfinal ψ ∧ StateClose A.output ψ ε

/-- The existence of a list of at most `bound` matrices whose sum equals `H`. -/
def HasTermDescription (bound : ℕ) (H : Matrix ι ι ℂ) : Prop :=
  ∃ terms : List (Matrix ι ι ℂ), H = terms.sum ∧ terms.length ≤ bound

/-- The existence of a matrix-sum description with length at most `C * (Fintype.card ι + 1) ^ d`
for natural numbers `C` and `d`. -/
def HasPolyTermDescription (H : Hamiltonian ι) : Prop :=
  ∃ C d : ℕ, HasTermDescription (C * (Fintype.card ι + 1) ^ d) H.mat

/-- The existence of natural `C` and `d` bounding the number of nonzero entries in every row by
`C * (Fintype.card ι + 1) ^ d`. -/
def RowPolynomialSparse (H : Matrix ι ι ℂ) : Prop :=
  ∃ C d : ℕ, ∀ i : ι, (Finset.univ.filter (fun j => H i j ≠ 0)).card ≤
    C * (Fintype.card ι + 1) ^ d

/-- Pointwise row sparsity together with a matrix-sum description bound `(Fintype.card ι + 1) ^
d` uniform over the real path parameter. -/
def ExplicitSparseFamily (H : ℝ → Hamiltonian ι) : Prop :=
  (∀ s : ℝ, RowPolynomialSparse (H s).mat) ∧
    ∃ d : ℕ, ∀ s : ℝ, HasTermDescription ((Fintype.card ι + 1) ^ d) (H s).mat

/-- The six-element type of states assigned to a grid site. -/
abbrev Particle6 := Fin 6

/-- Positions in a rectangular grid with `n` rows and `R + 1` columns. -/
abbrev GridPos (n R : ℕ) := Fin n × Fin (R + 1)

/-- Assignments of a six-state particle to every grid position. -/
abbrev GridBasis (n R : ℕ) := GridPos n R → Particle6

/-- The condition that two grid positions agree in one coordinate and differ by one in the
other. -/
def Neighbor {n R : ℕ} (a b : GridPos n R) : Prop :=
  (a.1 = b.1 ∧ (a.2.val + 1 = b.2.val ∨ b.2.val + 1 = a.2.val)) ∨
  (a.2 = b.2 ∧ (a.1.val + 1 = b.1.val ∨ b.1.val + 1 = a.1.val))

/-- The condition that a matrix entry vanishes whenever its two configurations differ at some
site outside `t`. -/
def SupportedOn {n R : ℕ} (t : Finset (GridPos n R))
    (A : Matrix (GridBasis n R) (GridBasis n R) ℂ) : Prop :=
  ∀ x y : GridBasis n R, (∃ a : GridPos n R, a ∉ t ∧ x a ≠ y a) → A x y = 0

/-- The condition that `t` has at most two sites, any distinct sites in `t` are neighbors, and
`A` satisfies `SupportedOn t A`. -/
def IsTwoLocalNeighborTerm {n R : ℕ} (t : Finset (GridPos n R))
    (A : Matrix (GridBasis n R) (GridBasis n R) ℂ) : Prop :=
  t.card ≤ 2 ∧ (∀ a ∈ t, ∀ b ∈ t, a ≠ b → Neighbor a b) ∧ SupportedOn t A

/-- The existence of a finite sum description whose terms each satisfy `IsTwoLocalNeighborTerm`
on their specified supports. -/
def IsTwoLocalNearestNeighbor {n R : ℕ}
    (H : Matrix (GridBasis n R) (GridBasis n R) ℂ) : Prop :=
  ∃ terms : List (Finset (GridPos n R) × Matrix (GridBasis n R) (GridBasis n R) ℂ),
    (∀ p ∈ terms, IsTwoLocalNeighborTerm p.1 p.2) ∧ H = (terms.map Prod.snd).sum

/-- The sum of the real diagonal entries of `ρ` over configurations whose first qubit is one. -/
def AcceptProb (m : ℕ) (ρ : Matrix (CompBasis (m + 1)) (CompBasis (m + 1)) ℂ) : ℝ :=
  ∑ x : CompBasis (m + 1), if x ⟨0, Nat.succ_pos m⟩ = 1 then (ρ x x).re else 0

/-- The acceptance expression for the pure state obtained by applying the first `Lg` gates to
the all-zero basis vector. -/
def CircuitAcceptProb (m Lg : ℕ) (gates : GateSeq (m + 1)) : ℝ :=
  AcceptProb m (ketDensity (prefixU gates Lg *ᵥ zeroBasis (m + 1)))

/-- The existence, for each Boolean input, of a circuit with polynomially bounded qubit and gate
counts and acceptance at least `2/3` on members and at most `1/3` on nonmembers. -/
def CircuitDecider (Lang : Set (List Bool)) : Prop :=
  ∃ C d : ℕ, ∀ x : List Bool,
    ∃ (m Lg : ℕ) (_hm : m + 1 ≤ C * (x.length + 1) ^ d)
      (gates : GateSeq (m + 1)),
      Lg ≤ C * (x.length + 1) ^ d ∧
      (x ∈ Lang → 2 / 3 ≤ CircuitAcceptProb m Lg gates) ∧
      (x ∉ Lang → CircuitAcceptProb m Lg gates ≤ 1 / 3)

/-- The existence, for each Boolean input, of data of locality `k` with polynomially bounded
qubit count and positive time, whose output satisfies the `2/3` and `1/3` acceptance
conditions. -/
def AdiabaticDecider (k : ℕ) (Lang : Set (List Bool)) : Prop :=
  ∃ C d : ℕ, ∀ x : List Bool,
    ∃ (m : ℕ) (A : AdiabaticComputation (CompBasis (m + 1))) (T : ℝ),
      A.locality = k ∧ 0 < T ∧
      m + 1 ≤ C * (x.length + 1) ^ d ∧
      T ≤ C * (x.length + 1) ^ d ∧
      (x ∈ Lang → 2 / 3 ≤ AcceptProb m A.output) ∧
      (x ∉ Lang → AcceptProb m A.output ≤ 1 / 3)

/-- The existence, for each Boolean input, of an `ExplicitSparseFamily` with polynomially
bounded qubit count and positive time, and a final ground vector satisfying the acceptance
conditions. -/
def SparseAdiabaticDecider (Lang : Set (List Bool)) : Prop :=
  ∃ C d : ℕ, ∀ x : List Bool,
    ∃ (m : ℕ) (H : ℝ → Hamiltonian (CompBasis (m + 1))) (T : ℝ) (ψ : Vector (CompBasis (m + 1))),
      ExplicitSparseFamily H ∧ 0 < T ∧
      m + 1 ≤ C * (x.length + 1) ^ d ∧
      T ≤ C * (x.length + 1) ^ d ∧
      IsGroundVector (H 1) ψ ∧
      (x ∈ Lang → 2 / 3 ≤ AcceptProb m (ketDensity ψ)) ∧
      (x ∉ Lang → AcceptProb m (ketDensity ψ) ≤ 1 / 3)

/-- The set of languages satisfying `AdiabaticDecider k`. -/
def AdiabaticPolyClass (k : ℕ) : Set (Set (List Bool)) :=
  {Lang | AdiabaticDecider k Lang}

/-- The set of languages satisfying `SparseAdiabaticDecider`. -/
def SparseAdiabaticPolyClass : Set (Set (List Bool)) :=
  {Lang | SparseAdiabaticDecider Lang}

/-- The set of languages satisfying `CircuitDecider`. -/
def StandardCircuitPolyClass : Set (Set (List Bool)) :=
  {Lang | CircuitDecider Lang}

/-- The proposition that every circuit with at least two time steps and every positive tolerance
possess grid data satisfying the stated locality, endpoint, time-bound, ground-state output,
circuit-state approximation, and term-description conditions. -/
def TwoLocalGridSimulatesCircuits : Prop :=
  ∀ (n L : ℕ), 2 ≤ L → ∀ (gates : GateSeq n) (ε : ℝ), 0 < ε →
    ∃ (R : ℕ) (A : AdiabaticComputation (GridBasis n R)) (T : ℝ),
      A.locality = 2 ∧ 0 < T ∧
      IsTwoLocalNearestNeighbor A.Hinit.mat ∧
      IsTwoLocalNearestNeighbor A.Hfinal.mat ∧
      (∃ C : ℝ, 0 < C ∧ ∃ d e : ℕ,
        T ≤ C * ((L : ℝ) + 1) ^ d * (1 / ε) ^ e) ∧
      (∃ ψ : Vector (GridBasis n R), AdiabaticRunsTo ε A ψ) ∧
      (∃ (out : Matrix (CompBasis n) (CompBasis n) ℂ),
        IsDensityMatrix out ∧ StateClose out (prefixU gates L *ᵥ zeroBasis n) ε) ∧
      HasPolyTermDescription A.Hinit ∧ HasPolyTermDescription A.Hfinal

end Qatlib.Papers.AdiabEquiv04.MainResults.Model
