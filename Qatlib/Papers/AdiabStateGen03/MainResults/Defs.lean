/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Definitions for adiabatic state generation

Introduces finite-dimensional states, Hamiltonian matrices, their operator realization, and
exponential time evolution. Abstract algorithm and circuit records support the predicates
`Simulatable`, `Generable`, and `AdiabaticGenerable`, while variational ground-state and gap
conditions specify the spectral data of an `AdiabaticPath`.

Additional records describe numerical certificates and circuit quantum sampling reductions. Real
matrix row sums, positive detailed balance, row sparsity, and the square-root similarity
transform `HM` provide the definitions used for the Markov-chain construction. See
[AharonovTaShma2007].

## Main statements

* `AdiabaticPath`: A differentiable Hermitian family with unique ground states, positive gap
  bounds, and simulatable Hamiltonians.
* `Simulatable`: Approximation of time evolution by circuit records with the prescribed size
  bound.
* `HM`: The identity minus the square-root-weight similarity transform of a real matrix.

## References

* [Aharonov and Ta‐Shma, 2007][AharonovTaShma2007]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace Qatlib.Papers.AdiabStateGen03.MainResults

variable {n : ℕ}

/-- The index type `Fin (2 ^ n)` for the coordinates of an `n`-qubit state. -/
abbrev Dim (n : ℕ) : Type := Fin (2 ^ n)

/-- The complex Euclidean space with `2 ^ n` coordinates. -/
abbrev State (n : ℕ) : Type := EuclideanSpace ℂ (Dim n)

/-- The complex continuous linear operators on `State n`. -/
abbrev Op (n : ℕ) : Type := State n →L[ℂ] State n

/-- The complex square matrices indexed by `Dim n`. -/
abbrev Ham (n : ℕ) : Type := Matrix (Dim n) (Dim n) ℂ

/-- The condition that a Hamiltonian matrix equals its conjugate transpose. -/
def IsHermitian (H : Ham n) : Prop := Hᴴ = H

/-- The continuous linear operator on Euclidean space represented by a Hamiltonian matrix. -/
def toOp (H : Ham n) : Op n := Matrix.toEuclideanCLM (n := Dim n) (𝕜 := ℂ) H

/-- Passing from a Hamiltonian matrix to its Euclidean operator preserves the norm. -/
theorem norm_toOp (H : Ham n) : ‖toOp H‖ = ‖H‖ := rfl

/-- The operator exponential of `-i t H`, using the Euclidean operator associated with `H`. -/
def timeEvolution (H : Ham n) (t : ℝ) : Op n :=
  NormedSpace.exp ((-t) • (Complex.I • toOp H))

/-- The matrix operator norm of a Hamiltonian. -/
abbrev spectralNorm (H : Ham n) : ℝ := ‖H‖

/-- The existence of natural constants giving a uniform polynomial upper bound on the
real-valued function. -/
def PolyBound (f : ℕ → ℝ) : Prop :=
  ∃ c k : ℕ, ∀ n : ℕ, f n ≤ (c : ℝ) * ((n : ℝ) + 1) ^ k + (c : ℝ)

/-- The existence of a polynomial upper-bound witness for the value `v` at the fixed size `n`. -/
def PolyBoundedAt (n : ℕ) (v : ℝ) : Prop :=
  ∃ c k : ℕ, v ≤ (c : ℝ) * ((n : ℝ) + 1) ^ k + (c : ℝ)

/-- The existence of a positive inverse-polynomial lower bound on `v` at size `n`. -/
def NonNegligibleAt (n : ℕ) (v : ℝ) : Prop :=
  ∃ c k : ℕ, 0 < c ∧ 1 / ((c : ℝ) * ((n : ℝ) + 1) ^ k) ≤ v

/-- An abstract algorithm record consisting of an output function on lists of natural numbers
and an assigned natural step count. -/
structure Algorithm (α : Type) where

  run : List ℕ → List (ℕ × α)

  steps : List ℕ → ℕ

/-- The existence of a uniform polynomial upper bound on the assigned step count in terms of
input-list length. -/
def PolyTime {α : Type} (prog : Algorithm α) : Prop :=
  ∃ c k : ℕ, ∀ inp : List ℕ, prog.steps inp ≤ c * (inp.length + 1) ^ k + c

/-- The list of nonzero entries in row `i`, paired with their natural column indices. -/
def rowEntries {α : Type} [Zero α] [DecidableEq α]
    (A : Matrix (Dim n) (Dim n) α) (i : Dim n) : List (ℕ × α) :=
  (Finset.univ.filter (fun j : Dim n => A i j ≠ 0)).toList.map (fun j => (j.val, A i j))

/-- The condition that every row has at most `D` nonzero entries. -/
def RowSparse {α : Type} [Zero α] [DecidableEq α]
    (A : Matrix (Dim n) (Dim n) α) (D : ℕ) : Prop :=
  ∀ i : Dim n, (Finset.univ.filter (fun j : Dim n => A i j ≠ 0)).card ≤ D

/-- The existence of a `PolyTime` algorithm record that outputs exactly the nonzero entries of
each row from its index. -/
def RowComputable {α : Type} [Zero α] [DecidableEq α]
    (A : Matrix (Dim n) (Dim n) α) : Prop :=
  ∃ prog : Algorithm α, PolyTime prog ∧ ∀ i : Dim n, prog.run [i.val] = rowEntries A i

/-- A complex continuous linear operator with a natural size and a proof that its action does
not increase vector norms. -/
structure Circuit (n : ℕ) where

  unitary : Op n

  size : ℕ

  contract : ∀ ψ : State n, ‖unitary ψ‖ ≤ ‖ψ‖

/-- The existence of a polynomial size-bound witness for the circuit at the fixed size `n`. -/
def PolySize (C : Circuit n) : Prop :=
  ∃ c k : ℕ, (C.size : ℝ) ≤ (c : ℝ) * ((n : ℝ) + 1) ^ k + (c : ℝ)

/-- The existence of a size-bound witness polynomial in the expression `n + t + 1 / α + 1`. -/
def PolySize3 (n : ℕ) (t α : ℝ) (C : Circuit n) : Prop :=
  ∃ c k : ℕ, (C.size : ℝ) ≤ (c : ℝ) * ((n : ℝ) + t + 1 / α + 1) ^ k + (c : ℝ)

/-- For every positive time and accuracy `0 < α < 1`, the existence of a circuit record with
`PolySize3` whose operator approximates `timeEvolution H t` within `α`. -/
def Simulatable (H : Ham n) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : Circuit n, PolySize3 n t α C ∧ ‖C.unitary - timeEvolution H t‖ ≤ α

/-- The Euclidean basis state at coordinate zero. -/
def zeroState (n : ℕ) : State n :=
  EuclideanSpace.single ⟨0, Nat.two_pow_pos n⟩ (1 : ℂ)

/-- Arbitrarily accurate approximation of a transfer from `ψ` to `φ` by circuit records
satisfying `PolySize`. -/
def TransfersState (ψ φ : State n) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : Circuit n, PolySize C ∧ ‖C.unitary ψ - φ‖ ≤ ε

/-- Arbitrarily accurate preparation from `zeroState n` in the sense of `TransfersState`. -/
def Generable (φ : State n) : Prop := TransfersState (zeroState n) φ

/-- An abbreviation for the state-generation predicate `Generable`. -/
abbrev QSamples (φ : State n) : Prop := Generable φ

/-- The real part of the expectation `⟪ψ, toOp H ψ⟫`; no normalization denominator is included. -/
def rayleigh (H : Ham n) (ψ : State n) : ℝ := (⟪ψ, toOp H ψ⟫_ℂ).re

/-- The condition that `ψ` is unit norm and minimizes `rayleigh H` among unit vectors. -/
def IsGroundstate (H : Ham n) (ψ : State n) : Prop :=
  ‖ψ‖ = 1 ∧ ∀ φ : State n, ‖φ‖ = 1 → rayleigh H ψ ≤ rayleigh H φ

/-- The condition that the Hamiltonian operator annihilates every variational ground state. -/
def GroundvalueZero (H : Ham n) : Prop :=
  ∀ ψ : State n, IsGroundstate H ψ → toOp H ψ = 0

/-- A variational ground state that is unique among ground states up to multiplication by a
complex scalar of norm one. -/
def HasUniqueGroundstate (H : Ham n) (ψ : State n) : Prop :=
  IsGroundstate H ψ ∧
    ∀ φ : State n, IsGroundstate H φ → ∃ z : ℂ, ‖z‖ = 1 ∧ φ = z • ψ

/-- The conditional gap bound: if `ψ` is a ground state, every unit vector orthogonal to it has
energy at least `γ` above it. -/
def SpectralGapAtLeast (H : Ham n) (ψ : State n) (γ : ℝ) : Prop :=
  IsGroundstate H ψ →
    ∀ φ : State n, ‖φ‖ = 1 → ⟪ψ, φ⟫_ℂ = 0 → γ ≤ rayleigh H φ - rayleigh H ψ

/-- A differentiable Hermitian Hamiltonian family with specified unique ground states, positive
lower gap bounds, and simulatable Hamiltonians at every real parameter. -/
structure AdiabaticPath (n : ℕ) where

  H : ℝ → Ham n

  herm : ∀ s : ℝ, IsHermitian (H s)

  deriv : ℝ → Ham n

  hasDeriv : ∀ s : ℝ, HasDerivAt H (deriv s) s

  groundState : ℝ → State n

  uniqueGround : ∀ s : ℝ, HasUniqueGroundstate (H s) (groundState s)

  gap : ℝ → ℝ

  gap_spec : ∀ s : ℝ, 0 < gap s ∧ SpectralGapAtLeast (H s) (groundState s) (gap s)

  simulatable : ∀ s : ℝ, Simulatable (H s)

/-- The condition `T * ε ≥ ‖P.deriv s‖ / (P.gap s) ^ 2` at every real path parameter. -/
def AdiabaticCondition (P : AdiabaticPath n) (T ε : ℝ) : Prop :=
  ∀ s : ℝ, T * ε ≥ ‖P.deriv s‖ / (P.gap s) ^ 2

/-- An adiabatic path with positive time and error parameters satisfying `AdiabaticCondition`
and a generable initial ground state. -/
structure AdiabaticGenerator (n : ℕ) where

  path : AdiabaticPath n

  T : ℝ

  ε : ℝ

  T_pos : 0 < T

  ε_pos : 0 < ε

  adiabatic : AdiabaticCondition path T ε

  initial_preparable : Generable (path.groundState 0)

/-- The existence of an adiabatic generator whose ground state at parameter one equals `φ`. -/
def AdiabaticGenerable (φ : State n) : Prop :=
  ∃ G : AdiabaticGenerator n, G.path.groundState 1 = φ

/-- A Boolean decision function on finite bit lists, with yes and no sets characterized by the
two possible outputs. -/
structure PromiseProblem where

  decide : List Bool → Bool

  yes : Set (List Bool)

  no : Set (List Bool)

  mem_yes : ∀ x, x ∈ yes ↔ decide x = true

  mem_no : ∀ x, x ∈ no ↔ decide x = false

/-- A record of a round count, completeness and soundness parameters, and polynomial bounds on
assigned verifier and simulator sizes. -/
structure SZKCertificate where

  rounds : ℕ

  completeness : ℝ

  soundness : ℝ

  verifierSize : List Bool → ℕ

  verifierPoly : ∃ c k : ℕ, ∀ x : List Bool,
    verifierSize x ≤ c * (x.length + 1) ^ k + c

  simulatorSize : List Bool → ℕ

  simulatorPoly : ∃ c k : ℕ, ∀ x : List Bool,
    simulatorSize x ≤ c * (x.length + 1) ^ k + c

  complete : 2 / 3 ≤ completeness

  sound : soundness ≤ 1 / 3

/-- The existence of an `SZKCertificate` with positive completeness. This predicate is
independent of its promise-problem argument. -/
def InSZK (_L : PromiseProblem) : Prop := ∃ cert : SZKCertificate, 0 < cert.completeness

/-- A circuit quantum sampling instance record with error in `[0,1/2]`, input and output sizes,
a gate count, and an output amplitude vector. -/
structure CQSInstance where

  err : ℝ

  err_nonneg : 0 ≤ err

  err_half : err ≤ 1 / 2

  nin : ℕ

  nout : ℕ

  gates : ℕ

  amp : State nout

/-- An indexed family of circuit quantum sampling instances and a Boolean solver function, with
a uniform polynomial bound on instance gate counts. -/
structure CQSFamily where

  inst : ℕ → CQSInstance

  solver : ℕ → Bool

  polyGates : ∃ c k : ℕ, ∀ m : ℕ, (inst m).gates ≤ c * (m + 1) ^ k + c

/-- A circuit quantum sampling family and a polynomially bounded input index map whose solver
output equals the decision function of `L`. -/
structure CQSReduction (L : PromiseProblem) where

  family : CQSFamily

  index : List Bool → ℕ

  polyIndex : ∃ c k : ℕ, ∀ x : List Bool,
    index x ≤ c * (x.length + 1) ^ k + c

  decides : ∀ x : List Bool, family.solver (index x) = L.decide x

/-- The existence of a `CQSReduction` record for the promise problem. -/
def CQSReducible (L : PromiseProblem) : Prop := Nonempty (CQSReduction L)

/-- The real square matrices indexed by the `2 ^ n` configurations. -/
abbrev MC (n : ℕ) : Type := Matrix (Dim n) (Dim n) ℝ

/-- The row-sum-one condition for a real matrix. -/
def IsStochastic (M : MC n) : Prop := ∀ i : Dim n, (∑ j : Dim n, M i j) = 1

/-- The condition that `π` is strictly positive and satisfies the detailed-balance identities `M
i j * π i = M j i * π j`. -/
def IsReversible (M : MC n) (π : Dim n → ℝ) : Prop :=
  (∀ i : Dim n, 0 < π i) ∧ ∀ i j : Dim n, M i j * π i = M j i * π j

/-- The identity minus the similarity expression formed from `M` and diagonal square-root
weights `sqrt (π i)` and their inverses. -/
def HM (M : MC n) (π : Dim n → ℝ) : Ham n :=
  1 - (diagonal (fun i : Dim n => (Real.sqrt (π i) : ℂ))) *
      (M.map (algebraMap ℝ ℂ)) *
      (diagonal (fun i : Dim n => ((Real.sqrt (π i))⁻¹ : ℂ)))

/-- The Euclidean vector with coordinates given by the nonnegative real square roots of `π`. -/
def ketOfDist (π : Dim n → ℝ) : State n :=
  EuclideanSpace.equiv (Dim n) ℂ |>.symm (fun i => (Real.sqrt (π i) : ℂ))

/-- A record of row sums one, positive detailed-balance weights, row computability, and a
row-sparsity bound with a `PolyBoundedAt` witness. -/
structure StronglySamplable (M : MC n) (π : Dim n → ℝ) where

  stochastic : IsStochastic M

  reversible : IsReversible M π

  rowComputable : RowComputable M

  positive : ∀ i : Dim n, 0 < π i

  D : ℕ

  rowSparse : RowSparse M D

  DPoly : PolyBoundedAt n (D : ℝ)

/-- The existence of a `NonNegligibleAt` gap bound for `HM M π` relative to `ketOfDist π` in the
sense of `SpectralGapAtLeast`. -/
def RapidlyMixing (M : MC n) (π : Dim n → ℝ) : Prop :=
  ∃ γ : ℝ, NonNegligibleAt n γ ∧ SpectralGapAtLeast (HM M π) (ketOfDist π) γ

/-- The condition that each sum of square roots of products of consecutive weights has a
`NonNegligibleAt` lower-bound witness. -/
def SlowlyVarying {T : ℕ} (π : Fin (T + 1) → Dim n → ℝ) : Prop :=
  ∀ t : Fin T, NonNegligibleAt n
    (∑ i : Dim n, Real.sqrt (π (Fin.castSucc t) i * π t.succ i))

end Qatlib.Papers.AdiabStateGen03.MainResults
