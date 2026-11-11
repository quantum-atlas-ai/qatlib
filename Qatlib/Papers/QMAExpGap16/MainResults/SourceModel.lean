/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# QMAExpGap16 — source model

Fefferman–Lin, *Quantum Merlin Arthur with Exponentially Small Gap*,
fixed arXiv:1601.01975v1 (8 Jan 2016).

This file records the paper-layer vocabulary needed to state Theorem 1
(`QMA_exp = PSPACE`) and its supporting results.  The paper works with promise
problems `L = (L_yes, L_no)` on bitstrings.  The quantum-circuit, Turing-machine
and matrix-decomposition backends are abstracted behind explicit interface
structures (`BoundedProtocol`, `SpaceDecider`, `QuantumSpaceDecider`,
`MatrixCertificate`); the paper only ever uses them through the bounds recorded
here.  This keeps every *statement* faithful to the source while locating the
shared machine models in `Concepts/WitnessClasses/PromiseVerifier` and
`Concepts/SpectralSketch/SpectrumPerturb` (both still `D`-level scaffolds, see
the block READMEs).

Definitions are numbered as in the paper:
* Definition 1 — `InQMA`;
* Definition 2 — `InBoundedQMA`;
* Definition 3 — `PQSPACE`;
* Definition 5 — `SuccinctMatrixEncoding`;
* Definition 7 — `GappedSuccinctMatrixSingularity`;
* Definition 8 — `PreciseKLocalHamiltonian`.

`QMAexp` is the class `⋃_{c-s > exp(-poly)} QMA(c,s)` of Theorem 1; `PSPACE` is
the class of promise problems decided in deterministic polynomial space.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMAExpGap16.MainResults

open scoped Classical

/-! ## Growth bounds -/

/-- `f` is polynomially bounded: `f n ≤ C · (n+1)^d` for fixed `C, d`. -/
def IsPolynomial (f : ℕ → ℕ) : Prop := ∃ C d : ℕ, ∀ n, f n ≤ C * (n + 1) ^ d

/-- `f` grows at most like `2^{poly}`: `f n ≤ 2^{C·(n+1)^d}` for fixed `C, d`. -/
def IsExponentialOfPolynomial (f : ℕ → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ n, f n ≤ 2 ^ (C * (n + 1) ^ d)

/-! ## Promise problems -/

/-- A promise problem over bitstrings: a YES-set and a NO-set (the promise is
that the two are disjoint, recorded by `WellPosed`). -/
structure PromiseProblem where
  yes : Set (List Bool)
  no : Set (List Bool)

/-- The promise of a promise problem: the YES- and NO-sets are disjoint. -/
def PromiseProblem.WellPosed (L : PromiseProblem) : Prop :=
  ∀ x, x ∈ L.yes → x ∈ L.no → False

/-- Polynomial-time many-one reduction between promise problems.  The reduction
function maps YES to YES and NO to NO, and runs in polynomial time (`time` is the
abstract runtime; the machine model is not needed at the paper layer). -/
structure PolyReduction (A B : PromiseProblem) where
  f : List Bool → List Bool
  map_yes : ∀ x, x ∈ A.yes → f x ∈ B.yes
  map_no : ∀ x, x ∈ A.no → f x ∈ B.no
  time : List Bool → ℕ
  time_poly : ∃ C d : ℕ, ∀ x, time x ≤ C * (x.length + 1) ^ d

/-- `A` polynomial-time reduces to `B`. -/
def ReducesTo (A B : PromiseProblem) : Prop := Nonempty (PolyReduction A B)

/-! ## Quantum Merlin–Arthur (Definitions 1 and 2) -/

/-- A bounded quantum Merlin–Arthur protocol for a promise problem `L`.

`time n`, `workspace n` and `witness n` are the paper's `t(|x|)`, `k(|x|)` and
`m(|x|)` (circuit size, workspace qubits, witness qubits).  `accept x r` says
that *some* witness of the protocol makes the verifier accept `x` with
probability `r`; this is the existential/universal interface of Equations (1)–(4).
The witness register itself is abstracted, as in Definition 2. -/
structure BoundedProtocol (L : PromiseProblem) where
  time : ℕ → ℕ
  workspace : ℕ → ℕ
  witness : ℕ → ℕ
  accept : List Bool → ℝ → Prop
  accept_nonneg : ∀ x r, accept x r → 0 ≤ r
  accept_le_one : ∀ x r, accept x r → r ≤ 1

/-- Definition 2: `L` belongs to `(t,k)`-bounded `QMA_m(c,s)` when some protocol
with circuit size `≤ t`, workspace `≤ k` and witness `≤ m` has completeness `c`
and soundness `s` (as functions of the input length, matching Remark 5). -/
def InBoundedQMA (t k m : ℕ → ℕ) (c s : ℕ → ℝ) (L : PromiseProblem) : Prop :=
  ∃ P : BoundedProtocol L,
    (∀ n, P.time n ≤ t n) ∧
    (∀ n, P.workspace n ≤ k n) ∧
    (∀ n, P.witness n ≤ m n) ∧
    (∀ x, x ∈ L.yes → ∃ r, P.accept x r ∧ c x.length ≤ r) ∧
    (∀ x, x ∈ L.no → ∀ r, P.accept x r → r ≤ s x.length)

/-- Definition 1: `QMA(c,s)` — polynomial size, polynomial workspace and
polynomial witness, with completeness `c` and soundness `s`. -/
def InQMA (c s : ℕ → ℝ) (L : PromiseProblem) : Prop :=
  ∃ t k m : ℕ → ℕ,
    IsPolynomial t ∧ IsPolynomial k ∧ IsPolynomial m ∧ InBoundedQMA t k m c s L

/-- `QMA_exp = ⋃_{c - s > exp(-poly)} QMA(c,s)` (Theorem 1).  The gap
`c(n) - s(n) > 2^{-p(n)}` holds for a fixed polynomial `p`, exponentiated as a
real power; this is the formal reading of `c - s > exp(-poly)`. -/
def QMAexp : Set PromiseProblem :=
  { L | L.WellPosed ∧
      ∃ c s : ℕ → ℝ, ∃ p : ℕ → ℕ, IsPolynomial p ∧
        (∀ n, s n + (2 : ℝ) ^ (-(p n : ℤ)) < c n) ∧ InQMA c s L }

/-! ## Space complexity classes (Definitions 3 and the `PSPACE` class) -/

/-- A deterministic decision procedure with an explicit space budget.  The
Turing machine is abstracted into `space`; the paper only uses the polynomial
space bound. -/
structure SpaceDecider (L : PromiseProblem) where
  run : List Bool → Bool
  correct_yes : ∀ x, x ∈ L.yes → run x = true
  correct_no : ∀ x, x ∈ L.no → run x = false
  space : List Bool → ℕ

/-- `PSPACE`: promise problems decided by a deterministic procedure using
polynomial space. -/
def PSPACE : Set PromiseProblem :=
  { L | L.WellPosed ∧
      ∃ p : ℕ → ℕ, IsPolynomial p ∧ ∃ D : SpaceDecider L, ∀ x, D.space x ≤ p x.length }

/-- An unbounded-error quantum decision procedure with a space budget
(Definition 3: quantum circuits on at most polynomially many qubits, accepting
YES instances with probability at least `c` and NO instances with probability at
most `s`, for some `c > s`). -/
structure QuantumSpaceDecider (L : PromiseProblem) where
  accept : List Bool → ℝ
  accept_nonneg : ∀ x, 0 ≤ accept x
  accept_le_one : ∀ x, accept x ≤ 1
  space : List Bool → ℕ

/-- Definition 3: `PQPSPACE`, unbounded-error quantum polynomial space. -/
def PQSPACE : Set PromiseProblem :=
  { L | L.WellPosed ∧
      ∃ p : ℕ → ℕ, IsPolynomial p ∧ ∃ D : QuantumSpaceDecider L,
        (∃ c s : ℝ, s < c ∧
          (∀ x, x ∈ L.yes → c ≤ D.accept x) ∧
          (∀ x, x ∈ L.no → D.accept x ≤ s)) ∧
        (∀ x, D.space x ≤ p x.length) }

/-! ## Amplified bounded classes (Theorem 8, Corollaries 9 and 10) -/

/-- The class `(2^poly, poly)`-bounded `QMA_m(1 - 2^{-(m+2)}, 2^{-(m+2)})` of
Corollary 10 and Theorem 11. -/
def FastAmplifiedClass : Set PromiseProblem :=
  { L | L.WellPosed ∧
      ∃ m : ℕ → ℕ, IsPolynomial m ∧ ∃ t k : ℕ → ℕ,
        IsExponentialOfPolynomial t ∧ IsPolynomial k ∧
        InBoundedQMA t k m
          (fun n => 1 - (2 : ℝ) ^ (-((m n : ℤ) + 2)))
          (fun n => (2 : ℝ) ^ (-((m n : ℤ) + 2))) L }

/-- The class `(r·2^poly, r·poly)`-bounded `QMA_poly(1 - 2^{-r}, 2^{-r})` of
Corollary 9. -/
def AmplifiedClass (r : ℕ) : Set PromiseProblem :=
  { L | L.WellPosed ∧
      ∃ t k m : ℕ → ℕ,
        (∃ C d : ℕ, ∀ n, t n ≤ r * 2 ^ (C * (n + 1) ^ d)) ∧
        (∃ C d : ℕ, ∀ n, k n ≤ r * C * (n + 1) ^ d) ∧
        IsPolynomial m ∧
        InBoundedQMA t k m
          (fun _ => 1 - (2 : ℝ) ^ (-(r : ℤ)))
          (fun _ => (2 : ℝ) ^ (-(r : ℤ))) L }

/-! ## Succinct matrices (Definitions 5 and 7) -/

/-- The data the paper's succinct decoder (Definition 5) exposes about an
encoded matrix: its dimension, the PSD / symmetry / sparsity / entry-alphabet
promises, and its smallest eigenvalue. -/
structure MatrixCertificate where
  dim : ℕ
  positiveSemidefinite : Prop
  symmetric : Prop
  sparse : Prop
  entriesIn012 : Prop
  minEigenvalue : ℝ

/-- Definition 5: a succinctly representable sparse matrix is given by a decoder
that, on the input encoding, returns the matrix data.  The decoding circuit is
abstracted into `decode`. -/
structure SuccinctMatrixEncoding where
  decode : List Bool → Option MatrixCertificate

/-- Definition 7: Gapped Succinct Matrix Singularity.  A YES instance encodes a
PSD, symmetric, sparse matrix with entries in `{0,1,2}` whose smallest
eigenvalue is `0`; a NO instance encodes such a matrix whose smallest
eigenvalue is at least `2^{-g(n)}` for some polynomial `g`. -/
def GappedSuccinctMatrixSingularity (enc : SuccinctMatrixEncoding) : PromiseProblem where
  yes := { x | ∃ M, enc.decode x = some M ∧ M.positiveSemidefinite ∧ M.symmetric ∧
                  M.sparse ∧ M.entriesIn012 ∧ M.minEigenvalue = 0 }
  no := { x | ∃ g : ℕ → ℕ, IsPolynomial g ∧ ∃ M, enc.decode x = some M ∧
                  M.positiveSemidefinite ∧ M.symmetric ∧ M.sparse ∧ M.entriesIn012 ∧
                  (2 : ℝ) ^ (-(g x.length : ℤ)) ≤ M.minEigenvalue }

/-! ## Precise local Hamiltonian (Definition 8) -/

/-- The ground-state energy of the Hamiltonian encoded by `x`, when `x` is a
valid instance.  The concrete encoding is abstracted; the paper uses only this
value. -/
abbrev GroundEnergyOracle := List Bool → Option ℝ

/-- Definition 8: the precise `k`-local Hamiltonian problem.  A YES instance has
ground energy at most `a(n)`; a NO instance has ground energy at least `b(n)`. -/
def PreciseKLocalHamiltonian (groundEnergyOf : GroundEnergyOracle) (k : ℕ)
    (a b : ℕ → ℝ) : PromiseProblem where
  yes := { x | 0 ≤ k ∧ ∃ E, groundEnergyOf x = some E ∧ E ≤ a x.length }
  no := { x | 0 ≤ k ∧ ∃ E, groundEnergyOf x = some E ∧ b x.length ≤ E }

/-! ## Function class `FPSPACE` (Corollary 3) -/

/-- A deterministic procedure computing a function on bitstrings, with an
explicit space budget. -/
structure SpaceComputable (f : List Bool → List Bool) where
  space : List Bool → ℕ

/-- `FPSPACE`: functions on bitstrings computable in deterministic polynomial
space. -/
def FPSPACE : Set (List Bool → List Bool) :=
  { f | ∃ p : ℕ → ℕ, IsPolynomial p ∧ ∃ M : SpaceComputable f, ∀ x, M.space x ≤ p x.length }

/-! ## Small structural facts -/

/-- The Gapped Succinct Matrix Singularity problem is a well-posed promise
problem: for a fixed decoder, YES (`λ_min = 0`) and NO (`λ_min ≥ 2^{-g} > 0`)
cannot both hold. -/
theorem gst_wellPosed (enc : SuccinctMatrixEncoding) :
    (GappedSuccinctMatrixSingularity enc).WellPosed := by
  intro x hy hn
  obtain ⟨My, hdy, -, -, -, -, hy0⟩ := hy
  obtain ⟨g, -, Mn, hdn, -, -, -, -, hgn⟩ := hn
  rw [hdy] at hdn
  injection hdn with hMn
  subst hMn
  rw [hy0] at hgn
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(g x.length : ℤ)) := zpow_pos (by norm_num) _
  linarith

/-- The precise `k`-local Hamiltonian problem is well posed whenever the promise
gap is positive: the YES bound `a(n)` is strictly below the NO bound `b(n)`. -/
theorem preciseKLocalHamiltonian_wellPosed (groundEnergyOf : GroundEnergyOracle)
    (k : ℕ) (a b : ℕ → ℝ) (hgap : ∀ n, a n < b n) :
    (PreciseKLocalHamiltonian groundEnergyOf k a b).WellPosed := by
  intro x hy hn
  obtain ⟨-, Ey, hEy, hyE⟩ := hy
  obtain ⟨-, En, hEn, hnE⟩ := hn
  rw [hEy] at hEn
  injection hEn with hEn
  subst hEn
  have hlt : a x.length < b x.length := hgap x.length
  linarith

end Qatlib.Papers.QMAExpGap16.MainResults
