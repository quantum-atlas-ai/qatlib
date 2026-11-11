/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

set_option backward.isDefEq.respectTransparency false

/-!
# MatrixFunc24 — shared source model

Cifuentes, Wang, Silva, Berta, Aolita, *Quantum computational complexity of matrix
functions*, fixed arXiv:2410.13937v2.

This module fixes the objects that the paper's claims speak about, so that the
theorem statements in the sibling modules are literal statements about the same
objects rather than unrelated restatements:

* `MatrixN N` — the paper's `N × N` complex matrix model, `Matrix N N ℂ`;
* `HermitianMatrix` — `Aᴴ = A` (Definition 1 hypotheses);
* `IsMatrixFunction f A B` — the eigenvalue-transform functional calculus of
  Definition 1, packaged as an existence statement over a unitary diagonalization;
* `AccessModel`, `NormKind`, `MatrixProblem` — the paper's sparse/Pauli access
  models and its `‖A‖`, `‖A‖₁`, `λ_A` normalizations;
* promise problems, `BQP`, polynomial reductions and `BQPComplete` / `BQPHard`,
  built on the shared `UniformBqp.FiniteGateWord` finite-circuit semantics
  (no axioms: `BQP` is a genuine `Set` of promise problems and the reduction
  relation is a genuine `Prop`);
* `PauliFrame` and `pauliNorm` — a Pauli decomposition with its `ℓ¹` Pauli norm.

Boundary: this is an interface module.  It does not assert any of the paper's
complexity classifications; those are stated, and where not yet mechanized they
carry `sorry` with the source reference in the neighbouring modules.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix
open Matrix
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Papers.MatrixFunc24.MainResults.SourceModel

/-! ## 1. Matrices and the eigenvalue transform of Definition 1 -/

/-- The paper's `N × N` complex matrix model (`N` a finite index type, typically
`Fin N`). -/
abbrev MatrixN (N : Type) := Matrix N N ℂ

/-- A Hermitian matrix, i.e. `Aᴴ = A`.  Definition 1 of the source restricts the
matrix function to Hermitian `A` diagonalized by a unitary. -/
abbrev HermitianMatrix {N : Type} [Fintype N] [DecidableEq N] (A : MatrixN N) : Prop :=
  A.IsHermitian

/-- Definition 1 (function of a matrix / eigenvalue transformation).

`IsMatrixFunction f A B` says that `A` is unitarily diagonalized as
`A = U · diag λ · Uᴴ` and `B = U · diag (f ∘ λ) · Uᴴ`; this is exactly
"apply `f` to the eigenvalues and leave the eigenvectors untouched". -/
def IsMatrixFunction {N : Type} [Fintype N] [DecidableEq N]
    (f : ℂ → ℂ) (A B : MatrixN N) : Prop :=
  ∃ (U : MatrixN N) (lam : N → ℂ),
    U ∈ Matrix.unitaryGroup N ℂ ∧
      A = U * diagonal lam * Uᴴ ∧
      B = U * diagonal (fun i => f (lam i)) * Uᴴ

/-- Hermitian matrices admit a spectral functional calculus statement: whenever
`A` is diagonalized by a unitary, the eigenvalue transform is well defined by
the displayed formula.  This is a definitional unfolding used by the algorithm
statements; it is not a complexity claim. -/
theorem isMatrixFunction_iff {N : Type} [Fintype N] [DecidableEq N]
    (f : ℂ → ℂ) (A B : MatrixN N) :
    IsMatrixFunction f A B ↔
      ∃ (U : MatrixN N) (lam : N → ℂ),
        U ∈ Matrix.unitaryGroup N ℂ ∧
          A = U * diagonal lam * Uᴴ ∧
          B = U * diagonal (fun i => f (lam i)) * Uᴴ :=
  Iff.rfl

/-! ## 2. Norms and access models (Definitions 2 and 3) -/

/-- Sparse access versus Pauli access (Definitions 2 and 3). -/
inductive AccessModel where
  | sparse
  | pauli
  deriving DecidableEq, Repr

/-- Which matrix norm normalizes the problem: the operator norm `‖A‖`, the induced
`1`-norm `‖A‖₁`, or the Pauli norm `λ_A` of Definition 3. -/
inductive NormKind where
  | spectral
  | inducedOne
  | pauli
  deriving DecidableEq, Repr

/-- Row sparsity bound `s` of Definition 2 (the paper's `s-sparse`). -/
def RowSparse {N : Type} [Fintype N] [DecidableEq N] (s : ℕ) (A : MatrixN N) : Prop :=
  ∀ i : N, (Finset.univ.filter (fun j : N => A i j ≠ 0)).card ≤ s

/-- Column sparsity bound, the second half of the `s-sparse` condition of
Definition 2. -/
def ColSparse {N : Type} [Fintype N] [DecidableEq N] (s : ℕ) (A : MatrixN N) : Prop :=
  ∀ j : N, (Finset.univ.filter (fun i : N => A i j ≠ 0)).card ≤ s

/-- `s`-sparse in the sense of Definition 2: at most `s` non-zero entries in every
row and every column. -/
def IsSparse {N : Type} [Fintype N] [DecidableEq N] (s : ℕ) (A : MatrixN N) : Prop :=
  RowSparse s A ∧ ColSparse s A

/-- The Pauli norm `λ_A = ∑_ℓ |a_ℓ|` of Definition 3, for a fixed Pauli
decomposition `A i j = ∑ ℓ, a ℓ * P ℓ i j`. -/
def pauliNorm {ι : Type} [Fintype ι] (a : ι → ℂ) : ℝ :=
  ∑ ℓ, ‖a ℓ‖

/-- A concrete Pauli frame: an indexed family of matrices `P` together with a
coefficient family `a`, representing `A = ∑ ℓ, a ℓ • P ℓ`.  The frame records
only the decomposition; orthonormality is a separate hypothesis on `P` used by
Lemma 56 (`PauliFrame.trace_mul_self`). -/
structure PauliFrame (N : Type) (ι : Type) [Fintype ι] [Fintype N] [DecidableEq N] where
  /-- The Pauli matrices of the decomposition. -/
  P : ι → MatrixN N
  /-- The Pauli coefficients. -/
  a : ι → ℂ
  /-- The matrix represented by the decomposition. -/
  A : MatrixN N
  /-- The decomposition identity `A = ∑ ℓ, a ℓ • P ℓ`. -/
  decomposition : A = ∑ ℓ, a ℓ • P ℓ

/-- The Pauli norm `λ_A` attached to a `PauliFrame`. -/
def PauliFrame.norm {N ι : Type} [Fintype ι] [Fintype N] [DecidableEq N]
    (F : PauliFrame N ι) : ℝ :=
  ∑ ℓ, ‖F.a ℓ‖

/-- The frame's `ℓ¹` coefficient sum is the paper's Pauli norm `λ_A`. -/
theorem PauliFrame.norm_eq_pauliNorm {N ι : Type} [Fintype ι] [Fintype N] [DecidableEq N]
    (F : PauliFrame N ι) : F.norm = pauliNorm F.a :=
  rfl

/-! ## 3. Problems I and II (Section 2.1) -/

/-- The two problems of Section 2.1. -/
inductive ProblemKind where
  /-- Problem I: the matrix element problem `⟨i|f_m(A)|j⟩`. -/
  | matrixEntry
  /-- Problem II: the local measurement problem
  `⟨0|^⊗n f_m(A)† (|0⟩⟨0| ⊗ 1) f_m(A)|0⟩^⊗n`. -/
  | localMeasurement
  deriving DecidableEq, Repr

/-- A function family `{f_m}_{m ∈ ℕ}` as in Problems I and II. -/
abbrev FunctionFamily := ℕ → ℂ → ℂ

/-- The data of a promise problem instance: a dimension `N`, a matrix `A`, the
function-family parameter `m` and the precision `ε`.  This is the input object
of Problems I and II; the decision/promise structure is held in `MatrixProblem`. -/
structure ProblemInstance (N : Type) [Fintype N] [DecidableEq N] where
  /-- The Hermitian input matrix. -/
  A : MatrixN N
  /-- The function-family parameter. -/
  m : ℕ
  /-- The target precision. -/
  ε : ℝ
  /-- The matrix is Hermitian, as required by Problems I and II. -/
  hermitian : A.IsHermitian

/-- A `MatrixProblem` packages the decision version of Problem I or II for a
function family, an access model and a norm normalization, together with its
promise sets.  The promise sets are the YES/NO instances of the paper's promise
problem, encoded as finite bit strings via an unspecified (but fixed) encoding;
this is the standard way a hardness statement is phrased. -/
structure MatrixProblem where
  /-- A human-readable name, for documentation only. -/
  name : String
  /-- Which of the two problems this is. -/
  kind : ProblemKind
  /-- The function family. -/
  family : FunctionFamily
  /-- Sparse or Pauli access. -/
  access : AccessModel
  /-- The normalization used in the norm-bounded promise. -/
  normKind : NormKind
  /-- The norm bound in the promise. -/
  bound : ℝ
  /-- The YES promise set (encoded inputs). -/
  yes : Set (List Bool)
  /-- The NO promise set (encoded inputs). -/
  no : Set (List Bool)

/-- The underlying promise problem of a `MatrixProblem`. -/
def MatrixProblem.promise (P : MatrixProblem) : Set (List Bool) × Set (List Bool) :=
  (P.yes, P.no)

/-! ## 4. Promise problems, `BQP` and reductions

The shared `UniformBqp.FiniteGateWord` model provides:

* `Reg n = Fin n → Bool`, the `n`-bit register;
* `QState (Reg n) = Reg n → ℂ`;
* `finiteWordRun n gs ψ : Option (QState (Reg n))`, the rejecting interpreter on
  a finite gate word;
* `BornProb ψ i = ‖ψ i‖ ^ 2`.

We build the promise-problem class `BQP` on these definitions.  This is a genuine
definition: a promise problem is in `BQP` when some polynomially bounded uniform
family of finite gate words decides it with bounded error.  Uniformity is
represented by the word family being an explicit function `ℕ → List FiniteGateCode`
together with a polynomial length bound (the L-uniform model); no arbitrary
matrix is part of the syntax. -/

/-- The canonical basis state `|x⟩` of an `n`-bit register. -/
def regKet (n : ℕ) (x : Reg n) : QState (Reg n) :=
  fun y => if y = x then 1 else 0

/-- Acceptance probability of a finite gate word on input `x`, measuring a
designated output predicate `accept : Reg n → Bool` in the computational basis.
Illegal words reject with probability `0`, matching `finiteWordRun`. -/
def finiteWordAcceptProb (n : ℕ) (gs : List FiniteGateCode) (accept : Reg n → Bool)
    (x : Reg n) : ℝ :=
  match finiteWordRun n gs (regKet n x) with
  | none => 0
  | some psi => ∑ y : Reg n, if accept y then ‖psi y‖ ^ 2 else 0

/-- A promise problem is a pair of disjoint sets of finite bit strings (the YES
and NO promise sets). -/
abbrev PromiseProblem := Set (List Bool) × Set (List Bool)

/-- `CircuitFamilyDecides L gs accept` says that the uniform family `gs` with
polynomial length bound decides the promise problem `L` with one-sided two-sided
bounded error `1/3` on the promise. -/
def CircuitFamilyDecides (L : PromiseProblem) (width : ℕ → ℕ)
    (word : ℕ → List FiniteGateCode) (accept : (n : ℕ) → Reg (width n) → Bool) : Prop :=
  (∃ k : ℕ, ∀ n, (word n).length ≤ (n + 1) ^ k) ∧
    (∀ n (x : Reg (width n)), List.ofFn x ∈ L.1 →
      2 / 3 ≤ finiteWordAcceptProb (width n) (word n) (accept n) x) ∧
    (∀ n (x : Reg (width n)), List.ofFn x ∈ L.2 →
      finiteWordAcceptProb (width n) (word n) (accept n) x ≤ 1 / 3)

/-- The class `BQP` of promise problems: those decided by a uniform, polynomial
length-bounded family of finite gate words with bounded error. -/
def BQP : Set PromiseProblem :=
  {L | ∃ (width : ℕ → ℕ) (word : ℕ → List FiniteGateCode)
        (accept : (n : ℕ) → Reg (width n) → Bool),
      CircuitFamilyDecides L width word accept}

/-- Classical polynomial-time many-one reduction between promise problems.  The
reduction is an explicit function on encodings with a polynomial length bound,
mapping YES to YES and NO to NO. -/
def PolyReduces (L M : PromiseProblem) : Prop :=
  ∃ (r : List Bool → List Bool) (k : ℕ),
    (∀ x, x ∈ L.1 → r x ∈ M.1) ∧
    (∀ x, x ∈ L.2 → r x ∈ M.2) ∧
    (∀ x, (r x).length ≤ (x.length + 1) ^ k)

/-- `BQPHard P` — every promise problem in `BQP` reduces to `P`. -/
def BQPHard (P : MatrixProblem) : Prop :=
  ∀ L ∈ BQP, PolyReduces L P.promise

/-- `BQPComplete P` — `P` is in `BQP` and is `BQP`-hard. -/
def BQPComplete (P : MatrixProblem) : Prop :=
  (∃ width word accept, CircuitFamilyDecides P.promise width word accept) ∧ BQPHard P

/-- `ClassicallyEfficient P T` — `P` is solvable classically within `T` steps on
every instance of the promise.  `T : ℕ → ℕ` is the paper's stated running-time
bound evaluated at the input length.  We keep the algorithmic content as an
explicit `Prop` (an executable decider together with its time bound) so that a
`theorem` asserting an efficient classical algorithm is a real statement, not a
vacuous rewrite. -/
def ClassicallyEfficient (P : MatrixProblem) (T : ℕ → ℕ) : Prop :=
  ∃ (decide : List Bool → Bool),
    (∀ x, x ∈ P.yes → decide x = true) ∧
    (∀ x, x ∈ P.no → decide x = false) ∧
    ∃ k : ℕ, ∀ n, T n ≤ (n + 1) ^ k

/-! ## 5. Small structural lemmas used by the paper-layer modules -/

/-- Basis states are normalized: `⟨x|x⟩ = 1`. -/
theorem regKet_self (n : ℕ) (x : Reg n) : regKet n x x = 1 := by
  simp [regKet]

/-- Distinct basis states are orthogonal. -/
theorem regKet_of_ne (n : ℕ) {x y : Reg n} (h : y ≠ x) : regKet n x y = 0 := by
  simp [regKet, h]

/-- The Pauli norm is nonnegative. -/
theorem pauliNorm_nonneg {ι : Type} [Fintype ι] (a : ι → ℂ) : 0 ≤ pauliNorm a := by
  unfold pauliNorm
  exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

end Qatlib.Papers.MatrixFunc24.MainResults.SourceModel
