/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option backward.isDefEq.respectTransparency false

/-!
# QSDPsolver17 — shared paper interface

Fixed source: van Apeldoorn--Gilyén--Gribling--de Wolf,
*Quantum SDP-Solvers: Better upper and lower bounds*, arXiv:1705.01843v4
(12 Feb 2020).  The definitions below reproduce the paper's notation for
SDP (1)--(2), the polytopes `P_ε(X)` and `P̃(ã, c')`, dual oracles and their
width, the soft-O convention, and the abstract circuit/solver interfaces used
by the paper-layer statements.

The records below pair mathematical outputs with independent resource annotations.
They contain no execution relation, query transcript, or gate decomposition and
therefore cannot certify algorithmic complexity. Unimplemented algorithm headlines
are recorded as `_statement : Prop` definitions, not existence theorems.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSDPsolver17.MainResults

open Matrix

/-! ## Asymptotic conventions -/

/-! These legacy predicates quantify constants at a single input. They do not
express uniform asymptotic bounds for a family of executions. -/

/-- `O(g)` for concrete nonnegative cost functions, with an explicit constant. -/
def BigOAt (cost bound : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ cost ≤ C * bound

/-- `Ω(g)` for concrete nonnegative cost functions, with an explicit constant. -/
def BigOmegaAt (value bound : ℝ) : Prop := ∃ c : ℝ, 0 < c ∧ c * bound ≤ value

/-- `Õ(g)`: at most a constant times `g` times some polylogarithm of `logArg`.
This is the paper's convention (Theorem 1 and throughout): logarithmic factors
in all parameters are hidden. -/
def IsSoftO (cost bound logArg : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, cost ≤ C * bound * (Real.log (2 + logArg)) ^ k

/-! ## Linear algebra predicates -/

/-- Hermitian positive semidefiniteness for complex matrices, matching the
paper's `M ⪰ 0` for `M ∈ ℂ^{n×n}`.  `Matrix.PosSemidef` in Mathlib requires an
ordered coefficient ring, which `ℂ` is not, so the quadratic-form definition is
used directly. -/
def PSD {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  M.IsHermitian ∧ ∀ x : Fin n → ℂ, 0 ≤ (∑ i, star (x i) * (M.mulVec x) i).re

/-- Row sparsity: at most `s` nonzero entries per row (paper Section 2 notation). -/
def RowSparse {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (s : ℕ) : Prop :=
  ∀ i, (Finset.univ.filter (fun k => A i k ≠ 0)).card ≤ s

/-- Diagonal matrix predicate (paper Lemma 11 and Corollary 12 use real diagonal matrices). -/
def IsDiagonal {n : ℕ} {α : Type*} [Zero α] (A : Matrix (Fin n) (Fin n) α) : Prop :=
  ∀ i k, i ≠ k → A i k = 0

/-- Operator-norm bound `‖A‖ ≤ c`, written with the induced `ℓ²` operator norm
through the defining inequality. -/
def OpNormLE {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) : Prop :=
  ∀ x : Fin n → ℂ, ‖A.mulVec x‖ ≤ c * ‖x‖

/-- Real-matrix version of `OpNormLE`, used for the real diagonal claims. -/
def OpNormLE_R {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) : Prop :=
  ∀ x : Fin n → ℝ, ‖A.mulVec x‖ ≤ c * ‖x‖

/-- Spectral operator norm of a complex matrix, defined as a supremum.  It is
used only inside distance statements (`‖U - target‖`), never unfolded. -/
def opNormℂ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ x : Fin n → ℂ, x ≠ 0 ∧ r = ‖A.mulVec x‖ / ‖x‖}

/-- Operator norm distance `‖A - B‖` in the paper's spectral norm. -/
def opDistℂ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : ℝ := opNormℂ (A - B)

section MatrixExp

attribute [local instance] Matrix.linftyOpNormedRing

/-- Matrix exponential `e^{-H}` for complex matrices (paper's Gibbs state). -/
def matExp {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (-H)

/-- Matrix exponential `e^{-H}` for real matrices. -/
def matExpR {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  NormedSpace.exp (-H)

end MatrixExp

/-! ## SDP (1)--(2) -/

/-- Data of the paper's SDP (1) and its dual (2):
`max Tr(CX)` subject to `Tr(A_j X) ≤ b_j`, `X ⪰ 0`, and
`min bᵀy` subject to `∑_j y_j A_j - C ⪰ 0`, `y ≥ 0`. -/
structure SdpData (n m : ℕ) where
  A : Fin m → Matrix (Fin n) (Fin n) ℂ
  C : Matrix (Fin n) (Fin n) ℂ
  b : Fin m → ℝ
  herm_A : ∀ j, (A j).IsHermitian
  herm_C : C.IsHermitian

namespace SdpData

variable {n m : ℕ} (P : SdpData n m)

/-- Primal feasibility of SDP (1). -/
def primalFeasible (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  PSD X ∧ ∀ j, (Matrix.trace (P.A j * X)).re ≤ P.b j

/-- Dual feasibility of SDP (2). -/
def dualFeasible (y : Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧ PSD (∑ j, (y j : ℂ) • P.A j - P.C)

/-- Primal objective `Tr(CX)`. -/
def primalObjective (X : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (Matrix.trace (P.C * X)).re

/-- Dual objective `bᵀy`. -/
def dualObjective (y : Fin m → ℝ) : ℝ := ∑ j, P.b j * y j

/-- `y` is a dual-feasible vector optimal up to additive error `ε`, i.e.
`bᵀy ≤ OPT + ε`; stated without assuming attainment of `OPT` by comparing
against every dual-feasible vector. -/
def dualEpsOptimal (y : Fin m → ℝ) (ε : ℝ) : Prop :=
  P.dualFeasible y ∧ ∀ y', P.dualFeasible y' → P.dualObjective y ≤ P.dualObjective y' + ε

/-- `R` bounds the trace of every primal-feasible point (paper's `R`). -/
def traceBound (R : ℝ) : Prop :=
  ∀ X, P.primalFeasible X → (Matrix.trace X).re ≤ R

/-- `r` bounds the `ℓ¹` norm of an optimal dual solution (paper's `r`). -/
def dualL1Bound (r : ℝ) : Prop :=
  ∃ y0, P.dualFeasible y0 ∧ (∑ j, y0 j) ≤ r ∧
    ∀ y, P.dualFeasible y → P.dualObjective y0 ≤ P.dualObjective y

/-- Paper's normalization assumptions: `‖A_j‖, ‖C‖ ≤ 1`; `s`-sparsity of all
input matrices; and `A_1 = I`, `b_1 = R`. -/
def instanceAssumptions (s : ℕ) (R : ℝ) (hm : 0 < m) : Prop :=
  (∀ j, OpNormLE (P.A j) 1) ∧ OpNormLE P.C 1 ∧
  (∀ j, RowSparse (P.A j) s) ∧ RowSparse P.C s ∧
  P.A ⟨0, hm⟩ = 1 ∧ P.b ⟨0, hm⟩ = R

end SdpData

/-- The paper's polytope `P_ε(X)`: `{y : bᵀy ≤ α, Tr((∑ y_j A_j - C)X) ≥ -ε, y ≥ 0}`. -/
def Polytope {n m : ℕ} (P : SdpData n m) (X : Matrix (Fin n) (Fin n) ℂ)
    (α ε : ℝ) : Set (Fin m → ℝ) :=
  {y | (∑ j, P.b j * y j) ≤ α ∧
       -ε ≤ (Matrix.trace ((∑ j, (y j : ℂ) • P.A j - P.C) * X)).re ∧
       ∀ j, 0 ≤ y j}

/-- The paper's `P̃(ã, c') = {y : bᵀy ≤ α, ∑ y_j ≤ r, ∑ ã_j y_j ≥ c', y ≥ 0}`. -/
def PTilde {n m : ℕ} (P : SdpData n m) (aTilde : Fin m → ℝ)
    (c' α r : ℝ) : Set (Fin m → ℝ) :=
  {y | (∑ j, P.b j * y j) ≤ α ∧ (∑ j, y j) ≤ r ∧
       c' ≤ ∑ j, aTilde j * y j ∧ ∀ j, 0 ≤ y j}

/-- Two SDPs with the same dimensions are equal up to a permutation of the
constraint labels and a permutation of the `n` coordinates, as in Theorem 19. -/
def conjPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := M.submatrix σ σ

/-- Permutation equivalence of SDPs (Theorem 19). -/
def PermutationEquivalent {n m : ℕ} (P Q : SdpData n m) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∃ π : Equiv.Perm (Fin m),
    (∀ j, Q.A j = conjPerm σ (P.A (π j))) ∧ Q.C = conjPerm σ P.C ∧
    (∀ j, Q.b j = P.b (π j))

/-- A dual oracle: `returns α X y` says that on the polytope `P_ε(X)` with
objective guess `α` the oracle may output `y`. -/
structure DualOracle (n m : ℕ) where
  returns : ℝ → Matrix (Fin n) (Fin n) ℂ → (Fin m → ℝ) → Prop

/-- `O` is a correct `Oracle_ε` for the SDP with `ℓ¹`-budget `r`: every output
lies in `P_ε(X) ∩ {∑ y ≤ r}`, and a legal output exists whenever
`P_0(X) ∩ {∑ y ≤ r}` is nonempty (paper Algorithm 2). -/
def IsOracleEps {n m : ℕ} (P : SdpData n m) (O : DualOracle n m)
    (ε α r : ℝ) : Prop :=
  (∀ X y, O.returns α X y →
      y ∈ Polytope P X α ε ∧ (∑ j, y j) ≤ r) ∧
  (∀ X, PSD X →
      (∃ y, y ∈ Polytope P X α 0 ∧ (∑ j, y j) ≤ r) →
      ∃ y, O.returns α X y)

/-- Width bound for a dual oracle: every output `y` on a psd `X` has
`Tr((∑ y_j A_j - C) X) ≤ w` (paper Definition 4). -/
def WidthBound {n m : ℕ} (P : SdpData n m) (O : DualOracle n m)
    (α w : ℝ) : Prop :=
  ∀ X y, PSD X → O.returns α X y →
    (Matrix.trace ((∑ j, (y j : ℂ) • P.A j - P.C) * X)).re ≤ w

/-! ## Algorithm interfaces -/

/-- Legacy output and resource specification for paper Theorem 1.
The probability and cost annotations are independent of `output`; this is not
an implementation certificate. -/
structure QuantumSdpSolver where
  output : ∀ {n m : ℕ}, SdpData n m → ℝ → (Fin m → ℝ)
  successProb : ∀ {n m : ℕ}, SdpData n m → ℝ → ℝ
  queryCost : ∀ {n m : ℕ}, SdpData n m → ℝ → ℝ
  gateCost : ∀ {n m : ℕ}, SdpData n m → ℝ → ℝ

/-- Abstract amplitude-estimation procedure of Lemma 9: `estimate p μ` estimates
the flag probability `p` at multiplicative error `μ`; the other fields are the
success probability and the number of uses of `U/U⁻¹` and gates. -/
structure AmplitudeEstimator where
  estimate : ℝ → ℝ → ℝ
  successProbability : ℝ → ℝ → ℝ
  usesU : ℝ → ℝ → ℝ
  gateCount : ℕ → ℝ → ℝ → ℝ

/-- A flag-circuit specification: `block` is the paper's compressed operator
`(⟨0| ⊗ I) Ũ (|0⟩ ⊗ I)` (or the corresponding prepared probability when
`prob` is used), with query and gate counts.  Used for Lemmas 11/13 and the
smooth-function specifications. No circuit execution is included. -/
structure FlagCircuit (n : ℕ) where
  block : Matrix (Fin n) (Fin n) ℂ
  queries : ℝ
  gates : ℝ

/-- Proposed flag probability and independent resource annotations
(paper Lemma 9/11/13 statements). No probability law or circuit is certified. -/
structure ProbabilityCircuit where
  prob : ℝ
  queries : ℝ
  gates : ℝ

/-- Real-diagonal version of `ProbabilityCircuit` (Lemma 11, Corollary 12). -/
structure RealProbabilityCircuit (n : ℕ) where
  prob : ℝ
  queries : ℝ
  gates : ℝ

/-- Abstract trace-estimation procedure for `Tr(Aρ)` with `ρ = e^{-H}/Tr(e^{-H})`:
`estimate A H θ` returns the additive `θ`-estimate for the pair `(A, H)`. -/
structure TraceEstimationProcedure where
  estimate : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ
  successProbability : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ
  queryCost : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ
  gateCost : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ

/-- A controlled Hamiltonian-simulation procedure of Lemma 36, with its query
and gate counts for the given parameters. -/
structure SimulationProcedure where
  queries : ℝ
  gates : ℝ

/-- Region `G` of Section 2.3: `q` is a probability vector whose convex
combination of the points `(b_j, ã_j)` lies in the upper-left region determined
by `α, c', r` (paper around Lemma 15/16). -/
def InRegionG {m : ℕ} (b aTilde : Fin m → ℝ) (c' α r : ℝ)
    (q : Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ q j) ∧ (∑ j, q j) = 1 ∧
  ∃ N : ℝ, 0 < N ∧ N ≤ r ∧ (∑ j, b j * q j) ≤ α / N ∧ c' / N ≤ ∑ j, aTilde j * q j

/-- A two-sparse oracle algorithm of Lemma 16 (simple version). -/
structure TwoSparseOracleAlgorithm where
  output : ∀ {m : ℕ}, (Fin m → ℝ) → (Fin m → ℝ) → ℝ → ℝ → ℝ → (Fin m → ℝ)
  queryCost : ℕ → ℝ
  otherGates : ℕ → ℝ

/-- Generalized oracle algorithm of Lemma 16 (general version). -/
structure GeneralSparseOracleAlgorithm where
  returns : ∀ {m : ℕ}, (Fin m → ℝ) → (Fin m → ℝ) → ℝ → ℝ → ℝ → (Fin m → ℝ) → Prop
  emptyConclusion : ∀ {m : ℕ}, (Fin m → ℝ) → (Fin m → ℝ) → ℝ → ℝ → ℝ → Prop
  successProbability : ∀ {m : ℕ}, (Fin m → ℝ) → (Fin m → ℝ) → ℝ → ℝ → ℝ → ℝ
  queryCost : ℕ → ℝ
  gateCost : ℕ → ℝ

/-! ## Majority--OR--majority promise problem (Section 4) -/

/-- Majority of `c` bits, true iff strictly more than half are `1`. -/
def Maj (c : ℕ) (z : Fin c → Bool) : Bool :=
  decide (c < 2 * (Finset.univ.filter (fun i => z i = true)).card)

/-- OR of `b` bits. -/
def OrBits (b : ℕ) (z : Fin b → Bool) : Bool := decide (∃ i, z i = true)

/-- The composed function `MAJ_a ∘ OR_b ∘ MAJ_c`. -/
def MajOrMaj (a b c : ℕ) (Z : Fin a → Fin b → Fin c → Bool) : Bool :=
  Maj a (fun i => OrBits b (fun j => Maj c (fun l => Z i j l)))

/-- The promise in Definition 25: every inner `MAJ_c` and the outer `MAJ_a` are
boundary cases. -/
def MajOrMajPromise (a b c : ℕ) (Z : Fin a → Fin b → Fin c → Bool) : Prop :=
  (∀ i j, (Finset.univ.filter (fun l => Z i j l = true)).card = c / 2 ∨
          (Finset.univ.filter (fun l => Z i j l = true)).card = c / 2 + 1) ∧
  (let zt := fun i => OrBits b (fun j => Maj c (fun l => Z i j l))
   (Finset.univ.filter (fun i => zt i = true)).card = a / 2 ∨
   (Finset.univ.filter (fun i => zt i = true)).card = a / 2 + 1)

/-- The quantity `∑_i max_j ∑_ℓ Z_{ijℓ}` of Lemma 27. -/
def MajOrMajValue (a b c : ℕ) (hb : 0 < b) (Z : Fin a → Fin b → Fin c → Bool) : ℝ :=
  ∑ i, Finset.sup' Finset.univ ⟨⟨0, hb⟩, Finset.mem_univ _⟩
    (fun j => ((Finset.univ.filter (fun l => Z i j l = true)).card : ℝ))

/-! ## Eigenvalues and Gibbs states -/

/-- `E` is the smallest eigenvalue of the Hermitian matrix `H` (an eigenvalue
with no smaller real eigenvalue). -/
def IsSmallestEigenvalue {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (E : ℝ) : Prop :=
  ∃ v : Fin n → ℂ, v ≠ 0 ∧ H.mulVec v = (E : ℂ) • v ∧
    ∀ w : Fin n → ℂ, w ≠ 0 → ∀ lam : ℝ, H.mulVec w = (lam : ℂ) • w → E ≤ lam

end Qatlib.Papers.QSDPsolver17.MainResults
