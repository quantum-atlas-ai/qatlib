/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdaptiveTest26.MainResults.AdaptiveFidelityTesting
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Measure.MeasureSpace

set_option backward.isDefEq.respectTransparency false

/-!
# AdaptiveTest26 — paper-layer vocabulary

Fixed source: arXiv:2609.08733v1 (*On the Power of Adaptivity in Testing Quantum States in
Fidelity*, Seyfried--Sen--Tomamichel, 2026-09-08), PDF
`prove/assets/2609.08733v1.pdf`.

This file extends the Frozen v2.0.2 vocabulary
`QuantumAlgorithm.Papers.AdaptiveTest26.MainResults` (single-copy global POVMs, non-adaptive and
adaptive strategies, copy ledgers, root fidelity `F(ρ,σ)=‖√ρ√σ‖₁`, `IsH1`, `SuccessFloor`,
`IsTildeOBound`, `IsTildeOmegaLowerBound`, `adaptiveEquivalenceBudget`) with the paper-layer
objects needed by the individual Claim statements:

* Hilbert--Schmidt quantities `‖A‖₂²` and subspace block norms `‖Π(ρ−σ)Π‖₂²` (Definition 3.2(ii),
  p.12);
* spectral block projections and the eigenbasis entries used by Lemma 3.7 (p.12, eq. (19));
* product states, marginals, tensor lifts, Umegaki relative entropy, mutual information and the
  quantum Markov chain condition `I(A:C|B)=0` (Section 8, p.46);
* certifier / subspace-ℓ₂ / independence correctness predicates (Thm 1.1, Lemma 3.12, Thm 1.3);
* Haar unitary laws (Lemma 3.14, p.15 and Section 7, p.39+);
* the qubit non-adaptive lower-bound schedule vocabulary of Section 7.

Bipartite and tripartite systems are indexed on `Fin A × Fin C` and `Fin A × Fin B × Fin C`
(as matrices), while Frozen strategies live on `Operator D = Matrix (Fin D) (Fin D) ℂ`; the
canonical identification `finProdFinEquiv : Fin A × Fin C ≃ Fin (A * C)` converts between the two.

All definitions are mathematical (no placeholder `True`); statements that need distributional
hypotheses carry them explicitly.
-/

namespace Qatlib.Papers.AdaptiveTest26.MainResults

open Qatlib.Papers.AdaptiveTest26.MainResults
open Qatlib.Foundations.PureStateMath
open Matrix MeasureTheory

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder ENNReal Matrix.Norms.L2Operator

variable {D O : ℕ}

/-! ## Hilbert--Schmidt quantities (Definition 3.2, p.12) -/

/-- Squared Hilbert--Schmidt norm `‖A‖₂² = tr(A†A)` (Definition 3.2(ii); written `‖·‖₂²` in the
paper). -/
def hsNormSq (A : Operator D) : ℝ := SchattenTwo A ^ 2

/-- Squared Hilbert--Schmidt norm of a block: `‖Π(ρ − σ)Π‖₂²`, the quantity tested by the subspace
ℓ₂ subroutine (Lemma 3.12, eq. (32), p.14). -/
def subspaceHSSq (P : Operator D) (ρ σ : Operator D) : ℝ :=
  hsNormSq (P * (ρ - σ) * P)

/-- A (Hermitian, idempotent) orthogonal projection. Positive semidefiniteness together with
`P * P = P` forces Hermiticity in finite dimension. -/
def IsProjection (P : Operator D) : Prop := P.PosSemidef ∧ P * P = P

/-- Dimension of the range of a projection (the `d_Π` of Lemma 3.12). -/
def projDim (P : Operator D) : ℕ := Matrix.rank P

/-- The spectral block projection `Π_S = Σ_{i∈S} |σ_i⟩⟨σ_i|` in an eigenbasis given by the columns
of the unitary `U` (Lemma 3.7, p.12). -/
def spectralProj (U : Operator D) (S : Finset (Fin D)) : Operator D :=
  U * Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0) * U.conjTranspose

/-- The eigenbasis matrix elements `⟨σ_i|ρ|σ_j⟩` of `ρ` in the eigenbasis given by `U`. -/
def eigenEntry (U : Operator D) (ρ : Operator D) (i j : Fin D) : ℂ :=
  (U.conjTranspose * ρ * U) i j

/-! ## Product states, marginals and tensor lifts -/

/-- Kronecker product of two operators, indexed on `Fin (A * C)` via `finProdFinEquiv`. -/
def kronState {A C : ℕ} (ρ : Operator A) (σ : Operator C) : Operator (A * C) :=
  fun p q =>
    ρ (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1 *
      σ (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2

/-- Marginal on the first factor of a bipartite operator. -/
def marginalA {A C : ℕ} (ρ : Operator (A * C)) : Operator A :=
  fun a a' => ∑ c, ρ (finProdFinEquiv (a, c)) (finProdFinEquiv (a', c))

/-- Marginal on the second factor of a bipartite operator. -/
def marginalC {A C : ℕ} (ρ : Operator (A * C)) : Operator C :=
  fun c c' => ∑ a, ρ (finProdFinEquiv (a, c)) (finProdFinEquiv (a, c'))

/-- The product of marginals `ρ_A ⊗ ρ_C` of a bipartite state. -/
def productOf {A C : ℕ} (ρ : Operator (A * C)) : Operator (A * C) :=
  kronState (marginalA ρ) (marginalC ρ)

/-- Product state predicate: `ρ_AC = ρ_A ⊗ ρ_C` (`H0` of independence testing, Theorem 1.3). -/
def IsProductState {A C : ℕ} (ρ : Operator (A * C)) : Prop :=
  ∃ ρA ρC, IsDensityOperator ρA ∧ IsDensityOperator ρC ∧ ρ = kronState ρA ρC

/-! ## Entropies, mutual information and quantum Markov chains (Section 8, p.46) -/

/-- Hermitian matrix logarithm via the continuous functional calculus, over an arbitrary finite
index type. -/
def matrixLogG {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  @CFC.log (Matrix ι ι ℂ)
    (inferInstanceAs (NormedRing (Matrix ι ι ℂ)))
    (inferInstanceAs (StarRing (Matrix ι ι ℂ)))
    (inferInstanceAs (NormedAlgebra ℝ (Matrix ι ι ℂ)))
    (inferInstanceAs (ContinuousFunctionalCalculus ℝ (Matrix ι ι ℂ) IsSelfAdjoint)) A

/-- Umegaki relative entropy `re tr[ρ(log ρ − log σ)]` over an arbitrary finite index type. -/
def relativeEntropyG {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ σ : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (ρ * (matrixLogG ρ - matrixLogG σ))).re

/-- Hermitian matrix logarithm on `Operator D`. -/
def matrixLog (A : Operator D) : Operator D := matrixLogG A

/-- Umegaki relative entropy `re tr[ρ(log ρ − log σ)]` on `Operator D`. -/
def relativeEntropy (ρ σ : Operator D) : ℝ := relativeEntropyG ρ σ

/-- Mutual information `I(A:C)_ρ = D(ρ_AC ‖ ρ_A ⊗ ρ_C)` of a bipartite state (used by Theorem 1.3,
p.6). -/
def mutualInformation {A C : ℕ} (ρ : Operator (A * C)) : ℝ :=
  relativeEntropy ρ (productOf ρ)

/-- Tripartite operators over `Fin A × Fin B × Fin C`. -/
abbrev TriOperator (A B C : ℕ) :=
  Matrix (Fin A × Fin B × Fin C) (Fin A × Fin B × Fin C) ℂ

/-- Marginal on the `BC` pair. -/
def triPtraceA {A B C : ℕ} (ρ : TriOperator A B C) : Operator (B * C) :=
  fun p q => ∑ a, ρ (a, (finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2)
    (a, (finProdFinEquiv.symm q).1, (finProdFinEquiv.symm q).2)

/-- Marginal on the `AB` pair. -/
def triPtraceC {A B C : ℕ} (ρ : TriOperator A B C) : Operator (A * B) :=
  fun p q => ∑ c, ρ ((finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2, c)
    ((finProdFinEquiv.symm q).1, (finProdFinEquiv.symm q).2, c)

/-- Marginal on the middle factor `B`. -/
def triPtraceB {A B C : ℕ} (ρ : TriOperator A B C) : Operator B :=
  fun b b' => ∑ a, ∑ c, ρ (a, b, c) (a, b', c)

/-- Lift `ρ_AB` to `ρ_AB ⊗ 1_C` on the triple register. -/
def liftABtoABC {A B C : ℕ} (M : Operator (A * B)) : TriOperator A B C :=
  fun p q =>
    if p.2.2 = q.2.2 then M (finProdFinEquiv (p.1, p.2.1)) (finProdFinEquiv (q.1, q.2.1))
    else 0

/-- Lift `ρ_B` to `ρ_B ⊗ 1_C` on the `BC` register. -/
def liftBtoBC {B C : ℕ} (M : Operator B) : Operator (B * C) :=
  fun p q =>
    if (finProdFinEquiv.symm p).2 = (finProdFinEquiv.symm q).2 then
      M (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1
    else 0

/-- Conditional mutual information
`I(A:C|B)_ρ = D(ρ_ABC ‖ ρ_AB ⊗ 1_C) − D(ρ_BC ‖ ρ_B ⊗ 1_C)` (Section 8, p.46). -/
def conditionalMutualInformation {A B C : ℕ} (ρ : TriOperator A B C) : ℝ :=
  relativeEntropyG ρ (liftABtoABC (triPtraceC ρ))
    - relativeEntropy (triPtraceA ρ) (liftBtoBC (triPtraceB ρ))

/-- A tripartite state is a quantum Markov chain when `I(A:C|B)_ρ = 0` (Section 8, p.46). -/
def IsQuantumMarkovChain {A B C : ℕ} (ρ : TriOperator A B C) : Prop :=
  conditionalMutualInformation ρ = 0

/-! ## Correctness predicates for the testing tasks -/

/-- Correctness of a *certifier* with a known reference state `σ` (Theorem 1.1 / Lemmas 4.1--4.3):
all copies are drawn from the ρ stream, `H0` (`ρ = σ`) is accepted and `H1` (`F(ρ,σ) ≤ 1−ε`) is
rejected, both with probability at least `SuccessFloor`. -/
def IsCorrectNonAdaptiveCertifier (S : RandomizedNonAdaptiveStrategy D O)
    (σ : Operator D) (ε : ℝ) : Prop :=
  IsAdmissibleRandomizedNonAdaptive S ∧
    (∀ i : Fin S.support, ∀ t : Fin (S.component i).steps,
      (S.component i).stream t = StreamTag.rho) ∧
    SuccessFloor ≤ randomizedAcceptProb S σ σ ∧
    (∀ ρ : Operator D, IsDensityOperator ρ → IsH1 ε ρ σ →
      randomizedAcceptProb S ρ σ ≤ 1 - SuccessFloor)

/-- Adaptive counterpart of `IsCorrectNonAdaptiveCertifier` (Lemma 4.3's lower bound is about
adaptive protocols). -/
def IsCorrectAdaptiveCertifier (S : AdaptiveStrategy D O) (σ : Operator D) (ε : ℝ) : Prop :=
  IsAdmissibleAdaptive S ∧
    (∀ (t : Fin S.steps) (hist : Fin t.val → Fin O), S.stream t hist = StreamTag.rho) ∧
    SuccessFloor ≤ adaptiveAcceptProb S σ σ ∧
    (∀ ρ : Operator D, IsDensityOperator ρ → IsH1 ε ρ σ →
      adaptiveAcceptProb S ρ σ ≤ 1 - SuccessFloor)

/-- Correctness of the subspace ℓ₂-testing subroutine of Lemma 3.12: distinguish
`ΠρΠ = ΠσΠ` from `‖Π(ρ−σ)Π‖₂² ≥ ε`, with both sample streams available. -/
def IsCorrectSubspaceL2Tester (S : AdaptiveStrategy D O) (P : Operator D) (ε : ℝ) : Prop :=
  IsAdmissibleAdaptive S ∧
    (∀ ρ σ : Operator D, IsDensityOperator ρ → IsDensityOperator σ →
      P * ρ * P = P * σ * P → SuccessFloor ≤ adaptiveAcceptProb S ρ σ) ∧
    (∀ ρ σ : Operator D, IsDensityOperator ρ → IsDensityOperator σ →
      ε ≤ subspaceHSSq P ρ σ → adaptiveAcceptProb S ρ σ ≤ 1 - SuccessFloor)

/-- Correctness of an independence tester for `ρ_AC` against `ρ_A ⊗ ρ_C` (Theorem 1.3, Lemma 6.2):
the ρ-stream supplies `ρ_AC`, the σ-stream supplies `ρ_A ⊗ ρ_C`, `H0` (`ρ_AC = ρ_A ⊗ ρ_C`) is
accepted and `H1` (`I(A:C)_ρ ≥ ε`) is rejected. -/
def IsCorrectAdaptiveIndependenceTester {A C : ℕ} (S : AdaptiveStrategy (A * C) O)
    (ε : ℝ) : Prop :=
  IsAdmissibleAdaptive S ∧
    (∀ ρ : Operator (A * C), IsDensityOperator ρ → IsProductState ρ →
      SuccessFloor ≤ adaptiveAcceptProb S ρ (productOf ρ)) ∧
    (∀ ρ : Operator (A * C), IsDensityOperator ρ → ε ≤ mutualInformation ρ →
      adaptiveAcceptProb S ρ (productOf ρ) ≤ 1 - SuccessFloor)

/-- Correctness of a randomized non-adaptive certifier when the alternative `H1` is only required to
be rejected on a restricted class of states `Markov` (Theorem 1.5(i), p.7: only quantum Markov
chains are considered). -/
def IsCorrectNonAdaptiveRestrictedCertifier (S : RandomizedNonAdaptiveStrategy D O)
    (σ : Operator D) (Markov : Operator D → Prop) (ε : ℝ) : Prop :=
  IsAdmissibleRandomizedNonAdaptive S ∧
    (∀ i : Fin S.support, ∀ t : Fin (S.component i).steps,
      (S.component i).stream t = StreamTag.rho) ∧
    SuccessFloor ≤ randomizedAcceptProb S σ σ ∧
    (∀ ρ : Operator D, IsDensityOperator ρ → Markov ρ → IsH1 ε ρ σ →
      randomizedAcceptProb S ρ σ ≤ 1 - SuccessFloor)

/-- Correctness of an adaptive equivalence tester restricted to a class `Markov` of states
(Theorem 1.5(ii), p.7). -/
def IsCorrectAdaptiveRestrictedTester (S : AdaptiveStrategy D O)
    (Markov : Operator D → Prop) (ε : ℝ) : Prop :=
  IsAdmissibleAdaptive S ∧
    (∀ ρ : Operator D, IsDensityOperator ρ → Markov ρ →
      SuccessFloor ≤ adaptiveAcceptProb S ρ ρ) ∧
    (∀ ρ σ : Operator D, IsDensityOperator ρ → IsDensityOperator σ →
      Markov ρ → Markov σ → IsH1 ε ρ σ →
        adaptiveAcceptProb S ρ σ ≤ 1 - SuccessFloor)

/-! ## Haar unitary laws -/

/-- A probability law on square matrices supported on unitaries and invariant under left and right
multiplication by unitaries: the model of "`U` is Haar random" used by Lemma 3.14 (p.15) and
Section 7 (p.39+). -/
structure HaarUnitaryLaw (D : ℕ) [MeasurableSpace (Operator D)] where
  /-- The underlying probability measure. -/
  μ : Measure (Operator D)
  /-- It is a probability measure. -/
  isProbability : IsProbabilityMeasure μ
  /-- Almost every sample is unitary. -/
  supported : ∀ᵐ U ∂μ, U.conjTranspose * U = 1
  /-- Left invariance under the unitary group. -/
  leftInvariant : ∀ V : Operator D, V.conjTranspose * V = 1 →
    Measure.map (fun U => V * U) μ = μ
  /-- Right invariance under the unitary group. -/
  rightInvariant : ∀ V : Operator D, V.conjTranspose * V = 1 →
    Measure.map (fun U => U * V) μ = μ

/-- The `i`-th column of a matrix, viewed as a vector. -/
def colVec (U : Operator D) (i : Fin D) : Fin D → ℂ := fun k => U k i

/-- The quadratic-form value `⟨v|M|v⟩` (real part), for Hermitian `M`. -/
def quadraticValue (M : Operator D) (v : Fin D → ℂ) : ℝ :=
  (∑ k, ∑ l, star (v k) * M k l * v l).re

/-- The random variable `tr[Σ_i (U_i† M U_i)²] = Σ_i ⟨U_i|M|U_i⟩²` of Lemma 3.14, for the
eigenvectors `U_i` (columns of the unitary `U`). -/
def haarEnergy (M : Operator D) (U : Operator D) : ℝ :=
  ∑ i : Fin D, (quadraticValue M (colVec U i)) ^ 2

/-! ## Section 7: qubit non-adaptive lower-bound schedule -/

/-- The computational basis vector `|0⟩` on two qubits. -/
def qubitZero : Fin 2 → ℂ := fun k => if k = 0 then 1 else 0

/-- A single-copy non-adaptive qubit measurement schedule: `N` measurements, each with `2`
weighted rank-one effects `c_{i,j}|M_i,j⟩⟨M_i,j|` (Section 7, p.40). The unit vectors
`vector i j` are `|M_i, j⟩`; `weight i j` is `c_{i,j}`. -/
structure QubitSchedule (N : ℕ) where
  /-- The unit vector `|M_i, j⟩`. -/
  vector : Fin N → Fin 2 → (Fin 2 → ℂ)
  /-- The POVM weight `c_{i,j}`. -/
  weight : Fin N → Fin 2 → ℝ
  /-- Weights are nonnegative. -/
  weight_nonneg : ∀ i j, 0 ≤ weight i j

/-- The bias `y_{i,j,U} = |⟨M_i,j|U|0⟩|²` of eq. (234), p.40. -/
def biasY {N : ℕ} (sch : QubitSchedule N) (U : Operator 2) (i : Fin N) (j : Fin 2) : ℝ :=
  Complex.normSq (∑ k, star (sch.vector i j k) * (U *ᵥ qubitZero) k)

/-- The qubit state `ρ_{ε,U} = U†((1−ε)|0⟩⟨0| + ε|1⟩⟨1|)U` of Section 7, p.40. -/
def rhoEps (ε : ℝ) (U : Operator 2) : Operator 2 :=
  U.conjTranspose * Matrix.diagonal (fun k => if k = 0 then ((1 - ε : ℝ) : ℂ) else (ε : ℂ)) * U

/-- The noise term `ε_{i,j,U} = ⟨M_i,j|ρ_{ε,U}|M_i,j⟩` of eq. (235), p.40. -/
def biasEps {N : ℕ} (sch : QubitSchedule N) (ε : ℝ) (U : Operator 2)
    (i : Fin N) (j : Fin 2) : ℝ :=
  quadraticValue (rhoEps ε U) (sch.vector i j)

/-- Membership in the bias bucket `S_{k,U}` (Lemma 7.2, p.41): for `k ≥ 1`,
`2^k ε ≤ y + ε ≤ 2^{k+1} ε`. -/
def inBiasBucket {N : ℕ} (sch : QubitSchedule N) (ε : ℝ) (U : Operator 2)
    (k : ℕ) (i : Fin N) (j : Fin 2) : Prop :=
  (2 : ℝ) ^ k * ε ≤ biasY sch U i j + biasEps sch ε U i j ∧
    biasY sch U i j + biasEps sch ε U i j ≤ (2 : ℝ) ^ (k + 1) * ε

/-- Membership in the lowest bucket `S_{0,U}`: `y + ε ≤ 2ε`. -/
def inLowBucket {N : ℕ} (sch : QubitSchedule N) (ε : ℝ) (U : Operator 2)
    (i : Fin N) (j : Fin 2) : Prop :=
  biasY sch U i j + biasEps sch ε U i j ≤ 2 * ε

/-- Total POVM weight in a bucket. -/
def bucketWeight {N : ℕ} (sch : QubitSchedule N) (U : Operator 2) (ε : ℝ) (k : ℕ) : ℝ := by
  classical
  exact ∑ p : Fin N × Fin 2, if inBiasBucket sch ε U k p.1 p.2 then sch.weight p.1 p.2 else 0

/-- Total POVM weight in the lowest bucket. -/
def lowBucketWeight {N : ℕ} (sch : QubitSchedule N) (U : Operator 2) (ε : ℝ) : ℝ := by
  classical
  exact ∑ p : Fin N × Fin 2, if inLowBucket sch ε U p.1 p.2 then sch.weight p.1 p.2 else 0

/-! ## `Õ` relative to `log(1/ε)` only (Lemma 4.2: no dimensional dependence) -/

/-- `Õ(B)` with polylogarithms in `log(1/ε)` only: `N ≤ C · B · log(1/ε)^k`. Used for Lemma 4.2,
whose polylogarithmic factors are explicitly dimension-free (p.20). -/
def IsTildeOBoundLog (N : ℕ) (B : ℝ) (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, (N : ℝ) ≤ C * B * (Real.log (1 / ε)) ^ k

/-! ## The tripartite index identification -/

/-- Canonical identification `Fin A × Fin B × Fin C ≃ Fin (A * B * C)` used to state Markov-chain
results on `Operator (A * B * C)` (Section 8, p.46). -/
def triIdx (A B C : ℕ) : Fin A × Fin B × Fin C ≃ Fin (A * B * C) :=
  (Equiv.prodAssoc (Fin A) (Fin B) (Fin C)).symm.trans
    ((Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin C))).trans finProdFinEquiv)

/-- The quantum Markov chain condition `I(A:C|B)=0` transported to `Operator (A * B * C)`
(Theorem 1.5, p.7; Section 8, p.46). -/
def IsQuantumMarkovChainOn {A B C : ℕ} (ρ : Operator (A * B * C)) : Prop :=
  IsQuantumMarkovChain (fun p q => ρ (triIdx A B C p) (triIdx A B C q))

/-! ## Bucket families (Algorithm 2, Section 5; Lemmas 5.2--5.7) -/

/-- An empirical bucketing `{Π̂_j}_{j=0}^{k}` with state approximations `H(σ, Π̂_j⁺)`, eigenvalue
bounds `s_j^max`, `s_j^min` (Algorithm 2, p.22; Lemma 5.2, eqs. (88)--(89)). -/
structure BucketFamily (D : ℕ) where
  /-- Number of buckets `k` (so there are `k + 1` indices `[k]_0`). -/
  k : ℕ
  /-- The bucket projections `Π̂_j` (`j ≤ k`). -/
  proj : ℕ → Operator D
  /-- The enlarged bucket projections `Π̂_j⁺` (`j ≤ k`). -/
  projPlus : ℕ → Operator D
  /-- The ideal eigenbuckets `Π_j⁺` of `ρ` used in the analysis (`j ≤ k`). -/
  idealPlus : ℕ → Operator D
  /-- The state approximations `H(σ, Π̂_j⁺)`. -/
  approx : ℕ → Operator D
  /-- The upper eigenvalue bounds `s_j^max`. -/
  smax : ℕ → ℝ
  /-- The lower eigenvalue bounds `s_j^min`. -/
  smin : ℕ → ℝ

/-- The two error guarantees of Lemma 5.2 (eqs. (88)--(89)) for an empirical bucketing of `σ`:
`‖H(σ,Π̂_j⁺) − Π̂_j⁺σΠ̂_j⁺‖_op ≤ α√(η s_j^max)` for `j ∈ [k−1]_0` and
`‖Π̂_j⁺σΠ̂_j⁺‖_op ≤ 2 s_j^max` for `j ∈ [k]_0`. -/
def IsGoodBucketing {D : ℕ} (B : BucketFamily D) (σ : Operator D) (α η : ℝ) : Prop :=
  (∀ j : ℕ, j < B.k →
    OperatorSpectralNorm (B.approx j - B.projPlus j * σ * B.projPlus j)
      ≤ α * Real.sqrt (η * B.smax j)) ∧
  (∀ j : ℕ, j ≤ B.k → OperatorSpectralNorm (B.projPlus j * σ * B.projPlus j)
      ≤ 2 * B.smax j)

/-- A two-dimensional (row/column) bucket family used in the independence-testing analysis of
Section 6 (Lemma 6.4): projections `Π⁺_{ij,kl}` indexed by `[k_A]_0 × [k_C]_0` with eigenvalue
bounds `s^max_{ij,kl}`, `s^min_{ij,kl}`. -/
structure TwoDimBucketFamily (D kA kC : ℕ) where
  /-- The enlarged bucket projections `Π⁺_{ij,kl}`. -/
  projPlus : Fin (kA + 1) → Fin (kC + 1) → Operator D
  /-- The upper eigenvalue bounds `s^max_{ij,kl}`. -/
  smax : Fin (kA + 1) → Fin (kC + 1) → ℝ
  /-- The lower eigenvalue bounds `s^min_{ij,kl}`. -/
  smin : Fin (kA + 1) → Fin (kC + 1) → ℝ

/-- A spectral block of a Hermitian operator `ρ`: an orthogonal projection `P` commuting with `ρ`
whose numerical range on `range P` lies in `[lo, hi]`. This is the only property of the ideal
eigenvalue buckets `Π_i` used by Lemmas 5.5--5.7. -/
def IsSpectralBlockOf {D : ℕ} (ρ P : Operator D) (lo hi : ℝ) : Prop :=
  IsProjection P ∧ P * ρ = ρ * P ∧
    (∀ v : Fin D → ℂ, P *ᵥ v = v → lo ≤ quadraticValue ρ v) ∧
    (∀ v : Fin D → ℂ, P *ᵥ v = v → quadraticValue ρ v ≤ hi)

/-! ## Section 7 quantities -/

/-- The qubit state `ρ_0 = |0⟩⟨0|` used in the lower-bound analysis of Lemma 7.2 (p.41). -/
def rhoZero : Operator 2 := Matrix.diagonal (fun k => if k = 0 then (1 : ℂ) else 0)

/-- The second-moment sum of Lemma 7.3 (eq. (254), p.42):
`Σ_i Σ_{T_i} (c_{i,j} ε_{i,j,U})² / Pr[T_i(ρ_0,U)]`, with `Pr[T_i(ρ_0,U)] = y_{i,j,U}`. -/
def secondMomentSum {N : ℕ} (sch : QubitSchedule N) (ε : ℝ) (U : Operator 2) : ℝ :=
  ∑ p : Fin N × Fin 2,
    (sch.weight p.1 p.2 * biasEps sch ε U p.1 p.2) ^ 2 / biasY sch U p.1 p.2

/-- The total weight of "light" elements `T_i(ρ_0,U) ≤ ε log(1/ε)` whose occurrence probability is
bounded in the second part of Lemma 7.3 (eqs. (258)--(260), p.43). -/
def lightWeight {N : ℕ} (sch : QubitSchedule N) (ε : ℝ) (U : Operator 2) : ℝ := by
  classical
  exact ∑ p : Fin N × Fin 2,
    if biasEps sch ε U p.1 p.2 ≤ ε * Real.log (1 / ε) then sch.weight p.1 p.2 else 0

/-- The typicality factor `g_typical^U = exp(E_R[Σ_i log(1 + c_{i,j}ε_{i,j,U}/Pr[R_i(ρ_0,U)])])`
of Lemma 7.4 (eq. (261), p.43), written as the exponential of the inner expectation `E`. -/
def gTypical (E : ℝ) : ℝ := Real.exp E

end

end Qatlib.Papers.AdaptiveTest26.MainResults
