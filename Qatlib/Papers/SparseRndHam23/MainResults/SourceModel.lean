/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option backward.isDefEq.respectTransparency false

/-!
# SparseRndHam23 — source model

Huang--Preskill--Soleimanifar, *Sparse random Hamiltonians are quantumly easy*,
fixed arXiv:2302.03394 (version downloaded in the PR assets; PDF
`2302.03394.pdf`).

This module sets up the objects appearing in every claim of the paper:

* `QubitSpace n` — the `n`-qubit register as a nested binary product;
* `pauli1`, `pauliTensor` — one-qubit Pauli matrices `{I,X,Y,Z}` and their
  tensor products;
* `HPS` — the random Pauli string Hamiltonian of Eq. (2),
  `H_PS = m^{-1/2} Σ_j r_j σ_j`;
* `Draw`, `drawProb`, `ensembleExpectation` — the uniform finite ensemble of
  `m` Pauli labels and `m` signs;
* `schattenNorm` — the normalized Schatten `p`-norm of Eq. (4),
  `(N^{-1} Tr |O|^p)^{1/p}` for deterministic `O`, and `randomSchattenNorm`
  for its expectation over a random model;
* `lambdaMin`, `lambdaMax` — extreme real eigenvalues of a Hermitian matrix;
* `resolvent` — the resolvent `R = (H - ω + iη)^{-1}` of Eq. (6)/(11);
* `GUEModel` — a probability space carrying a standard GUE-distributed
  Hermitian matrix; `gueNorm` and `gueResolventNorm` are the expected
  normalized `p`-norms over that space;
* `CircuitArch` — a circuit architecture of `G` two-qubit gates with its
  reachable-state family `Circ(G)` and prepared density matrices;
* `matrixTensorPower`, `MomentsMatchUpTo`, `LpStat`, `sigmaSq` — the moment
  statistics of Theorem IV.1;
* `traceAbs` — `Tr |M|`, used for resolvent moments.

The model is used only by the paper-layer statement files; it does not alter
shared Foundations/Concepts.
-/

set_option autoImplicit false
noncomputable section

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.SparseRndHam23.MainResults

/-! ## Qubit registers and Pauli strings -/

/-- The register of `n` qubits, represented as a nested binary product. -/
def QubitSpace : ℕ → Type
  | 0 => PUnit
  | n + 1 => Fin 2 × QubitSpace n

instance qubitSpaceFintype (n : ℕ) : Fintype (QubitSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n _ => exact inferInstanceAs (Fintype (Fin 2 × QubitSpace n))

instance qubitSpaceDecidableEq (n : ℕ) : DecidableEq (QubitSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n _ => exact inferInstanceAs (DecidableEq (Fin 2 × QubitSpace n))

/-- The dimension of the `n`-qubit register is `2^n`. -/
theorem card_qubitSpace (n : ℕ) : Fintype.card (QubitSpace n) = 2 ^ n := by
  induction n with
  | zero => simp [QubitSpace]
  | succ n ih =>
      change Fintype.card (Fin 2 × QubitSpace n) = 2 ^ (n + 1)
      rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]
      ring

/-- One-qubit Pauli matrices, indexed by `0, 1, 2, 3 = I, X, Y, Z`. -/
def pauli1 (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![1, !![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]] i

/-- The tensor product of the Pauli labels `f` over an `n`-qubit register. -/
def pauliTensor : (n : ℕ) → (Fin n → Fin 4) → Matrix (QubitSpace n) (QubitSpace n) ℂ
  | 0, _ => 1
  | n + 1, f => Matrix.kronecker (pauli1 (f 0)) (pauliTensor n (fun i => f i.succ))

/-- The real sign associated with a uniformly random sign bit. -/
def signVal (b : Bool) : ℝ := if b then 1 else -1

/-- The random Pauli string Hamiltonian of Eq. (2):
`H_PS = m^{-1/2} Σ_{j < m} r_j σ_j`. -/
def HPS (n m : ℕ) (σ : Fin m → Fin n → Fin 4) (r : Fin m → Bool)
    : Matrix (QubitSpace n) (QubitSpace n) ℂ :=
  ((Real.sqrt m)⁻¹ : ℂ) • ∑ j : Fin m, (signVal (r j) : ℂ) • pauliTensor n (σ j)

/-- The finite sample space of the Pauli-string ensemble: `m` Pauli labels and
`m` independent uniform signs. -/
abbrev Draw (n m : ℕ) : Type := (Fin m → Fin n → Fin 4) × (Fin m → Bool)

/-- Uniform probability of an event over the finite Pauli-string ensemble. -/
def drawProb (n m : ℕ) (E : Draw n m → Prop) : ℝ :=
  letI := Classical.decPred E
  (Fintype.card {x : Draw n m // E x} : ℝ) / (Fintype.card (Draw n m) : ℝ)

/-- Uniform expectation over the finite Pauli-string ensemble. -/
def ensembleExpectation (n m : ℕ) (f : Draw n m → ℝ) : ℝ :=
  (∑ x : Draw n m, f x) / (Fintype.card (Draw n m) : ℝ)

/-! ## Spectral quantities and Schatten norms -/

/-- The set of real eigenvalues of a complex matrix. -/
def realEigenvalueSet {ι : Type} [Fintype ι] (A : Matrix ι ι ℂ) : Set ℝ :=
  {x : ℝ | ∃ v : ι → ℂ, v ≠ 0 ∧ A *ᵥ v = (x : ℂ) • v}

/-- Smallest real eigenvalue (for Hermitian matrices this is `λ_min`). -/
def lambdaMin {ι : Type} [Fintype ι] (A : Matrix ι ι ℂ) : ℝ := sInf (realEigenvalueSet A)

/-- Largest real eigenvalue (for Hermitian matrices this is `λ_max`). -/
def lambdaMax {ι : Type} [Fintype ι] (A : Matrix ι ι ℂ) : ℝ := sSup (realEigenvalueSet A)

/-- `Tr |M|`, the sum of the singular values of `M`. -/
def traceAbs {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : ℝ :=
  let h : (Mᴴ * M).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  ∑ i, Real.sqrt (max 0 (h.eigenvalues i))

/-- `Tr |M|^p` for a natural exponent `p`, used for resolvent moments. -/
def traceAbsPow {ι : Type} [Fintype ι] [DecidableEq ι] (p : ℕ) (M : Matrix ι ι ℂ) : ℝ :=
  let h : (Mᴴ * M).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  ∑ i, Real.rpow (max 0 (h.eigenvalues i)) ((p : ℝ) / 2)

/-- Normalized Schatten `p`-norm of Eq. (4):
`(N^{-1} Tr |O|^p)^{1/p}`, implemented as `(N^{-1} Tr (OᴴO)^{p/2})^{1/p}`. -/
def schattenNorm {ι : Type} [Fintype ι] [DecidableEq ι] (p : ℕ) (A : Matrix ι ι ℂ) : ℝ :=
  ((Fintype.card ι : ℝ)⁻¹ * traceAbsPow p A) ^ (1 / (p : ℝ))

/-! ## GUE sampling model -/

/-- A probability space carrying a standard GUE-distributed Hermitian matrix.
`mat` is the GUE draw (`H_GUE`), `μ` its law. The distributional content is the
standard GUE law (independent Gaussian entries with variance `1/N`, normalized
so that `E ‖H‖_2 = 1`); it is recorded by the name and docstring of the
structure, while all analytic content of the claims is stated in terms of `mat`
and integrals against `μ`. -/
structure GUEModel (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] where
  /-- The GUE law. -/
  μ : Measure Ω
  /-- `μ` is a probability measure. -/
  isProbability : IsProbabilityMeasure μ
  /-- The random Hermitian matrix. -/
  mat : Ω → Matrix ι ι ℂ
  /-- Every draw is Hermitian. -/
  isHermitian : ∀ ω, (mat ω).IsHermitian

/-- Expected normalized Schatten `p`-norm of a GUE draw, i.e. `|||H_GUE|||_p`. -/
def gueNorm {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (G : GUEModel Ω ι) (p : ℕ) : ℝ :=
  (∫ ω, (schattenNorm p (G.mat ω)) ^ p ∂G.μ) ^ (1 / (p : ℝ))

/-- The resolvent of Eq. (6)/(11): `R = (H - ω + iη)^{-1}`. -/
def zResolvent {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (ω η : ℝ) : Matrix ι ι ℂ :=
  H - (ω : ℂ) • 1 + ((η : ℂ) * Complex.I) • 1

/-- `R = (H - ω + iη)^{-1}`. -/
def resolvent {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (ω η : ℝ) : Matrix ι ι ℂ :=
  (zResolvent H ω η)⁻¹

/-! ## Random matrix families and moment statistics -/

/-- The `k`-fold tensor power `A^{⊗k}`, with matrix units indexed by
`Fin k → ι` and entries `∏ i, A (x i) (y i)`. -/
def matrixTensorPower {ι : Type} [Fintype ι] (k : ℕ) (A : Matrix ι ι ℂ) :
    Matrix (Fin k → ι) (Fin k → ι) ℂ :=
  fun x y => ∏ i : Fin k, A (x i) (y i)

/-- Componentwise expectation of a matrix-valued random variable. -/
def matrixExpectation {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (X : Ω → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => ∫ ω, X ω i j ∂μ

/-- The first `t` tensor moments of `A` and `B` agree. -/
def MomentsMatchUpTo {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (A B : Ω → Matrix ι ι ℂ) (t : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ t →
    (fun x y => ∫ ω, matrixTensorPower k (A ω) x y ∂μ) =
      (fun x y => ∫ ω, matrixTensorPower k (B ω) x y ∂μ)

/-- Expected normalized Schatten `p`-norm of a matrix-valued random variable. -/
def randomSchattenNorm {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] (μ : Measure Ω) (X : Ω → Matrix ι ι ℂ) (p : ℕ) : ℝ :=
  (∫ ω, (schattenNorm p (X ω)) ^ p ∂μ) ^ (1 / (p : ℝ))

/-- Expected normalized Schatten `p`-norm `|||H_PS|||_p` of Eq. (5) over the
uniform Pauli-string ensemble. -/
def pauliSchattenNorm (n m p : ℕ) : ℝ :=
  (ensembleExpectation n m (fun x => (schattenNorm p (HPS n m x.1 x.2)) ^ p)) ^
    (1 / (p : ℝ))

/-- Expected `p`-norm `|||R_PS|||_p` of the resolvent of the Pauli-string
ensemble, Eq. (7): the uniform finite expectation of the normalized Schatten
`p`-norm of `(H_PS - ω + iη)^{-1}`. -/
def pauliResolventNorm (n m : ℕ) (ω η : ℝ) (p : ℕ) : ℝ :=
  (ensembleExpectation n m
      (fun x => (schattenNorm p (resolvent (HPS n m x.1 x.2) ω η)) ^ p)) ^
    (1 / (p : ℝ))

/-- The `L_{p,k}` statistic of Theorem IV.1, including both families. -/
def LpStat {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {m : ℕ} (μ : Measure Ω) (A B : Fin m → Ω → Matrix ι ι ℂ) (p k : ℕ) : ℝ :=
  (∑ i : Fin m,
      ((randomSchattenNorm μ (A i) p) ^ k + (randomSchattenNorm μ (B i) p) ^ k)) ^
    (1 / (k : ℝ))

/-- The variance statistic `σ² = Σ_i (‖E A_i²‖ + ‖E Ã_i²‖)` of Theorem IV.1. -/
def sigmaSq {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {m : ℕ} (μ : Measure Ω) (A B : Fin m → Ω → Matrix ι ι ℂ) : ℝ :=
  ∑ i : Fin m,
    (‖matrixExpectation μ (fun ω => A i ω * A i ω)‖ +
      ‖matrixExpectation μ (fun ω => B i ω * B i ω)‖)

/-- Essential operator-norm supremum of a matrix-valued random variable. -/
def essOpNorm {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (X : Ω → Matrix ι ι ℂ) : ℝ :=
  sSup (Set.range fun ω => ‖X ω‖)

/-- `L_{∞,∞} = max_i max(‖A_i‖_∞, ‖Ã_i‖_∞)` of the second bound of Theorem IV.1. -/
def LInfStat {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {m : ℕ} (A B : Fin m → Ω → Matrix ι ι ℂ) : ℝ :=
  sSup {r : ℝ | ∃ i : Fin m, r = max (essOpNorm (A i)) (essOpNorm (B i))}

/-- Essential supremum of the normalized Schatten `q`-norm of a random matrix. -/
def essSchattenNorm {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] (X : Ω → Matrix ι ι ℂ) (q : ℕ) : ℝ :=
  sSup (Set.range fun ω => schattenNorm q (X ω))

/-- `L_{q,∞} = max_i max(|||A_i|||_q, |||Ã_i|||_q)` as used in Theorem IV.2. -/
def LqInfStat {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {m : ℕ} (A B : Fin m → Ω → Matrix ι ι ℂ) (q : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ i : Fin m, r = max (essSchattenNorm (A i) q) (essSchattenNorm (B i) q)}

/-- Sum of a finite family of random matrices. -/
def sumFamily {Ω ι : Type} [Fintype ι] {m : ℕ}
    (A : Fin m → Ω → Matrix ι ι ℂ) (ω : Ω) : Matrix ι ι ℂ :=
  ∑ i : Fin m, A i ω

/-- Resolvent norm `|||R|||_p` of a random matrix `H`. -/
def randomResolventNorm {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] (μ : Measure Ω) (H : Ω → Matrix ι ι ℂ) (ω η : ℝ) (p : ℕ) : ℝ :=
  randomSchattenNorm μ (fun x => resolvent (H x) ω η) p

/-- Expected `p`-norm `|||R_GUE|||_p` of the GUE resolvent, Eq. (7). -/
def gueResolventNorm {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (G : GUEModel Ω ι) (ω η : ℝ) (p : ℕ) : ℝ :=
  randomResolventNorm G.μ G.mat ω η p

/-- The `L_q` norm `(E |X|^q)^{1/q}` of a real random variable. -/
def randomLpNorm {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (q : ℕ) : ℝ :=
  (∫ ω, |X ω| ^ q ∂μ) ^ (1 / (q : ℝ))

/-- The variance-like quantity
`σ*(A)² = sup_{‖u‖=‖v‖=1} E |⟨u|A|v⟩|²` of Theorem A.1 / Proposition B.1. -/
def sigmaStar {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (X : Ω → Matrix ι ι ℂ) : ℝ :=
  sSup {r : ℝ | ∃ u v : ι → ℂ,
    (∑ i, ‖u i‖ ^ 2) = 1 ∧ (∑ i, ‖v i‖ ^ 2) = 1 ∧
      r = ∫ ω, ‖∑ i, (starRingEnd ℂ (u i)) * (X ω *ᵥ v) i‖ ^ 2 ∂μ}

/-! ## Circuits and state expectations -/

/-- The expectation `⟨ψ|A|ψ⟩ / ⟨ψ|ψ⟩` of a matrix in a state vector. -/
def qExpect {ι : Type} [Fintype ι] (A : Matrix ι ι ℂ) (ψ : ι → ℂ) : ℝ :=
  ((∑ i, (starRingEnd ℂ (ψ i)) * (A *ᵥ ψ) i).re) / (∑ i, ‖ψ i‖ ^ 2)

/-- A circuit architecture of `G` two-qubit gates: it carries its reachable
state family `Circ(G)` (states obtained from `|0…0⟩`) and the density matrices
it can prepare. This is the source-level interface for Theorem II.1,
Theorem II.2, Proposition V.1 and Lemma D.1; gate-level compilation is not
reconstructed here. -/
structure CircuitArch (n : ℕ) where
  /-- Number of two-qubit gates in the architecture. -/
  G : ℕ
  /-- The family `Circ(G)` of reachable pure states. -/
  states : Set ((QubitSpace n) → ℂ)
  /-- Density matrices preparable by the architecture. -/
  prepares : Matrix (QubitSpace n) (QubitSpace n) ℂ → Prop

/-- A density matrix in the paper's sense. -/
def IsDensityMatrix {ι : Type} [Fintype ι] (ρ : Matrix ι ι ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- A classical verifier for a candidate witness density matrix: `accepts` is
its verification predicate and `runtime` its cost, in Pauli-string operations. -/
structure WitnessVerifier (n : ℕ) where
  /-- Cost of the verification procedure. -/
  runtime : ℝ
  /-- The verification predicate. -/
  accepts : Matrix (QubitSpace n) (QubitSpace n) ℂ → Prop

/-- Cost of evaluating the `(dm)^{2d}` Pauli terms of the degree-`d` ansatz of
Proposition V.1, at `O(n)` per Pauli multiplication. -/
def classicalWitnessCost (d m n : ℕ) : ℝ := ((d * m : ℝ) ^ (2 * d)) * (n : ℝ) ^ d

end Qatlib.Papers.SparseRndHam23.MainResults
