/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.GkslBridge.GkslBridge.QuantumMixingSourceBoundsDefs
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.SchattenDiamond.DiamondNorm

set_option backward.isDefEq.respectTransparency false

/-!
# Paper-layer vocabulary for *Quantum Thermal State Preparation*

Chen–Kastoryano–Brandão–Gilyén, arXiv:2303.18224v2.

This module fixes the paper-level vocabulary shared by all claim files of
`ThermalState23`.  It reuses the shared GKSL
vocabulary (`GKSLData`, `gkslMap`, `evolveAt`, `gkslStationary`,
`thermalMixingTime`, `gibbsDensity`, `SchattenOne`, `boxFilteredFixedPoint`,
`WeakBathDetailedBalance`, `GaussianMetropolisBath`,
`purifiedProxyDiscriminant`, `purifiedGibbsVector`, `ProxySpectralGap`,
`BlockUnitaryLindbladian`) from
`Qatlib.Concepts.GkslBridge.GkslBridge` and adds only the paper's
own constructions: the discriminant superoperator, the operator Fourier
transforms, the two-sided DFT, block encodings and the filtered averages for
the Gaussian window.

Scope note: the contracts `ThermalThI1Spec`, `ThermalThI3Spec` and
`ThermalThI4Spec` admit counterexamples without additional side conditions.
The paper's statements are formalized here with positive mixing time and
the existence of a filtered approximate fixed point made explicit.
-/

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory
open scoped Classical BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Qatlib.Papers.ThermalState23.MainResults

open Qatlib.Concepts.GkslBridge.GkslBridge
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

/-! ## Discriminants and approximate detailed balance (Section II) -/

/-- The fourth root `ρ^{1/4}` of a positive matrix, written as
`√(√ρ)` using the continuous functional calculus. -/
noncomputable def fourthRoot {n : ℕ} (ρ : Operator n) : Operator n :=
  CFC.sqrt (CFC.sqrt ρ)

/-- The paper's discriminant superoperator, Definition II.2 (main text before
Eq. (II.3)):
`D(ρ,L)[X] = ρ^{-1/4} L[ρ^{1/4} X ρ^{1/4}] ρ^{-1/4}`. -/
noncomputable def discriminantOf {n : ℕ} (ρ : Operator n)
    (L : Operator n → Operator n) : Operator n → Operator n :=
  fun X => (fourthRoot ρ)⁻¹ * L (fourthRoot ρ * X * fourthRoot ρ) * (fourthRoot ρ)⁻¹

/-- Hilbert–Schmidt inner product `tr(X† Y)`. -/
def hsInner {n : ℕ} (X Y : Operator n) : ℂ := Matrix.trace (Xᴴ * Y)

/-- `Ldag` is the Hilbert–Schmidt adjoint of `L`. -/
def IsHSAdjoint {n : ℕ} (L Ldag : Operator n → Operator n) : Prop :=
  ∀ X Y : Operator n, hsInner (L X) Y = hsInner X (Ldag Y)

/-- The paper's `ε`-approximate `ρ`-detailed balance condition,
Definition II.2: some superoperator `Ddag` is the Hilbert–Schmidt adjoint of
`D(ρ,L)` and `½‖D(ρ,L) − Ddag‖_{2→2} ≤ ε`, written pointwise as
`½‖(D − Ddag)X‖₂ ≤ ε‖X‖₂`. -/
def ApproxDetailedBalance {n : ℕ} (ε : ℝ) (ρ : Operator n)
    (L : Operator n → Operator n) : Prop :=
  ∃ Ddag : Operator n → Operator n,
    IsHSAdjoint (discriminantOf ρ L) Ddag ∧
      ∀ X : Operator n, (1 / 2 : ℝ) * ‖discriminantOf ρ L X - Ddag X‖ ≤ ε * ‖X‖

/-- A full-rank density matrix. -/
def IsFullRankDensity {n : ℕ} (ρ : Operator n) : Prop :=
  IsDensityOperator ρ ∧ ρ.det ≠ 0

/-- The self-adjoint component `H(ρ,L)` used in Proposition II.3 is modelled by
its two top eigenvalues; this predicate records the spectral data appearing in
the statement `lam₁/lamgap ≤ 1/100`. -/
def HasTopTwoEigenvalues {n : ℕ} (H : Operator n) (lam1 lam2 : ℝ) : Prop :=
  H.IsHermitian ∧ lam2 ≤ lam1

/-! ## Discriminant proxies from jump operators (Section III) -/

/-- The self-adjoint discriminant superoperator `D(P,{L_j})` of
Proposition III.4, before vectorization. -/
noncomputable def discriminantSuper {D m : ℕ} (G : GKSLData D m)
    (P : Fin m → Fin m) : Operator D → Operator D :=
  fun X =>
    (1 / 2 : ℂ) • ∑ j : Fin m,
      (G.jumps j * X * (G.jumps (P j))ᴴ + (G.jumps j)ᴴ * X * G.jumps (P j)
        - (G.jumps j)ᴴ * G.jumps j * X - X * (G.jumps j)ᴴ * G.jumps j)

/-- Vectorization of a superoperator with respect to the matrix-unit basis. -/
noncomputable def vectorizeSuper {n : ℕ} (L : Operator n → Operator n) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  Matrix.of fun (i, j) (k, l) => L (Matrix.single k l (1 : ℂ)) i j

/-- Matrix exponential `e^{tH}` for a matrix `H` and real time `t`. -/
noncomputable def matExp {n : ℕ} (t : ℝ) (H : Operator n) : Operator n :=
  NormedSpace.exp ((t : ℂ) • H)

/-- The scalar phase `e^{-iωt}`. -/
noncomputable def scalarPhase (ω t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (ω : ℂ) * (t : ℂ))

/-- The one-sided operator Fourier transform (Eq. (A1)):
`Â_a^f(ω) = ∑_t f(t) e^{-iωt} e^{iHt} A_a e^{-iHt}`. -/
noncomputable def operatorFourier {n m N : ℕ} (A : Fin m → Operator n)
    (H : Operator n) (f : Fin N → ℂ) (a : Fin m) (ω : Fin N) : Operator n :=
  ∑ t : Fin N,
    f t • (scalarPhase (ω : ℝ) (t : ℝ) • matExp (t : ℝ) H * A a *
      matExp (-(t : ℝ)) H)

/-- The two-sided operator Fourier transform (Eq. (3.15)):
`Ô^f(Ē₂,Ē₁) = ∑_{t₁,t₂} f(t₁) f(-t₂) e^{-i(Ē₂-H)t₂} O e^{-i(Ē₁-H)t₁}`. -/
noncomputable def twoSidedDFT {n m N : ℕ} (A : Fin m → Operator n)
    (H : Operator n) (f : Fin N → ℂ) (a : Fin m) (E2 E1 : Fin N) : Operator n :=
  ∑ t1 : Fin N, ∑ t2 : Fin N,
    (f t1 * f (-t2)) •
      ((scalarPhase (E2 : ℝ) (t2 : ℝ) • matExp (t2 : ℝ) H) * A a *
        (scalarPhase (E1 : ℝ) (t1 : ℝ) • matExp (t1 : ℝ) H))

/-- Loewner order `A ⪯ B`, written as positive semidefiniteness of `B - A`. -/
def MatLe {n : ℕ} (A B : Operator n) : Prop := (B - A).PosSemidef

/-- Squared 2-norm of a vector of coefficients, `∑_t |f(t)|²`. -/
noncomputable def l2NormSq {N : ℕ} (f : Fin N → ℂ) : ℝ := ∑ t : Fin N, ‖f t‖ ^ 2

/-- Rayleigh quotient `⟨w, H w⟩` of a Hermitian matrix. -/
noncomputable def rayleigh {n : ℕ} (H : Operator n) (w : Fin n → ℂ) : ℝ :=
  Complex.re (∑ i : Fin n, (starRingEnd ℂ) (w i) * (H *ᵥ w) i)

/-- `v` is a normalized top eigenvector of `H` with eigenvalue `lam`. -/
def IsTopEigenvector {n : ℕ} (H : Operator n) (v : Fin n → ℂ) (lam : ℝ) : Prop :=
  ‖toEuclidean_fromVec v‖ = 1 ∧
    (∀ i : Fin n, (H *ᵥ v) i = (lam : ℂ) * v i) ∧
      ∀ w : Fin n → ℂ, ‖toEuclidean_fromVec w‖ = 1 → rayleigh H w ≤ lam

/-- The top two eigenvalues `lam₁ ≥ lam₂` of a Hermitian matrix, with the second
eigenvalue characterized by Rayleigh quotients on the orthogonal complement of
a second eigenvector (multiplicity caveat documented in the claim files). -/
def IsTopTwoEigenvalues {n : ℕ} (H : Operator n) (lam1 lam2 : ℝ) : Prop :=
  H.IsHermitian ∧ (∃ v : Fin n → ℂ, IsTopEigenvector H v lam1) ∧ lam2 ≤ lam1 ∧
    ∃ v2 : Fin n → ℂ,
      ‖toEuclidean_fromVec v2‖ = 1 ∧
        (∀ i : Fin n, (H *ᵥ v2) i = (lam2 : ℂ) * v2 i) ∧
          ∀ w : Fin n → ℂ, ‖toEuclidean_fromVec w‖ = 1 →
            (∑ i : Fin n, (starRingEnd ℂ) (v2 i) * w i = 0) → rayleigh H w ≤ lam2

/-- The top two eigenvalues `lam₁ ≥ lam₂` of a vectorized (square) matrix.
This is the vectorized-matrix analogue of `IsTopTwoEigenvalues`, used for
discriminant proxies which live on `Fin n × Fin n`. -/
def HasTopTwoEigenvaluesMat {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℂ) (lam1 lam2 : ℝ) : Prop :=
  H.IsHermitian ∧ lam2 ≤ lam1

/-! ## Block encodings and resource profiles (Section I and III) -/

/-- Oracle/query and qubit resources of a block-encoding construction. -/
structure OracleProfile where
  queriesPrep : ℕ
  queriesW : ℕ
  queriesVjump : ℕ
  queriesQFT : ℕ
  queriesF : ℕ
  queriesP : ℕ
  hamSimTime : ℝ
  qubits : ℕ

/-- Exact block encoding of a (possibly rectangular) target matrix inside a
unitary `U`, with ancilla index type `ι` and distinguished ancilla state
`zero`. -/
def IsBlockEncoding {σ τ ι : Type*} [Fintype ι]
    (zero : ι) (U : Matrix (σ × ι) (τ × ι) ℂ) (target : Matrix σ τ ℂ) : Prop :=
  ∀ i j, (∑ k : ι, U (i, k) (j, zero)) = target i j

/-- Approximate block encoding with spectral-norm error `ε` on every entry of
the encoded block. -/
def IsApproxBlockEncoding {σ τ ι : Type*} [Fintype ι]
    (zero : ι) (U : Matrix (σ × ι) (τ × ι) ℂ) (target : Matrix σ τ ℂ)
    (ε : ℝ) : Prop :=
  ∀ i j, ‖(∑ k : ι, U (i, k) (j, zero)) - target i j‖ ≤ ε

/-- The target block operator (1.17) of the discretized Lindblad operators:
the map from the system register to `(frequency, jump) ⊗ system` with entries
`√γ(ω) Â_a(ω) / f(ω)`. -/
noncomputable def lindbladJumpBlock {n m N : ℕ} (Â : Fin m → Fin N → Operator n)
    (γ : Fin N → ℝ) (f : Fin N → ℂ) :
    Matrix (Fin n) ((Fin N × Fin m) × Fin n) ℂ :=
  Matrix.of fun i ((ω, a), j) => (Real.sqrt (γ ω) : ℂ) * Â a ω i j / f ω

/-! ## Filtered fixed points (Theorems I.1 and I.3) -/

/-- `ρfix` is the average of the box-window filtered semigroup applied to some
density matrix.  This is the paper's `ρfix(L_β)` for the weight
`f(t) = 1(t ≤ |T|/2)/√T`. -/
def IsBoxFilteredFixedPoint {D m : ℕ} (G : GKSLData D m) (T : ℝ)
    (ρfix : Operator D) : Prop :=
  ∃ ρ₀ : Operator D, IsDensityOperator ρ₀ ∧ ρfix = boxFilteredFixedPoint G T ρ₀

/-- The normalized Gaussian time filter `f(t) ∝ e^{-t²/(4σt²)}`. -/
noncomputable def gaussianWindowFilter (σt t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2) / (4 * σt ^ 2))

/-- The Gaussian-window filtered fixed point: the normalized average of
`evolveAt G s ρ₀` against the Gaussian window on `[0,T]`. -/
noncomputable def gaussianFilteredFixedPoint {D m : ℕ} (G : GKSLData D m)
    (σt T : ℝ) (ρ₀ : Operator D) : Operator D :=
  ((∫ s in (0 : ℝ)..T, gaussianWindowFilter σt s)⁻¹) •
    ∫ s in (0 : ℝ)..T, gaussianWindowFilter σt s • evolveAt G s ρ₀

/-- `ρfix` is the Gaussian-window filtered average of some density matrix. -/
def IsGaussianFilteredFixedPoint {D m : ℕ} (G : GKSLData D m) (σt T : ℝ)
    (ρfix : Operator D) : Prop :=
  ∃ ρ₀ : Operator D, IsDensityOperator ρ₀ ∧
    ρfix = gaussianFilteredFixedPoint G σt T ρ₀

/-! ## Secular approximation vocabulary (Appendix A/B) -/

/-- The secular-approximated Lindbladian built from explicit jump operators
`S` and weights `γ` (Lemma A.2 and Lemma B.3). -/
noncomputable def secularLindbladian {D m N : ℕ} (S : Fin m → Fin N → Operator D)
    (γ : Fin N → ℝ) : Operator D → Operator D :=
  fun X =>
    ∑ a : Fin m, ∑ ω : Fin N,
      (γ ω : ℂ) •
        (S a ω * X * (S a ω)ᴴ - (1 / 2 : ℂ) • ((S a ω)ᴴ * S a ω * X + X * (S a ω)ᴴ * S a ω))

/-- The secular-approximated discriminant proxy built from explicit jump
operators `S` and weights `γ` (Lemma B.3). -/
noncomputable def secularDiscriminant {D m N : ℕ} (S : Fin m → Fin N → Operator D)
    (γ : Fin N → ℝ) : Operator D → Operator D :=
  fun X =>
    ∑ a : Fin m, ∑ ω : Fin N,
      ((Real.sqrt (γ ω * γ (-ω)) : ℂ) • (S a ω * X * (S a ω)ᴴ)
        - (γ ω / 2 : ℂ) • ((S a ω)ᴴ * S a ω * X + X * (S a ω)ᴴ * S a ω))

/-- The Lindbladian `L(f,H)` built from a one-sided operator Fourier transform
(Corollary A.1/A.2). -/
noncomputable def lindbladianFromFourier {D m N : ℕ} (A : Fin m → Operator D)
    (H : Operator D) (f : Fin N → ℂ) (γ : Fin N → ℝ) :
    Operator D → Operator D :=
  fun X =>
    ∑ a : Fin m, ∑ ω : Fin N,
      (γ ω : ℂ) •
        (operatorFourier A H f a ω * X * (operatorFourier A H f a ω)ᴴ
          - (1 / 2 : ℂ) •
            ((operatorFourier A H f a ω)ᴴ * operatorFourier A H f a ω * X
              + X * (operatorFourier A H f a ω)ᴴ * operatorFourier A H f a ω))

/-- The discriminant proxy `D(f,H)` built from a one-sided operator Fourier
transform (Corollary A.1/A.2). -/
noncomputable def discriminantFromFourier {D m N : ℕ} (A : Fin m → Operator D)
    (H : Operator D) (f : Fin N → ℂ) (γ : Fin N → ℝ) :
    Operator D → Operator D :=
  fun X =>
    ∑ a : Fin m, ∑ ω : Fin N,
      ((Real.sqrt (γ ω * γ (-ω)) : ℂ) •
          (operatorFourier A H f a ω * X * (operatorFourier A H f a ω)ᴴ)
        - (γ ω / 2 : ℂ) •
            ((operatorFourier A H f a ω)ᴴ * operatorFourier A H f a ω * X
              + X * (operatorFourier A H f a ω)ᴴ * operatorFourier A H f a ω))

/-- Euclidean norm of a coefficient vector indexed by an arbitrary finite type,
used for vectorized matrices (indices `Fin n × Fin n`). -/
noncomputable def coefNorm {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i : ι, ‖v i‖ ^ 2)

/-- Matrix element `⟨v|A|w⟩` of a matrix between two coefficient vectors. -/
def vecMatrixElement {n : ℕ} (v : Fin n → ℂ) (A : Operator n) (w : Fin n → ℂ) : ℂ :=
  ∑ p : Fin n, ∑ q : Fin n, (starRingEnd ℂ) (v p) * A p q * w q

/-- Apply a vectorized superoperator to a matrix. -/
noncomputable def vecApply {n : ℕ} (Dop : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (X : Operator n) : Operator n :=
  Matrix.of fun i j => ∑ k : Fin n, ∑ l : Fin n, Dop (i, j) (k, l) * X k l

/-- The vectorized square root `|√ρ⟩`. -/
noncomputable def sqrtVec {n : ℕ} (ρ : Operator n) : Fin n × Fin n → ℂ :=
  fun i => CFC.sqrt ρ i.1 i.2

/-- `Dop` is an `ε`-discriminant proxy for `L` at `ρ` (Proposition III.3). -/
def IsDiscriminantProxy {n : ℕ} (Dop : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ρ : Operator n) (L : Operator n → Operator n) (ε : ℝ) : Prop :=
  ∃ Ldag : Operator n → Operator n,
    IsHSAdjoint (discriminantOf ρ L) Ldag ∧
      ∀ X : Operator n, ‖vecApply Dop X - discriminantOf ρ L X‖ ≤ ε * ‖X‖

/-- The jump-operator matrix `(i, (j,a)) ↦ (L_a)_{ij}`. -/
def jumpMatrix {D m : ℕ} (G : GKSLData D m) : Matrix (Fin D) (Fin D × Fin m) ℂ :=
  fun i (j, a) => G.jumps a i j

/-- The Gram matrix `∑_a L_a† L_a`. -/
noncomputable def gramMatrix {D m : ℕ} (G : GKSLData D m) : Operator D :=
  ∑ a : Fin m, (G.jumps a)ᴴ * G.jumps a

/-- Operator norm of a rectangular matrix, defined as the supremum of the
output coefficient norm over unit input vectors. -/
noncomputable def rectOpNorm {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ v : Fin n → ℂ, coefNorm v ≤ 1 ∧ r = coefNorm (fun i => (M *ᵥ v) i)}

/-- Pointwise `1→1` norm bound for a superoperator. -/
def SuperOpTraceBound {n : ℕ} (L : Operator n → Operator n) (δ : ℝ) : Prop :=
  ∀ X : Operator n, SchattenOne (L X) ≤ δ * SchattenOne X

/-- Pointwise `2→2` norm bound for a superoperator. -/
def SuperOpL2Bound {n : ℕ} (L : Operator n → Operator n) (δ : ℝ) : Prop :=
  ∀ X : Operator n, ‖L X‖ ≤ δ * ‖X‖

/-- The cyclic negation on `Fin N`. -/
def finNeg {N : ℕ} (i : Fin N) : Fin N :=
  ⟨(N - i.val) % N, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-- The discrete Fourier transform on the cyclic group `Fin N`. -/
noncomputable def dft {N : ℕ} (f : Fin N → ℂ) (ω : Fin N) : ℂ :=
  ∑ t : Fin N,
    f t * Complex.exp (-Complex.I * 2 * Real.pi * (ω : ℝ) * (t : ℝ) / (N : ℝ))

/-- The inverse discrete Fourier transform on the cyclic group `Fin N`. -/
noncomputable def inverseDFT {N : ℕ} (g : Fin N → ℂ) (t : Fin N) : ℂ :=
  (N : ℂ)⁻¹ *
    ∑ ω : Fin N,
      g ω * Complex.exp (Complex.I * 2 * Real.pi * (ω : ℝ) * (t : ℝ) / (N : ℝ))

/-- The secular-approximated operator Fourier transform of Proposition A.4:
`Ŝ_{f,s}(ω) = Â^{fs}(ω)` with `fs` the inverse DFT of `f̂·s`. -/
noncomputable def secularOFT {n m N : ℕ} (A : Fin m → Operator n) (H : Operator n)
    (f s : Fin N → ℂ) (a : Fin m) (ω : Fin N) : Operator n :=
  ∑ t : Fin N,
    f t • (∑ ν : Fin N,
      (s (ω - ν) * scalarPhase (ν : ℝ) (t : ℝ)) •
        (matExp (t : ℝ) H * A a * matExp (-(t : ℝ)) H))

/-- The perturbed weight `fs` of Proposition A.4: inverse DFT of `f̂·s`. -/
noncomputable def perturbedWeight {N : ℕ} (f s : Fin N → ℂ) : Fin N → ℂ :=
  fun t => inverseDFT (fun ω => dft f ω * s ω) t

/-- Truncation of a weight function at time `T`. -/
noncomputable def truncateWeight {N : ℕ} (f : Fin N → ℂ) (T : ℝ) : Fin N → ℂ :=
  fun t => if |(t : ℝ)| ≤ T then f t else 0

/-- The continuous operator Fourier transform of Proposition A.2/A.5. -/
noncomputable def continuousOperatorFourier {n m : ℕ} (A : Fin m → Operator n)
    (H : Operator n) (f : ℝ → ℂ) (a : Fin m) (ω : ℝ) : Operator n :=
  ∫ t : ℝ, f t • (scalarPhase ω t • matExp t H * A a * matExp (-t) H)

/-- `ℓ²` distance between two finite weight vectors. -/
noncomputable def l2Dist {N : ℕ} (f g : Fin N → ℂ) : ℝ :=
  Real.sqrt (∑ i : Fin N, ‖f i - g i‖ ^ 2)

/-- `L²` distance between two continuous weight functions. -/
noncomputable def l2DistCont (f g : ℝ → ℂ) : ℝ :=
  Real.sqrt (∫ t : ℝ, ‖f t - g t‖ ^ 2)

/-- The block operator of Lemma A.1, with entries
`√γ(ω) Â_a^f(ω)`. -/
noncomputable def fourierJumpBlock {n m N : ℕ} (A : Fin m → Operator n)
    (H : Operator n) (f : Fin N → ℂ) (γ : Fin N → ℝ) :
    Matrix (Fin n) ((Fin N × Fin m) × Fin n) ℂ :=
  Matrix.of fun i ((ω, a), j) => (Real.sqrt (γ ω) : ℂ) * operatorFourier A H f a ω i j

/-- The continuous Lindbladian `L(f,H)` of Corollary A.2. -/
noncomputable def lindbladianContinuous {n m : ℕ} (A : Fin m → Operator n)
    (H : Operator n) (f : ℝ → ℂ) (γ : ℝ → ℝ) : Operator n → Operator n :=
  fun X =>
    ∑ a : Fin m, ∫ ω : ℝ,
      (γ ω : ℂ) •
        (continuousOperatorFourier A H f a ω * X * (continuousOperatorFourier A H f a ω)ᴴ
          - (1 / 2 : ℂ) •
            ((continuousOperatorFourier A H f a ω)ᴴ * continuousOperatorFourier A H f a ω * X
              + X * (continuousOperatorFourier A H f a ω)ᴴ *
                continuousOperatorFourier A H f a ω))

/-- The continuous discriminant proxy `D(f,H)` of Corollary A.2. -/
noncomputable def discriminantContinuous {n m : ℕ} (A : Fin m → Operator n)
    (H : Operator n) (f : ℝ → ℂ) (γ : ℝ → ℝ) : Operator n → Operator n :=
  fun X =>
    ∑ a : Fin m, ∫ ω : ℝ,
      ((Real.sqrt (γ ω * γ (-ω)) : ℂ) •
          (continuousOperatorFourier A H f a ω * X *
            (continuousOperatorFourier A H f a ω)ᴴ)
        - (γ ω / 2 : ℂ) •
            ((continuousOperatorFourier A H f a ω)ᴴ * continuousOperatorFourier A H f a ω * X
              + X * (continuousOperatorFourier A H f a ω)ᴴ *
                continuousOperatorFourier A H f a ω))

/-- Block-diagonal matrix assembled from square blocks. -/
noncomputable def blockDiag {κ n : ℕ} (B : Fin κ → Operator n) :
    Matrix (Fin κ × Fin n) (Fin κ × Fin n) ℂ :=
  Matrix.of fun (k, i) (l, j) => if k = l then B k i j else 0

/-- Kronecker product of two square matrices. -/
noncomputable def kron {m n : ℕ} (A : Operator m) (B : Operator n) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  Matrix.of fun (i, k) (j, l) => A i j * B k l

/-! ## Uniform and Gaussian weight functions (Appendix A) -/

/-- Uniform weight on a window of half-width `T` with spacing `t0`:
`f(t) = 1(-T ≤ t < T)/√(2T/t0)`. -/
noncomputable def uniformWeight (T t0 : ℝ) (t : ℝ) : ℂ :=
  if -T ≤ t ∧ t < T then (Real.sqrt (2 * T / t0) : ℂ)⁻¹ else 0

/-- Gaussian weight normalized on the discrete time grid. -/
noncomputable def gaussianWeight {N : ℕ} (σt : ℝ) (t : Fin N → ℝ) (j : Fin N) : ℂ :=
  ((Real.sqrt (∑ k : Fin N, Real.exp (-(t k) ^ 2 / (2 * σt ^ 2))) : ℝ) : ℂ)⁻¹ *
    (Real.exp (-(t j) ^ 2 / (4 * σt ^ 2)) : ℂ)

end Qatlib.Papers.ThermalState23.MainResults
