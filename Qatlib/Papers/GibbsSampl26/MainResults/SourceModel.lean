/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.ParentWeightedForm
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# GibbsSampl26 — paper-layer vocabulary

Fixed source: Leng–Jiang–Lin, *Accelerating quantum Gibbs sampling without quantum walks*,
arXiv:2604.22996v2 (2026-09-30), cited below as "the paper".

This module fixes the objects that every claim of the paper refers to. It contains no
theorem about the paper's results; all substantive statements live in the sibling modules
of `Qatlib.Papers.GibbsSampl26.MainResults`.

Notation and source locations:

* `hsInner`, `kmsInner` — Hilbert–Schmidt and KMS inner products, paper Eq. (A3) p.10:
  `⟨A,B⟩_{σ,s} = Tr(A† σ^{1-s} B σ^s)`; the KMS case is `s = 1/2`;
* `symBilinForm` — the symmetric bilinear form `E(X,Y) = -⟨X, L†Y⟩_σ`, Eq. (A12) p.11;
* `parentHamiltonian` — `H(X) = -σ^{-1/4} L[σ^{1/4} X σ^{1/4}] σ^{-1/4}`, Eq. (A6) p.10,
  built from the frozen `fourthRoot`;
* `gWeight` — `g(t) = 1 / (β cosh(2πt/β))`, Eq. (A30) p.13;
* `parentSOS` — `(B^♯ X - X B^♭)†(B^♯ X - X B^♭)` with the Hilbert–Schmidt adjoint of the
  frozen `parentFactor`, so that the paper's time integral Eq. (A30) is an integral of
  `parentSOS`;
* `evol`, `bohrJump` — `e^{iHt} B e^{-iHt}` and the Bohr sum
  `Σ_ν Q_{ν,j} e^{iνt} e^{βν/4} A_ν`, Eq. (A15) p.12;
* `quadratureNodes`, `quadratureGram` — the midpoint quadrature of Eqs. (B3)–(B4) p.19;
* `superOpHSNormSq` / `hsNormSq` — Hilbert–Schmidt norm of matrices, used by Lemmas 7 and 9;
* `cwHamiltonian`, `magOp`, `sgnM`, `gibbsState`, `tauHalf`, `warmOverlap` — the
  inhomogeneous Curie–Weiss model of Appendix C, Eqs. (C1)–(C6) p.25;
* `zn`, `rn`, `Cn` — the constants of Lemma 18, Eq. (C50)–(C51) p.32;
* `traceDistance`, `kmsVariance` — trace distance and KMS variance of Definition II.3 /
  Appendix C p.24.
-/

set_option autoImplicit false

noncomputable section

open Qatlib.Concepts.QuantumGibbs.FormAlgebra

namespace Qatlib.Papers.GibbsSampl26.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {D : ℕ}

/-! ## Hilbert–Schmidt and KMS inner products (paper Eq. (A3), p.10) -/

/-- Hilbert–Schmidt squared norm `‖A‖₂² = Σ_{ij} |A_{ij}|²`. -/
noncomputable def hsNormSq (A : Operator D) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

/-- Hilbert–Schmidt norm `‖A‖₂`. -/
noncomputable def hsNorm (A : Operator D) : ℝ := Real.sqrt (hsNormSq A)

/-- The KMS inner product `⟨X,Y⟩_σ = Tr(X† σ^{1/2} Y σ^{1/2})`, paper Eq. (A3) with `s = 1/2`. -/
noncomputable def kmsInner (σ X Y : Operator D) : ℂ :=
  Matrix.trace (Xᴴ * (CFC.sqrt σ * Y * CFC.sqrt σ))

/-! ## Symmetric bilinear form and parent Hamiltonian (paper Eqs. (A6), (A12)) -/

/-- The symmetric bilinear form `E(X,Y) = -⟨X, L†(Y)⟩_σ` of Eq. (A12) p.11. The argument
`Ldag` is the Heisenberg-picture adjoint `L†` of the Lindbladian `L`. -/
noncomputable def symBilinForm (σ : Operator D) (Ldag : Operator D → Operator D)
    (X Y : Operator D) : ℂ :=
  - kmsInner σ X (Ldag Y)

/-- The parent Hamiltonian `H(X) = -σ^{-1/4} L[σ^{1/4} X σ^{1/4}] σ^{-1/4}`, Eq. (A6) p.10. -/
noncomputable def parentHamiltonian (σ : Operator D) (L : Operator D → Operator D)
    (X : Operator D) : Operator D :=
  - (fourthRoot σ)⁻¹ * L (fourthRoot σ * X * fourthRoot σ) * (fourthRoot σ)⁻¹

/-- `g(t) = 1 / (β cosh(2πt/β))`, the time weight of Eq. (A30) p.13. -/
noncomputable def gWeight (β t : ℝ) : ℝ := 1 / (β * Real.cosh (2 * Real.pi * t / β))

/-- Hilbert–Schmidt adjoint of the first-order parent factor `ℬ[X] = B^♯ X - X B^♭`:
`ℬ†[Y] = (B^♯)† Y - Y (B^♭)†`. -/
noncomputable def parentFactorHSAdjoint (σ B : Operator D) : Operator D →ₗ[ℂ] Operator D :=
  LinearMap.mulLeft ℂ (sharp σ B)ᴴ - LinearMap.mulRight ℂ (flat σ B)ᴴ

/-- `ℬ†(ℬ(X))`: the operator appearing under the time integral of Eq. (A30). -/
noncomputable def parentSOS (σ B : Operator D) : Operator D →ₗ[ℂ] Operator D :=
  (parentFactorHSAdjoint σ B).comp (parentFactor σ B)

/-- The time-evolved operator `e^{iHt} B e^{-iHt}` (paper Eq. (A9), p.11). -/
noncomputable def evol (H : Operator D) (t : ℝ) (B : Operator D) : Operator D :=
  NormedSpace.exp ((Complex.I * (t : ℂ)) • H) * B *
    NormedSpace.exp (-(Complex.I * (t : ℂ)) • H)

/-- The Bohr-weighted jump operator `B_{j,t} = Σ_ν Q_{ν,j} e^{iνt} e^{βν/4} A_ν`
of Eq. (A15) p.12, written as a weighted sum of time-evolved Hermitian components. -/
noncomputable def bohrJump {ι : Type*} [Fintype ι] {J : ℕ} (β : ℝ) (H : Operator D)
    (Q : ι → Fin J → ℂ) (ν : ι → ℝ) (A : ι → Operator D) (j : Fin J) (t : ℝ) :
    Operator D :=
  ∑ i, (Q i j) • (Real.exp (β * ν i / 4) : ℂ) • evol H t (A i)

/-! ## Quadrature discretisation (paper Eqs. (B3)–(B4), p.19) -/

/-- Midpoint quadrature nodes `t_k = -T + 2Tk/N`, Eq. (B29) p.22. -/
noncomputable def quadratureNodes (T : ℝ) (N : ℕ) (k : Fin N) : ℝ :=
  -T + 2 * T * (k : ℝ) / (N : ℝ)

/-- The quadrature step `h = 2T/N`. -/
noncomputable def quadratureStep (T : ℝ) (N : ℕ) : ℝ := 2 * T / (N : ℝ)

/-- The truncated-and-quadrature Gram operator `B†B X = h Σ_k g(t_k) Σ_j ℬ†_{j,t_k}ℬ_{j,t_k} X`
of Eq. (B3): this is the finite matrix `B†B` of Lemma 7. -/
noncomputable def quadratureGram {J : ℕ} (β T : ℝ) (N : ℕ) (σ : Operator D)
    (B : Fin J → ℝ → Operator D) (X : Operator D) : Operator D :=
  quadratureStep T N •
    ∑ k : Fin N, (gWeight β (quadratureNodes T N k) : ℂ) •
      ∑ j : Fin J, parentSOS σ (B j (quadratureNodes T N k)) X

/-- The exact time-integral parent Hamiltonian of Eq. (A30) applied to `X`. -/
noncomputable def timeIntegralParent {J : ℕ} (β : ℝ) (σ : Operator D)
    (B : Fin J → ℝ → Operator D) (X : Operator D) : Operator D :=
  ∫ t : ℝ, (gWeight β t : ℂ) • ∑ j : Fin J, parentSOS σ (B j t) X

/-! ## Trace distance and KMS variance (Appendix C, p.24 and Lemma 19) -/

/-- Trace distance `d(ρ,η) = ½‖ρ-η‖₁` (Appendix C, p.24), expressed via the trace norm. -/
noncomputable def traceDistance (ρ η : Operator D) : ℝ := (1 / 2) * Matrix.traceNorm (ρ - η)

/-- KMS variance `⟨F₀,F₀⟩_σ` of the centred observable `F - Tr(σF)·I`. -/
noncomputable def kmsVariance (σ F : Operator D) : ℂ :=
  kmsInner σ (F - (Matrix.trace (σ * F)).re • (1 : Operator D))
    (F - (Matrix.trace (σ * F)).re • (1 : Operator D))

/-- `hsNormSq` is the real part of the frozen Hilbert–Schmidt inner product. -/
theorem hsNormSq_eq_hsInner (A : Operator D) :
    hsNormSq A = (hsInner A A).re := by
  rw [Qatlib.Concepts.QuantumGibbs.FormAlgebra.hsInner_self_re_sum]
  rfl

/-- `σ^{1/2}` is a ground state of `H` with spectral gap at least `Δ`: it is annihilated by
`H`, and every Hilbert–Schmidt vector orthogonal to it has Rayleigh quotient at least `Δ`.
This is the paper-level formalisation of "the spectral gap of `H` is `Δ`" used in Lemma 9. -/
def HasSpectralGap (H : Operator D) (v : Operator D) (Δ : ℝ) : Prop :=
  H * v = 0 ∧ ∀ X : Operator D, (hsInner X v).re = 0 →
    Δ * hsNormSq X ≤ (hsInner X (H * X)).re

/-- `ψ` is a unit eigenvector of `M` for the eigenvalue `lam`, and `lam` is the smallest
eigenvalue of `M` on unit Hilbert–Schmidt vectors. This is the paper-level formalisation of
"`ψ_g` is the right singular vector of `B` for its smallest singular value" (`M = B†B`). -/
def IsLowestEigenvector (M : Operator D) (lam : ℝ) (ψ : Operator D) : Prop :=
  hsNorm ψ = 1 ∧ (hsInner ψ (M * ψ)).re = lam ∧
    ∀ φ : Operator D, hsNorm φ = 1 → lam ≤ (hsInner φ (M * φ)).re

/-- A paper-level quantum algorithm: an output map on the target error and explicit resource
fields (query count, qubit count, maximal evolution time). The structure intentionally does not
model circuits, oracles or query semantics; it only records the guarantees that Theorems 12
and 17 of the paper state about the algorithm's outputs and resources. -/
structure QuantumAlgorithm (D : ℕ) where
  /-- The state produced at target error `ε`. -/
  output : ℝ → Operator D
  /-- Number of oracle queries used at target error `ε`. -/
  queries : ℝ → ℝ
  /-- Number of warm-start states consumed at target error `ε`. -/
  warmStarts : ℝ → ℝ
  /-- Number of logical qubits used at target error `ε`. -/
  qubits : ℝ → ℝ
  /-- Maximal Hamiltonian evolution time used at target error `ε`. -/
  maxEvolTime : ℝ → ℝ

/-! ## Inhomogeneous Curie–Weiss model (Appendix C, Eqs. (C1)–(C6), p.25) -/

/-- The computational basis `Fin n → Bool` of `n` qubits. -/
abbrev BitIdx (n : ℕ) := Fin n → Bool

/-- Pauli `Z` on qubit `i`, diagonal in the computational basis. -/
noncomputable def spinZ (n : ℕ) (i : Fin n) : Matrix (BitIdx n) (BitIdx n) ℂ :=
  Matrix.diagonal (fun x => if x i then (-1 : ℂ) else 1)

/-- Pauli `X` on qubit `i` as the bit-flip permutation matrix. -/
noncomputable def spinX (n : ℕ) (i : Fin n) : Matrix (BitIdx n) (BitIdx n) ℂ :=
  Matrix.of (fun x y => if y = Function.update x i (!(x i)) then (1 : ℂ) else 0)

/-- The standard equivalence between the bit-string basis and `Fin (2^n)`. -/
noncomputable def bitEquiv (n : ℕ) : BitIdx n ≃ Fin (2 ^ n) :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_fun]; simp)

/-- Transport a `BitIdx n` matrix to the `Operator (2^n)` index used by the frozen
matrix library. -/
noncomputable def toOp (n : ℕ) (M : Matrix (BitIdx n) (BitIdx n) ℂ) : Operator (2 ^ n) :=
  Matrix.reindex (bitEquiv n) (bitEquiv n) M

/-- Total magnetisation operator `M = Σ_i Z_i`. -/
noncomputable def magOp (n : ℕ) : Operator (2 ^ n) :=
  toOp n (∑ i, spinZ n i)

/-- Magnetisation eigenvalue `M(x) = Σ_i (-1)^{x_i}` on a basis vector. -/
noncomputable def spinSum (n : ℕ) (x : BitIdx n) : ℝ :=
  ∑ i, if x i then (-1 : ℝ) else 1

/-- The inhomogeneous Curie–Weiss Hamiltonian (C1): `H = H_cl + V` with
`H_cl = -M²/(2n) - M/n` and `V = -Σ_{i<j} J_{ij} X_i X_j`. -/
noncomputable def cwHamiltonian (n : ℕ) (Jm : Fin n → Fin n → ℝ) : Operator (2 ^ n) :=
  toOp n (-((1 : ℂ) / (2 * (n : ℂ))) • ((∑ i, spinZ n i) * (∑ i, spinZ n i))
    - ((1 : ℂ) / (n : ℂ)) • (∑ i, spinZ n i)
    - (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).sum
        (fun p => ((Jm p.1 p.2 : ℝ) : ℂ) • (spinX n p.1 * spinX n p.2)))

/-- The phase-sign observable `F = sgn(M)` of Lemma 19. -/
noncomputable def sgnM (n : ℕ) : Operator (2 ^ n) :=
  toOp n (Matrix.diagonal (fun x => if 0 < spinSum n x then (1 : ℂ) else (-1 : ℂ)))

/-- The canonical Gibbs state `σ = e^{-βH}/Tr(e^{-βH})` of Eq. (C2). -/
noncomputable def gibbsState (n : ℕ) (β : ℝ) (H : Operator (2 ^ n)) : Operator (2 ^ n) :=
  (Matrix.trace (NormedSpace.exp ((-(β : ℂ)) • H))).re⁻¹ •
    NormedSpace.exp ((-(β : ℂ)) • H)

/-- The product state `τ = e^{aM}/(2cosh a)^n` of Eq. (C4), as a diagonal density. -/
noncomputable def tauState (n : ℕ) (a : ℝ) : Operator (2 ^ n) :=
  toOp n (Matrix.diagonal (fun x =>
    ((Real.exp (a * spinSum n x) / (2 * Real.cosh a) ^ n : ℝ) : ℂ)))

/-- The positive square root `τ^{1/2}` of the product state, used for the canonical
purification `|Φ⟩ = |τ^{1/2}⟩⟩` of Eq. (C6). -/
noncomputable def tauHalf (n : ℕ) (a : ℝ) : Operator (2 ^ n) :=
  toOp n (Matrix.diagonal (fun x =>
    ((Real.sqrt (Real.exp (a * spinSum n x) / (2 * Real.cosh a) ^ n) : ℝ) : ℂ)))

/-- The warm-start overlap `|⟨Φ|σ^{1/2}⟩⟩|²` of Lemma 14, Eq. (C9), with `|Φ⟩ = |τ^{1/2}⟩⟩`. -/
noncomputable def warmOverlap (n : ℕ) (a β : ℝ) (Jm : Fin n → Fin n → ℝ) : ℝ :=
  Complex.normSq (hsInner (tauHalf n a) (CFC.sqrt (gibbsState n β (cwHamiltonian n Jm))))

/-! ## Lemma 18 constants (paper Eqs. (C50)–(C51), p.32) -/

/-- `z_n = (8κ)^{⌊n/8⌋-1}` of Eq. (C50). -/
noncomputable def zn (κ : ℝ) (n : ℕ) : ℝ := (8 * κ) ^ (n / 8 - 1)

/-- `r_n = e^{-(β/4 - log 2)n}` of Eq. (C50). -/
noncomputable def rn (β : ℝ) (n : ℕ) : ℝ := Real.exp (-(β / 4 - Real.log 2) * (n : ℝ))

/-- `C_n = 2 z_n + 4 e^{-n/80} + 2 √r_n` of Eq. (C51). -/
noncomputable def Cn (κ β : ℝ) (n : ℕ) : ℝ :=
  2 * zn κ n + 4 * Real.exp (-(n : ℝ) / 80) + 2 * Real.sqrt (rn β n)

end Qatlib.Papers.GibbsSampl26.MainResults
