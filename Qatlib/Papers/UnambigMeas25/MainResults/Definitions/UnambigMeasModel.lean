/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Fine-grained unambiguous measurements: shared model

This file fixes the object language of the paper

  Quentin Buzet and André Chailloux, *Fine-Grained Unambiguous Measurements*,
  arXiv:2510.07298v2 (4 Nov 2025).

Everything below is a paper-layer encoding of the paper's own vocabulary:

* `F2 n` is the vector space `𝔽₂ⁿ` (Definition 2 / Notation Section 2);
* `StateVec n` is `ℂ^{𝔽₂ⁿ}`, `Op n` is the space of operators on it;
* `chi` is the character `(-1)^{x·y}` and `fourierBasis` is Definition 8's dual
  basis `|b_x⟩ = 2^{-n/2} ∑_y (-1)^{x·y} |y⟩`;
* `SymFamily` is Definition 2/16's symmetric family with `|ψ_x⟩ = X_x |ψ_0⟩`;
* `Measurement`, `IsPOVM`, `Gamma`, `GammaS` encode Definitions 3, 4, 13, 14, 17;
* `score`, `rho`, `rho2`, `thm1Expr` encode Definitions 15 and Theorem 1's
  objective function;
* `PrimalFamily`, `PrimalFeasible`, `lambdaValue`, `rhoL` encode Definition 6;
* `DualFeasible`, `sigmaValue`, `sigmaL` encode Section 4.1's dual program;
* `Cthr`, `CAv`, `epsilonOut` are the threshold/average score functions and the
  tail mass of the Fourier distribution;
* `UniversalFinset`, `UniversalParity`, `AffineKSubspace` encode Definitions 20/21
  and Proposition 16;
* `MargFamily` / `MargFeasible` is the *compact* linear program of Section 3.3
  after marginalising the `y` variables (the paper uses this form in the proofs
  of Propositions 12, 13 and in Appendix A);
* `EknSet`, `complementIndex`, `maxRep`, `minRep` encode Definitions 23/24 and the
  coset-leader vocabulary of Appendix A.

Nothing in this file asserts any of the paper's theorems; it is pure vocabulary.
The paper works with dual cosets `D_H(s) = {x : G_H x = s}` (Definition 11), where
`G_H ∈ Λ_{n-k}` is a parity-check matrix with `Im(G_Hᵀ) = ker H`.  Each `D_H(s)`
is an affine subspace of dimension `k` (a coset of `rowspace H` with `2^k`
elements), and two vectors `i, j` lie in the same dual coset of `H` exactly when
`i + j ∈ range(Hᵀ)`; this relation is `SameDualCoset H i j`.  Constraint (1)/(2)
of Definition 6 is constant on these cosets, and Constraint (3) of Section 4.1
quantifies over them as `G_H x = s`; both are encoded below with the parity-check
parametrisation `cosetSum b G s` (`G : Lam n (n - k)`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UnambigMeas25.MainResults

open Matrix BigOperators
open scoped Classical MatrixOrder ComplexOrder BigOperators

/-! ## The ambient vector space `𝔽₂ⁿ` and the characters -/

/-- `𝔽₂ⁿ`, encoded as functions `Fin n → ZMod 2`. -/
abbrev F2 (n : ℕ) := Fin n → ZMod 2

/-- The canonical inner product `x · y` of `𝔽₂ⁿ`, with values in `ZMod 2`. -/
def f2dot {n : ℕ} (x y : F2 n) : ZMod 2 := ∑ j, x j * y j

/-- The sign character `(-1)^{x·y}` as a complex number. -/
def chi {n : ℕ} (x y : F2 n) : ℂ := if f2dot x y = 0 then 1 else -1

/-- Hamming weight `|x|_H`. -/
def hammingWeight {n : ℕ} (i : F2 n) : ℕ :=
  (Finset.univ.filter (fun j => i j ≠ 0)).card

/-- The Hamming ball `B_d = {i : |i|_H ≤ d}` (Section 4.2). -/
def ball {n : ℕ} (d : ℕ) : Set (F2 n) := {i | hammingWeight i ≤ d}

/-! ## States, operators, Fourier basis -/

/-- A state vector in `ℂ^{𝔽₂ⁿ}`. -/
abbrev StateVec (n : ℕ) := F2 n → ℂ

/-- An operator on `ℂ^{𝔽₂ⁿ}`. -/
abbrev Op (n : ℕ) := Matrix (F2 n) (F2 n) ℂ

/-- The normalisation `√(2ⁿ)` used by the Fourier basis (Definition 8). -/
def sqrtTwoPow (n : ℕ) : ℂ := ((Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ)

/-- Fourier coefficients `α̂_i = ⟨b_i|ψ_0⟩ = 2^{-n/2} ∑_j (-1)^{i·j} α_j`. -/
def fourierCoeffM {n : ℕ} (α : StateVec n) (i : F2 n) : ℂ :=
  (sqrtTwoPow n)⁻¹ * ∑ j, chi i j * α j

/-- The dual (Fourier) basis vector `|b_i⟩` of Definition 8. -/
def fourierBasis {n : ℕ} (i : F2 n) : StateVec n :=
  fun j => (sqrtTwoPow n)⁻¹ * chi i j

/-- The computational basis vector `|x⟩`. -/
def basisVec {n : ℕ} (x : F2 n) : StateVec n :=
  fun i => if i = x then 1 else 0

/-- The bra-ket `⟨φ|ψ⟩`. -/
def braKet {n : ℕ} (φ ψ : StateVec n) : ℂ :=
  ∑ i, (starRingEnd ℂ) (φ i) * ψ i

/-- The Born expectation `⟨ψ|F|ψ⟩ = Tr(F |ψ⟩⟨ψ|)`. -/
def expect {n : ℕ} (ψ : StateVec n) (F : Op n) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (ψ i) * F i j * ψ j

/-- The rank-one operator `|ψ⟩⟨ψ|`. -/
def outer {n : ℕ} (ψ : StateVec n) : Op n :=
  fun i j => ψ i * (starRingEnd ℂ) (ψ j)

/-- The shift operator `X_a |x⟩ = |x + a⟩` (Definition 7). -/
def Xop {n : ℕ} (a : F2 n) : Op n := fun i j => if i = j + a then 1 else 0

/-- The phase operator `Z_b |x⟩ = (-1)^{x·b} |x⟩` (Definition 7). -/
def Zop {n : ℕ} (b : F2 n) : Op n := fun i j => if i = j then chi b i else 0

/-- The tensor Hadamard / quantum Fourier transform `H^{⊗n}` (Definition 8). -/
def Hadamard (n : ℕ) : Op n := fun i j => (sqrtTwoPow n)⁻¹ * chi i j

/-- The Fourier transform `M ↦ M̂ = H^{⊗n} M H^{⊗n}` of an operator, written
entrywise: `M̂_{i,j} = 2^{-n} ∑_{a,b} (-1)^{i·a + j·b} M_{a,b}`. -/
def opFourier {n : ℕ} (F : Op n) (i j : F2 n) : ℂ :=
  ((2 : ℂ) ^ n)⁻¹ * ∑ a, ∑ b, chi i a * chi j b * F a b

/-- The Fourier diagonal element `⟨b_i|F|b_i⟩`, taken as a real number.  The paper
shows it is real for the symmetric POVM elements it considers (Proposition 8). -/
def fourierDiag {n : ℕ} (F : Op n) (i : F2 n) : ℝ := (expect (fourierBasis i) F).re

/-- Translation of amplitudes: `(shift x α)(i) = α(i + x)`. -/
def shift {n : ℕ} (x : F2 n) (α : StateVec n) : StateVec n := fun i => α (i + x)

/-! ## Symmetric families (Definitions 2 and 16) -/

/-- A symmetric family `S = {|ψ_x⟩}`: `|ψ_x⟩ = X_x |ψ_0⟩`. -/
structure SymFamily (n : ℕ) where
  /-- The amplitude vector `|ψ_0⟩`. -/
  α : StateVec n
  /-- The family `x ↦ |ψ_x⟩`. -/
  ψ : F2 n → StateVec n
  /-- The symmetry condition `|ψ_x⟩ = X_x|ψ_0⟩`. -/
  shifted : ∀ x, ψ x = shift x α

namespace SymFamily

variable {n : ℕ}

/-- The Fourier coefficients `α̂_i = ⟨b_i|ψ_0⟩`. -/
def hat (S : SymFamily n) (i : F2 n) : ℂ := fourierCoeffM S.α i

end SymFamily

/-- Full dual support (Definition 18): every Fourier coefficient is nonzero. -/
def FullDualSupport {n : ℕ} (S : SymFamily n) : Prop := ∀ i, S.hat i ≠ 0

/-! ## Full-rank matrices and the measurement families -/

/-- `k × n` matrices over `𝔽₂`. -/
abbrev MatZ (k n : ℕ) := Matrix (Fin k) (Fin n) (ZMod 2)

/-- `Λ_{n,k}` (Definition 9): the `k × n` matrices of full rank `k`,
as a subtype. -/
abbrev Lam (n k : ℕ) := { H : MatZ k n // Matrix.rank H = k }

/-- Matrix-vector product over `𝔽₂`. -/
def matVec {k n : ℕ} (H : MatZ k n) (x : F2 n) : Fin k → ZMod 2 := H.mulVec x

/-- The transpose action `(Hᵀ u)_j = ∑_i H_{i,j} u_i`. -/
def transposeVec {k n : ℕ} (H : MatZ k n) (u : Fin k → ZMod 2) : F2 n :=
  fun j => ∑ i, H i j * u i

/-- A fine-grained measurement family `{F_{H,y}}` indexed by every full-rank `H`
and every `y ∈ 𝔽₂^{rank H}`. -/
structure Measurement (n : ℕ) where
  /-- The POVM element attached to the outcome `(H, y)`. -/
  w : (k : ℕ) → Lam n k → (Fin k → ZMod 2) → Op n

/-- The total POVM weight `∑_{k,H,y} F_{H,y}`. -/
def totalWeight {n : ℕ} (M : Measurement n) : Op n :=
  ∑ k : Fin (n + 1), ∑ H : Lam n k.1,
    ∑ y : (Fin k.1 → ZMod 2), M.w k.1 H y

/-- The POVM axioms of Definition 3 (items 1 and 2). -/
def IsPOVM {n : ℕ} (M : Measurement n) : Prop :=
  (∀ (k : ℕ) (H : Lam n k) (y : Fin k → ZMod 2), (M.w k H y).PosSemidef) ∧
    totalWeight M = 1

/-- `Γ(S)` (Definitions 3, 13, 14): a POVM whose outcome `(H,y)` is never
produced on `|ψ_x⟩` when `H x ≠ y`. -/
def Gamma {n : ℕ} (S : SymFamily n) (M : Measurement n) : Prop :=
  IsPOVM M ∧
    ∀ (k : ℕ) (H : Lam n k) (y : Fin k → ZMod 2) (x : F2 n),
      matVec H.1 x ≠ y → expect (S.ψ x) (M.w k H y) = 0

/-- `Γ_s(S)` (Definition 17): the symmetric elements of `Γ(S)`, satisfying
`X_a F_{H,y} X_a = F_{H,y+Ha}`. -/
def GammaS {n : ℕ} (S : SymFamily n) (M : Measurement n) : Prop :=
  Gamma S M ∧
    ∀ (k : ℕ) (H : Lam n k) (y : Fin k → ZMod 2) (a : F2 n),
      Xop a * M.w k H y * Xop a = M.w k H (y + matVec H.1 a)

/-! ## The optimisation programs ρ, ρ₂, ρ^L, σ^L -/

/-- `ρ(S, {F_{H,y}})` of Definition 15: the uniform average over `x` of the
`C`-weighted success mass. -/
def score {n : ℕ} (S : SymFamily n) (C : ℕ → ℝ) (M : Measurement n) : ℝ :=
  ((∑ x : F2 n, ∑ k : Fin (n + 1), ∑ H : Lam n k.1,
      ∑ y : (Fin k.1 → ZMod 2),
        C k.1 * (expect (S.ψ x) (M.w k.1 H y)).re) / (2 : ℝ) ^ n)

/-- `ρ(S) = max_{Γ(S)} ρ(S, {F})`. -/
def rho {n : ℕ} (S : SymFamily n) (C : ℕ → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ M : Measurement n, Gamma S M ∧ score S C M = v}

/-- The value of a symmetrised measurement on `|ψ_0⟩` alone. -/
def rho2 {n : ℕ} (S : SymFamily n) (C : ℕ → ℝ) (M : Measurement n) : ℝ :=
  ∑ k : Fin (n + 1), ∑ H : Lam n k.1, ∑ y : (Fin k.1 → ZMod 2),
    C k.1 * (expect (S.ψ 0) (M.w k.1 H y)).re

/-- `max_{Γ_s(S)} ρ₂(S, {F})` (Proposition 7). -/
def rho2Max {n : ℕ} (S : SymFamily n) (C : ℕ → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ M : Measurement n, GammaS S M ∧ rho2 S C M = v}

/-- The Fourier-diagonal objective of Theorem 1:
`∑_{k,H,y,i} C(k) |α̂_i|² ⟨b_i|F_{H,y}|b_i⟩`. -/
def thm1Expr {n : ℕ} (S : SymFamily n) (C : ℕ → ℝ) (M : Measurement n) : ℝ :=
  ∑ k : Fin (n + 1), ∑ H : Lam n k.1, ∑ y : (Fin k.1 → ZMod 2),
    ∑ i : F2 n, C k.1 * Complex.normSq (S.hat i) * fourierDiag (M.w k.1 H y) i

/-- `max_{Γ_s(S)}` of the Fourier-diagonal objective (right-hand side of
Theorem 1). -/
def thm1Value {n : ℕ} (S : SymFamily n) (C : ℕ → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ M : Measurement n, GammaS S M ∧ thm1Expr S C M = v}

/-! ## The primal linear program (Definition 6) -/

/-- A family of primal variables `λ_i^{H,y}`. -/
abbrev PrimalFamily (n : ℕ) :=
  (k : ℕ) → Lam n k → (Fin k → ZMod 2) → F2 n → ℝ

/-- The primal objective `∑ C(k) |α̂_i|² λ_i^{H,y}`. -/
def lambdaValue {n : ℕ} (S : SymFamily n) (C : ℕ → ℝ) (lam : PrimalFamily n) : ℝ :=
  ∑ k : Fin (n + 1), ∑ H : Lam n k.1, ∑ y : (Fin k.1 → ZMod 2),
    ∑ i : F2 n, C k.1 * Complex.normSq (S.hat i) * lam k.1 H y i

/-- `i` and `j` lie in the same dual coset `D_H(s)` of Definition 11, i.e. their
difference belongs to the row space of `H` (equivalently `i + j ∈ range Hᵀ`). -/
def SameDualCosetMat {n k : ℕ} (H : MatZ k n) (i j : F2 n) : Prop :=
  ∃ u : Fin k → ZMod 2, transposeVec H u = i + j

/-- The same relation for `H : Λ_k`, i.e. `i, j ∈ D_H(s)` for some `s`. -/
def SameDualCoset {n k : ℕ} (H : Lam n k) (i j : F2 n) : Prop :=
  SameDualCosetMat H.1 i j

/-- Feasibility for the primal program of Definition 6: nonnegativity,
Equation (1) (`∑ λ_i^{H,y} = 1`), and Equation (2) (the Fourier-diagonal
relations, constant on the dual cosets `D_H(s)` of Definition 11). -/
def PrimalFeasible {n : ℕ} (S : SymFamily n) (lam : PrimalFamily n) : Prop :=
  (∀ (k : ℕ) (H : Lam n k) (y : Fin k → ZMod 2) (i : F2 n), 0 ≤ lam k H y i) ∧
    (∀ i : F2 n,
      (∑ k : Fin (n + 1), ∑ H : Lam n k.1, ∑ y : (Fin k.1 → ZMod 2),
        lam k.1 H y i) = 1) ∧
    (∀ (k : ℕ) (H : Lam n k) (y : Fin k → ZMod 2) (i j : F2 n),
      SameDualCoset H i j →
        Complex.normSq (S.hat i) * lam k H y i = Complex.normSq (S.hat j) * lam k H y j)

/-- `ρ^L(S)` (Definition 6). -/
def rhoL {n : ℕ} (S : SymFamily n) (C : ℕ → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ lam : PrimalFamily n, PrimalFeasible S lam ∧ lambdaValue S C lam = v}

/-! ## The compact (marginalised) primal program -/

/-- Primal variables after marginalising `y` (Section 3.3). -/
abbrev MargFamily (n : ℕ) := (k : ℕ) → Lam n k → F2 n → ℝ

/-- Objective of the compact program. -/
def margValue {n : ℕ} (S : SymFamily n) (C : ℕ → ℝ) (lam : MargFamily n) : ℝ :=
  ∑ k : Fin (n + 1), ∑ H : Lam n k.1, ∑ i : F2 n,
    C k.1 * Complex.normSq (S.hat i) * lam k.1 H i

/-- Feasibility of the compact program: constraints (1) and (2) of Section 3.3. -/
def MargFeasible {n : ℕ} (S : SymFamily n) (lam : MargFamily n) : Prop :=
  (∀ (k : ℕ) (H : Lam n k) (i : F2 n), 0 ≤ lam k H i) ∧
    (∀ i : F2 n,
      (∑ k : Fin (n + 1), ∑ H : Lam n k.1, lam k.1 H i) = 1) ∧
    (∀ (k : ℕ) (H : Lam n k) (i j : F2 n),
      SameDualCoset H i j →
        Complex.normSq (S.hat i) * lam k H i = Complex.normSq (S.hat j) * lam k H j)

/-- `ρ^L` of the compact program. -/
def rhoLMarg {n : ℕ} (S : SymFamily n) (C : ℕ → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ lam : MargFamily n, MargFeasible S lam ∧ margValue S C lam = v}

/-! ## The dual program (Section 4.1) -/

/-- `∑_{i ∈ D_H(s)} b_i` in the generator-matrix parametrisation of
Definition 11: `G ∈ Λ_{n-k}` is the canonical generator `G_C` of `C = ker H`,
and `D_H(s) = {i : G i = s}` (an affine subspace of dimension `k`). -/
def cosetSum {n k : ℕ} (b : F2 n → ℝ) (G : Lam n (n - k))
    (s : Fin (n - k) → ZMod 2) : ℝ :=
  ∑ i : F2 n, if matVec G.1 i = s then b i else 0

/-- Dual feasibility (constraint (3) of Section 4.1).  As `H` ranges over `Λ_k`
with `k ∈ [[0,n]]`, the canonical generators `G_H` range over `Λ_{n-k}`, so this
is the paper's condition `∀ k ∈ [[0,n]], ∀ H ∈ Λ_k, ∀ s ∈ F₂^{n-k},
∑_{i ∈ D_H(s)} b_i ≥ C(k) 2^k`.  The range guard `k ≤ n` matters: in the paper
`Λ_k` is empty for `k > n`, while the generator parametrisation `Lam n (n - k)`
would degenerate to `Lam n 0` under truncated subtraction. -/
def DualFeasible {n : ℕ} (C : ℕ → ℝ) (b : F2 n → ℝ) : Prop :=
  (∀ i, 0 ≤ b i) ∧
    ∀ (k : ℕ), k ≤ n → ∀ (G : Lam n (n - k)) (s : Fin (n - k) → ZMod 2),
      C k * (2 : ℝ) ^ k ≤ cosetSum b G s

/-- The dual objective `σ^L(S, (b_i)) = ∑ b_i |α̂_i|²`. -/
def sigmaValue {n : ℕ} (S : SymFamily n) (b : F2 n → ℝ) : ℝ :=
  ∑ i, b i * Complex.normSq (S.hat i)

/-- `σ^L(S)`, the optimum of the dual program. -/
def sigmaL {n : ℕ} (S : SymFamily n) (C : ℕ → ℝ) : ℝ :=
  sInf {v : ℝ | ∃ b : F2 n → ℝ, DualFeasible C b ∧ sigmaValue S b = v}

/-! ## Score functions of the two settings -/

/-- The threshold score `C_τ(k) = 1` for `k ≥ τ` and `0` otherwise. -/
def Cthr (τ : ℕ) : ℕ → ℝ := fun k => if τ ≤ k then 1 else 0

/-- The average-number-of-parities score `C(k) = k`. -/
def CAv : ℕ → ℝ := fun k => (k : ℝ)

/-- The tail mass `ε = ∑_{i ∉ B_d} |α̂_i|²`. -/
def epsilonOut {n : ℕ} (S : SymFamily n) (d : ℕ) : ℝ :=
  ∑ i : F2 n, if hammingWeight i ≤ d then 0 else Complex.normSq (S.hat i)

/-! ## Universal sets and affine subspaces (Definitions 20, 21) -/

/-- A `k`-dimensional affine subspace of `𝔽₂ⁿ`: a fibre of a full-rank
`(n-k) × n` matrix. -/
def AffineKSubspace (n k : ℕ) (V : Set (F2 n)) : Prop :=
  ∃ (H : Lam n (n - k)) (s : Fin (n - k) → ZMod 2),
    V = {x | matVec H.1 x = s}

/-- `k`-universality against affine subspaces (Definition 21). -/
def UniversalFinset (n k : ℕ) (V : Finset (F2 n)) : Prop :=
  ∀ W : Set (F2 n), AffineKSubspace n k W → ∃ i ∈ V, i ∈ W

/-- `k`-universality against the dual cosets `D_H(s)`, `H ∈ Λ_k`, `s ∈ F₂^{n-k}`
(Proposition 16's equivalent formulation).  In the generator parametrisation of
Definition 11 this reads: every fibre of every `G ∈ Λ_{n-k}` meets `V`. -/
def UniversalParity (n k : ℕ) (V : Finset (F2 n)) : Prop :=
  ∀ (G : Lam n (n - k)) (s : Fin (n - k) → ZMod 2), ∃ i ∈ V, matVec G.1 i = s

/-- The right-hand side of Proposition 3 and 17. -/
def universalValue {n : ℕ} (S : SymFamily n) (τ : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ V : Finset (F2 n), UniversalFinset n τ V ∧
    v = (2 : ℝ) ^ τ * ∑ i ∈ V, Complex.normSq (S.hat i)}

/-! ## Coset representatives and the sets `E_k^n` (Definitions 23, 24) -/

/-- The `j`-th standard basis vector of `𝔽₂ⁿ`. -/
def stdVec {n : ℕ} (j : Fin n) : F2 n := fun t => if t = j then 1 else 0

/-- `E_k^n` (Definition 24): the ordered `k`-row submatrices of the identity,
i.e. matrices whose rows are `e_{f 0}, …, e_{f (k-1)}` for a strictly monotone
`f : Fin k → Fin n`. -/
def EknSet (n k : ℕ) : Set (MatZ k n) :=
  {H | ∃ f : Fin k → Fin n, StrictMono f ∧
    ∀ (r : Fin k) (j : Fin n), H r j = if j = f r then 1 else 0}

/-- The identity matrix `I_n`. -/
def identityMat (n : ℕ) : MatZ n n := fun i j => if i = j then 1 else 0

/-- The all-ones vector `𝟙 ∈ 𝔽₂ⁿ`. -/
def onesVec (n : ℕ) : F2 n := fun _ => 1

/-- The complement of the row index set of `f : Fin k → Fin n`. -/
def complementIndex {n k : ℕ} (f : Fin k → Fin n) := {j : Fin n // j ∉ Set.range f}

/-- Membership in the range of a map from a finite index type is decidable. -/
instance decidableMemRange {n k : ℕ} (f : Fin k → Fin n) (j : Fin n) :
    Decidable (j ∈ Set.range f) :=
  inferInstanceAs (Decidable (∃ i, f i = j))

/-- The complement of the selected coordinates is finite. -/
instance finiteComplementIndex {n k : ℕ} (f : Fin k → Fin n) :
    Finite (complementIndex f) :=
  Finite.of_injective (fun x : complementIndex f => x.1) (fun a b h => Subtype.ext h)

/-- The finite type of coordinates outside the selected range. -/
instance complementIndexFintype {n k : ℕ} (f : Fin k → Fin n) :
    Fintype (complementIndex f) := Fintype.ofFinite _

/-- The canonical parity-check matrix `I_{S^c}` associated with the row index
set `S = range f`, indexed directly by the complement subtype. -/
def canonG {n k : ℕ} (f : Fin k → Fin n) :
    Matrix (complementIndex f) (Fin n) (ZMod 2) :=
  fun j t => if t = j.1 then 1 else 0

/-- The canonical dual coset `D_H(s) = {x : x|_{S^c} = s}` of Definition 11 /
Lemma 3, for `H = I_S`. -/
def canonCoset {n k : ℕ} (f : Fin k → Fin n)
    (s : complementIndex f → ZMod 2) : Set (F2 n) :=
  {x | ∀ j, x j.1 = s j}

/-- Weight of a vector indexed by the complement subtype. -/
def complementWeight {n k : ℕ} {f : Fin k → Fin n}
    (s : complementIndex f → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun j => s j ≠ 0)).card

/-- The fibre `{x : G x = s}` of a parity-check matrix, as a finite set. -/
def cosetFinset {n m : ℕ} (G : MatZ m n) (s : Fin m → ZMod 2) : Finset (F2 n) :=
  Finset.univ.filter (fun x => matVec G x = s)

/-- A maximum-weight representative of a dual coset (`r_H^MAX(s)`, Definition 23). -/
def IsMaxRep {n m : ℕ} (G : MatZ m n) (s : Fin m → ZMod 2) (x : F2 n) : Prop :=
  matVec G x = s ∧ ∀ y : F2 n, matVec G y = s → hammingWeight y ≤ hammingWeight x

/-- A minimum-weight representative (coset leader, `r_H^min(s)`, Definition 23). -/
def IsMinRep {n m : ℕ} (G : MatZ m n) (s : Fin m → ZMod 2) (x : F2 n) : Prop :=
  matVec G x = s ∧ ∀ y : F2 n, matVec G y = s → hammingWeight x ≤ hammingWeight y

/-- A nonempty dual coset yields a nonempty `cosetFinset`. -/
lemma cosetFinset_nonempty {n m : ℕ} (G : MatZ m n) (s : Fin m → ZMod 2)
    (h : ∃ x : F2 n, matVec G x = s) : (cosetFinset G s).Nonempty := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, by simp [cosetFinset, hx]⟩

/-- Every nonempty dual coset contains a maximum-weight representative. -/
lemma exists_maxRep {n m : ℕ} (G : MatZ m n) (s : Fin m → ZMod 2)
    (h : ∃ x : F2 n, matVec G x = s) : ∃ x : F2 n, IsMaxRep G s x := by
  have hmem := Finset.exists_max_image (cosetFinset G s) (fun x => hammingWeight x)
    (cosetFinset_nonempty G s h)
  obtain ⟨x, hx, hmax⟩ := hmem
  refine ⟨x, ?_, ?_⟩
  · simp only [cosetFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx
  · intro y hy
    exact hmax y (by simp [cosetFinset, hy])

/-- Every nonempty dual coset contains a minimum-weight representative (coset leader). -/
lemma exists_minRep {n m : ℕ} (G : MatZ m n) (s : Fin m → ZMod 2)
    (h : ∃ x : F2 n, matVec G x = s) : ∃ x : F2 n, IsMinRep G s x := by
  have hmem := Finset.exists_min_image (cosetFinset G s) (fun x => hammingWeight x)
    (cosetFinset_nonempty G s h)
  obtain ⟨x, hx, hmin⟩ := hmem
  refine ⟨x, ?_, ?_⟩
  · simp only [cosetFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx
  · intro y hy
    exact hmin y (by simp [cosetFinset, hy])

/-- A chosen maximum-weight representative of a nonempty dual coset. -/
def maxRep {n m : ℕ} (G : MatZ m n) (s : Fin m → ZMod 2)
    (h : ∃ x : F2 n, matVec G x = s) : F2 n :=
  Classical.choose (exists_maxRep G s h)

/-- The chosen maximum-weight representative satisfies `IsMaxRep`. -/
lemma maxRep_spec {n m : ℕ} (G : MatZ m n) (s : Fin m → ZMod 2)
    (h : ∃ x : F2 n, matVec G x = s) : IsMaxRep G s (maxRep G s h) :=
  Classical.choose_spec (exists_maxRep G s h)

/-- A chosen coset leader (minimum-weight representative). -/
def minRep {n m : ℕ} (G : MatZ m n) (s : Fin m → ZMod 2)
    (h : ∃ x : F2 n, matVec G x = s) : F2 n :=
  Classical.choose (exists_minRep G s h)

/-- The chosen coset leader satisfies `IsMinRep`. -/
lemma minRep_spec {n m : ℕ} (G : MatZ m n) (s : Fin m → ZMod 2)
    (h : ∃ x : F2 n, matVec G x = s) : IsMinRep G s (minRep G s h) :=
  Classical.choose_spec (exists_minRep G s h)

/-! ## Represented compact programs for Appendix A

Definition 22 replaces `Λ_k` by the duplicate-free set `Λ̃_k`.  The Propositions
23–25 display `λ^H` on the standard matrices `E_k^n` (resp. on the full identity
and on `Λ̃_{n-1}`), so they refer to this duplicate-free bookkeeping.  The
structure below records one representative per kernel together with the
requirement that the standard matrices `E_k^n` are among the representatives.
-/

/-- A duplicate-free representative system `Λ̃_k` (Definition 22). -/
structure RepresentativeSystem (n : ℕ) where
  /-- The representative matrices for each `k`. -/
  rep : (k : ℕ) → Finset (MatZ k n)
  /-- Every representative has full rank. -/
  fullRank : ∀ (k : ℕ) (H : MatZ k n), H ∈ rep k → Matrix.rank H = k
  /-- Every full-rank matrix is kernel-equivalent to exactly one representative. -/
  complete : ∀ (k : ℕ) (H : MatZ k n), Matrix.rank H = k →
    ∃! H' : MatZ k n, H' ∈ rep k ∧ ∀ x : F2 n, matVec H' x = 0 ↔ matVec H x = 0

/-- A family of primal variables over a representative system. -/
abbrev RepFamily (n : ℕ) (R : RepresentativeSystem n) :=
  (k : ℕ) → (H : MatZ k n) → F2 n → ℝ

/-- Objective of the compact program over a representative system. -/
def repValue {n : ℕ} (S : SymFamily n) (C : ℕ → ℝ) (R : RepresentativeSystem n)
    (lam : RepFamily n R) : ℝ :=
  ∑ k : Fin (n + 1), ∑ H ∈ R.rep k.1, ∑ i : F2 n,
    C k.1 * Complex.normSq (S.hat i) * lam k.1 H i

/-- Feasibility of the compact program over a representative system. -/
def RepFeasible {n : ℕ} (S : SymFamily n) (R : RepresentativeSystem n)
    (lam : RepFamily n R) : Prop :=
  (∀ (k : ℕ) (H : MatZ k n), H ∈ R.rep k → ∀ i : F2 n, 0 ≤ lam k H i) ∧
    (∀ i : F2 n,
      (∑ k : Fin (n + 1), ∑ H ∈ R.rep k.1, lam k.1 H i) = 1) ∧
    (∀ (k : ℕ) (H : MatZ k n), H ∈ R.rep k → ∀ i j : F2 n,
      SameDualCosetMat H i j →
        Complex.normSq (S.hat i) * lam k H i = Complex.normSq (S.hat j) * lam k H j)

end Qatlib.Papers.UnambigMeas25.MainResults
