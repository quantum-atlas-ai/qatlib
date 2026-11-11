/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Shared finite-matrix source model for LightConeBos22

Kuwahara--Vu--Saito, arXiv:2206.14736v3 (fixed version, 22 Mar 2024).

The paper works with unbounded bosonic operators on an infinite-dimensional Fock
space.  The paper layer of this library records the *quantitative* content of
every active claim in a finite-dimensional matrix model on a finite lattice
`ι`; this is the usual finite cutoff used in the paper itself (the paper's
`CutBasis`/truncation).  All statements below are therefore the corresponding
finite-cutoff inequalities.  The model provides:

* `opLe A B` for the operator order `A ⪯ B` (`B - A` positive semidefinite);
* `evolve H O t` for the Heisenberg evolution `e^{iHt} O e^{-iHt}`;
* `expVal ρ O` for `tr(ρ O)`;
* `trNorm A` for the trace norm `tr √(A†A)`;
* `frobNorm A` for the Frobenius norm `√(tr(A A†))`;
* `nSum n X` for the number operator `n̂_X = ∑_{i ∈ X} n̂_i`;
* `nEig n X k` for the eigenvalue of `n̂_X` on the occupation-basis state `k`,
  with `dExpVal` the corresponding diagonal expectation;
* the paper's numerical constants (`lambdaC`, `cTau1`, `cTau2`, `chatD`,
  `fTau`, `ftildeTau`, the optimization constants `alphaBar`/`chiAlpha`, the
  moment sums `Ntilde`/`N1p`, and `lbarTR`).

The unboundedness of the Fock-space operators is not modelled; the paper's
estimates are uniform in the cutoff, so their finite-cutoff instances are the
statements recorded here.  Number operators are diagonal in the occupation
basis; `dExpVal` therefore computes `tr(ρ O)` for diagonal `O` exactly.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped MatrixOrder ComplexOrder BigOperators

namespace Qatlib.Papers.LightConeBos22.MainResults

/-- A finite set of lattice sites of the paper (the finite system `Λ`). -/
abbrev Site (N : Type*) := N

/-- Operator order `A ⪯ B`: `B - A` is positive semidefinite (paper, Sec. II:
`O₁ ⪯ O₂` iff `σ(O₂ - O₁)` is positive semidefinite). -/
def opLe {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) : Prop :=
  (B - A).PosSemidef

/-- Heisenberg evolution `O(A,t) = e^{iAt} O e^{-iAt}` (paper Eq. (32)). -/
def evolve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H O : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  NormedSpace.exp ((Complex.I * (t : ℂ)) • H) * O *
    NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H)

/-- Expectation `tr(ρ O)` as a real number (real part of the matrix trace). -/
def expVal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ O : Matrix ι ι ℂ) : ℝ := (Matrix.trace (ρ * O)).re

/-- Trace norm `‖A‖₁ = tr √(A† A)` (paper, Supplementary Note 1). -/
def trNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ℝ := (Matrix.trace (CFC.sqrt (Aᴴ * A))).re

/-- Frobenius norm `‖A‖_F = √(tr(A A†))` (paper, Corollary 26). -/
def frobNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ℝ := Real.sqrt (Matrix.trace (A * Aᴴ)).re

/-- Number operator on a subset: `n̂_X = ∑_{i ∈ X} n̂_i` (paper Eq. (24)). -/
def nSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ι → Matrix ι ι ℂ) (X : Finset ι) : Matrix ι ι ℂ :=
  ∑ i ∈ X, n i

/-- The extended subset `X[r] = {i ∈ Λ | d_{i,X} ≤ r}` (paper Eq. (2)). -/
def extend {N : Type*} [Fintype N] (dist : N → N → ℝ) (X : Finset N) (r : ℝ) : Finset N :=
  Finset.univ.filter (fun i => ∃ j ∈ X, dist i j ≤ r)

/-- Distance from a site to a finite set: `d_{i,X}`. -/
def distTo {N : Type*} (dist : N → N → ℝ) (i : N) (X : Finset N) : ℝ :=
  if h : X.Nonempty then X.inf' h (fun j => dist i j) else 0

/-- The surface `∂X = {i ∈ X^c | d_{i,X} = 1}` (paper, Supplementary Note 1). -/
def boundary {N : Type*} [Fintype N] [DecidableEq N] (dist : N → N → ℝ) (X : Finset N) : Finset N :=
  Finset.univ.filter (fun i => i ∉ X ∧ ∃ j ∈ X, dist i j = 1)

/-! ## Diagonal (occupation-basis) model

Number operators `n̂_i` are diagonal in the boson occupation basis.  For a
cutoff basis `ι`, `n i k` is the eigenvalue of `n̂_i` on the basis state `k`. -/

/-- Diagonal operator with real eigenvalues. -/
def diagOp {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun k => (f k : ℂ))

/-- `e^{s f}` as a diagonal operator (imaginary/real time evolution of a
diagonal number operator). -/
def diagExp {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (s : ℝ) : Matrix ι ι ℂ :=
  diagOp (fun k => Real.exp (s * f k))

/-- Spectral projection `Π_{f ≥ x}` of a diagonal operator with eigenvalues `f`. -/
def projGE {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (x : ℝ) : Matrix ι ι ℂ :=
  diagOp (fun k => if x ≤ f k then 1 else 0)

/-- Spectral projection `Π_{f ≤ x}`. -/
def projLE {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (x : ℝ) : Matrix ι ι ℂ :=
  diagOp (fun k => if f k ≤ x then 1 else 0)

/-- Spectral projection `Π_{f > x}`. -/
def projGT {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (x : ℝ) : Matrix ι ι ℂ :=
  diagOp (fun k => if x < f k then 1 else 0)

/-- Eigenvalue of `n̂_X = ∑_{i∈X} n̂_i` on the basis state `k` (paper Eq. (24)). -/
def nEig {ι : Type*} [Fintype ι] (n : ι → ι → ℝ) (X : Finset ι) (k : ι) : ℝ :=
  ∑ i ∈ X, n i k

/-- Diagonal weight of a state: `k ↦ (ρ)_{kk}` (real part).  For a number
operator diagonal in the occupation basis, `tr(ρ n̂_X) = ∑_k diagWeight ρ k * nEig n X k`. -/
def diagWeight {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ) (k : ι) : ℝ :=
  (ρ k k).re

/-- Diagonal expectation `tr(ρ O)` for a diagonal operator with eigenvalues `f`
and a state whose diagonal weights are `ρ`. -/
def dExpVal {ι : Type*} [Fintype ι] (ρ f : ι → ℝ) : ℝ :=
  ∑ k, ρ k * f k

/-! ## Paper constants -/

/-- `λ_c = 1 + c^{-D-1} e^c γ D!` (paper Eq. (12)). -/
def lambdaC (D : ℕ) (c γ : ℝ) : ℝ :=
  1 + (c ^ (D + 1))⁻¹ * Real.exp c * γ * (D.factorial : ℝ)

/-- `c_{τ,1} = 40 e^{4γJ̄τ}` (paper Eq. (76)). -/
def cTau1 (γ J τ : ℝ) : ℝ := 40 * Real.exp (4 * γ * J * τ)

/-- `c_{τ,2} = e^{4γJ̄τ+1}(1 + 8γJ̄τ) + τ` (paper Eq. (76)). -/
def cTau2 (γ J τ : ℝ) : ℝ := Real.exp (4 * γ * J * τ + 1) * (1 + 8 * γ * J * τ) + τ

/-- `D̂_X = ∑_{i∈∂X}∑_{j∈Λ} e^{-d_{i,j}} n̂_j` (paper Eq. (75)). -/
def chatD {N : Type*} [Fintype N] [DecidableEq N]
    (dist : N → N → ℝ) (n : N → Matrix N N ℂ) (X : Finset N) : Matrix N N ℂ :=
  ∑ i ∈ boundary dist X, ∑ j : N, Real.exp (-dist i j) • n j

/-- `f_τ = (1/2) log(1 + 1/(5 c_{τ,1} λ^{1/2} + 2))` (paper Eq. (243)). -/
def fTau (c1 lam : ℝ) : ℝ := (1 / 2) * Real.log (1 + 1 / (5 * c1 * Real.sqrt lam + 2))

/-- `f̃_τ = (1/2) log(1 + 1/(10 e c_{τ,1} λ^{1/2} + 2))` (paper Eq. (361)). -/
def ftildeTau (c1 lam : ℝ) : ℝ :=
  (1 / 2) * Real.log (1 + 1 / (10 * Real.exp 1 * c1 * Real.sqrt lam + 2))

/-- `ᾱ_∞ = ∑_{j=-∞}^{∞} α_{|j|}` (paper Eq. (211)), for a coefficient sequence
`α_j` indexed by the absolute distance. -/
def alphaBar (β : ℕ → ℝ) : ℝ := β 0 + 2 * ∑' n : ℕ, β (n + 1)

/-- `χ_α = max_{j≥0} ∑_{p≥1} α_{p+j}/α_j` (paper Eq. (213)). -/
def chiAlpha (β : ℕ → ℝ) : ℝ := ⨆ j : ℕ, (∑' p : ℕ, β (p + j + 1) / β j)

/-- Absolute difference of two natural numbers, `|a-b|`. -/
def natDist (a b : ℕ) : ℕ := if a ≤ b then b - a else a - b

/-- `Ñ_p = ∑_{j=1}^{p̃} α_{|p-j|} N_j` (paper, Lemma 13). -/
def Ntilde (β : ℕ → ℝ) (N : ℕ → ℝ) (ptilde p : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 ptilde, β (natDist p j) * N j

/-- `N_{1:p} = ∑_{j=1}^{p} N_j`. -/
def N1p (N : ℕ → ℝ) (p : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 p, N j

/-- `ℓ̄_{t,R} = c̄₀ t log(R q₀)` (paper Eq. (433)). -/
def lbarTR (c0 t q0 R : ℝ) : ℝ := c0 * t * Real.log (R * q0)

/-- Imaginary-time evolution `e^{τH} O e^{-τH}` (paper Eq. (72)). -/
def imagEvolve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H O : Matrix ι ι ℂ) (τ : ℝ) : Matrix ι ι ℂ :=
  NormedSpace.exp (((τ : ℝ) : ℂ) • H) * O * NormedSpace.exp ((-(((τ : ℝ) : ℂ))) • H)

/-- Commutator `[A,B] = AB - BA`. -/
def commutator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) : Matrix ι ι ℂ := A * B - B * A

/-- `m`-fold nested commutator `D_m(O) = [H,[H,...[H,O]]]` (paper Eq. (139)). -/
def commutatorPower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ → Matrix ι ι ℂ
  | 0, O => O
  | Nat.succ k, O => commutator H (commutatorPower H k O)

/-- Imaginary-time moment `M_{X₁..X_s}(H,τ) = tr[∏_j n̂_{X_j}(iτ) ρ]`. -/
def imagMoment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (n : ι → Matrix ι ι ℂ) (Xs : List (Finset ι))
    (ρ : Matrix ι ι ℂ) (τ : ℝ) : ℝ :=
  (Matrix.trace ((Xs.map (fun X => imagEvolve H (nSum n X) τ)).prod * ρ)).re

/-- `D̂_X` with the `3/4` exponential weight used in Proposition 16:
`∑_{j ∈ X[ℓ]^c} e^{-3d_{j,X[ℓ]}/4} n̂_j` (paper Eq. (242)). -/
def chatD34 {N : Type*} [Fintype N] [DecidableEq N]
    (dist : N → N → ℝ) (n : N → Matrix N N ℂ) (X : Finset N) (ℓ : ℝ) : Matrix N N ℂ :=
  ∑ j ∈ (extend dist X ℓ)ᶜ, Real.exp (-(3 * distTo dist j X / 4)) • n j

end Qatlib.Papers.LightConeBos22.MainResults
