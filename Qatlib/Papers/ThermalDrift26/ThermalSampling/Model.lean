/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixExpTrace.GibbsNorm

set_option backward.isDefEq.respectTransparency false

/-!
# ThermalDrift26 — shared paper-layer vocabulary

Fixed source: Jiang, Jing, Lai, Wang, Zhang, *Thermal-Drift Sampling: Generating
Thermal Ensembles for Learning Many-Body Systems*, arXiv:2602.05912v2.
Read from the pre-fetched PDF/text at `assets/2602.05912v2.{pdf,txt}`.

This file collects the small amount of notation shared by the claim modules:
the normalized Gibbs state, the matrix commutator and iterated adjoint action,
the palindromic exponential product of Lemma S10, the partial trace / block
trace used in Theorem S6, and the ordered thermal branches `E_σ^↑`, `E_σ^↓`.

These definitions are paper vocabulary only. They make no proof claim; every
claim module states its own theorem with the original hypotheses and bounds.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.ThermalDrift26.ThermalSampling

/-- Normalized Gibbs (thermal) state `e^A / Tr[e^A]`.

Source: arXiv:2602.05912v2, Eq. (C.6) and the definition of `G_{β,H}`. -/
noncomputable def gibbsState {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) : Matrix I I ℂ :=
  ((Matrix.trace (NormedSpace.exp A)).re : ℂ)⁻¹ • NormedSpace.exp A

/-- Matrix commutator `[A,B] = AB - BA`. -/
def commutator {I : Type} [Fintype I] (A B : Matrix I I ℂ) : Matrix I I ℂ := A * B - B * A

/-- Iterated adjoint action `ad_A^r(B)`, with `ad_A^0(B) = B` and
`ad_A^{r+1}(B) = [A, ad_A^r(B)]`. -/
def adPow {I : Type} [Fintype I] (A : Matrix I I ℂ) :
    ℕ → Matrix I I ℂ → Matrix I I ℂ
  | 0, B => B
  | r + 1, B => commutator A (adPow A r B)

/-- Partial sum `S_k = ∑_{j=1}^{k} B_j` of Lemma S10. -/
noncomputable def partialSum {I : Type} (B : ℕ → Matrix I I ℂ) (k : ℕ) :
    Matrix I I ℂ :=
  ∑ j ∈ Finset.range k, B (j + 1)

/-- Right palindromic half `∏_{j=2}^{k} e^{B_j}` (with `rightProd 0 = rightProd 1 = 1`). -/
noncomputable def rightProd {I : Type} [Fintype I] [DecidableEq I]
    (B : ℕ → Matrix I I ℂ) : ℕ → Matrix I I ℂ
  | 0 => 1
  | 1 => 1
  | n + 2 => rightProd B (n + 1) * NormedSpace.exp (B (n + 2))

/-- Left palindromic half `∏_{j=k}^{2} e^{B_j} = e^{B_k} ⋯ e^{B_2}`
(with `leftProd 0 = leftProd 1 = 1`). -/
noncomputable def leftProd {I : Type} [Fintype I] [DecidableEq I]
    (B : ℕ → Matrix I I ℂ) : ℕ → Matrix I I ℂ
  | 0 => 1
  | 1 => 1
  | n + 2 => NormedSpace.exp (B (n + 2)) * leftProd B (n + 1)

/-- The palindromic product `∏_{j=N}^{2} e^{B_j} · e^{2B_1} · ∏_{j=2}^{N} e^{B_j}`
of Lemma S10, Eq. (C.8). -/
noncomputable def palindrome {I : Type} [Fintype I] [DecidableEq I]
    (N : ℕ) (B : ℕ → Matrix I I ℂ) : Matrix I I ℂ :=
  leftProd B N * NormedSpace.exp ((2 : ℂ) • B 1) * rightProd B N

/-- The cubic term `Δ_N = -(1/6) ∑_{k=2}^{N} [B_k + 2S_{k-1}, [B_k, 2S_{k-1}]]`
of Lemma S10, Eq. (C.8). -/
noncomputable def deltaTerm {I : Type} [Fintype I] (N : ℕ) (B : ℕ → Matrix I I ℂ) :
    Matrix I I ℂ :=
  -((1 / 6 : ℂ)) •
    (∑ k ∈ Finset.Icc 2 N,
      commutator (B k + (2 : ℂ) • partialSum B (k - 1))
        (commutator (B k) ((2 : ℂ) • partialSum B (k - 1))))

/-- Partial trace over the first (ancilla) factor `A` of a matrix on `A × S`. -/
noncomputable def partialTraceA {A S : Type} [Fintype A] [DecidableEq A]
    [Fintype S] [DecidableEq S] (X : Matrix (A × S) (A × S) ℂ) : Matrix S S ℂ :=
  fun s s' => ∑ a, X (a, s) (a, s')

/-- `Tr_{AB}[(Π_AB ⊗ I_S) · X]` for a matrix `X` on `AB × S` and a matrix `Π`
on `AB`. This is the left side of Theorem S6, Eq. (B.24). -/
noncomputable def blockTrace {A S : Type} [Fintype A] [DecidableEq A]
    [Fintype S] [DecidableEq S] (P : Matrix A A ℂ)
    (X : Matrix (A × S) (A × S) ℂ) : Matrix S S ℂ :=
  fun s s' => ∑ a, ∑ a', P a a' * X (a', s) (a, s')

/-- The ordered thermal branch `E_σ^↑(ρ) = e^{+τσ/2} ρ e^{+τσ/2}`. -/
noncomputable def thermalUpBranch {S : Type} [Fintype S] [DecidableEq S]
    (τ : ℝ) (σ : Matrix S S ℂ) (ρ : Matrix S S ℂ) : Matrix S S ℂ :=
  NormedSpace.exp (((τ / 2 : ℝ) : ℂ) • σ) * ρ *
    NormedSpace.exp (((τ / 2 : ℝ) : ℂ) • σ)

/-- The ordered thermal branch `E_σ^↓(ρ) = e^{-τσ/2} ρ e^{-τσ/2}`. -/
noncomputable def thermalDownBranch {S : Type} [Fintype S] [DecidableEq S]
    (τ : ℝ) (σ : Matrix S S ℂ) (ρ : Matrix S S ℂ) : Matrix S S ℂ :=
  NormedSpace.exp (((-τ / 2 : ℝ) : ℂ) • σ) * ρ *
    NormedSpace.exp (((-τ / 2 : ℝ) : ℂ) • σ)

end Qatlib.Papers.ThermalDrift26.ThermalSampling
