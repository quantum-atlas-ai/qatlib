/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumLWE25.MainResults.SourceModel
import Mathlib.Analysis.Fourier.PoissonSummation

set_option backward.isDefEq.respectTransparency false

/-!
# QuantumLWE25 — Poisson summation (Lemma 10)

Fixed arXiv:2310.00644v2, Lemma 10, p.9 (part of §2, "Preliminaries").

Source statement: for any lattice `L` and any Schwartz function `f : ℝⁿ → ℂ`,
`f(L) = det(L*) · f̂(L*)`, where `f(L) = ∑_{x∈L} f(x)` and `f̂` is the Euclidean
Fourier transform.

Model: a full-rank lattice is presented by a real basis matrix `B`; its points are
`B·z` for `z ∈ ℤⁿ`, and the dual lattice has basis `B⁻ᵀ` with `det(L*) = 1/|det B|`.
This keeps the paper's exact numerical content. The `n`-dimensional Poisson formula is
not in Mathlib (Mathlib only proves the one-dimensional form `SchwartzMap.tsum_eq_tsum_fourier`),
so the general statement is recorded as the statement-only definition
`poisson_summation_formula`; the one-dimensional integer-lattice case is proved below from
Mathlib.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumLWE25.MainResults

open scoped BigOperators Matrix SchwartzMap FourierTransform
open MeasureTheory

/-- The lattice sum `f(L) = ∑_{z ∈ ℤⁿ} f(B·z)` for a lattice with basis `B`. -/
def latticeSum {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (f : (Fin n → ℝ) → ℂ) : ℂ :=
  ∑' z : Fin n → ℤ, f (B *ᵥ fun i => (z i : ℝ))

/-- The Euclidean Fourier transform `f̂(y) = ∫ f(x) e^{-2πi⟨x,y⟩} dx` of the paper (§2, p.9). -/
def fourierTransform {n : ℕ} (f : (Fin n → ℝ) → ℂ) (y : Fin n → ℝ) : ℂ :=
  ∫ x : Fin n → ℝ, f x * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (∑ i, x i * y i : ℝ))

/-- The dual lattice sum `f̂(L*) = ∑_{w ∈ ℤⁿ} f̂(B⁻ᵀ·w)`. -/
def dualLatticeSum {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (f : (Fin n → ℝ) → ℂ) : ℂ :=
  ∑' w : Fin n → ℤ, fourierTransform f ((Bᵀ)⁻¹ *ᵥ fun i => (w i : ℝ))

/-- **Lemma 10 (Poisson Summation Formula), p.9.**
For any full-rank lattice `L` with basis `B` and any Schwartz function `f`,
`f(L) = det(L*) · f̂(L*)`. Since `det(L*) = 1/|det B|`, the right side is
`|det B|⁻¹ · f̂(L*)`.

The paper's proof route (p.9 and its appendix in [Gra08, Prop. 2.2.11]) uses the
one-dimensional formula applied coordinatewise together with the Fourier identities
(2) and (3) of p.9. Mathlib supplies only the one-dimensional case
(`SchwartzMap.tsum_eq_tsum_fourier`), not the `n`-dimensional lattice formula; the
gap is the multivariable Poisson summation theorem for a full-rank lattice together
with summability of `z ↦ f(B·z)` for `f` Schwartz. A future proof should build the
`n`-fold product formula from `Real.tsum_eq_tsum_fourier` and identify `1/|det B|`
with the covolume. -/
def poisson_summation_formula {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.det ≠ 0) (f : (Fin n → ℝ) → ℂ) : Prop := latticeSum B f = ((|B.det| : ℝ) : ℂ)⁻¹ * dualLatticeSum B f

/-- **Lemma 10, proved one-dimensional integer case.** For the lattice `ℤ ⊆ ℝ`
(basis `B = 1`, `det(ℤ*) = 1`) and a Schwartz function `f`, Poisson summation reads
`∑_{n∈ℤ} f(n) = ∑_{n∈ℤ} f̂(n)`. This is Mathlib's
`SchwartzMap.tsum_eq_tsum_fourier` with the `fourier` character evaluated at `0`. -/
theorem poisson_summation_integer (f : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, f (n : ℝ)) = ∑' n : ℤ, 𝓕 f (n : ℝ) := by
  have h := SchwartzMap.tsum_eq_tsum_fourier f 0
  simpa [fourier_eval_zero, add_zero] using h

end Qatlib.Papers.QuantumLWE25.MainResults
