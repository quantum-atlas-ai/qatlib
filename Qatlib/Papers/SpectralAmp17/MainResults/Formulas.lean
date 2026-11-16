/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralAmp17.MainResults.SourceModel.PolynomialToolkit

@[expose] public section


/-! # Exact polynomial formulas from arXiv:1707.05391; no error bound is claimed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.SpectralAmp17.MainResults
open Qatlib.Papers.SpectralAmp17.MainResults.SourceModel

/-- The sign approximation is the shifted error-function polynomial by definition. -/
theorem lemma13_pSgn_value (κ δ ε₁ : ℝ) (n : ℕ) :
    pSgn κ δ ε₁ n = (pErf (2 * kSgn κ ε₁) n).comp
      (Polynomial.C (1 / 2) * (Polynomial.X - Polynomial.C δ)) := rfl

/-- The rectangle polynomial is the symmetric average of two sign polynomials. -/
theorem lemma14_pRect_value (w κ ε₁ : ℝ) (n : ℕ) :
    pRect w κ ε₁ n = Polynomial.C (1 / 2) *
      (pSgn κ ((w + κ) / 2) ε₁ (n + 1) +
        (pSgn κ ((w + κ) / 2) ε₁ (n + 1)).comp (-Polynomial.X)) := rfl

/-- The linear polynomial multiplies the rectangle polynomial by its defining linear factor. -/
theorem lemma15_pLin_value (Γ ε₁ : ℝ) (n : ℕ) :
    pLin Γ ε₁ n = (Polynomial.C (1 / (2 * Γ)) * Polynomial.X) * pRect (2 * Γ) (2 * Γ) ε₁ (n - 1) := rfl

/-- The gap function unfolds to its defining shifted sign formula. -/
theorem lemma16_fGap_value (Δ ε x : ℝ) :
    fGap Δ ε x = (x + 1 - Δ) / Δ * (1 - fSgn Δ (2 * ε) (x + 1 - 3 * Δ / 2)) / 2 := rfl

/-- The exponential truncation is its defining finite Bessel expansion. -/
theorem eq62_pExp_value (β : ℝ) (n : ℕ) :
    pExp β n = Polynomial.C (Real.exp (-β)) *
      (Polynomial.C (besselI 0 β) +
        2 * ∑ j ∈ Finset.Icc 1 n,
          Polynomial.C (besselI j β) * (chebT j).comp (-Polynomial.X)) := rfl

/-- The error-function polynomial is its defining odd Bessel expansion. -/
theorem eq70_pErf_value (k : ℝ) (n : ℕ) :
    pErf k n = Polynomial.C (2 * k * Real.exp (-(k ^ 2) / 2) / Real.sqrt Real.pi) *
      (Polynomial.C (besselI 0 (k ^ 2 / 2)) * Polynomial.X +
        ∑ j ∈ Finset.Icc 1 ((n - 1) / 2),
          Polynomial.C (besselI j (k ^ 2 / 2) * (-1 : ℝ) ^ j) *
            (Polynomial.C ((2 * j + 1 : ℝ)⁻¹) * chebT (2 * j + 1) -
              Polynomial.C ((2 * j - 1 : ℝ)⁻¹) * chebT (2 * j - 1))) := rfl

/-- The shifted error-function polynomial composes with the affine half-scale map. -/
theorem eq72_pErfShift_value (k δ : ℝ) (n : ℕ) :
    pErfShift k δ n = (pErf (2 * k) n).comp
      (Polynomial.C (1 / 2) * (Polynomial.X - Polynomial.C δ)) := rfl

end Qatlib.Papers.SpectralAmp17.MainResults
