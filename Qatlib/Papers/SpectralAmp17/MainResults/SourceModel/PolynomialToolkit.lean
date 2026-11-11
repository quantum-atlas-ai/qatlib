/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpectralAmp17.MainResults.SourceModel.PaperModel
import Qatlib.Concepts.QsvtCore.ApproxToolkit.EffectiveNearOptimalSignWindow

set_option backward.isDefEq.respectTransparency false

/-!
# SpectralAmp17 — polynomial toolkit (paper constructions)

Fixed source: arXiv:1707.05391.  This module records the concrete functions and
polynomials that the paper constructs, so that Lem. 9–16 and Cor. 3–8 can be
stated with the paper's own formulas.

* `fSgn`  — `f_sgn,κ,ε(x) = erf(k x)`, `k = (√2/κ)·log^{1/2}(2/(π ε²))` (Lem. 10, Eq. 58).
* `fRect` — `f_rect,w,κ,ε(x) = ½(erf(k(x+δ)) + erf(k(δ−x)))`, `δ = (w+κ)/2` (Lem. 11, Eq. 59).
* `fLin`  — `f_lin,Γ,ε(x) = x/(2Γ)·f_rect,2Γ,2Γ,ε(x)` (Lem. 12, Eq. 60).
* `fGap`  — `f_gap,Δ,ε(x) = ((x+1−Δ)/Δ)·(1 − f_sgn,Δ,2ε(x+1−3Δ/2))/2` (Lem. 15, Eq. 77).
* `chebT` — Chebyshev polynomial `T_j` (used by Eq. 61–78).
* `besselI` — modified Bessel function `I_j(β)` as its defining power series.
* `pExp`  — `p_exp,β,n` (Eq. 62) and `epsExp` — `ε_exp,β,n` (Eq. 63).
* `pGauss` — `p_gauss,γ,n` (Eq. 69).
* `pErf`, `pErfShift`, `pSgn`, `pRect`, `pLin` — Eq. 70, 72, 73, 74, 75.
-/

open scoped BigOperators
open Polynomial
open Qatlib.Concepts.QsvtCore.ApproxToolkit

namespace Qatlib.Papers.SpectralAmp17.MainResults.SourceModel

/-- The paper's `k = (√2/κ)·log^{1/2}(2/(π ε²))` (Lem. 10). -/
noncomputable def kSgn (κ ε : ℝ) : ℝ :=
  Real.sqrt 2 / κ * Real.sqrt (Real.log (2 / (Real.pi * ε ^ 2)))

/-- `f_sgn,κ,ε(x) = erf(k x)` (Eq. 58). -/
noncomputable def fSgn (κ ε x : ℝ) : ℝ := erf (kSgn κ ε * x)

/-- `f_rect,w,κ,ε(x) = ½(erf(k(x+δ)) + erf(k(δ−x)))`, `δ = (w+κ)/2` (Eq. 59). -/
noncomputable def fRect (w κ ε x : ℝ) : ℝ :=
  let δ := (w + κ) / 2
  1 / 2 * (erf (kSgn κ ε * (x + δ)) + erf (kSgn κ ε * (δ - x)))

/-- `f_lin,Γ,ε(x) = x/(2Γ)·f_rect,2Γ,2Γ,ε(x)` (Eq. 60). -/
noncomputable def fLin (Γ ε x : ℝ) : ℝ :=
  x / (2 * Γ) * fRect (2 * Γ) (2 * Γ) ε x

/-- `f_gap,Δ,ε(x) = ((x+1−Δ)/Δ)·(1 − f_sgn,Δ,2ε(x+1−3Δ/2))/2` (Eq. 77). -/
noncomputable def fGap (Δ ε x : ℝ) : ℝ :=
  (x + 1 - Δ) / Δ * (1 - fSgn Δ (2 * ε) (x + 1 - 3 * Δ / 2)) / 2

/-- Chebyshev polynomial `T_j` of the first kind. -/
noncomputable def chebT : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X
  | (n + 2) => 2 * Polynomial.X * chebT (n + 1) - chebT n

/-- Modified Bessel function of the first kind,
`I_j(β) = ∑_m (β/2)^{2m+j} / (m! (m+j)!)`. -/
noncomputable def besselI (j : ℕ) (β : ℝ) : ℝ :=
  ∑' m : ℕ, (β / 2) ^ (2 * m + j) /
    ((m.factorial : ℝ) * ((m + j).factorial : ℝ))

/-- Eq. 62: the Chevyshev truncation `p_exp,β,n` of `e^{-β(x+1)}`. -/
noncomputable def pExp (β : ℝ) (n : ℕ) : Polynomial ℝ :=
  Polynomial.C (Real.exp (-β)) *
    (Polynomial.C (besselI 0 β) +
      2 * ∑ j ∈ Finset.Icc 1 n,
        Polynomial.C (besselI j β) * (chebT j).comp (-Polynomial.X))

/-- Eq. 63: the truncation error `ε_exp,β,n = 2e^{-β} ∑_{j>n} |I_j(β)|`. -/
noncomputable def epsExp (β : ℝ) (n : ℕ) : ℝ :=
  2 * Real.exp (-β) * ∑' j : ℕ, |besselI (j + n + 1) β|

/-- Eq. 69: `p_gauss,γ,n(x) = p_exp,γ²/2,n/2(2x²−1)`. -/
noncomputable def pGauss (γ : ℝ) (n : ℕ) : Polynomial ℝ :=
  (pExp (γ ^ 2 / 2) (n / 2)).comp (2 * Polynomial.X ^ 2 - 1)

/-- Eq. 70: `p_erf,k,n`. -/
noncomputable def pErf (k : ℝ) (n : ℕ) : Polynomial ℝ :=
  Polynomial.C (2 * k * Real.exp (-(k ^ 2) / 2) / Real.sqrt Real.pi) *
    (Polynomial.C (besselI 0 (k ^ 2 / 2)) * Polynomial.X +
      ∑ j ∈ Finset.Icc 1 ((n - 1) / 2),
        Polynomial.C (besselI j (k ^ 2 / 2) * (-1 : ℝ) ^ j) *
          (Polynomial.C ((2 * j + 1 : ℝ)⁻¹) * chebT (2 * j + 1) -
            Polynomial.C ((2 * j - 1 : ℝ)⁻¹) * chebT (2 * j - 1)))

/-- Eq. 72: `p_erf,k,δ,n(x) = p_erf,2k,n((x−δ)/2)`. -/
noncomputable def pErfShift (k δ : ℝ) (n : ℕ) : Polynomial ℝ :=
  (pErf (2 * k) n).comp (Polynomial.C (1 / 2) * (Polynomial.X - Polynomial.C δ))

/-- Eq. 73: `p_sgn,κ,δ,n(x) = p_erf,k,δ,n(x)` with `k = kSgn κ ε₁`. -/
noncomputable def pSgn (κ δ ε₁ : ℝ) (n : ℕ) : Polynomial ℝ :=
  pErfShift (kSgn κ ε₁) δ n

/-- Eq. 74: `p_rect,w,κ,n(x) = ½(p_sgn,κ,δ,n+1(x) + p_sgn,κ,δ,n+1(−x))`,
`δ = (w+κ)/2`. -/
noncomputable def pRect (w κ ε₁ : ℝ) (n : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / 2) *
    (pSgn κ ((w + κ) / 2) ε₁ (n + 1) +
      (pSgn κ ((w + κ) / 2) ε₁ (n + 1)).comp (-Polynomial.X))

/-- Eq. 75: `p_lin,Γ,n(x) = x/(2Γ)·p_rect,2Γ,2Γ,n−1(x)`. -/
noncomputable def pLin (Γ ε₁ : ℝ) (n : ℕ) : Polynomial ℝ :=
  (Polynomial.C (1 / (2 * Γ)) * Polynomial.X) * pRect (2 * Γ) (2 * Γ) ε₁ (n - 1)

end Qatlib.Papers.SpectralAmp17.MainResults.SourceModel
