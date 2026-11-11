/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# Source model for arXiv:2510.25750v1

This file fixes the numerical vocabulary of Kean Chen, *Inverse-free quantum state estimation
with Heisenberg scaling* (arXiv:2510.25750v1, 2025-10-29), Section 3–5.  It records the
coefficients `x_i, y_i` (Eq. (16)), `α_i, β_i` (Eq. (11)), `f_i` (Eq. (22)) and `g_i`
(Eq. (23)), the Γ-shaped Young diagram dimensions via the Weyl formula (Eq. (5)), and the
scalar quantities Eq. (17), (20), (21), (24), (25).

The source assumes `n` is a multiple of `2d`, `L = n/(2d)` and `N = (d+1)L`.  The defined
functions take `(d, L, N, i)` explicitly so every paper-layer statement can be read against
the typeset formula.  Nothing here asserts positivity of the Weyl dimensions or the Haar
average; those are the separate obligations of the claim theorems.

Boundary: these are paper-level scalar definitions, not a formalization of Schur–Weyl duality,
Gelfand–Tsetlin bases, Haar measure, or the pretty-good measurement.
-/

set_option autoImplicit false

namespace Qatlib.Papers.HeisenbergEst25.MainResults.Model

open scoped BigOperators

/-- Eq. (16): the coefficient `x_i` of the Γ-shaped tableau chain. -/
noncomputable def xCoeff (d L N i : ℕ) : ℝ :=
  Real.sqrt ((((N : ℝ) + (d : ℝ) - (i : ℝ) - 1) * ((N : ℝ) - (i : ℝ) + 1)) /
    ((((L : ℝ) + (N : ℝ) + (d : ℝ) - 2 * (i : ℝ) - 1)) *
      ((L : ℝ) + (N : ℝ) + (d : ℝ) - 2 * (i : ℝ))))

/-- Eq. (16): the coefficient `y_i` of the Γ-shaped tableau chain. -/
noncomputable def yCoeff (d L N i : ℕ) : ℝ :=
  Real.sqrt ((((L : ℝ) - (i : ℝ) + 1) * ((L : ℝ) + (d : ℝ) - (i : ℝ) - 1)) /
    ((((L : ℝ) + (N : ℝ) + (d : ℝ) - 2 * (i : ℝ) + 1)) *
      ((L : ℝ) + (N : ℝ) + (d : ℝ) - 2 * (i : ℝ))))

/-- Eq. (11): the Clebsch–Gordan coefficient `α_i`. -/
noncomputable def alphaCoeff (d L N i : ℕ) : ℝ :=
  ((N : ℝ) + (d : ℝ) - (i : ℝ) - 1) /
    ((L : ℝ) + (N : ℝ) + (d : ℝ) - 2 * (i : ℝ) - 1)

/-- Eq. (11): the Clebsch–Gordan coefficient `β_i`. -/
noncomputable def betaCoeff (d L N i : ℕ) : ℝ :=
  ((L : ℝ) - (i : ℝ)) /
    ((L : ℝ) + (N : ℝ) + (d : ℝ) - 2 * (i : ℝ) - 1)

/-- Eq. (23): `g_i = (i+1)(L+N+d-i)`. -/
noncomputable def gCoeff (d L N i : ℕ) : ℝ :=
  ((i : ℝ) + 1) * ((L : ℝ) + (N : ℝ) + (d : ℝ) - (i : ℝ))

/-- Eq. (22): the instantiated weight `f_i`.  The two products run over `2 ≤ j ≤ d-1`,
matching the paper's `∏_{j=2}^{d-1}`. -/
noncomputable def fCoeff (d L N i : ℕ) : ℝ :=
  gCoeff d L N i *
    Real.sqrt (((L : ℝ) + (N : ℝ) + (d : ℝ) - 2 * (i : ℝ) - 1) *
      (∏ j ∈ Finset.Icc 2 (d - 1), ((N : ℝ) + (j : ℝ) - (i : ℝ) - 1)) *
      (∏ j ∈ Finset.Icc 2 (d - 1), ((L : ℝ) + (d : ℝ) - (j : ℝ) - (i : ℝ))))

/-- Row lengths `1..d` of the Γ_i Young diagram of Figure 1(a): row 1 has `L+N-i`,
rows `2..d-1` have `L`, row `d` has `i`. -/
def gammaRow (d L N i k : ℕ) : ℤ :=
  if k = 1 then (L : ℤ) + (N : ℤ) - (i : ℤ)
  else if k = d then (i : ℤ)
  else (L : ℤ)

/-- Row lengths `1..d` of the Γ_i^+ Young diagram of Figure 1(b): row 1 has
`L+N+1-i`; the other rows agree with `Γ_i`. -/
def gammaPlusRow (d L N i k : ℕ) : ℤ :=
  if k = 1 then (L : ℤ) + (N : ℤ) + 1 - (i : ℤ)
  else if k = d then (i : ℤ)
  else (L : ℤ)

/-- Weyl dimension formula (Eq. (5)) for a shape with at most `d` rows:
`∏_{1 ≤ a < b ≤ d} (λ_a - a - λ_b + b)/(b - a)`. -/
noncomputable def weylDim (d : ℕ) (shape : ℕ → ℤ) : ℝ :=
  ∏ p ∈ ((Finset.Icc 1 d).product (Finset.Icc 1 d)).filter (fun p => p.1 < p.2),
    (((shape p.1 - (p.1 : ℤ) - shape p.2 + (p.2 : ℤ) : ℤ)) : ℝ) /
      ((p.2 : ℝ) - (p.1 : ℝ))

/-- Weyl dimension of `Q^d_{γ_i}` (Eq. (5) applied to the shape of `Γ_i`). -/
noncomputable def gammaDim (d L N i : ℕ) : ℝ := weylDim d (gammaRow d L N i)

/-- Weyl dimension of `Q^d_{γ_i^+}`. -/
noncomputable def gammaPlusDim (d L N i : ℕ) : ℝ := weylDim d (gammaPlusRow d L N i)

/-- The dimension ratio `dim(Q^d_{γ_i}) / dim(Q^d_{γ_i^+})` appearing in Fact 5.2. -/
noncomputable def gammaDimRatio (d L N i : ℕ) : ℝ :=
  gammaDim d L N i / gammaPlusDim d L N i

/-- The dimension ratio `dim(Q^d_{γ_{i-1}}) / dim(Q^d_{γ_i^+})` appearing in Fact 5.2. -/
noncomputable def gammaDimRatioPrev (d L N i : ℕ) : ℝ :=
  gammaDim d L N (i - 1) / gammaPlusDim d L N i

/-- Eq. (17): the expected squared fidelity `f_0² x_0² + Σ_{i=1}^{L} (f_i x_i + f_{i-1} y_i)²`.
It is also the numerator `Σ_{i=0}^{L} (f_i x_i + f_{i-1} y_i)²` of Eq. (21) with `f_{-1}=0`. -/
noncomputable def eq17 (d L N : ℕ) (f : ℕ → ℝ) : ℝ :=
  (f 0 * xCoeff d L N 0) ^ 2 +
    ∑ i ∈ Finset.Icc 1 L,
      (f i * xCoeff d L N i + f (i - 1) * yCoeff d L N i) ^ 2

/-- Eq. (20): the PGM fidelity numerator expressed through the Clebsch–Gordan coefficients and
the Weyl dimension ratios.  The first term is written as the square of `f_0 α_0 √(dim ratio)`,
which equals the paper's `f_0² α_0² dim(Qγ_0)/dim(Qγ_0^+)` when the ratio is nonnegative. -/
noncomputable def eq20 (d L N : ℕ) (f : ℕ → ℝ) : ℝ :=
  (f 0 * alphaCoeff d L N 0 * Real.sqrt (gammaDimRatio d L N 0)) ^ 2 +
    ∑ i ∈ Finset.Icc 1 L,
      (f i * alphaCoeff d L N i * Real.sqrt (gammaDimRatio d L N i) +
        f (i - 1) * betaCoeff d L N (i - 1) * Real.sqrt (gammaDimRatioPrev d L N i)) ^ 2

/-- Eq. (21): the homogeneous fidelity ratio, with `f_{-1}=0`. -/
noncomputable def eq21 (d L N : ℕ) (f : ℕ → ℝ) : ℝ :=
  eq17 d L N f / (∑ i ∈ Finset.Icc 0 L, (f i) ^ 2)

/-- Eq. (24): the ratio obtained from `1 - Eq. (21)` after instantiating `f_i` by Eq. (22).
The numerator carries `(g_i - g_{i-1})²/(L+N+d-2i)` and the denominator
`(g_i² - g_{i-1}²)/(d-1)`, both multiplied by the two products `∏_{j=1}^{d-1}`. -/
noncomputable def eq24 (d L N : ℕ) (g : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.Icc 0 L,
      ((g i - (if i = 0 then 0 else g (i - 1))) ^ 2 /
          ((L : ℝ) + (N : ℝ) + (d : ℝ) - 2 * (i : ℝ))) *
        (∏ j ∈ Finset.Icc 1 (d - 1), ((N : ℝ) + (j : ℝ) - (i : ℝ))) *
        (∏ j ∈ Finset.Icc 1 (d - 1), ((L : ℝ) + (j : ℝ) - (i : ℝ)))) /
    (∑ i ∈ Finset.Icc 0 L,
      (((g i) ^ 2 - (if i = 0 then 0 else g (i - 1)) ^ 2) / ((d : ℝ) - 1)) *
        (∏ j ∈ Finset.Icc 1 (d - 1), ((N : ℝ) + (j : ℝ) - (i : ℝ))) *
        (∏ j ∈ Finset.Icc 1 (d - 1), ((L : ℝ) + (j : ℝ) - (i : ℝ))))

/-- Eq. (25): the closed form `(d-1)/(L+N+d+(2/(d+1))NL)^2`. -/
noncomputable def eq25 (d L N : ℕ) : ℝ :=
  ((d : ℝ) - 1) /
    (((L : ℝ) + (N : ℝ) + (d : ℝ) + (2 / ((d : ℝ) + 1)) * (N : ℝ) * (L : ℝ)) ^ 2)

/-- The expected infidelity `1 - Eq. (21)` of Protocol 1 with the Eq. (22) weights, for the
paper's parameters `N = (d+1)L`. -/
noncomputable def paperInfidelity (d L : ℕ) : ℝ :=
  1 - eq21 d L ((d + 1) * L) (fCoeff d L ((d + 1) * L))

/-- The number of forward queries in the paper's parameterization: `n = 2dL`. -/
def paperQueries (d L : ℕ) : ℕ := 2 * d * L

/-- Markov lower bound on `Pr[1 - fidelity² ≤ ε²/10]` when the expected infidelity is `m`:
`1 - m/(ε²/10)`. -/
noncomputable def markovSuccessProb (m ε : ℝ) : ℝ := 1 - m / (ε ^ 2 / 10)

/-- The amplitude-estimation error obtained from a state estimate with expected infidelity `m`
through Fact 5.1: `√(2m)` (half the trace distance bound, with the pure-state identity). -/
noncomputable def amplitudeErrorBound (m : ℝ) : ℝ := Real.sqrt (2 * m)

end Qatlib.Papers.HeisenbergEst25.MainResults.Model
