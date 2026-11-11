/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# ViscositySol25 — estimating `f(x*)` at the minimiser (Lemmas 20, 21)

Paper: arXiv:2512.07919 (fixed version), "Quantum algorithms for viscosity solutions
to nonlinear Hamilton-Jacobi equations based on an entropy penalisation method".

* Lemma 20, Eq. (77), p.22 — analog protocol (claim `c011`);
* Lemma 21, Eq. (80)-(82), p.23 — digital protocol (claim `c012`).

## Modeling note

Both protocols estimate the expectation `⟨u(t)|f(x̂)|u(t)⟩` to precision
`ζ = εf − εmin` by sampling.  The number of copies of `|u(t)⟩` needed is the
variance/ζ² repetition count; the variance of the estimator is bounded by
`L · maxᵢ⟨gᵢ²(x̂)⟩` (union-bound over the `L` polynomial terms).  We model the copy
count by `varRepetitions var ζ = var/ζ²` and prove the paper's closed form
`O(L maxᵢ⟨gᵢ²⟩/(εf−εmin)²)`.  The minimisation-gap `|f(x*)−f(x*ν)|` is handled by
`lemma19_*`; here it is folded into `εmin`, exactly as the paper's total-error split
`εf = εmin + ζ` (Eq. (76)/(81)).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ViscositySol25.MainResults.OptimizationReadout

/-- Variance-driven repetition count: estimating a quantity of variance `var` to
standard error `ζ` costs `var/ζ²` copies (median-of-means / Chebyshev constant
absorbed by the caller). -/
noncomputable def varRepetitions (var ζ : ℝ) : ℝ := var / ζ ^ 2

/-- **Lemma 20, Eq. (77), p.22 (claim `c011`).**

With `εf = εmin + ζ`, sampling the expectation `⟨f(x̂)⟩ = ⟨u(t)|f(x̂)|u(t)⟩` to
precision `ζ` uses `var/ζ² ≤ L·maxᵢ⟨gᵢ²(x̂)⟩/(εf−εmin)²` copies of `|u(t)⟩`, where
`L·maxᵢ⟨gᵢ²⟩` bounds the estimator variance.  This is the paper's
`O(L maxᵢ⟨gᵢ²(x̂)⟩/(εf−εmin)²)` with the precise constant `1`. -/
theorem lemma20_expectation_preparations
    (var L maxg εf εmin : ℝ) (hvar : var ≤ L * maxg) (hgap : 0 < εf - εmin) :
    varRepetitions var (εf - εmin)
      ≤ L * maxg / (εf - εmin) ^ 2 := by
  unfold varRepetitions
  have hpos : 0 < (εf - εmin) ^ 2 := by positivity
  gcongr

/-- **Lemma 20, choice `ν = O(εmin⁴/d²)`, p.23 (claim `c011`).**

The regularisation `ν` in Algorithm 3 is chosen at the order `εmin⁴/d²`; concretely
some `ν > 0` of that order exists (the constant `c` absorbs Lemma 3's constant). -/
theorem lemma20_nu_order
    (d εmin c : ℝ) (hd : 0 < d) (hc : 0 < c) (hεmin : 0 < εmin) :
    ∃ ν : ℝ, 0 < ν ∧ ν = c * εmin ^ 4 / d ^ 2 := by
  refine ⟨c * εmin ^ 4 / d ^ 2, ?_, rfl⟩
  positivity

/-- **Lemma 21, Eq. (80)-(82), p.23 (claim `c012`).**

Digital protocol: the copy count is the same `O(L maxᵢ⟨gᵢ²(x̂)⟩/(εf−εmin)²)`; the
discretisation only changes `εmin` (`|⟨f(x̂)⟩ − ⟨f(X̂)⟩| ≲ 1/(ν Nx²)`, Eq. (80)). -/
theorem lemma21_expectation_preparations
    (var L maxg εf εmin : ℝ) (hvar : var ≤ L * maxg) (hgap : 0 < εf - εmin) :
    varRepetitions var (εf - εmin)
      ≤ L * maxg / (εf - εmin) ^ 2 :=
  lemma20_expectation_preparations var L maxg εf εmin hvar hgap

/-- **Lemma 21, choice `ν = (εmin − O(√(d/Nx)))/Nx`, p.23 (claim `c012`).**

With `β = εmin − c·√(d/Nx) > 0` (the paper's `β ≪ 1`), the choice `ν = β/Nx²`
realises the stated order `ν = (εmin − O(√(d/Nx)))/Nx`; here `c` is the explicit
`O`-constant. -/
theorem lemma21_nu_order
    (d Nx εmin c : ℝ) (hNx : 0 < Nx) (hβ : 0 < εmin - c * Real.sqrt (d / Nx)) :
    ∃ ν : ℝ, 0 < ν ∧ ν = (εmin - c * Real.sqrt (d / Nx)) / Nx := by
  refine ⟨(εmin - c * Real.sqrt (d / Nx)) / Nx, ?_, rfl⟩
  positivity

end Qatlib.Papers.ViscositySol25.MainResults.OptimizationReadout
