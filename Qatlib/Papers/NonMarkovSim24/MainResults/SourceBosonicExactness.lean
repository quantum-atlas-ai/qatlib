/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonMarkovSim24.MainResults.DQMEModel

set_option backward.isDefEq.respectTransparency false

/-!
# c001 — Bosonic DQME-SQ: exactness, HEOM equivalence and universality

Paper: arXiv:2401.17255v4, Sec. II A-C, Eq. (2), (4), (5), (8), (11), (12).

Claim (c001): the bosonic DQME-SQ of Eq. (4) yields exact non-Markovian
dynamics for any Gaussian environment whose hybridization correlation function
decomposes into a sum of exponentials.  Sec. II B validates this by a formal
equivalence to the bosonic HEOM, and Sec. II C extends the same equation to
several degrees of freedom coupled to more than one environment (Eq. (12)).

The two formal cores of that argument are formalized here:

* `dissipaton_autocorrelation_sum` — Eq. (2) with `c_k(t) = η_k e^{-γ_k t}`:
  the delta-correlated dissipaton two-point function sums to the full
  correlation function `C(t) = Σ_k η_k e^{-γ_k t}` (Eq. (5)).
* `bosonic_dqme_sq_exact` — the second-quantized equation Eq. (4)/(12) is
  exactly the EDMD/HEOM component equation Eq. (8), for an arbitrary finite
  mode set `ι` (so multiple environments and multiple system DOF are covered
  by taking `ι = environment × DOF`).

The mode set is a general `Fintype ι`, which is precisely the universality
asserted in Sec. II C; the single-environment equation Eq. (4) is the case
`ι = Unit`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.NonMarkovSim24.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exponential decomposition of the environment hybridization correlation
function, Eq. (5) of the paper: `C(t) = Σ_k η_k e^{-γ_k t}`. -/
def correlExp (η γ : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ k, η k * Complex.exp (-(γ k) * (t : ℂ))

/-- **Eq. (2) of the paper.**  Dissipatons are delta-correlated,
`⟨f̂_k(t) f̂_{k'}(0)⟩_D = δ_{kk'} c_k(t)` with `c_k(t) = η_k e^{-γ_k t}`;
summing over `k, k'` therefore reproduces the full environment correlation
function `C(t) = Σ_k η_k e^{-γ_k t}` of Eq. (5).  This is the dissipaton
decomposition (DD) protocol (1)-(2) preserving `C(t)` exactly. -/
theorem dissipaton_autocorrelation_sum (η γ : ι → ℂ) (t : ℝ) :
    (∑ k, ∑ k', if k = k' then η k * Complex.exp (-(γ k) * (t : ℂ)) else 0)
      = correlExp η γ t := by
  unfold correlExp
  refine Finset.sum_congr rfl ?_
  intro k _
  simp [Finset.sum_ite_eq]

/-- **c001: bosonic DQME-SQ exactness and universality (Eq. (4), (8), (12)).**

For any finite set `ι` of dissipaton modes (obtained from exponential
decompositions of one or several environment correlation functions), and any
coefficients `γ, ζ, ξ`, the second-quantized generator `dqmeSqRHS` of
Eq. (4)/(12) coincides, coefficient by coefficient on the dissipaton occupation
basis, with the EDMD/HEOM right-hand side `heomRHS` of Eq. (8).  Consequently
the DQME-SQ inherits the exactness of the HEOM, and the construction applies
without change to multiple environments and degrees of freedom.

The physical hypotheses of the claim (Gaussian environment, exponential
decomposition of `C(t)`, validity of the HEOM truncation) enter through the
choice of `ι` and of the coefficients `γ, ζ, ξ`; they are not additional Lean
assumptions beyond what is written here.  The separate correlation-function
content of Eq. (2) is `dissipaton_autocorrelation_sum`. -/
theorem bosonic_dqme_sq_exact {d : ℕ} (H : Op d) (Q : ι → Op d)
    (γ ζ ξ η : ι → ℂ) :
    (∀ (ρ : (ι → ℕ) → Op d) (n : ι → ℕ),
        dqmeSqRHS H Q γ ζ ξ ρ n = heomRHS H Q γ ζ ξ ρ n)
      ∧ (∀ (t : ℝ), (∑ k, ∑ k', if k = k' then η k * Complex.exp (-(γ k) * (t : ℂ)) else 0)
          = correlExp η γ t) := by
  exact ⟨fun ρ n => ladder_expansion H Q γ ζ ξ ρ n,
    fun t => dissipaton_autocorrelation_sum η γ t⟩

end Qatlib.Papers.NonMarkovSim24.MainResults
