/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProdFormSpec21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 1 (eigenstate as initial state) — paper-layer Lean

Source: *Spectral Analysis of Product Formulas for Quantum Simulation*,
arXiv:2102.12655v2, **Corollary 1**, p.3, Eq (16)–(17); proof in Appendix C
(p.10–11), building on Lemma 1 (p.3, Eq (13)) and Lemma 2 (p.3, Eq (14)–(15)).

Paper statement.  For any `H` and any eigenstate `|ψk⟩` separated from the rest of
the spectrum by a gap `lam`, the 1st-order product formula satisfies

  `T(δt)^L |ψk⟩ = √(1−f) e^{iθ} U(t)|ψk⟩ + √f |ψk⊥⟩`,

with fidelity error and phase error

  `|θ| = O(L h δt²)`  (Eq 16),      `f = min{ O(h²δt²/lam²), O(L²h²δt⁴) }`  (Eq 17),

where `h` is Lemma 2's Magnus constant.

Appendix C derives this in two steps:
* the eigenvector-overlap defect `ε = 1 − ‖⟨ψk|ψ̃k⟩‖² ≤ (hδt/lam)²` (Lemma 1 at
  `s = 0` combined with Lemma 2's `‖H̃'‖ = O(h)`), giving `f ≤ 4ε`;
* the phase defect `|θ| ≤ |Ẽk − Ek|·t + O(ε)` with `|Ẽk − Ek| ≤ ‖H̃ − H‖ = O(hδt)`
  (Weyl's inequality, Eq (11), plus Lemma 2), giving `|θ| = O(L h δt²)`.

The theorem below is the paper's **combination step**: it takes the Appendix-C
defects and the Lemma-1 / Lemma-2 inputs as hypotheses (exactly as the paper's
"Combine with Lemma 2") and derives the stated `min`-form.  It is a faithful
*bridging* theorem: the deep analytic estimates of Lemma 1 / Lemma 2 are the
residual, since neither has a Lean formalisation in the library.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ProdFormSpec21.MainResults

open Qatlib.Foundations.PureStateMath
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- **Corollary 1, Eq (16)–(17) — combination step.**  Write `ε` for the
eigenvector-overlap defect `1 − ‖⟨ψk|ψ̃k⟩‖²`, `ΔE = |Ẽk − Ek|` for the effective
energy shift, and `f`, `θ` for the fidelity and phase defects.  Given

* `ε ≤ (h·δt/lam)²`  — Lemma 1 (Eq (13)) evaluated at `s = 0` with Lemma 2's `‖H̃'‖`;
* `ΔE ≤ h·δt`       — Weyl + Lemma 2 (Eq (11), Eq (14));
* `f ≤ 4ε`          — Appendix C, from `1−f = ‖1−ε+η‖²`, `‖η‖ ≤ ε`;
* `f ≤ (L h δt²)²`  — Appendix A, Eq (7), with the general `Δ = O(Lhδt²)`;
* `|θ| ≤ ΔE·t + 2π ε` — Appendix C phase-defect bound, `t = L·δt`;

the conclusions of Corollary 1 hold:
`f ≤ 4(hδt/lam)²`, `f ≤ (L h δt²)²` (the two branches of the `min` in Eq (17)),
and `|θ| ≤ L h δt² + 2π (hδt/lam)² = O(L h δt²)` (Eq (16)). -/
theorem corollary1_eigenstate
    (h δt lam θ ΔE f ε : ℝ) (L : ℕ) (t : ℝ)
    (hh : 0 ≤ h) (hδt : 0 ≤ δt) (hlam : 0 < lam) (ht : t = (L : ℝ) * δt)
    (hε_lem1 : ε ≤ (h * δt / lam) ^ 2)
    (hΔE : ΔE ≤ h * δt)
    (hf : f ≤ 4 * ε)
    (hf2 : f ≤ ((L : ℝ) * h * δt ^ 2) ^ 2)
    (hθ : |θ| ≤ ΔE * t + 2 * Real.pi * ε) :
    f ≤ 4 * (h * δt / lam) ^ 2 ∧
      f ≤ ((L : ℝ) * h * δt ^ 2) ^ 2 ∧
      |θ| ≤ (L : ℝ) * h * δt ^ 2 + 2 * Real.pi * (h * δt / lam) ^ 2 := by
  refine ⟨?_, hf2, ?_⟩
  · have hsq : (0 : ℝ) ≤ (h * δt / lam) ^ 2 := sq_nonneg _
    nlinarith [hε_lem1, hf, hsq]
  · have ht_nonneg : 0 ≤ t := by rw [ht]; positivity
    have h1 : ΔE * t ≤ h * δt * t := mul_le_mul_of_nonneg_right hΔE ht_nonneg
    have h2 : h * δt * t = (L : ℝ) * h * δt ^ 2 := by rw [ht]; ring
    have h3 : 2 * Real.pi * ε ≤ 2 * Real.pi * (h * δt / lam) ^ 2 := by
      have hp : (0 : ℝ) ≤ 2 * Real.pi := by positivity
      exact mul_le_mul_of_nonneg_left hε_lem1 hp
    linarith [hθ, h1, h2, h3]

/-- **Corollary 1 — the vector decomposition.**  The Appendix-C polar decomposition
`T(δt)^L|ψk⟩ = √(1−f) e^{iθ} U(t)|ψk⟩ + √f |ψk⊥⟩` with `|ψk⊥⟩` orthogonal to
`U(t)|ψk⟩`.  Concretely, if the overlap amplitude is `a = ⟨Uψk | Tψk⟩` with
`‖a‖² = 1 − f` and `arg a = θ`, then `Tψk = a·Uψk + w` where `w ⟂ Uψk` and
`‖w‖² = f` (for normalized `Uψk`, `Tψk`).

This is the elementary Gram–Schmidt content of the displayed equation; the
non-trivial numerical content is the bound theorem above. -/
theorem corollary1_decomposition
    (Uψ Tψ w : QState I) (f θ : ℝ)
    (hU : Normalized Uψ) (hT : Normalized Tψ)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (horth : Inner Uψ w = 0)
    (hdecomp : Tψ = (Real.sqrt (1 - f) : ℂ) • ((Complex.exp (Complex.I * θ)) • Uψ)
        + (Real.sqrt f : ℂ) • w) :
    Inner Uψ Tψ = (Real.sqrt (1 - f) : ℂ) * Complex.exp (Complex.I * θ) := by
  -- `⟨Uψ|Tψ⟩ = √(1−f) e^{iθ} ⟨Uψ|Uψ⟩ + √f ⟨Uψ|w⟩ = √(1−f) e^{iθ}`.
  have hnorm : Inner Uψ Uψ = 1 := (normalized_iff_inner_self Uψ).mp hU
  rw [hdecomp]
  simp only [Inner_add_right, Inner_smul_right, horth, hnorm, mul_one, mul_zero, add_zero]

end Qatlib.Papers.ProdFormSpec21.MainResults
