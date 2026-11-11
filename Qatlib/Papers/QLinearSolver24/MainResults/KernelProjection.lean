/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearSolver24.MainResults.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# QLinearSolver24 — Lemma 2: KP refines a QLSS solution (claim c002)

Fixed source: arXiv:2406.12086, Lemma 2, p. 20–21, Eqs. (57)–(58).

The lemma post-selects the output `ρ̃` of a QLSS on the success of kernel
projection (KP) with parameters `(κ, η)`, and bounds the overlap with the
exact solution `x` and the trace distance to `|x⟩⟨x|`.

The algorithm is not modelled here; what is formalised is the scalar
accounting that the paper's proof carries out.  Writing `p` for the KP
success probability and `μ²` for the mass that `ρ̃` puts on the orthogonal
complement of `x` (so `⟨x|ρ̃|x⟩ = 1 - μ²` by hypothesis, p. 20), KP's
filter of Lemma 1 with accuracy `η` sends that mass to weight `μ²η²`
(p. 21, the paragraph deriving `δ₁′ = K + 1 ∈ [0, 4η/(1+η)]`), so

* `p = 1 - μ² + μ²η² = kpSuccessProb μ η` (upper bound; the paper only
  claims `p ≥ 1 - μ²`, which is recorded as a hypothesis), and
* the post-selected overlap is `⟨x|ρ_out|x⟩ = (1 - μ²)/p`.

The two displayed bounds (57), (58) then follow by monotonicity of
`u ↦ (1-μ²)/u` and of `√` on the positive reals.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearSolver24.MainResults.KernelProjection

open Qatlib.Papers.QLinearSolver24.MainResults

/-- KP success probability model, `1 - μ² + μ²η²`, of Lemma 2 (p. 21):
`ρ̃` puts mass `1 - μ²` on `x` (success) and mass `μ²` off `x`, of which
the filter of Lemma 1 retains at most a fraction `η²`. -/
def kpSuccessProb (μ η : ℝ) : ℝ := 1 - μ ^ 2 + μ ^ 2 * η ^ 2

/-- The post-selected overlap `⟨x|ρ_out|x⟩ = (1-μ²)/p` (Lemma 2, p. 21). -/
def lemma2Overlap (μ p : ℝ) : ℝ := (1 - μ ^ 2) / p

/-- The trace-distance bound `μη/√p` of Eq. (58), p. 21. -/
def lemma2TraceDistance (μ η p : ℝ) : ℝ := μ * η / Real.sqrt p

/-- **Lemma 2, Eqs. (57)–(58)** (p. 21).  Let `0 < μ < 1`, `0 < η ≤ 1`, and
let `p` be an upper bound on the KP success probability with
`1 - μ² ≤ p ≤ 1 - μ² + μ²η²` (the lower bound is KP's success claim of the
lemma, the upper bound is the filter accounting).  Then the post-selected
overlap satisfies

`⟨x|ρ_out|x⟩ ≥ 1 - μ²η²/(1-μ²+μ²η²) ≥ 1 - μ²η²/(1-μ²)`,

and the trace distance satisfies `μη/√(1-μ²+μ²η²) ≤ μη/√(1-μ²)`. -/
theorem lemma2_kp_refinement (μ η p : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hη0 : 0 < η) (_hη1 : η ≤ 1) (hp1 : 1 - μ ^ 2 ≤ p)
    (hp2 : p ≤ kpSuccessProb μ η) (hp0 : 0 < p) :
    (1 - μ ^ 2 * η ^ 2 / (1 - μ ^ 2)
        ≤ 1 - μ ^ 2 * η ^ 2 / kpSuccessProb μ η) ∧
      (1 - μ ^ 2 * η ^ 2 / kpSuccessProb μ η ≤ lemma2Overlap μ p) ∧
      (lemma2TraceDistance μ η (kpSuccessProb μ η)
        ≤ lemma2TraceDistance μ η (1 - μ ^ 2)) := by
  have h1μ : (0 : ℝ) < 1 - μ ^ 2 := by nlinarith
  have hq : (0 : ℝ) < kpSuccessProb μ η := by
    unfold kpSuccessProb
    nlinarith [sq_nonneg μ, sq_nonneg η, sq_nonneg (μ * η)]
  have hq1 : 1 - μ ^ 2 ≤ kpSuccessProb μ η := by
    unfold kpSuccessProb
    nlinarith [sq_nonneg (μ * η)]
  have hnum : (0 : ℝ) ≤ μ ^ 2 * η ^ 2 := by positivity
  -- first inequality: the two lower bounds of (57)
  have hfirst : μ ^ 2 * η ^ 2 / kpSuccessProb μ η
      ≤ μ ^ 2 * η ^ 2 / (1 - μ ^ 2) := by
    rw [div_le_div_iff₀ hq h1μ]
    nlinarith
  constructor
  · linarith
  constructor
  · -- `1 - μ²η²/q = (1-μ²)/q ≤ (1-μ²)/p`
    have hsplit : 1 - μ ^ 2 * η ^ 2 / kpSuccessProb μ η
        = (1 - μ ^ 2) / kpSuccessProb μ η := by
      unfold kpSuccessProb
      field_simp
      ring
    rw [hsplit, lemma2Overlap]
    exact div_le_div_of_nonneg_left (le_of_lt h1μ) hp0 hp2
  · -- `μη/√q ≤ μη/√(1-μ²)` since `√(1-μ²) ≤ √q`
    have hsq : Real.sqrt (1 - μ ^ 2) ≤ Real.sqrt (kpSuccessProb μ η) :=
      Real.sqrt_le_sqrt hq1
    have hs1 : (0 : ℝ) < Real.sqrt (1 - μ ^ 2) := Real.sqrt_pos.mpr h1μ
    have hs2 : (0 : ℝ) < Real.sqrt (kpSuccessProb μ η) := Real.sqrt_pos.mpr hq
    have hinv : 1 / Real.sqrt (kpSuccessProb μ η) ≤ 1 / Real.sqrt (1 - μ ^ 2) :=
      one_div_le_one_div_of_le hs1 hsq
    have hμη : (0 : ℝ) ≤ μ * η := by positivity
    have := mul_le_mul_of_nonneg_left hinv hμη
    unfold lemma2TraceDistance
    simpa [div_eq_mul_inv] using this

end Qatlib.Papers.QLinearSolver24.MainResults.KernelProjection
