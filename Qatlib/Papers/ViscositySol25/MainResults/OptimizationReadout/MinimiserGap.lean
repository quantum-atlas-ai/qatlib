/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# ViscositySol25 — Lemma 19: minimiser gap under strong convexity + Lipschitz

Paper: arXiv:2512.07919 (fixed version), "Quantum algorithms for viscosity solutions
to nonlinear Hamilton-Jacobi equations based on an entropy penalisation method",
Lemma 19, Eq. (73)-(74), p.21.

The paper proves (74): if `Sν` is `μ`-strongly convex at time `t` and approximates the
viscosity solution `S` within `ε^2` in value (Lemma 3 with `ν = O(ε^2/d^2)`), and `f`
is `K`-Lipschitz, then the minimisers `x*` of `S` and `x*ν` of `Sν` satisfy
`‖x* − x*ν‖ ≤ 2ε/√μ` and consequently `|f x* − f x*ν| ≤ 2Kε/√μ`.

We work in an abstract real inner-product space `E`; the torus/`ℝ^d` instance is the
paper's setting.  This is a genuine analytic inequality and we prove it here in full.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace

namespace Qatlib.Papers.ViscositySol25.MainResults.OptimizationReadout

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Lemma 19, distance form (Eq. (74), p.21, claim `c010`).**

Let `S` be the viscosity solution with a global minimiser `m = x*`, and `Sν` a
`μ`-strongly convex regularisation with gradient `g` and minimiser `mν = x*ν`
(`g mν = 0`).  If `Sν` approximates `S` within `ε^2` in value, `|Sν y − S y| ≤ ε^2`,
then `‖m − mν‖ ≤ 2ε/√μ`.

The proof is exactly the paper's chain: strong convexity gives
`Sν m ≥ Sν mν + (μ/2)‖m − mν‖²`; the value error plus `S m ≤ S mν` gives
`Sν m − Sν mν ≤ 2ε^2`; combining yields `‖m − mν‖² ≤ 4ε^2/μ`. -/
theorem lemma19_minimiser_distance
    (S Sν f : E → ℝ) (g : E → E) (m mν : E) (μ K ε : ℝ)
    (hμ : 0 < μ) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hmin : ∀ y, S m ≤ S y)
    (hminν : ∀ y, Sν mν ≤ Sν y)
    (hstrong : ∀ x y, Sν x + ⟪g x, y - x⟫_ℝ + (μ / 2) * ‖y - x‖ ^ 2 ≤ Sν y)
    (hgrad : g mν = 0)
    (happrox : ∀ y, |Sν y - S y| ≤ ε ^ 2)
    (hlip : ∀ x y, |f x - f y| ≤ K * ‖x - y‖) :
    ‖m - mν‖ ≤ 2 * ε / Real.sqrt μ := by
  -- Step 1: value-error chain `Sν m − Sν mν ≤ 2ε²`.
  have hval : Sν m - Sν mν ≤ 2 * ε ^ 2 := by
    have hm1 : Sν m - S m ≤ ε ^ 2 := by
      have := (abs_le.mp (happrox m)).2; linarith
    have hm2 : S mν - Sν mν ≤ ε ^ 2 := by
      have := (abs_le.mp (happrox mν)).1; linarith
    have hminm : S m ≤ S mν := hmin mν
    linarith
  -- Step 2: strong-convexity quadratic lower bound at `mν`.
  have hquad : Sν mν + (μ / 2) * ‖m - mν‖ ^ 2 ≤ Sν m := by
    have := hstrong mν m
    simp only [hgrad, inner_zero_left, add_zero] at this
    exact this
  -- Step 3: `‖m − mν‖² ≤ 4ε²/μ`.
  have hsq : ‖m - mν‖ ^ 2 ≤ 4 * ε ^ 2 / μ := by
    have h1 : (μ / 2) * ‖m - mν‖ ^ 2 ≤ 2 * ε ^ 2 := by linarith
    rw [le_div_iff₀ hμ]
    nlinarith [h1]
  -- Step 4: take square roots.
  have hb_nonneg : 0 ≤ 2 * ε / Real.sqrt μ := by positivity
  have hsq2 : (2 * ε / Real.sqrt μ) ^ 2 = 4 * ε ^ 2 / μ := by
    rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt hμ)]
    ring
  have hnorm_eq : ‖m - mν‖ = Real.sqrt (‖m - mν‖ ^ 2) := by
    rw [Real.sqrt_sq (norm_nonneg _)]
  calc ‖m - mν‖ = Real.sqrt (‖m - mν‖ ^ 2) := hnorm_eq
    _ ≤ Real.sqrt (4 * ε ^ 2 / μ) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt ((2 * ε / Real.sqrt μ) ^ 2) := by rw [hsq2]
    _ = 2 * ε / Real.sqrt μ := Real.sqrt_sq hb_nonneg

/-- **Lemma 19, function-value form (Eq. (73), p.21, claim `c010`).**

With the same hypotheses as `lemma19_minimiser_distance`, an `K`-Lipschitz `f`
satisfies `|f x* − f x*ν| ≤ 2Kε/√μ`. -/
theorem lemma19_lipschitz_value_gap
    (S Sν f : E → ℝ) (g : E → E) (m mν : E) (μ K ε : ℝ)
    (hμ : 0 < μ) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hmin : ∀ y, S m ≤ S y)
    (hminν : ∀ y, Sν mν ≤ Sν y)
    (hstrong : ∀ x y, Sν x + ⟪g x, y - x⟫_ℝ + (μ / 2) * ‖y - x‖ ^ 2 ≤ Sν y)
    (hgrad : g mν = 0)
    (happrox : ∀ y, |Sν y - S y| ≤ ε ^ 2)
    (hlip : ∀ x y, |f x - f y| ≤ K * ‖x - y‖) :
    |f m - f mν| ≤ 2 * K * ε / Real.sqrt μ := by
  have hdist : ‖m - mν‖ ≤ 2 * ε / Real.sqrt μ :=
    lemma19_minimiser_distance S Sν f g m mν μ K ε hμ hε hK
      hmin hminν hstrong hgrad happrox hlip
  have h1 : |f m - f mν| ≤ K * ‖m - mν‖ := hlip m mν
  calc |f m - f mν| ≤ K * ‖m - mν‖ := h1
    _ ≤ K * (2 * ε / Real.sqrt μ) := by
          exact mul_le_mul_of_nonneg_left hdist hK
    _ = 2 * K * ε / Real.sqrt μ := by ring

end Qatlib.Papers.ViscositySol25.MainResults.OptimizationReadout
