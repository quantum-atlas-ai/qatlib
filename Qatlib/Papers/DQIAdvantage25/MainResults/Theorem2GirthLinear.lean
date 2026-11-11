/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DQIAdvantage25.MainResults.Model.CutGirthModel
import Qatlib.Papers.DQIAdvantage25.MainResults.Lemma4Eigenvalue

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 2: constant DQI excess forces linear girth (paper p.9)

Source: Ojas Parekh, *No Quantum Advantage in Decoded Quantum Interferometry for MaxCut*,
arXiv:2509.19966v2 (2025-09-30), Theorem 2, Section 2.3, p.9.

> **Theorem 2.** If the expected number of edges cut by DQI in a graph `G ∈ 𝒢` is `(1/2 + ε)m` for
> some constant `ε > 0`, the girth `g` must be linear in `m`.

**Paper proof** (p.9). If the girth is not linear then `g = o(m)` (using that `lim g/m` exists),
so `l ≤ (g-1)/2 = o(m)` and Lemma 4 gives expected cut `(1/2)(1+o(1))m`, contradicting the
constant excess `ε`.

**Formalisation.** In sequence form, the hypothesis is that the DQI expected cut
`(m + λmax(A^{(m,l(m))}))/2` (Lemma 3) exceeds `(1/2 + ε)m` eventually, with the algorithm's
parameter `l(m) = ⌊(g(m)-1)/2⌋`; the conclusion is `GirthLinear g`. The quantitative core is the
elementary Gershgorin bound `λmax(A^{(m,l)}) ≤ 2√(m·l)` (Lemma 4, `maxEigenvalue_dijMatrix_le`,
proved), which already yields the contrapositive *pointwise*: expected cut `≥ (1/2+ε)m` forces
`ε² m ≤ l ≤ g/2`, hence `(ε²/4) m ≤ g`. This gives the theorem without the `o(m)` bookkeeping and
in fact with a stronger, uniform constant.
-/

open scoped BigOperators
open Filter Matrix
open Qatlib.Papers.DQIAdvantage25.MainResults.Model

namespace Qatlib.Papers.DQIAdvantage25.MainResults

namespace Theorem2

/-- **Theorem 2** (Parekh, arXiv:2509.19966v2, Theorem 2, p.9), in sequence form.

If a family of graphs indexed by the number of edges `m` has DQI expected cut at least
`(1/2 + ε) m` for a constant `ε > 0` (with the DQI parameter `l(m) = ⌊(g(m)-1)/2⌋`), then the
girth is linear in `m`: `GirthLinear g`.

The hypotheses `hg1` (`g ≥ 1` eventually, excluding forest inputs, for which the Mathlib girth is
the junk value `0`) and `hlm` (`l(m) ≤ m`, automatic for graphs with at most `m+1` vertices) are
bookkeeping conditions on the asymptotic family; the mathematical content is the Gershgorin bound
of Lemma 4. The proof is complete. -/
theorem theorem2_girth_linear_of_constant_excess
    (girth : ℕ → ℕ)
    (hg1 : ∀ᶠ m : ℕ in atTop, 1 ≤ girth m)
    (hlm : ∀ᶠ m : ℕ in atTop, (girth m - 1) / 2 ≤ m)
    (hexcess : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ m : ℕ in atTop,
      (1 / 2 + ε) * (m : ℝ) ≤ dqiExpectedCut m ((girth m - 1) / 2)) :
    GirthLinear girth := by
  obtain ⟨ε, hε, hexc⟩ := hexcess
  refine ⟨ε ^ 2 / 4, by positivity, ?_⟩
  filter_upwards [hexc, hg1, hlm, eventually_ge_atTop (1 : ℕ)] with m hmex hg1m hlm_m hm1
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  -- The constant excess forces `λmax(A^{(m,l)}) ≥ 2 ε m`.
  have hlam : 2 * ε * (m : ℝ) ≤ maxEigenvalue (dijMatrix m ((girth m - 1) / 2)) := by
    have h := hmex
    unfold dqiExpectedCut at h
    nlinarith
  -- Gershgorin bound from Lemma 4.
  have hbound := Lemma4.maxEigenvalue_dijMatrix_le m ((girth m - 1) / 2) hlm_m
  -- Hence `ε m ≤ √(m · l)`.
  have hsqrt_le : ε * (m : ℝ)
      ≤ Real.sqrt ((m : ℝ) * (((girth m - 1) / 2 : ℕ) : ℝ)) := by
    nlinarith
  -- Squaring and dividing by `m` gives `ε² m ≤ l`.
  have hsq : (ε * (m : ℝ)) ^ 2 ≤ (m : ℝ) * (((girth m - 1) / 2 : ℕ) : ℝ) := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ε * (m : ℝ)) hsqrt_le 2
    rw [Real.sq_sqrt (by positivity)] at h
    exact h
  have hdiv : ε ^ 2 * (m : ℝ) ≤ (((girth m - 1) / 2 : ℕ) : ℝ) := by
    apply le_of_mul_le_mul_left _ hmpos
    nlinarith [hsq]
  -- And `2 l + 1 ≤ g`, so `l ≤ g/2`.
  have hnat : 2 * ((girth m - 1) / 2) + 1 ≤ girth m := by
    have hdiv : (girth m - 1) / 2 * 2 ≤ girth m - 1 := Nat.div_mul_le_self _ _
    omega
  have hreal : 2 * (((girth m - 1) / 2 : ℕ) : ℝ) + 1 ≤ (girth m : ℝ) := by
    exact_mod_cast hnat
  show ε ^ 2 / 4 * (m : ℝ) ≤ (girth m : ℝ)
  nlinarith

end Theorem2

end Qatlib.Papers.DQIAdvantage25.MainResults
