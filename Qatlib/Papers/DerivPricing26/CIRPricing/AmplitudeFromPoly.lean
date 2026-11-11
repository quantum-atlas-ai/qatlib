/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# CIRPricing.AmplitudeFromPoly

Source: Herman, Sun, Liu, Pistoia, Che, Otter, Chakrabarti, Harrow,
*Quantum Speedups for Derivative Pricing Beyond Black-Scholes*,
fixed version arXiv:2602.03725v1, Appendix F, Lemma F.1
(v1 text, line 6777 of the extracted source):

> Let `h : X → ℝ`, `p : X → ℝ+` be two continuous functions over a compact set
> `X ⊂ ℝ`, and `εpoly := sqrt ‖h - p‖∞`. For `εpoly < 1`, we have
> `‖p - h²‖∞ ≤ 3 εpoly`.

The printed proof is the chain

`‖p - h²‖∞ ≤ ‖√p - h‖∞ ‖√p + h‖∞ ≤ ‖√p - h‖∞ (2‖√p‖∞ + ‖√p - h‖∞) ≤ 3 εpoly`,

which uses `‖√p‖∞ ≤ 1` for a probability density. The chain bounds
`‖p - h²‖∞` by `‖√p - h‖∞`, so that is the error quantity the module uses:
`lemmaF1_uniform` proves the displayed implication for an arbitrary index set
`X` with the uniform hypothesis `|√p - h| ≤ ε` and `p ≤ 1`.

**Discrepancy with the printed hypothesis.** Read literally with
`εpoly = sqrt ‖h - p‖∞`, the statement is false: on a one-point `X` with
`p ≡ h ≡ 1/2` one has `εpoly = 0` while `‖p - h²‖∞ = 1/4`
(`lemmaF1_printed_hypothesis_false`). The two error quantities are related by
`|h - p| ≤ ε + 1/4` (`lemmaF1_printed_epsPoly_bound`), so a printed `εpoly`
corresponds to `ε = ‖√p - h‖∞` only through `εpoly ≤ sqrt (ε + 1/4)`; the
`3 εpoly` bound therefore does not follow from the printed hypothesis at the
scale the paper uses.

Boundary: only the numerical conversion from a uniform `√p`-approximation error
to a `p`-versus-`h²` error is covered. Existence of the approximating
polynomial, its degree, and the state-preparation gate count `O(log N · d_δ)`
are *not* formalised here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DerivPricing26.CIRPricing.AmplitudeFromPoly

/-- Lemma F.1, the chain displayed in the paper's proof: on any index set `X`,
if `p` is a probability (`0 ≤ p ≤ 1`), `h` is a uniform `ε`-approximation of
`√p`, and `ε < 1`, then `|p - h²| ≤ 3 ε` uniformly. This is the statement the
printed proof actually establishes, with `ε = ‖√p - h‖∞`. -/
theorem lemmaF1_uniform {X : Type*} (p h : X → ℝ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (hclose : ∀ x, |Real.sqrt (p x) - h x| ≤ ε) :
    ∀ x, |p x - (h x) ^ 2| ≤ 3 * ε := by
  intro x
  have hsq : Real.sqrt (p x) ^ 2 = p x := Real.sq_sqrt (hp0 x)
  have hsqrt1 : |Real.sqrt (p x)| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_le_left (by norm_num)).mpr (by nlinarith [hp1 x])
  have hh : |h x| ≤ 1 + ε := by
    have h1 : |h x| ≤ |Real.sqrt (p x)| + |Real.sqrt (p x) - h x| := by
      have hkey : h x = (h x - Real.sqrt (p x)) + Real.sqrt (p x) := by ring
      calc |h x| = |(h x - Real.sqrt (p x)) + Real.sqrt (p x)| := congrArg abs hkey
        _ ≤ |h x - Real.sqrt (p x)| + |Real.sqrt (p x)| := abs_add_le _ _
        _ = |Real.sqrt (p x)| + |Real.sqrt (p x) - h x| := by
            rw [abs_sub_comm (h x) (Real.sqrt (p x))]
            ring
    have h3 := hclose x
    linarith
  have hph : |Real.sqrt (p x) + h x| ≤ ε + 2 := by
    have h1 : |Real.sqrt (p x) + h x| ≤ |Real.sqrt (p x)| + |h x| := abs_add_le _ _
    linarith
  have hfactor : p x - (h x) ^ 2 =
      (Real.sqrt (p x) - h x) * (Real.sqrt (p x) + h x) := by
    have hprod : (Real.sqrt (p x) - h x) * (Real.sqrt (p x) + h x)
        = Real.sqrt (p x) ^ 2 - (h x) ^ 2 := by ring
    rw [hprod, hsq]
  have hprod : |Real.sqrt (p x) - h x| * |Real.sqrt (p x) + h x| ≤ ε * (ε + 2) :=
    mul_le_mul (hclose x) hph (abs_nonneg _) hε0
  have hbound : ε * (ε + 2) ≤ 3 * ε := by nlinarith
  rw [hfactor, abs_mul]
  linarith

/-- Relation between the printed `εpoly = sqrt ‖h - p‖∞` and the error
`ε = ‖√p - h‖∞` of the printed proof: with `p ≤ 1`, `|h - p| ≤ ε + 1/4`. The
`1/4` is the maximum of `√p (1 - √p)`. -/
theorem lemmaF1_printed_epsPoly_bound {X : Type*} (p h : X → ℝ) {ε : ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (hclose : ∀ x, |Real.sqrt (p x) - h x| ≤ ε) (x : X) :
    |h x - p x| ≤ ε + 1 / 4 := by
  have hsq : Real.sqrt (p x) ^ 2 = p x := Real.sq_sqrt (hp0 x)
  have hsqrt0 : 0 ≤ Real.sqrt (p x) := Real.sqrt_nonneg _
  have hsqrt1 : Real.sqrt (p x) ≤ 1 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by nlinarith [hp1 x])
  have hsecond : |Real.sqrt (p x) - p x| ≤ 1 / 4 := by
    have hfac : Real.sqrt (p x) - p x = Real.sqrt (p x) * (1 - Real.sqrt (p x)) := by
      have hprod : Real.sqrt (p x) * (1 - Real.sqrt (p x))
          = Real.sqrt (p x) - Real.sqrt (p x) ^ 2 := by ring
      rw [hprod, hsq]
    rw [hfac, abs_mul, abs_of_nonneg hsqrt0, abs_of_nonneg (by linarith)]
    nlinarith [sq_nonneg (Real.sqrt (p x) - 1 / 2)]
  calc |h x - p x| = |(h x - Real.sqrt (p x)) + (Real.sqrt (p x) - p x)| := by ring_nf
    _ ≤ |h x - Real.sqrt (p x)| + |Real.sqrt (p x) - p x| := abs_add_le _ _
    _ ≤ ε + 1 / 4 := by
        have h1 := hclose x
        rw [abs_sub_comm] at h1
        linarith

/-- The printed hypothesis `εpoly = sqrt ‖h - p‖∞` cannot be read literally:
with `p = h = 1/2` we have `εpoly = 0` but `|p - h²| = 1/4 > 3 εpoly`. This
records the discrepancy between Lemma F.1's printed `εpoly` and the quantity
`‖√p - h‖∞` that its proof actually bounds. -/
theorem lemmaF1_printed_hypothesis_false :
    ∃ p h : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ |h| ≤ 1 ∧
      ¬ (|p - h ^ 2| ≤ 3 * Real.sqrt |h - p|) := by
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [sub_self, abs_zero, Real.sqrt_zero]
  norm_num

end Qatlib.Papers.DerivPricing26.CIRPricing.AmplitudeFromPoly
