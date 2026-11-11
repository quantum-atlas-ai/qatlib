/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommGibbsSamp14.MainResults.Framework.ObservableCalculus

set_option backward.isDefEq.respectTransparency false

/-!
# Commuting Gibbs samplers — projection calculus and the variance inequality

Fixed source: arXiv:1409.3435v3, Proposition 20, p. 20, Eqs. (61)–(65), and the identity
displayed as Eq. (63).

This file proves, at the abstract `L²(ρ)` level, the two Hilbert-space facts used by the
paper's proof of Proposition 20:

* a self-adjoint idempotent map is an orthogonal projection and is a contraction on the
  difference `f - P f` (`norm_sub_projection_le`);
* the algebraic identity Eq. (63) `‖u − a − b‖² = ‖u − a‖² + ‖u − b‖² − ‖u‖² + 2⟨a,b⟩`.

Proposition 20 itself is `prop20_variance_inequality` below: a complete tactic proof.
-/

set_option autoImplicit false

namespace Qatlib.Papers.CommGibbsSamp14.MainResults.Framework

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## Orthogonal projections -/

/-- A self-adjoint idempotent map is an orthogonal projection:
`P f ⊥ f - P f`. -/
lemma inner_projection_eq_zero (P : V → V)
    (hself : ∀ f g : V, ⟪P f, g⟫_ℝ = ⟪f, P g⟫_ℝ)
    (hidem : ∀ f : V, P (P f) = P f) (f : V) :
    ⟪P f, f - P f⟫_ℝ = 0 := by
  have h1 : ⟪P f, P f⟫_ℝ = ⟪P f, f⟫_ℝ := by
    rw [hself f (P f), hidem f, hself f f]
  rw [inner_sub_right, h1, sub_self]

/-- An orthogonal projection is a contraction on the difference: `‖f − P f‖ ≤ ‖f‖`.
This is the "`(id − E_{A∪B})` is contractive" step used in the proof of Proposition 20
(paper, p. 20, between Eqs. (63) and (64)). -/
lemma norm_sub_projection_le (P : V → V)
    (hself : ∀ f g : V, ⟪P f, g⟫_ℝ = ⟪f, P g⟫_ℝ)
    (hidem : ∀ f : V, P (P f) = P f) (f : V) :
    ‖f - P f‖ ≤ ‖f‖ := by
  have horth : ⟪P f, f - P f⟫_ℝ = 0 := inner_projection_eq_zero P hself hidem f
  have hpy : ‖f‖ * ‖f‖ = ‖P f‖ * ‖P f‖ + ‖f - P f‖ * ‖f - P f‖ := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    have hsum : P f + (f - P f) = f := by abel
    rwa [hsum] at h
  nlinarith [norm_nonneg (f - P f), norm_nonneg f, norm_nonneg (P f)]

/-! ## The identity of Eq. (63) -/

/-- The algebraic identity used in the proof of Proposition 20 (paper, Eq. (63), p. 20):
`‖u − a − b‖² = ‖u − a‖² + ‖u − b‖² − ‖u‖² + 2⟨a, b⟩`. -/
lemma sq_norm_sub_sub (u a b : V) :
    ‖u - a - b‖ ^ 2 = ‖u - a‖ ^ 2 + ‖u - b‖ ^ 2 - ‖u‖ ^ 2 + 2 * ⟪a, b⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right]
  rw [real_inner_comm b a]
  ring

/-! ## Proposition 20 -/

/-- **Proposition 20** (arXiv:1409.3435v3, p. 20, Eqs. (61)–(62)).

Let `ρ ∈ S_Λ^+`, let `A, B ⊆ Λ` overlap, and let `E` be a conditional expectation of the
paper.  Suppose that for every observable `f`

`Cov_{A∪B}(E_A f, E_B f) ≤ ε Var_{A∪B}(f)`  (Eq. (61)),

where `Cov_{A∪B}(g,h) = ⟨g − E_{A∪B} g, h − E_{A∪B} h⟩_ρ` and `Var_{A∪B}(g)` is its
diagonal.  Then

`Var_{A∪B}(f) ≤ (1 − 2ε)⁻¹ (Var_A(f) + Var_B(f))`  (Eq. (62)).

The paper's proof (Eq. (63)) only uses `E_{A∪B} ∘ E_A = E_{A∪B} = E_{A∪B} ∘ E_B`
(the pair `(E, L)` has the same kernel, so the conditional expectations are nested); it
does not use locality or the Gibbs form of `ρ` (paper's remark after Eq. (65)).  These
absorption identities are exactly the hypotheses below. -/
theorem prop20_variance_inequality
    (EA EB EAB : V → V) (eps : ℝ)
    (hA_abs : ∀ f : V, EAB (EA f) = EAB f)
    (hB_abs : ∀ f : V, EAB (EB f) = EAB f)
    (hBound : ∀ f : V, condCov EAB (EA f) (EB f) ≤ eps * condVar EAB f)
    (heps1 : 2 * eps < 1) :
    ∀ f : V, condVar EAB f ≤ (1 - 2 * eps)⁻¹ * (condVar EA f + condVar EB f) := by
  intro f
  set u : V := f - EAB f with hu
  set a : V := EA f - EAB f with ha
  set b : V := EB f - EAB f with hb
  have hua : u - a = f - EA f := by rw [hu, ha]; abel
  have hub : u - b = f - EB f := by rw [hu, hb]; abel
  have ha' : a = EA f - EAB (EA f) := by rw [ha, hA_abs f]
  have hb' : b = EB f - EAB (EB f) := by rw [hb, hB_abs f]
  have hcov : ⟪a, b⟫_ℝ = condCov EAB (EA f) (EB f) := by
    rw [ha', hb']; simp only [condCov]
  have hVA : ‖u - a‖ ^ 2 = condVar EA f := by rw [condVar_eq_norm_sq, hua]
  have hVB : ‖u - b‖ ^ 2 = condVar EB f := by rw [condVar_eq_norm_sq, hub]
  have hVAB : ‖u‖ ^ 2 = condVar EAB f := by rw [condVar_eq_norm_sq, hu]
  -- The squared norm is non-negative (Eq. (63) states `0 ≤ ‖…‖²`).
  have h0 : (0 : ℝ) ≤ ⟪u - a - b, u - a - b⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]; positivity
  have h0n : (0 : ℝ) ≤ ‖u - a - b‖ ^ 2 := by
    have h := h0
    rwa [real_inner_self_eq_norm_sq] at h
  -- Expand with the identity of Eq. (63).
  have h1 : (0 : ℝ) ≤ ‖u - a‖ ^ 2 + ‖u - b‖ ^ 2 - ‖u‖ ^ 2 + 2 * ⟪a, b⟫_ℝ := by
    rwa [sq_norm_sub_sub] at h0n
  have h2 : (0 : ℝ) ≤ condVar EA f + condVar EB f - condVar EAB f
      + 2 * condCov EAB (EA f) (EB f) := by
    rw [hVA, hVB, hVAB, hcov] at h1
    exact h1
  -- Eq. (64): apply the covariance bound (61).
  have h3 : condVar EAB f ≤ condVar EA f + condVar EB f
      + 2 * (eps * condVar EAB f) := by
    nlinarith [h2, hBound f]
  have h4 : (1 - 2 * eps) * condVar EAB f ≤ condVar EA f + condVar EB f := by
    nlinarith [h3]
  have hpos : 0 < 1 - 2 * eps := by linarith
  have hne : (1 - 2 * eps) ≠ 0 := ne_of_gt hpos
  calc condVar EAB f
      = (1 - 2 * eps)⁻¹ * ((1 - 2 * eps) * condVar EAB f) := by
        rw [inv_mul_cancel_left₀ hne]
    _ ≤ (1 - 2 * eps)⁻¹ * (condVar EA f + condVar EB f) :=
        mul_le_mul_of_nonneg_left h4 (inv_nonneg.mpr hpos.le)

end Qatlib.Papers.CommGibbsSamp14.MainResults.Framework
