/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMAPerfect26.MainResults.SourceLemma33

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3.7: existence of a valid certificate on YES instances

Fixed paper: Grewal–Rudolph, *QMA has perfect completeness*, arXiv:2609.13032v1, Lemma 3.7, p.10.

On a YES instance there is a valid certificate `(z,a,b)` with `a/b = Γ_z > 2`. The integers
are obtained from `2^{hℓ} Γ_z = k ∈ ℤ` (Lemma 3.3): take `z` with `Γ_z > 2`, `a = k`,
`b = 2^{hℓ}`; then `a/b = Γ_z` and `a > 2b`.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QMAPerfect26.MainResults

/-- Lemma 3.7 (p.10): on a YES instance, there exist `z` and integers `a, b` with `b > 0`,
`a/b = Γ_z`, `Γ_z > 2`, and `a > 2b`. -/
theorem lemma37 {m : ℕ} (E : ProofMat m) (h ℓ : ℕ) (hint : IsDyadicMat h E)
    (htrace : (2 : ℝ) ^ m * 2 < (((2 : ℝ) • E) ^ ℓ).trace) :
    ∃ (z : Idx m) (a b : ℤ),
      0 < b ∧ (a : ℝ) / (b : ℝ) = Gamma ((2 : ℝ) • E) ℓ z ∧
        2 < Gamma ((2 : ℝ) • E) ℓ z ∧ 2 * (b : ℝ) < (a : ℝ) := by
  obtain ⟨z, hz⟩ := lemma33_yes_exists E ℓ htrace
  obtain ⟨k, hk⟩ := Gamma_integer E h ℓ z hint
  -- cast the integer denominator `2^{hℓ}` to `ℝ`
  have hb : (((2 : ℤ) ^ (h * ℓ) : ℤ) : ℝ) = (2 : ℝ) ^ (h * ℓ) := by
    push_cast
    norm_num
  -- candidate denominator `b = 2^{hℓ}`, numerator `a = k = 2^{hℓ} Γ_z`
  refine ⟨z, k, (2 : ℤ) ^ (h * ℓ), ?_, ?_, hz, ?_⟩
  · positivity
  · -- `k / 2^{hℓ} = Γ_z`
    rw [hb, div_eq_iff (by positivity), mul_comm]
    exact hk.symm
  · -- `2 · 2^{hℓ} < k = 2^{hℓ} · Γ_z` because `Γ_z > 2`
    rw [hb]
    have hmul : 2 * (2 : ℝ) ^ (h * ℓ) < (2 : ℝ) ^ (h * ℓ) * Gamma ((2 : ℝ) • E) ℓ z := by
      have hstep : (2 : ℝ) ^ (h * ℓ) * 2 < (2 : ℝ) ^ (h * ℓ) * Gamma ((2 : ℝ) • E) ℓ z :=
        mul_lt_mul_of_pos_left hz (by positivity)
      nlinarith [hstep]
    nlinarith [hk, hmul]

end Qatlib.Papers.QMAPerfect26.MainResults
