/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMAPerfect26.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3.3: arithmetic of `Γ_z = ⟨z|A^ℓ|z⟩`

Fixed paper: Grewal–Rudolph, *QMA has perfect completeness*, arXiv:2609.13032v1, Lemma 3.3, p.8.

`A = 2E`, and for every `z ∈ {0,1}^m` the number `Γ_z = ⟨z|A^ℓ|z⟩` satisfies
`0 ≤ Γ_z ≤ 2^ℓ` and `2^{hℓ} Γ_z ∈ ℤ`; on a YES instance some `z` has `Γ_z > 2`.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QMAPerfect26.MainResults

/-- Lemma 3.3, first part (p.8): for `A = 2E` with `E` positive semidefinite,
`0 ≤ Γ_z ≤ 2^ℓ` and `2^{hℓ} Γ_z ∈ ℤ` whenever `2^h E` is an integer matrix.
The bound `‖A v‖ ≤ 2‖v‖` is the operator-norm form of `A ⪯ 2·I` (`0 ≤ E ⪯ I`). -/
theorem lemma33 {m : ℕ} (E : ProofMat m) (h ℓ : ℕ) (z : Idx m)
    (hE : E.PosSemidef)
    (hbound : ∀ v : Idx m → ℝ, ‖((2 : ℝ) • E) *ᵥ v‖ ≤ 2 * ‖v‖)
    (hint : IsDyadicMat h E) :
    0 ≤ Gamma ((2 : ℝ) • E) ℓ z ∧ Gamma ((2 : ℝ) • E) ℓ z ≤ 2 ^ ℓ ∧
      ∃ k : ℤ, (2 : ℝ) ^ (h * ℓ) * Gamma ((2 : ℝ) • E) ℓ z = (k : ℝ) :=
  ⟨Gamma_nonneg _ _ _ (hE.smul (by norm_num)),
   Gamma_le _ _ _ hbound,
   Gamma_integer E h ℓ z hint⟩

/-- Lemma 3.3, `Γ_z` is a `(h+1)ℓ`-bit rational: `Γ_z = k / 2^{hℓ}` with integer `k`,
`0 ≤ k`, and `k ≤ 2^{ℓ} · 2^{hℓ}`. (The bit-count corollary of the integrality and
upper bound above.) -/
theorem lemma33_denominator {m : ℕ} (E : ProofMat m) (h ℓ : ℕ) (z : Idx m)
    (hint : IsDyadicMat h E) (hΓ : 0 ≤ Gamma ((2 : ℝ) • E) ℓ z) :
    ∃ k : ℤ, 0 ≤ k ∧ Gamma ((2 : ℝ) • E) ℓ z = (k : ℝ) / (2 : ℝ) ^ (h * ℓ) := by
  obtain ⟨k, hk⟩ := Gamma_integer E h ℓ z hint
  refine ⟨k, ?_, ?_⟩
  · -- `0 ≤ k` from `2^{hℓ} Γ_z = k` and `0 ≤ Γ_z`
    have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ (h * ℓ) * Gamma ((2 : ℝ) • E) ℓ z :=
      mul_nonneg (by positivity) hΓ
    rw [hk] at hnn
    exact_mod_cast hnn
  · rw [← hk]
    field_simp

/-- Lemma 3.3, YES-instance pigeonhole (p.8): if the (unnormalised) trace of `A^ℓ = (2E)^ℓ`
exceeds `2^m · 2`, then some diagonal entry `Γ_z` is `> 2`. -/
theorem lemma33_yes_exists {m : ℕ} (E : ProofMat m) (ℓ : ℕ)
    (htrace : (2 : ℝ) ^ m * 2 < (((2 : ℝ) • E) ^ ℓ).trace) :
    ∃ z : Idx m, 2 < Gamma ((2 : ℝ) • E) ℓ z :=
  Gamma_yes_exists _ _ htrace

end Qatlib.Papers.QMAPerfect26.MainResults
