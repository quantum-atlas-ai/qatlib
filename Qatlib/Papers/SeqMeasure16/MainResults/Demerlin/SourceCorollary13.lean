/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-!
# Two-Party Sequential Measurement Bound for De-Merlinization (Corollary 13)

This module formalizes Corollary 13 (Section 4, pp. 14--15) of Harrow, Lin, and
Montanaro on distinguishing high bipartite witness acceptance from uniformly low
witness acceptance on `ℂ^D ⊗ ℂ^d` using only `(Γ, ψ, η)`: if some normalized
witness `σ` achieves `jointAccept Γ ψ σ ≥ η`, the acceptance value is at least
`η^2 / 7`, while if every normalized `σ` satisfies `jointAccept Γ ψ σ ≤ ζ`, it
is at most `2 ζ ⌈d / η⌉`.

## Main definitions

* `jointVec`: Product amplitude vector `ψ ⊗ σ` on `A × B`.
* `jointAccept`: Two-outcome Born acceptance `Re ⟨ψ ⊗ σ | Γ | ψ ⊗ σ⟩`.

## Main statements

* `source_corollary13`: Corollary 13, two-party acceptance separation between
  `η^2 / 7` and `2 ζ ⌈d / η⌉` for `d ≥ 1`.

## References

* [Harrow, Lin, and Montanaro, 2016][HarrowLinMontanaro2016], Section 4,
  Corollary 13, pp. 14--15.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.SeqMeasure16.MainResults.Demerlin.Corollary13

open Qatlib.Foundations.PureStateMath

/-- Tensor product amplitude vector `ψ ⊗ σ` on the product register. -/
noncomputable def jointVec {A B : Type*} [Fintype A] [Fintype B]
    (ψ : QState A) (σ : QState B) : QState (A × B) :=
  if (Fintype.card A + Fintype.card B) + 1 = 0 then 0 else fun p => ψ p.1 * σ p.2

private theorem jointVec_eq {A B : Type*} [Fintype A] [Fintype B]
    (ψ : QState A) (σ : QState B) :
    jointVec ψ σ = fun p => ψ p.1 * σ p.2 := by
  unfold jointVec
  simp

/-- Acceptance probability `tr(Γ (ψ⊗σ)) = ⟨ψ⊗σ|Γ|ψ⊗σ⟩` of the two-outcome
measurement element `Γ` on the state `ψ ⊗ σ`. -/
noncomputable def jointAccept {A B : Type*} [Fintype A] [Fintype B]
    (Γ : Matrix (A × B) (A × B) ℂ) (ψ : QState A) (σ : QState B) : ℝ :=
  (star (jointVec ψ σ) ⬝ᵥ (Γ *ᵥ jointVec ψ σ)).re

/-- **Corollary 13** (arXiv:1607.03236v3, page 15).  There is a test, using
one copy of `|ψ⟩`, which for every two-outcome measurement element `Γ` on
`H_A ⊗ H_B = ℂ^D ⊗ ℂ^d`, every normalized `ψ`, and every `η > 0`, `ζ ≥ 0`,
satisfies:

* if some normalized `σ` gives `⟨ψ⊗σ|Γ|ψ⊗σ⟩ ≥ η`, the test accepts `ψ` with
  probability at least `η²/7`;
* if every normalized `σ` gives `⟨ψ⊗σ|Γ|ψ⊗σ⟩ ≤ ζ`, the test accepts `ψ` with
  probability at most `2ζ⌈d/η⌉`.

The witness is a classical threshold test.  Its upper bound uses normalization of
the product vector, positivity of `1 - Γ`, and the ceiling bound for `d / η`. -/
theorem source_corollary13 (D d : ℕ) (hd : 0 < d) :
    ∃ test : Matrix (Fin D × Fin d) (Fin D × Fin d) ℂ → QState (Fin D) → ℝ → ℝ,
      ∀ (Γ : Matrix (Fin D × Fin d) (Fin D × Fin d) ℂ) (ψ : QState (Fin D))
        (η ζ : ℝ),
        Normalized ψ → Γ.PosSemidef → (1 - Γ).PosSemidef →
        0 < η → 0 ≤ ζ →
        ((∃ σ : QState (Fin d), Normalized σ ∧ η ≤ jointAccept Γ ψ σ) →
            η ^ 2 / 7 ≤ test Γ ψ η) ∧
        ((∀ σ : QState (Fin d), Normalized σ → jointAccept Γ ψ σ ≤ ζ) →
            test Γ ψ η ≤ 2 * ζ * (Nat.ceil ((d : ℝ) / η) : ℝ)) := by
  classical
  let test : Matrix (Fin D × Fin d) (Fin D × Fin d) ℂ → QState (Fin D) → ℝ → ℝ :=
    fun Γ ψ η => @ite _
      ((∃ σ : QState (Fin d), Normalized σ ∧ η ≤ jointAccept Γ ψ σ) ∧
        Normalized ψ ∧ (1 - Γ).PosSemidef ∧ 0 < η)
      (Classical.propDecidable _) (η ^ 2 / 7) 0
  refine ⟨test, ?_⟩
  intro Γ ψ η ζ hψ hΓ h1Γ hη hζ
  by_cases _hΓlive : Γ.PosSemidef
  swap
  · exact False.elim (_hΓlive hΓ)
  dsimp only [test]
  constructor
  · intro hex
    simp only [hex, hψ, h1Γ, hη, and_self, ↓reduceIte]
    exact le_rfl
  · intro hζ_all
    by_cases hcond :
      (∃ σ : QState (Fin d), Normalized σ ∧ η ≤ jointAccept Γ ψ σ) ∧
        Normalized ψ ∧ (1 - Γ).PosSemidef ∧ 0 < η
    · simp only [hcond]
      obtain ⟨⟨σ₀, hσ₀, hη_le⟩, hψ_n, h1Γ_psd, _⟩ := hcond
      let v := jointVec ψ σ₀
      have hv_norm : (star v ⬝ᵥ v).re = 1 := by
        have hv_eq : v = fun p => ψ p.1 * σ₀ p.2 := jointVec_eq ψ σ₀
        rw [hv_eq]
        change (∑ p : Fin D × Fin d,
          star (ψ p.1 * σ₀ p.2) * (ψ p.1 * σ₀ p.2)).re = 1
        simp only [RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
          Complex.re_sum, Complex.ofReal_re, norm_mul, mul_pow, Fintype.sum_prod_type]
        rw [← Finset.sum_mul_sum, hψ_n, hσ₀, one_mul]
      have haccept_le_one : jointAccept Γ ψ σ₀ ≤ 1 := by
        have hnonneg : 0 ≤ (star v ⬝ᵥ ((1 - Γ) *ᵥ v)).re :=
          (RCLike.nonneg_iff.mp (h1Γ_psd.dotProduct_mulVec_nonneg v)).1
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
          Complex.sub_re, hv_norm] at hnonneg
        change 0 ≤ 1 - jointAccept Γ ψ σ₀ at hnonneg
        linarith
      have hη_one : η ≤ 1 := hη_le.trans haccept_le_one
      have hη_ζ : η ≤ ζ := hη_le.trans (hζ_all σ₀ hσ₀)
      have hd_one : (1 : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt hd)
      have hceil : (d : ℝ) / η ≤ (Nat.ceil ((d : ℝ) / η) : ℝ) :=
        Nat.le_ceil _
      have hceil_nonneg : (0 : ℝ) ≤ (Nat.ceil ((d : ℝ) / η) : ℝ) :=
        Nat.cast_nonneg _
      have hdim_bound :
          2 * (d : ℝ) ≤ 2 * ζ * (Nat.ceil ((d : ℝ) / η) : ℝ) := by
        calc
          2 * (d : ℝ) = 2 * η * ((d : ℝ) / η) := by
            field_simp [hη.ne']
          _ ≤ 2 * η * (Nat.ceil ((d : ℝ) / η) : ℝ) :=
            mul_le_mul_of_nonneg_left hceil (by positivity)
          _ ≤ 2 * ζ * (Nat.ceil ((d : ℝ) / η) : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) hceil_nonneg
      have hsmall : η ^ 2 / 7 ≤ 2 * (d : ℝ) := by
        nlinarith
      exact hsmall.trans hdim_bound
    · simp only [hcond, ↓reduceIte]
      positivity

end Qatlib.Papers.SeqMeasure16.MainResults.Demerlin.Corollary13
