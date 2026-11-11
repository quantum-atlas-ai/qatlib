/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.AchievableSufficiencyRestrictedLowc
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxSourceWord

/-!
# Endpoint normalization for source words

This module normalizes an even real polynomial pair at the endpoint `1` before conversion to the
source-word form of quantum signal processing [LowChuang2017]. The polynomial
`lcEndpointNormalize A B` is the linear combination of `A` and `B` weighted by their endpoint
values; when those values have squared sum one, its endpoint value is exactly one.

The normalization preserves even parity and a common degree bound, retains the required weighted
square inequality, and changes `A` by at most `6 * ε` under explicit endpoint and completion
bounds. `lcEndpointNormalize_source` combines these facts with polynomial sufficiency and
`lcSourceWord_of_normalized` to produce a source phase list of the prescribed positive even
length.

## Main statements

* `lcEndpointNormalize_one` proves exact endpoint normalization.
* `lcEndpointNormalize_bound` preserves the weighted square constraint with the polynomial `Qt`.
* `lcEndpointNormalize_error` bounds the normalization perturbation by `6 * ε`.
* `lcEndpointNormalize_source` realizes the normalized polynomial amplitude as `lcPlusAmp` on
  `[0, 2 * Real.pi]`.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.QspSimulation.Achievability

open Polynomial

/-- The polynomial `A.eval 1 * A + B.eval 1 * B`, with the scalar factors represented by
constant polynomials. -/
noncomputable def lcEndpointNormalize (A B : Polynomial ℝ) : Polynomial ℝ :=
  C (A.eval 1) * A + C (B.eval 1) * B

/-- Evaluating the endpoint-normalized polynomial at `x` gives `A.eval 1 * A.eval x + B.eval 1 *
B.eval x`. -/
theorem lcEndpointNormalize_eval (A B : Polynomial ℝ) (x : ℝ) :
    (lcEndpointNormalize A B).eval x = A.eval 1 * A.eval x + B.eval 1 * B.eval x := by
  simp [lcEndpointNormalize]

/-- If the squared endpoint values of `A` and `B` sum to one, their endpoint-normalized
polynomial evaluates to one at `1`. -/
theorem lcEndpointNormalize_one (A B : Polynomial ℝ)
    (h : A.eval 1 ^ 2 + B.eval 1 ^ 2 = 1) :
    (lcEndpointNormalize A B).eval 1 = 1 := by
  rw [lcEndpointNormalize_eval]
  nlinarith only [h]

/-- Endpoint normalization preserves even parity when both input polynomials are even. -/
theorem lcEndpointNormalize_parity (A B : Polynomial ℝ)
    (hA : A.comp (-X) = A) (hB : B.comp (-X) = B) :
    (lcEndpointNormalize A B).comp (-X) = lcEndpointNormalize A B := by
  simp only [lcEndpointNormalize, add_comp, mul_comp, C_comp, hA, hB]

/-- A common degree bound for `A` and `B` also bounds their endpoint-normalized polynomial. -/
theorem lcEndpointNormalize_degree (A B : Polynomial ℝ) (d : ℕ)
    (hA : A.degree ≤ (d : WithBot ℕ)) (hB : B.degree ≤ (d : WithBot ℕ)) :
    (lcEndpointNormalize A B).degree ≤ (d : WithBot ℕ) := by
  unfold lcEndpointNormalize
  apply degree_add_le_of_degree_le
  · by_cases hz : A.eval 1 = 0
    · simp [hz]
    · rw [degree_C_mul hz]; exact hA
  · by_cases hz : B.eval 1 = 0
    · simp [hz]
    · rw [degree_C_mul hz]; exact hB

/-- When the endpoint values of `A` and `B` have squared sum one, replacing their square sum by
the square of `lcEndpointNormalize A B` preserves the stated weighted bound with `Qt`. -/
theorem lcEndpointNormalize_bound (A B Qt : Polynomial ℝ) (x : ℝ)
    (h1 : A.eval 1 ^ 2 + B.eval 1 ^ 2 = 1)
    (hx : A.eval x ^ 2 + B.eval x ^ 2 + (1 - x * x) * Qt.eval x ^ 2 ≤ 1) :
    (lcEndpointNormalize A B).eval x ^ 2 + (1 - x * x) * Qt.eval x ^ 2 ≤ 1 := by
  rw [lcEndpointNormalize_eval]
  have hsq := sq_nonneg (A.eval 1 * B.eval x - B.eval 1 * A.eval x)
  have he : (A.eval 1 * A.eval x + B.eval 1 * B.eval x) ^ 2 +
      (A.eval 1 * B.eval x - B.eval 1 * A.eval x) ^ 2 = A.eval x ^ 2 + B.eval x ^ 2 := by
    calc
      _ = (A.eval 1 ^ 2 + B.eval 1 ^ 2) * (A.eval x ^ 2 + B.eval x ^ 2) := by ring
      _ = _ := by rw [h1, one_mul]
  linarith

/-- Under the stated bounds on `A`, its endpoint error, and the squares of the two values of
`B`, endpoint normalization changes `A.eval x` by at most `6 * ε`. -/
theorem lcEndpointNormalize_error (A B : Polynomial ℝ) (x ε : ℝ)
    (hε : 0 ≤ ε) (hA : |A.eval x| ≤ 1)
    (ha : |A.eval 1 - 1| ≤ 2 * ε)
    (hb1 : B.eval 1 ^ 2 ≤ 4 * ε) (hbx : B.eval x ^ 2 ≤ 4 * ε) :
    |(lcEndpointNormalize A B).eval x - A.eval x| ≤ 6 * ε := by
  have hp : |B.eval 1 * B.eval x| ≤ 4 * ε := by
    apply abs_le.mpr
    constructor
    · nlinarith [sq_nonneg (B.eval 1 + B.eval x)]
    · nlinarith [sq_nonneg (B.eval 1 - B.eval x)]
  have hs : |(A.eval 1 - 1) * A.eval x| ≤ 2 * ε := by
    rw [abs_mul]
    calc
      _ ≤ (2 * ε) * 1 := mul_le_mul ha hA (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  rw [lcEndpointNormalize_eval,
    show A.eval 1 * A.eval x + B.eval 1 * B.eval x - A.eval x =
      (A.eval 1 - 1) * A.eval x + B.eval 1 * B.eval x by ring]
  exact (abs_add_le _ _).trans (by linarith)

/-- For positive even `d`, the stated parity, degree, endpoint, and weighted square bounds yield
a source phase list of length `d`. Its amplitude is the endpoint-normalized `A, B`
polynomial plus the sine-weighted imaginary contribution from `Qt` on `[0, 2 * Real.pi]`. -/
theorem lcEndpointNormalize_source (d : ℕ) (A B Qt : Polynomial ℝ)
    (hd : Even d) (hdpos : 0 < d)
    (hA : A.comp (-X) = A) (hB : B.comp (-X) = B) (hQ : Qt.comp (-X) = -Qt)
    (hAdeg : A.degree ≤ (d : WithBot ℕ)) (hBdeg : B.degree ≤ (d : WithBot ℕ))
    (hQdeg : Qt.degree < (d : WithBot ℕ))
    (h1 : A.eval 1 ^ 2 + B.eval 1 ^ 2 = 1)
    (hcond : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      A.eval x ^ 2 + B.eval x ^ 2 + (1 - x * x) * Qt.eval x ^ 2 ≤ 1) :
    ∃ phis : List ℝ, phis.length = d ∧
      ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
        lcPlusAmp phis θ =
          realEval (lcEndpointNormalize A B) (Real.cos (θ / 2) : ℂ) +
            Complex.I * (Real.sin (θ / 2) : ℂ) * realEval Qt (Real.cos (θ / 2) : ℂ) := by
  have hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      (lcEndpointNormalize A B).eval x * (lcEndpointNormalize A B).eval x +
        (1 - x * x) * (Qt.eval x * Qt.eval x) ≤ 1 := by
    intro x hx
    simpa only [pow_two] using! lcEndpointNormalize_bound A B Qt x h1 (hcond x hx)
  obtain ⟨γ₀, γ₁, qs, hlen, hamp⟩ := achievableSufficiencyCore d
    (lcEndpointNormalize A B) Qt hd hdpos (lcEndpointNormalize_parity A B hA hB) hQ
    (lcEndpointNormalize_degree A B d hAdeg hBdeg) hQdeg hbound
  have hone : lcRepoAmp γ₀ γ₁ qs 1 = 1 := by
    rw [hamp 1 (by norm_num)]
    simp only [realEval]
    rw [map_eval_ofReal, lcEndpointNormalize_one A B h1]
    norm_num
  obtain ⟨phis, hp, hs⟩ := lcSourceWord_of_normalized γ₀ γ₁ qs hone
  refine ⟨phis, hp.trans hlen, ?_⟩
  intro θ hθ
  have hx : Real.cos (θ / 2) ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hsin : Real.sqrt (1 - Real.cos (θ / 2) * Real.cos (θ / 2)) = Real.sin (θ / 2) := by
    have ht : 0 ≤ Real.sin (θ / 2) := Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith [hθ.1]) (by linarith [hθ.2])
    rw [show 1 - Real.cos (θ / 2) * Real.cos (θ / 2) = Real.sin (θ / 2) ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq (θ / 2)], Real.sqrt_sq ht]
  rw [hs θ hθ, hamp _ hx, hsin]

end Qatlib.Concepts.QspSimulation.Achievability
