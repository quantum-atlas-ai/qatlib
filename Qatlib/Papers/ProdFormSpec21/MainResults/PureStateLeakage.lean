/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Pure-state leakage bound for Theorem 1

This module proves the vector form of [YiCrosson2022], Theorem 1, in a
general complex inner-product space with its true Euclidean norm and
the true operator norm of continuous linear maps.  Here `P` is an
orthogonal projector (recorded by its Pythagorean identity), `Q` is
the effective projector, and `U` is a norm-preserving evolution that
preserves the effective subspace (`U ∘ Q = Q ∘ U` pointwise).  For a
unit vector `ψ` in the range of `P`, the leakage
`1 - ‖P (U ψ)‖²` equals the squared Euclidean distance from `U ψ` to
the range of `P` and is at most `4 ‖P - Q‖²`, where `‖P - Q‖` is the
operator norm.  This is the pure-state case of the rank-`m` trace
identity (Appendix D, Eq. (46)) that
`Qatlib.Papers.ProdFormSpec21.MainResults.theorem1_leakage` carries as
a hypothesis for mixed states; the mixed-state trace extension is not
claimed here.
[Fixed source](https://arxiv.org/abs/2102.12655v1).
-/

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Papers.ProdFormSpec21.MainResults

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Theorem 1, pure-state leakage.**  Let `P Q U : E →L[ℂ] E`, where
`P` satisfies the orthogonal-projector Pythagorean identity
`‖x‖² = ‖P x‖² + ‖x - P x‖²` for every `x`, `U` preserves the
Euclidean norm, and `U` commutes with `Q` pointwise.  For a unit
vector `ψ` with `P ψ = ψ`, the leakage after evolution satisfies
`1 - ‖P (U ψ)‖² ≤ 4 * ‖P - Q‖²` in the operator norm. -/
theorem pure_state_leakage_le (P Q U : E →L[ℂ] E)
    (hP : ∀ x : E, ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2)
    (hU : ∀ x : E, ‖U x‖ = ‖x‖)
    (hcomm : ∀ x : E, U (Q x) = Q (U x))
    (ψ : E) (hψ : ‖ψ‖ = 1) (hPψ : P ψ = ψ) :
    1 - ‖P (U ψ)‖ ^ 2 ≤ 4 * ‖P - Q‖ ^ 2 := by
  set φ : E := U ψ with hφdef
  have hφ : ‖φ‖ = 1 := by rw [hφdef, hU, hψ]
  have hleak : 1 - ‖P φ‖ ^ 2 = ‖φ - P φ‖ ^ 2 := by
    have h := hP φ
    rw [hφ] at h
    linarith
  have hsplit : φ - P φ = (φ - Q φ) + (Q φ - P φ) := by abel
  have hnorm1 : ‖φ - Q φ‖ ≤ ‖P - Q‖ := by
    have h1 : φ - Q φ = U (ψ - Q ψ) := by
      rw [hφdef, ← hcomm ψ, ← map_sub]
    have h2 : ψ - Q ψ = (P - Q) ψ := by
      rw [sub_apply, hPψ]
    rw [h1, hU, h2]
    calc ‖(P - Q) ψ‖ ≤ ‖P - Q‖ * ‖ψ‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖P - Q‖ := by rw [hψ, mul_one]
  have hnorm2 : ‖Q φ - P φ‖ ≤ ‖P - Q‖ := by
    have h1 : Q φ - P φ = (Q - P) φ := by
      rw [sub_apply]
    rw [h1]
    calc ‖(Q - P) φ‖ ≤ ‖Q - P‖ * ‖φ‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖P - Q‖ := by rw [hφ, mul_one, norm_sub_rev]
  have hdist : ‖φ - P φ‖ ≤ 2 * ‖P - Q‖ := by
    rw [hsplit]
    calc ‖(φ - Q φ) + (Q φ - P φ)‖ ≤ ‖φ - Q φ‖ + ‖Q φ - P φ‖ :=
          norm_add_le _ _
      _ ≤ 2 * ‖P - Q‖ := by linarith [hnorm1, hnorm2]
  rw [hleak]
  calc ‖φ - P φ‖ ^ 2 ≤ (2 * ‖P - Q‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hdist 2
    _ = 4 * ‖P - Q‖ ^ 2 := by ring

/-- **Theorem 1, explicit `m h² δt² / λ²` scale.**  Under the hypotheses
of `pure_state_leakage_le`, if additionally the squared operator-norm
distance satisfies `‖P - Q‖² ≤ m * h ^ 2 * δt ^ 2 / lam ^ 2` (the
projector-distance estimate of Lemma 1 / Lemma 2 for a rank-`m`
subspace), then the pure-state leakage is at most
`4 * (m * h ^ 2 * δt ^ 2 / lam ^ 2)`. -/
theorem pure_state_leakage_le_scale (P Q U : E →L[ℂ] E)
    (hP : ∀ x : E, ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2)
    (hU : ∀ x : E, ‖U x‖ = ‖x‖)
    (hcomm : ∀ x : E, U (Q x) = Q (U x))
    (m : ℕ) (h δt lam : ℝ) (_hm : 0 < m) (_hlam : 0 < lam)
    (hd : ‖P - Q‖ ^ 2 ≤ m * h ^ 2 * δt ^ 2 / lam ^ 2) :
    ∀ ψ : E, ‖ψ‖ = 1 → P ψ = ψ →
      1 - ‖P (U ψ)‖ ^ 2 ≤ 4 * (m * h ^ 2 * δt ^ 2 / lam ^ 2) := by
  intro ψ hψ hPψ
  exact (pure_state_leakage_le P Q U hP hU hcomm ψ hψ hPψ).trans
    (mul_le_mul_of_nonneg_left hd (by norm_num))

end Qatlib.Papers.ProdFormSpec21.MainResults
