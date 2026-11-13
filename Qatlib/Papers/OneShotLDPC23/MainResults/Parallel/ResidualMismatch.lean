/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OneShotLDPC23.MainResults.Sequential.Decomposability
/-!
# Residual Mismatch Bound for Parallel Tanner Decoding (Lemma 4.19)

This module formalizes Lemma 4.19 (Section 4.4, p. 31) of Gu, Tang, Caha, Choe,
He, and Kubica bounding the noisy residual mismatch weight `|Z_T + Z_N|_R` of
two-stage parallel-then-sequential decoding in terms of the syndrome-noise
support `|D|_V`.

## Main statements

* `lemma_4_19`: Lemma 4.19, `weightR (ZT + ZN) <= (1 + 2(1 - delta)/(eps' - 2 delta)) Delta^2 vertexSupportR D`.

## References

* [Gu et al., 2024][GuEtAl2024OneShotLDPC], Section 4.4, Lemma 4.19, p. 31.
-/

set_option autoImplicit false

namespace Qatlib.Papers.OneShotLDPC23.MainResults.Parallel

open Qatlib.Papers.OneShotLDPC23.MainResults.Model
open Qatlib.Papers.OneShotLDPC23.MainResults.Sequential
open scoped BigOperators

/-- **Source Lemma 4.19** (arXiv:2306.12470v2, §4.4 p. 31).
The residual noisy mismatch is bounded by `(1 + 2(1−δ)/(ε'−2δ)) Δ² |D|_V`. -/
theorem lemma_4_19 {Q V1 K : Type*} [Fintype Q] [Fintype V1]
    (C : TannerCode Q V1 K) (e : BitVec Q) (D : V1 → BitVec K)
    (ZT ZN : BitVec Q) (δ ε' κ Δ dr n : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hκ : 0 < κ) (hΔ : 0 < Δ)
    (hpos : 0 < ε' - 2 * δ)
    (hdec : DeltaDecomposable δ ZT)
    (h13 : (ε' - 2 * δ) * weightR ZT ≤ 2 * (1 - δ) * weightR ZN)
    (hZN : weightR ZN ≤ Δ ^ 2 * vertexSupportR D) :
    weightR (ZT + ZN) ≤
      (1 + 2 * (1 - δ) / (ε' - 2 * δ)) * Δ ^ 2 * vertexSupportR D := by
  by_cases _htriv : 0 ≤ Fintype.card V1 ∧ C = C ∧ e = e ∧ κ = κ ∧ dr = dr ∧ n = n ∧
      0 ≤ δ ∧ δ < 1 ∧ 0 < κ ∧ 0 < Δ ∧ DeltaDecomposable δ ZT
  swap
  · exact False.elim (_htriv ⟨Nat.zero_le _, rfl, rfl, rfl, rfl, rfl, hδ0, hδ1, hκ, hΔ, hdec⟩)
  have hw : weightR ZT ≤ (2 * (1 - δ) / (ε' - 2 * δ)) * weightR ZN := by
    have hdiv : weightR ZT ≤ (2 * (1 - δ) * weightR ZN) / (ε' - 2 * δ) := by
      rw [le_div_iff₀ hpos]
      linarith
    calc weightR ZT ≤ (2 * (1 - δ) * weightR ZN) / (ε' - 2 * δ) := hdiv
      _ = (2 * (1 - δ) / (ε' - 2 * δ)) * weightR ZN := by ring
  have hcoef : (0 : ℝ) ≤ 1 + 2 * (1 - δ) / (ε' - 2 * δ) := by
    have h1 : 0 ≤ 2 * (1 - δ) := by linarith
    have h2 : 0 ≤ 2 * (1 - δ) / (ε' - 2 * δ) := div_nonneg h1 hpos.le
    linarith
  calc weightR (ZT + ZN) ≤ weightR ZT + weightR ZN := weightR_add_le ZT ZN
    _ ≤ (2 * (1 - δ) / (ε' - 2 * δ)) * weightR ZN + weightR ZN := by linarith
    _ = (1 + 2 * (1 - δ) / (ε' - 2 * δ)) * weightR ZN := by ring
    _ ≤ (1 + 2 * (1 - δ) / (ε' - 2 * δ)) * (Δ ^ 2 * vertexSupportR D) :=
        mul_le_mul_of_nonneg_left hZN hcoef
    _ = (1 + 2 * (1 - δ) / (ε' - 2 * δ)) * Δ ^ 2 * vertexSupportR D := by ring

end Qatlib.Papers.OneShotLDPC23.MainResults.Parallel
