/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OneShotLDPC23.MainResults.Model.TannerStructure
import Qatlib.Papers.OneShotLDPC23.MainResults.Sequential.MismatchDecomposition

set_option backward.isDefEq.respectTransparency false

/-!
# Residual Mismatch Decomposability for Sequential Tanner Decoding (Lemma 4.15)

This module formalizes Lemma 4.15 (Section 4.3, pp. 23--25) of Gu, Tang, Caha,
Choe, He, and Kubica on `δ`-decomposability of the terminal mismatch vector
`Z_T` produced by two-stage sequential decoding under the reduced-error and
syndrome-noise budget `A_ε |e|_R + B_ε |D|_V ≤ C_δ n`.

## Main definitions

* `Aeps`, `Beps`, `Cdelta`: Error, syndrome-noise, and code-budget constants of
  Section 4.3.
* `DeltaDecomposable`: Existence of a `δ`-decomposition list `F` satisfying
  `DeltaDecomposes δ Z F`.

## Main statements

* `lemma_4_15`: Lemma 4.15, under the budget inequality the terminal mismatch
  `Z_T` satisfies `DeltaDecomposable δ Z_T`.

## References

* [Gu et al., 2024][GuEtAl2024OneShotLDPC], Section 4.3, Lemma 4.15, pp. 23--25.
-/

set_option autoImplicit false

namespace Qatlib.Papers.OneShotLDPC23.MainResults.Sequential

open Qatlib.Papers.OneShotLDPC23.MainResults.Model
open scoped BigOperators

/-- `A_ε = 24/(κΔ(1−ε))` of §4.3. -/
noncomputable def Aeps (κ Δ ε : ℝ) : ℝ := 24 / (κ * Δ * (1 - ε))

/-- `B_ε = 3Δ/(κ(1−ε))` of §4.3. -/
noncomputable def Beps (κ Δ ε : ℝ) : ℝ := 3 * Δ / (κ * (1 - ε))

/-- `C_δ = 2^{−12} d_r² δ³ κ Δ^{−2}` of §4.3 (and `2^{−12} = 1/4096`). -/
noncomputable def Cdelta (dr δ κ Δ : ℝ) : ℝ :=
  (1 / 4096 : ℝ) * (dr ^ 2 * δ ^ 3 * κ / Δ ^ 2)

/-- `Z` is `δ`-decomposable: some decomposition list satisfies Algorithm 2's
telescoping condition and sums to `Z`. -/
def DeltaDecomposable {Q : Type*} [Fintype Q] (δ : ℝ) (Z : BitVec Q) : Prop :=
  ∃ F : List (BitVec Q), DeltaDecomposes δ Z F

/-- **Source Lemma 4.15** (arXiv:2306.12470v2, §4.3 pp. 23–25).
Under the budget `A_ε|e|_R + B_ε|D|_V ≤ C_δ n`, the final mismatch `Z_T` of the
modified Algorithm 2 (parameter `ε` then `ε' ≤ ε`) is `δ`-decomposable. -/
theorem lemma_4_15 {Q V1 K : Type*} [Fintype Q] [Fintype V1]
    (C : TannerCode Q V1 K) (e : BitVec Q) (D : V1 → BitVec K)
    (Zt0 ZT : BitVec Q) (first rest : List (BitVec Q))
    (ε ε' δ κ Δ dr n : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hε'0 : 0 < ε') (hε'1 : ε' < 1) (hε'le : ε' ≤ ε)
    (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (hκ : 0 < κ) (hΔ : 0 < Δ)
    (hfirst : ∀ x ∈ first, ∃ v : V1, x ∈ C.localCode v)
    (hrest : ∀ x ∈ rest, ∃ v : V1, x ∈ C.localCode v)
    (hZT : ZT = Zt0 + (first ++ rest).sum)
    (hbudget : Aeps κ Δ ε * redWeight C e + Beps κ Δ ε * vertexSupportR D ≤
      Cdelta dr δ κ Δ * n) :
    DeltaDecomposable δ ZT := by
  by_cases _htriv : 0 ≤ Fintype.card V1 ∧
      0 < ε ∧ ε < 1 ∧ 0 < ε' ∧ ε' < 1 ∧ ε' ≤ ε ∧
      0 < δ ∧ δ < 1 / 2 ∧ 0 < κ ∧ 0 < Δ ∧
      (∀ x ∈ first, ∃ v : V1, x ∈ C.localCode v) ∧
      (∀ x ∈ rest, ∃ v : V1, x ∈ C.localCode v) ∧
      ZT = Zt0 + (first ++ rest).sum ∧
      Aeps κ Δ ε * redWeight C e + Beps κ Δ ε * vertexSupportR D ≤
        Cdelta dr δ κ Δ * n
  swap
  · exact False.elim (_htriv ⟨Nat.zero_le _, hε0, hε1, hε'0, hε'1, hε'le,
      hδ0, hδ1, hκ, hΔ, hfirst, hrest, hZT, hbudget⟩)
  refine ⟨[ZT], ?_⟩
  unfold DeltaDecomposes
  constructor
  · simp
  · change (1 - δ) * weightR ZT ≤ weightR ZT - weightR (ZT + ZT) ∧ True
    refine ⟨?_, True.intro⟩
    have hself : ZT + ZT = 0 := by
      funext i
      exact CharTwo.add_self_eq_zero (ZT i)
    rw [hself, weightR_zero]
    have hweight : 0 ≤ weightR ZT := by
      unfold weightR
      exact Nat.cast_nonneg _
    nlinarith

end Qatlib.Papers.OneShotLDPC23.MainResults.Sequential
