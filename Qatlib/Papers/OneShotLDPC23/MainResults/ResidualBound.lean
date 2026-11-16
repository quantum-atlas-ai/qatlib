/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.OneShotLDPC23.MainResults.Model.TannerStructure
public import Qatlib.Papers.OneShotLDPC23.MainResults.Sequential.MismatchDecomposition

@[expose] public section


/-!
# OneShotLDPC23.MainResults.Parallel.ResidualMismatch — Lemma 4.19

Fixed paper: **arXiv:2306.12470v2**, §4.4, p. 31.

**Lemma 4.19.**  Let `Z̃^{(k)}` be the mismatch after `k` parallel iterations and
`Z̃_T^{(k)}` the residual mismatch of the sequential decoder (parameter `ε'`) run
from `Z̃^{(k)}`.  If `A|e|_R + B|D|_V ≤ C_δ n` then, for every `k ≥ 1`,

  `|Z̃_T^{(k)}| ≤ (1 + 2(1−δ)/(ε' − 2δ)) Δ² |D|_V ≡ (1 + ζ) Δ² |D|_V`.

Source proof: `Z_T^{(k)}` is `δ`-decomposable by Lemma 4.15 (parameters
`ε = 1/2`, then `ε'`); Lemma 4.13 with `F* = ∅` gives
`|Z_T^{(k)}| ≤ 2(1−δ)/(ε' − 2δ) |Z_N|`; then
`|Z̃_T| = |Z_T + Z_N| ≤ |Z_T| + |Z_N| ≤ (1 + ζ)|Z_N| ≤ (1 + ζ)Δ²|D|_V`.

The last part is proved here from the two numeric inputs
`(ε' − 2δ)|Z_T| ≤ 2(1−δ)|Z_N|` (Lemma 4.13 at `F* = ∅`) and
`|Z_N| ≤ Δ²|D|_V` (Proposition (13)), using the triangle inequality
`weightR_add_le`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.OneShotLDPC23.MainResults

open Qatlib.Papers.OneShotLDPC23.MainResults.Model
open Qatlib.Papers.OneShotLDPC23.MainResults.Sequential
open scoped BigOperators

/-- **Source Lemma 4.19** (arXiv:2306.12470v2, §4.4 p. 31).
The residual noisy mismatch is bounded by `(1 + 2(1−δ)/(ε'−2δ)) Δ² |D|_V`. -/
theorem lemma_4_19 {Q V1 K : Type*} [Fintype Q] [Fintype V1]
    (D : V1 → BitVec K) (ZT ZN : BitVec Q) (δ ε' Δ : ℝ)
    (hδ1 : δ < 1)
    (hpos : 0 < ε' - 2 * δ)
    (h13 : (ε' - 2 * δ) * weightR ZT ≤ 2 * (1 - δ) * weightR ZN)
    (hZN : weightR ZN ≤ Δ ^ 2 * vertexSupportR D) :
    weightR (ZT + ZN) ≤
      (1 + 2 * (1 - δ) / (ε' - 2 * δ)) * Δ ^ 2 * vertexSupportR D := by
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

end Qatlib.Papers.OneShotLDPC23.MainResults
