/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClawFinding07.MainResults.Spectral.JohnsonSpectrum
import Qatlib.Papers.ClawFinding07.MainResults.Spectral.ProductGap

/-!
# Gap bounds for product Johnson walks

This module combines the Johnson-chain contraction estimates with the product-chain theorem for
the claw-finding walk of [Tani2009]. For subset sizes at least two and at most half the
corresponding domain sizes, it obtains the reciprocal-size gap bound for the product.

## Main statements

* `johnsonVertex_nonempty`: existence of vertices under `k ≤ n`.
* `productJohnson_spectralGap`: a bound with parameter `min (1/l) (1/m)`.
* `productJohnson_spectralGap_inv_right`: the parameter `1/m` when `l ≤ m`.

## References

* [Tani, 2009][Tani2009]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ClawFinding07.MainResults.Spectral

open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.TwoLevelLower (IsTransitionMatrix)
open scoped BigOperators

/-- There exists a `k`-element subset of `Fin n` whenever `k ≤ n`. -/
theorem johnsonVertex_nonempty {n k : ℕ} (h : k ≤ n) : Nonempty (JohnsonVertex n k) := by
  classical
  refine ⟨⟨(Finset.range k).attach.map ?_, ?_⟩⟩
  · refine ⟨fun x => ⟨x.1, ?_⟩, ?_⟩
    · exact lt_of_lt_of_le (Finset.mem_range.mp x.2) h
    · intro x y hxy
      exact Subtype.ext (by
        simpa using congrArg (fun z : Fin n => (z : ℕ)) hxy)
  · simp

/-- A bound `SpectralGapAtLeast P δ` implies the bound at any `δ'` with `0 ≤ δ' ≤ δ ≤ 1`. -/
theorem spectralGap_mono {I : Type*} [Fintype I] {P : I → I → ℝ} {δ δ' : ℝ}
    (h : SpectralGapAtLeast P δ) (_hδ'0 : 0 ≤ δ') (hδ'δ : δ' ≤ δ) (hδ1 : δ ≤ 1) :
    SpectralGapAtLeast P δ' := by
  obtain ⟨ht, hs, hg⟩ := h
  refine ⟨ht, hs, ?_⟩
  intro v hv
  have h0 : 0 ≤ 1 - δ := by linarith
  have hle : 1 - δ ≤ 1 - δ' := by linarith
  have hsq : (1 - δ) ^ 2 ≤ (1 - δ') ^ 2 := by
    have hm := mul_self_le_mul_self h0 hle
    calc (1 - δ) ^ 2 = (1 - δ) * (1 - δ) := by ring
      _ ≤ (1 - δ') * (1 - δ') := hm
      _ = (1 - δ') ^ 2 := by ring
  have hsqv : 0 ≤ sqNorm v := by
    simp only [sqNorm]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  calc sqNorm (act P v) ≤ (1 - δ) ^ 2 * sqNorm v := hg v hv
    _ ≤ (1 - δ') ^ 2 * sqNorm v := mul_le_mul_of_nonneg_right hsq hsqv

/-- For `2 ≤ l`, `2*l ≤ N`, `2 ≤ m`, and `2*m ≤ M`, the product Johnson chain satisfies
`SpectralGapAtLeast` with parameter `min (1/l) (1/m)`; see [Tani2009]. -/
theorem productJohnson_spectralGap {N M l m : ℕ}
    (hl2 : 2 ≤ l) (hln : 2 * l ≤ N) (hm2 : 2 ≤ m) (hmn : 2 * m ≤ M) :
    SpectralGapAtLeast (chainProduct (johnsonChain N l) (johnsonChain M m))
      (min (1 / (l : ℝ)) (1 / (m : ℝ))) := by
  haveI : Nonempty (JohnsonVertex N l) := johnsonVertex_nonempty (by omega)
  haveI : Nonempty (JohnsonVertex M m) := johnsonVertex_nonempty (by omega)
  have h1l : 1 / (l : ℝ) ≤ 1 := by
    have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (by omega : 1 ≤ l)
    simpa using one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hl1
  have h1m : 1 / (m : ℝ) ≤ 1 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
    simpa using one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hm1
  exact spectralGap_chainProduct (by positivity) h1l (by positivity) h1m
    (johnsonChain_spectralGap hl2 hln) (johnsonChain_spectralGap hm2 hmn)

/-- Under the Johnson size conditions and `l ≤ m`, the product Johnson chain satisfies
`SpectralGapAtLeast` with parameter `1/m`, as used in [Tani2009]. -/
theorem productJohnson_spectralGap_inv_right {N M l m : ℕ}
    (hl2 : 2 ≤ l) (hln : 2 * l ≤ N) (hm2 : 2 ≤ m) (hmn : 2 * m ≤ M)
    (hlm : l ≤ m) :
    SpectralGapAtLeast (chainProduct (johnsonChain N l) (johnsonChain M m))
      (1 / (m : ℝ)) := by
  have h := productJohnson_spectralGap hl2 hln hm2 hmn
  have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 0 < l)
  have hml : 1 / (m : ℝ) ≤ 1 / (l : ℝ) := by
    apply one_div_le_one_div_of_le hl0
    exact_mod_cast hlm
  have h1l : 1 / (l : ℝ) ≤ 1 := by
    have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (by omega : 1 ≤ l)
    simpa using one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hl1
  exact spectralGap_mono h (by positivity) (le_min hml le_rfl)
    (le_trans (min_le_left _ _) h1l)

end Qatlib.Papers.ClawFinding07.MainResults.Spectral
