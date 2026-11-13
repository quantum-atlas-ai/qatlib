/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector
import Qatlib.Concepts.WalkSearch.ProjectorCS
import Qatlib.Concepts.WalkSearch.FrameSpectral.SpectralBounds

/-!
# Applications of random-power walk detection

The module specializes the corrected detector to chains with gap greater than `1 / k`. Choosing
the random-power range as the ceiling of `1000 * sqrt (k / ε)` gives a constant average
detection guarantee and an explicit rounding bound.

A further specialization uses `k = ceil (n ^ (2 / 3))` for the element-distinctness parameter
choice. See [Szegedy2004] for the mathematical background.

## Main statements

* `source_theorem_three_reduction`: detection with the chosen power range.
* `source_theorem_three_total_cost`: setup-plus-range bound.
* `source_corollary_one_element_distinctness`: the element-distinctness specialization.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.FrameSpectral
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.Execution.WorkspaceCP

namespace Qatlib.Concepts.WalkSearch.Detection.Applications

/-- Under the stated chain, preparation, and marked-fraction hypotheses with `δ > 1 / k`, the
range `ceil (1000 * sqrt (k / ε))` gives average detection probability at least `1 / 32` and
is at most `1000 * sqrt (k / ε) + 1`. See [Szegedy2004]. -/
theorem source_theorem_three_reduction
    (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ ε : ℝ) (k : ℕ) (j : I)
    (U : Matrix (I × I) (I × I) ℂ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : SymmetricChainGap P δ)
    (hk : 0 < k) (hδk : 1 / (k : ℝ) < δ)
    (hε : 0 < ε) (hεp : ε ≤ markedFraction S)
    (hU : U ∈ Matrix.unitaryGroup (I × I) ℂ)
    (hp : ∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) :
    (1 / 32 : ℝ) ≤
        (∑ kk : Fin (Nat.ceil (1000 * Real.sqrt ((k : ℝ) / ε))),
          detectionProbability U S j (kk.val + 1)) /
          ((Nat.ceil (1000 * Real.sqrt ((k : ℝ) / ε)) : ℕ) : ℝ) ∧
    ((Nat.ceil (1000 * Real.sqrt ((k : ℝ) / ε)) : ℕ) : ℝ) ≤
      1000 * Real.sqrt ((k : ℝ) / ε) + 1 := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hde : 0 < δ * ε := mul_pos hδ hε
  have hrat : 0 < ε / (k : ℝ) := div_pos hε hkR
  have hroot : 0 < Real.sqrt ((k : ℝ) / ε) := Real.sqrt_pos.mpr (div_pos hkR hε)
  have hkey : (0 : ℝ) < 1000 * Real.sqrt ((k : ℝ) / ε) :=
    mul_pos (by norm_num : (0 : ℝ) < 1000) hroot
  have hLpos : 0 < Nat.ceil (1000 * Real.sqrt ((k : ℝ) / ε)) :=
    Nat.ceil_pos.mpr hkey
  have hgt : ε / (k : ℝ) < δ * ε := by
    calc ε / (k : ℝ) = ε * (1 / (k : ℝ)) := by ring
      _ < ε * δ := mul_lt_mul_of_pos_left hδk hε
      _ = δ * ε := by ring
  have hlt : Real.sqrt (ε / (k : ℝ)) < Real.sqrt (δ * ε) :=
    (Real.sqrt_lt_sqrt_iff_of_pos hde).mpr hgt
  have hsinv : Real.sqrt (ε / (k : ℝ)) = (Real.sqrt ((k : ℝ) / ε))⁻¹ := by
    have e : ε / (k : ℝ) = ((k : ℝ) / ε)⁻¹ := by rw [inv_div]
    rw [e, Real.sqrt_inv]
  have hstep : 1000 / Real.sqrt (ε / (k : ℝ)) = 1000 * Real.sqrt ((k : ℝ) / ε) := by
    rw [hsinv, div_eq_mul_inv, inv_inv]
  have hmain : 1000 / Real.sqrt (δ * ε) ≤ 1000 * Real.sqrt ((k : ℝ) / ε) := by
    rw [← hstep]
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hde) (Real.sqrt_pos.mpr hrat)]
    exact mul_le_mul_of_nonneg_left hlt.le (by norm_num)
  have hscale : 1000 / Real.sqrt (δ * ε) ≤
      ((Nat.ceil (1000 * Real.sqrt ((k : ℝ) / ε)) : ℕ) : ℝ) :=
    hmain.trans (Nat.le_ceil _)
  refine ⟨?_, ?_⟩
  · exact (corrected_szegedy_actual_random_power_detection I P S δ ε
      (Nat.ceil (1000 * Real.sqrt ((k : ℝ) / ε))) j U
      hδ hδ1 hgap hε hεp hLpos hscale hU hp).1
  · exact (Nat.ceil_lt_add_one hkey.le).le

/-- For `ε > 0`, setup cost `k` plus the ceiling of `1000 * sqrt (k / ε)` is at most `k + 1000 *
sqrt (k / ε) + 1`. -/
theorem source_theorem_three_total_cost
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (k : ℝ) + (Nat.ceil (1000 * Real.sqrt ((k : ℝ) / ε)) : ℝ) ≤
      (k : ℝ) + 1000 * Real.sqrt ((k : ℝ) / ε) + 1 := by
  have hnn : (0 : ℝ) ≤ 1000 * Real.sqrt ((k : ℝ) / ε) := by positivity
  linarith [(Nat.ceil_lt_add_one hnn).le]

/-- Specializes the random-power detection guarantee to `k = ceil (n ^ (2 / 3))`, with success
at least `1 / 32` and the displayed range bound involving `n ^ (2 / 3) + 1`. See
[Szegedy2004]. -/
theorem source_corollary_one_element_distinctness
    (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ ε : ℝ) (n : ℕ) (j : I)
    (U : Matrix (I × I) (I × I) ℂ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : SymmetricChainGap P δ)
    (_hn : 0 < n) (hk : 0 < Nat.ceil ((n : ℝ) ^ ((2 : ℝ) / 3)))
    (hδk : 1 / ((Nat.ceil ((n : ℝ) ^ ((2 : ℝ) / 3)) : ℕ) : ℝ) < δ)
    (hε : 0 < ε) (hεp : ε ≤ markedFraction S)
    (hU : U ∈ Matrix.unitaryGroup (I × I) ℂ)
    (hp : ∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) :
    (1 / 32 : ℝ) ≤
        (∑ kk : Fin (Nat.ceil (1000 * Real.sqrt
            (((Nat.ceil ((n : ℝ) ^ ((2 : ℝ) / 3)) : ℕ) : ℝ) / ε))),
          detectionProbability U S j (kk.val + 1)) /
          ((Nat.ceil (1000 * Real.sqrt
            (((Nat.ceil ((n : ℝ) ^ ((2 : ℝ) / 3)) : ℕ) : ℝ) / ε)) : ℕ) : ℝ) ∧
    ((Nat.ceil (1000 * Real.sqrt
        (((Nat.ceil ((n : ℝ) ^ ((2 : ℝ) / 3)) : ℕ) : ℝ) / ε)) : ℕ) : ℝ) ≤
      1000 * Real.sqrt ((((n : ℝ) ^ ((2 : ℝ) / 3)) + 1) / ε) + 1 := by
  have hred := source_theorem_three_reduction I P S δ ε
    (Nat.ceil ((n : ℝ) ^ ((2 : ℝ) / 3))) j U hδ hδ1 hgap hk hδk hε hεp hU hp
  refine ⟨hred.1, ?_⟩
  have hk_le : ((Nat.ceil ((n : ℝ) ^ ((2 : ℝ) / 3)) : ℕ) : ℝ) ≤
      (n : ℝ) ^ ((2 : ℝ) / 3) + 1 :=
    (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) (2 / 3 : ℝ))).le
  have hroot : Real.sqrt (((Nat.ceil ((n : ℝ) ^ ((2 : ℝ) / 3)) : ℕ) : ℝ) / ε) ≤
      Real.sqrt ((((n : ℝ) ^ ((2 : ℝ) / 3)) + 1) / ε) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right hk_le hε.le
  have hmul : 1000 * Real.sqrt (((Nat.ceil ((n : ℝ) ^ ((2 : ℝ) / 3)) : ℕ) : ℝ) / ε) ≤
      1000 * Real.sqrt ((((n : ℝ) ^ ((2 : ℝ) / 3)) + 1) / ε) :=
    mul_le_mul_of_nonneg_left hroot (by norm_num)
  linarith [hred.2]

end Qatlib.Concepts.WalkSearch.Detection.Applications
