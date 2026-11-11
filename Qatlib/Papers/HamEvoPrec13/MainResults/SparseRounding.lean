/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Real.Archimedean
import Qatlib.Papers.HamEvoPrec13.MainResults.SparseMatching
import Qatlib.Papers.HamEvoPrec13.MainResults.MatchedBlocks

/-!
# Rounding a real scalar to an equal-weight sum of unit coefficients

Berry--Cleve--Somma, "Exponential improvement in precision for Hamiltonian-evolution
simulation", fixed arXiv:1308.5424v3, Lemma 1 and Eq. (3).

The proof of Lemma 1 rounds every off-diagonal value `x ∈ [-g, g]` to the nearest
multiple `(h/ℓ) g` of the granularity `g/ℓ`, with rounding error at most `g/(2ℓ)`.
Eq. (3) then writes `h` as a sum of `ℓ` integer coefficients in `{−1, 0, +1}`.

This file isolates those scalar facts: the coefficient family `unitCoeff`, the identity
`∑_{i<ℓ} unitCoeff h i = h` for `|h| ≤ ℓ`, and the rounding-error bounds that give the
max-norm accuracy `γ` used in the statement of Lemma 1.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamEvoPrec13.MainResults

/-- Coefficient `i` of the paper's rounding `h = ∑_{j<ℓ} c_j` with `c_j ∈ {-1, 0, 1}`.

Following Eq. (3), a positive integer `h` contributes `+1` to the first `h` coefficients,
a negative integer contributes `-1` to the first `-h` coefficients, and the remaining
coefficients are zero. -/
def unitCoeff (h : ℤ) (i : ℕ) : ℝ :=
  if 0 ≤ h then (if (i : ℤ) < h then 1 else 0)
  else (if (i : ℤ) < -h then -1 else 0)

/-- Every unit coefficient lies in `{-1, 0, 1}`. -/
theorem unitCoeff_eq_one_or_zero_or_neg (h : ℤ) (i : ℕ) :
    unitCoeff h i = 1 ∨ unitCoeff h i = 0 ∨ unitCoeff h i = -1 := by
  unfold unitCoeff
  split_ifs <;> simp

/-- The unit coefficients of `0` all vanish. -/
theorem unitCoeff_zero (i : ℕ) : unitCoeff 0 i = 0 := by
  unfold unitCoeff
  rw [if_pos le_rfl]
  have : ¬((i : ℤ) < 0) := by omega
  rw [if_neg this]

/-- A coefficient that is switched off by the indicator of vanishing is orthogonal to the
coefficient it replaces. -/
theorem indicator_mul_zero (y c : ℝ) : (if y = 0 then c else 0) * y = 0 := by
  by_cases hy : y = 0 <;> simp [hy]

/-- The indicator family is normalized: a unit coefficient is either `±1`, contributing
`1` to `y * y`, or `0`, in which case the indicator contributes `1`. -/
theorem indicator_unit (y c : ℝ) (hc : c = 1 ∨ c = -1)
    (hy : y = 1 ∨ y = 0 ∨ y = -1) :
    (if y = 0 then c else 0) * (if y = 0 then c else 0) + y * y = 1 := by
  rcases hy with hy | hy | hy <;> rcases hc with hc | hc <;> rw [hy, hc] <;> norm_num

/-- A signed one is a unit: used for the `±1` blocks of the decomposition. -/
theorem signed_one_unit (b : Bool) :
    (if b then (1 : ℝ) else -1) = 1 ∨ (if b then (1 : ℝ) else -1) = -1 := by
  cases b <;> simp

/-- The paper's integer decomposition Eq. (3): for `|h| ≤ ℓ`, the `ℓ` unit coefficients
in `{-1, 0, 1}` sum to `h`. -/
theorem sum_unitCoeff : ∀ (ℓ : ℕ) (h : ℤ), |h| ≤ (ℓ : ℤ) →
    ∑ i : Fin ℓ, unitCoeff h (i : ℕ) = (h : ℝ)
  | 0, h, hh => by
    have h0 : h = 0 := by
      have hb := abs_le.mp hh
      omega
    simp [h0]
  | ℓ + 1, h, hh => by
    have hb := abs_le.mp hh
    rw [Fin.sum_univ_castSucc]
    have hsum : (∑ i : Fin ℓ, unitCoeff h ((Fin.castSucc i : Fin (ℓ + 1)) : ℕ))
        = ∑ i : Fin ℓ, unitCoeff h (i : ℕ) :=
      Finset.sum_congr rfl fun i _ => by rw [Fin.val_castSucc]
    rw [hsum]
    have hlast_val : ((Fin.last ℓ : Fin (ℓ + 1)) : ℕ) = ℓ := Fin.val_last ℓ
    rw [hlast_val]
    by_cases hpos : 0 ≤ h
    · by_cases hle : h ≤ (ℓ : ℤ)
      · have hlt : ¬((ℓ : ℤ) < h) := by omega
        have hlast : unitCoeff h ℓ = 0 := by
          unfold unitCoeff
          rw [if_pos hpos, if_neg hlt]
        have hih : ∑ i : Fin ℓ, unitCoeff h (i : ℕ) = (h : ℝ) :=
          sum_unitCoeff ℓ h (abs_le.mpr ⟨by omega, hle⟩)
        rw [hlast, add_zero, hih]
      · have hval : h = (ℓ : ℤ) + 1 := by omega
        subst hval
        have hge : (0 : ℤ) ≤ (ℓ : ℤ) + 1 := by omega
        have hall : ∀ i : Fin ℓ, unitCoeff ((ℓ : ℤ) + 1) (i : ℕ) = 1 := by
          intro i
          have hi : (i : ℤ) < (ℓ : ℤ) := by exact_mod_cast i.isLt
          unfold unitCoeff
          rw [if_pos hge, if_pos (by omega)]
        have hlast : unitCoeff ((ℓ : ℤ) + 1) ℓ = 1 := by
          unfold unitCoeff
          rw [if_pos hge, if_pos (by omega)]
        have hsum1 : (∑ _i : Fin ℓ, (1 : ℝ)) = (ℓ : ℝ) := by simp
        rw [Finset.sum_congr rfl fun i _ => hall i, hlast, hsum1]
        push_cast
        ring
    · have hneg : h < 0 := by omega
      by_cases hle : -h ≤ (ℓ : ℤ)
      · have hlt : ¬((ℓ : ℤ) < -h) := by omega
        have hlast : unitCoeff h ℓ = 0 := by
          unfold unitCoeff
          rw [if_neg hpos, if_neg hlt]
        have hih : ∑ i : Fin ℓ, unitCoeff h (i : ℕ) = (h : ℝ) :=
          sum_unitCoeff ℓ h (abs_le.mpr ⟨by omega, by omega⟩)
        rw [hlast, add_zero, hih]
      · have hval : -h = (ℓ : ℤ) + 1 := by omega
        have hall : ∀ i : Fin ℓ, unitCoeff h (i : ℕ) = -1 := by
          intro i
          have hi : (i : ℤ) < (ℓ : ℤ) := by exact_mod_cast i.isLt
          unfold unitCoeff
          rw [if_neg hpos, if_pos (by omega)]
        have hlast : unitCoeff h ℓ = -1 := by
          unfold unitCoeff
          rw [if_neg hpos, if_pos (by omega)]
        have hsum1 : (∑ _i : Fin ℓ, (-1 : ℝ)) = -((ℓ : ℝ)) := by simp
        rw [Finset.sum_congr rfl fun i _ => hall i, hlast, hsum1]
        have hval' : (-(h : ℝ)) = (ℓ : ℝ) + 1 := by exact_mod_cast hval
        linarith

/-- Rounding to the nearest multiple of the granularity `g/ℓ` has absolute error at most
`g/(2ℓ)`, as used for the max-norm accuracy of Lemma 1. -/
theorem abs_sub_round_granularity {x g : ℝ} {ℓ : ℕ} (hg : 0 < g) (hℓ : 0 < ℓ) :
    |x - (g / (ℓ : ℝ)) * (round ((ℓ : ℝ) * x / g) : ℝ)| ≤ g / (2 * ℓ) := by
  have hkey : x - (g / (ℓ : ℝ)) * (round ((ℓ : ℝ) * x / g) : ℝ)
      = (g / (ℓ : ℝ)) * (((ℓ : ℝ) * x / g) - (round ((ℓ : ℝ) * x / g) : ℝ)) := by
    field_simp
  rw [hkey, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < g / (ℓ : ℝ))]
  have hround := abs_sub_round ((ℓ : ℝ) * x / g)
  calc (g / (ℓ : ℝ)) * |((ℓ : ℝ) * x / g) - (round ((ℓ : ℝ) * x / g) : ℝ)|
      ≤ (g / (ℓ : ℝ)) * (1 / 2) := mul_le_mul_of_nonneg_left hround (by positivity)
    _ = g / (2 * ℓ) := by field_simp

/-- The rounded integer never exceeds the granularity count: if `|x| ≤ g`, then
`round (ℓ x / g)` lies in `[-ℓ, ℓ]`, which is the hypothesis of Eq. (3). -/
theorem abs_round_le_of_abs_le {x g : ℝ} {ℓ : ℕ} (hg : 0 < g) (hx : |x| ≤ g) :
    |round ((ℓ : ℝ) * x / g)| ≤ (ℓ : ℤ) := by
  have hy : |(ℓ : ℝ) * x / g| ≤ (ℓ : ℝ) := by
    rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ℓ : ℝ)), abs_of_pos hg,
      div_le_iff₀ hg]
    nlinarith [abs_nonneg x]
  have hround : |((ℓ : ℝ) * x / g) - (round ((ℓ : ℝ) * x / g) : ℝ)| ≤ 1 / 2 :=
    abs_sub_round _
  have htri : |(round ((ℓ : ℝ) * x / g) : ℝ)| ≤ (ℓ : ℝ) + 1 / 2 := by
    have hdecomp : (round ((ℓ : ℝ) * x / g) : ℝ)
        = ((round ((ℓ : ℝ) * x / g) : ℝ) - (ℓ : ℝ) * x / g) + (ℓ : ℝ) * x / g := by ring
    rw [hdecomp]
    have h1 : |((round ((ℓ : ℝ) * x / g) : ℝ) - (ℓ : ℝ) * x / g)| ≤ 1 / 2 := by
      rw [abs_sub_comm]; exact hround
    calc |((round ((ℓ : ℝ) * x / g) : ℝ) - (ℓ : ℝ) * x / g) + (ℓ : ℝ) * x / g|
        ≤ |((round ((ℓ : ℝ) * x / g) : ℝ) - (ℓ : ℝ) * x / g)| + |(ℓ : ℝ) * x / g| :=
          abs_add_le _ _
      _ ≤ 1 / 2 + (ℓ : ℝ) := by linarith
      _ = (ℓ : ℝ) + 1 / 2 := by ring
  have hlt : (|round ((ℓ : ℝ) * x / g)| : ℝ) < (ℓ : ℝ) + 1 := by
    have hcast : (↑(|round ((ℓ : ℝ) * x / g)|) : ℝ) = |(round ((ℓ : ℝ) * x / g) : ℝ)| :=
      Int.cast_abs
    rw [← hcast]
    linarith
  have hlt' : |round ((ℓ : ℝ) * x / g)| < (ℓ : ℤ) + 1 := by exact_mod_cast hlt
  exact Int.lt_add_one_iff.mp hlt'

end Qatlib.Papers.HamEvoPrec13.MainResults
