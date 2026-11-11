/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHControlled

/-!
# Odd commutator mass and repetition bounds

This module sums the odd commutator majorants of degrees three and higher into `commutatorMass`.
These quantities control the higher-order logarithmic terms of symmetric product formulas in
[AftabAnTrivisa2026].

Under `OddControl`, the mass series is summable throughout the closed real interval of control.
Repeating a step at time `t / q` gives the quadratic suppression proved by `repeated_mass_le`.

## Main statements

* `massTerm_summable`: Under `OddControl xs r J`, the mass terms are summable for every real `t`
  with `|t| ≤ r`.
* `repeated_massTerm_le`: For positive `q`, the mass of `q` repetitions at time `t / q` is at
  most the original mass term divided by `q²`.
* `repeated_mass_le`: Under odd-profile control and `|t| ≤ r`, the commutator mass of `q`
  repetitions at time `t / q` is at most `commutatorMass xs t / q²` for positive `q`.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHCommMass

open scoped BigOperators Classical Matrix.Norms.L2Operator NNReal ENNReal
open BCHControlled
open Qatlib.Concepts.TrotterFormula.GeneralOrder
set_option warningAsError false

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The odd-degree majorant `|t|^(2 * j + 3) * pfCommAlphaSelf xs (2 * j + 3) / (2 * j + 3)²`. -/
def massTerm (xs : List (Matrix I I ℂ)) (t : ℝ) (j : ℕ) : ℝ :=
  |t| ^ (2 * j + 3) * pfCommAlphaSelf xs (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ) ^ 2

/-- The sum of the odd commutator majorants of degrees three and higher. -/
def commutatorMass (xs : List (Matrix I I ℂ)) (t : ℝ) : ℝ := ∑' j, massTerm xs t j

/-- The self-commutator profile `pfCommAlphaSelf xs n` is nonnegative. -/
theorem profile_nonneg (xs : List (Matrix I I ℂ)) (n : ℕ) : 0 ≤ pfCommAlphaSelf xs n :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Every odd commutator mass term is nonnegative. -/
theorem massTerm_nonneg (xs : List (Matrix I I ℂ)) (t : ℝ) (j : ℕ) : 0 ≤ massTerm xs t j :=
  div_nonneg (mul_nonneg (pow_nonneg (abs_nonneg t) _) (profile_nonneg xs _)) (sq_nonneg _)

/-- The mass term is monotone with respect to the absolute value of its time parameter. -/
theorem massTerm_mono (xs : List (Matrix I I ℂ)) (t u : ℝ) (h : |t| ≤ |u|) (j : ℕ) :
    massTerm xs t j ≤ massTerm xs u j := by
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg t) h _) (profile_nonneg xs _)

/-- `OddControl xs r J` implies summability of the mass terms at the radius `r`. -/
theorem massTerm_summable_radius (xs : List (Matrix I I ℂ)) (r : ℝ≥0) (J : ℕ)
    (hc : OddControl xs r J) : Summable (massTerm xs (r : ℝ)) := by
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by decide)
  have ho : Summable (fun j : ℕ => 1 / ((2 * j + 3 : ℕ) : ℝ) ^ 2) :=
    hp.comp_injective (by intro a b h; change 2 * a + 3 = 2 * b + 3 at h; omega)
  apply (summable_nat_add_iff J).mp
  apply ((summable_nat_add_iff J).mpr ho).of_nonneg_of_le
    (fun j => massTerm_nonneg xs r (j + J))
  intro j
  have hn : Odd (2 * (j + J) + 3) := ⟨j + J + 1, by omega⟩
  have h := hc _ (by omega) hn
  dsimp only [massTerm]
  have habs : |(r : ℝ)| = (r : ℝ) := abs_of_nonneg r.2
  rw [habs]
  exact div_le_div_of_nonneg_right h (sq_nonneg _)

/-- Under `OddControl xs r J`, the mass terms are summable for every real `t` with `|t| ≤ r`. -/
theorem massTerm_summable (xs : List (Matrix I I ℂ)) (r : ℝ≥0) (J : ℕ)
    (hc : OddControl xs r J) (t : ℝ) (ht : |t| ≤ r) : Summable (massTerm xs t) := by
  have habs : |(r : ℝ)| = (r : ℝ) := abs_of_nonneg r.2
  exact (massTerm_summable_radius xs r J hc).of_nonneg_of_le (massTerm_nonneg xs t)
    (fun j => massTerm_mono xs t r (by simpa only [habs] using! ht) j)

/-- The commutator mass is nonnegative. -/
theorem commutatorMass_nonneg (xs : List (Matrix I I ℂ)) (t : ℝ) : 0 ≤ commutatorMass xs t :=
  tsum_nonneg (massTerm_nonneg xs t)

/-- For positive `q`, multiplying `(t / q)^(2 * j + 3)` by `q` gives `t^(2 * j + 3) / q^(2 * j +
2)`. -/
theorem repetition_scalar (t : ℝ) (q : ℕ) (hq : 0 < q) (j : ℕ) :
    (q : ℝ) * (t / q) ^ (2 * j + 3) = t ^ (2 * j + 3) / (q : ℝ) ^ (2 * j + 2) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have he : (q : ℝ) ^ (2 * j + 3) = (q : ℝ) ^ (2 * j + 2) * q := by
    rw [show 2 * j + 3 = (2 * j + 2) + 1 by omega, pow_succ]
  rw [div_pow, he]
  field_simp

/-- For positive `q`, the mass of `q` repetitions at time `t / q` is at most the original mass
term divided by `q²`. -/
theorem repeated_massTerm_le (xs : List (Matrix I I ℂ)) (t : ℝ)
    (q : ℕ) (hq : 0 < q) (j : ℕ) :
    (q : ℝ) * massTerm xs (t / q) j ≤ massTerm xs t j / (q : ℝ) ^ 2 := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ (2 * j + 2) :=
    pow_le_pow_right₀ hq1 (by omega)
  have he : |t / q| = |t| / q := by rw [abs_div, abs_of_pos hqp]
  dsimp only [massTerm]
  rw [he]
  calc
    _ = (|t| ^ (2 * j + 3) * pfCommAlphaSelf xs (2 * j + 3) /
        ((2 * j + 3 : ℕ) : ℝ) ^ 2) / (q : ℝ) ^ (2 * j + 2) := by
      have hs := repetition_scalar |t| q hq j
      calc
        _ = ((q : ℝ) * (|t| / q) ^ (2 * j + 3)) *
            pfCommAlphaSelf xs (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ) ^ 2 := by ring
        _ = _ := by rw [hs]; ring
    _ ≤ _ := div_le_div_of_nonneg_left (massTerm_nonneg xs t j) (pow_pos hqp _) hd

/-- Under odd-profile control and `|t| ≤ r`, the commutator mass of `q` repetitions at time `t /
q` is at most `commutatorMass xs t / q²` for positive `q`. -/
theorem repeated_mass_le (xs : List (Matrix I I ℂ)) (r : ℝ≥0) (J : ℕ)
    (hc : OddControl xs r J) (t : ℝ) (ht : |t| ≤ r) (q : ℕ) (hq : 0 < q) :
    (q : ℝ) * commutatorMass xs (t / q) ≤ commutatorMass xs t / (q : ℝ) ^ 2 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsmall : |t / q| ≤ |t| := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < q)]
    exact div_le_self (abs_nonneg _) hq1
  have hs := massTerm_summable xs r J hc t ht
  have hsq := massTerm_summable xs r J hc (t / q) (hsmall.trans ht)
  dsimp only [commutatorMass]
  rw [← tsum_mul_left, ← tsum_div_const]
  exact Summable.tsum_le_tsum (repeated_massTerm_le xs t q hq) (hsq.mul_left _) (hs.div_const _)

end Qatlib.Papers.CommutLCHS26.MainResults.BCHCommMass
