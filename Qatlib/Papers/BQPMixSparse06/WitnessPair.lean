/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPMixSparse06.MainResults.Theorem4QcmaDecay
import Qatlib.Papers.BQPMixSparse06.SignedClock.ClockRepair

/-!
# Witness-pair states and decision gaps

The localized state `psiMinus j` is prepared by a Hadamard gate followed by a phase flip on the
doubled-vertex bit. The midpoint inequalities and `wPlus_separates_midpoint` translate separated
parameter ranges into a decision threshold.

The output flip `Yprime` exchanges the two output rows of a matrix. Its action preserves
`plusWeight` and negates `minusWeight`, providing elementary witness-pair identities for
[JanzingWocjan2006].

## Main statements

* `witnessState_prep`: an explicit gate expression for the localized antisymmetric state.
* `wPlus_separates_midpoint`: the corrected clock weight lies on opposite sides of one half in
  the two parameter ranges.
* `amplitude_probability_gap`: squaring preserves an explicit separation for the stated
  amplitude bounds.

## References

* [Janzing and Wocjan, 2006][JanzingWocjan2006]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.WitnessPair

open Finset Matrix
open Qatlib.Papers.BQPMixSparse06.MainResults
open Qatlib.Papers.BQPMixSparse06.SignedClock

/-- The state `psiMinus j` is zero away from vertex `j` and has coordinates `1 / √2` and `-1 /
√2` on its two copies [JanzingWocjan2006]. -/
theorem witnessState_apply {N : ℕ} (j : Fin N) (s : Fin 2) (i : Fin N) :
    psiMinus j (s, i) =
      if i = j then (if s = 0 then 1 / Real.sqrt 2 else -(1 / Real.sqrt 2)) else 0 := by
  by_cases h : i = j
  · subst h
    simp [psiMinus, liftVec, Pi.single_eq_same, phiMinus]
  · simp [psiMinus, liftVec, Pi.single_eq_of_ne h, phiMinus, h]

/-- The coordinate of `psiMinus j` at the first copy of `j` is `1 / √2`. -/
theorem witnessState_zero {N : ℕ} (j : Fin N) : psiMinus j (0, j) = 1 / Real.sqrt 2 := by
  rw [witnessState_apply]; simp

/-- The coordinate of `psiMinus j` at the second copy of `j` is `-1 / √2`. -/
theorem witnessState_one {N : ℕ} (j : Fin N) : psiMinus j (1, j) = -(1 / Real.sqrt 2) := by
  rw [witnessState_apply]; simp

/-- The real phase-flip matrix with diagonal entries one and minus one. -/
def zGate : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- The real Hadamard matrix with entries scaled by `1 / √2`. -/
def hGate : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / Real.sqrt 2, 1 / Real.sqrt 2; 1 / Real.sqrt 2, -(1 / Real.sqrt 2)]

/-- Applying the Hadamard gate and then the phase-flip gate to the zero basis vector produces
`phiMinus`. -/
theorem zH_single_zero (s : Fin 2) :
    ((zGate * hGate) *ᵥ (Pi.single 0 (1 : ℝ))) s = phiMinus s := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  fin_cases s <;>
    simp [zGate, hGate, phiMinus, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;>
    field_simp <;> nlinarith

/-- Expresses `psiMinus j` as the localized vertex basis vector multiplied by the two-point
state prepared by the Hadamard and phase-flip gates [JanzingWocjan2006]. -/
theorem witnessState_prep {N : ℕ} (j : Fin N) (s : Fin 2) (i : Fin N) :
    psiMinus j (s, i) =
      (if i = j then (1 : ℝ) else 0) * ((zGate * hGate) *ᵥ (Pi.single 0 (1 : ℝ))) s := by
  rw [witnessState_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h, one_mul]
    exact (zH_single_zero s).symm
  · rw [if_neg h, if_neg h, zero_mul]

/-- The arithmetic midpoint `(a + b) / 2` of two real numbers. -/
def midpoint (a b : ℝ) : ℝ := (a + b) / 2

/-- For `a < b`, the midpoint of `a` and `b` is strictly greater than `a`. -/
theorem midpoint_gt_left {a b : ℝ} (hab : a < b) : a < midpoint a b := by
  unfold midpoint; linarith

/-- For `a < b`, the midpoint of `a` and `b` is strictly less than `b`. -/
theorem midpoint_lt_right {a b : ℝ} (hab : a < b) : midpoint a b < b := by
  unfold midpoint; linarith

/-- If `a ≤ b` and `x ≥ b`, then `x` is at least the midpoint of `a` and `b`. -/
theorem accept_of_ge_upper {a b x : ℝ} (hab : a ≤ b) (hx : b ≤ x) :
    midpoint a b ≤ x := by
  unfold midpoint; linarith

/-- If `a ≤ b` and `x ≤ a`, then `x` is at most the midpoint of `a` and `b`. -/
theorem reject_of_le_lower {a b x : ℝ} (hab : a ≤ b) (hx : x ≤ a) :
    x ≤ midpoint a b := by
  unfold midpoint; linarith

/-- If `a < b` and `x ≥ b`, then `x ≤ a` is impossible. -/
theorem decision_exclusive {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    ¬ (x ≤ a) := by
  intro h
  linarith

/-- The midpoint of `1 / 3` and `2 / 3` is `1 / 2` [JanzingWocjan2006]. -/
theorem midpoint_thirds : midpoint (1 / 3) (2 / 3) = 1 / 2 := by
  unfold midpoint; norm_num

/-- The corrected clock weight is above the midpoint `1 / 2` for `p ≤ 1 / 3` and below it for `p
≥ 2 / 3` [JanzingWocjan2006]. -/
theorem wPlus_separates_midpoint {p : ℝ} :
    (p ≤ 1 / 3 → midpoint (1 / 3) (2 / 3) < wPlus p) ∧
      (2 / 3 ≤ p → wPlus p < midpoint (1 / 3) (2 / 3)) := by
  constructor
  · intro h
    have hlow := wPlus_lower h
    have hhalf : (1 / 2 : ℝ) < (1 + 1 / (3 * Real.sqrt 2)) / 2 := by
      have hs := sqrt2_pos
      have hpos : 0 < 1 / (3 * Real.sqrt 2) := by positivity
      linarith
    rw [midpoint_thirds]
    linarith
  · intro h
    have hup := wPlus_upper h
    have hhalf : (1 - 1 / (3 * Real.sqrt 2)) / 2 < (1 / 2 : ℝ) := by
      have hs := sqrt2_pos
      have hpos : 0 < 1 / (3 * Real.sqrt 2) := by positivity
      linarith
    rw [midpoint_thirds]
    linarith

/-- The two-point swap matrix acting on the output coordinate. -/
def outFlip : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The matrix `outFlip * Y`, obtained by exchanging the two output rows of `Y`. -/
def Yprime (Y : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ := outFlip * Y

/-- The output-flip matrix squares to the identity. -/
theorem outFlip_sq : outFlip * outFlip = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [outFlip]

/-- The output flip can be moved between the two arguments of the real dot product. -/
theorem dot_outFlip (u v : Fin 2 → ℝ) :
    dot (outFlip *ᵥ u) v = dot u (outFlip *ᵥ v) := by
  unfold dot
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp [outFlip, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Applying the output flip twice to a vector returns that vector. -/
theorem outFlip_mulVec_involutive (u : Fin 2 → ℝ) :
    outFlip *ᵥ (outFlip *ᵥ u) = u := by
  funext i
  fin_cases i <;>
    simp [outFlip, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The zero-zero entry of the output-flipped matrix is the one-zero entry of the original
matrix [JanzingWocjan2006]. -/
theorem Yprime_accept (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    Yprime Y 0 0 = Y 1 0 := by
  unfold Yprime outFlip
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The one-zero entry of the output-flipped matrix is the zero-zero entry of the original
matrix. -/
theorem Yprime_accept_one (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    Yprime Y 1 0 = Y 0 0 := by
  unfold Yprime outFlip
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Half the sum of all four entries of the two-by-two matrix `Y`. -/
def plusWeight (Y : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (Y 0 0 + Y 0 1 + Y 1 0 + Y 1 1) / 2

/-- Half the alternating sum `Y 0 0 - Y 0 1 - Y 1 0 + Y 1 1`. -/
def minusWeight (Y : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (Y 0 0 - Y 0 1 - Y 1 0 + Y 1 1) / 2

/-- Flipping the output rows leaves `plusWeight` unchanged [JanzingWocjan2006]. -/
theorem plusWeight_Yprime (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    plusWeight (Yprime Y) = plusWeight Y := by
  unfold plusWeight Yprime outFlip
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Flipping the output rows negates `minusWeight` [JanzingWocjan2006]. -/
theorem minusWeight_Yprime (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    minusWeight (Yprime Y) = -minusWeight Y := by
  unfold minusWeight Yprime outFlip
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- If `p ≥ 2 / 3` and `0 ≤ q ≤ 1 / 3`, their squares satisfy `q ^ 2 + 1 / 3 ≤ p ^ 2`
[JanzingWocjan2006]. -/
theorem amplitude_probability_gap {p q : ℝ} (hp : 2 / 3 ≤ p) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 3) :
    q ^ 2 + (1 / 3 : ℝ) ≤ p ^ 2 := by
  have hp0 : 0 ≤ p := by linarith
  have hple : (4 / 9 : ℝ) ≤ p ^ 2 := by
    have h : ((2 / 3 : ℝ)) ^ 2 ≤ p ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hp 2
    norm_num at h ⊢
    exact h
  have hqle : q ^ 2 ≤ (1 / 9 : ℝ) := by
    have h : q ^ 2 ≤ ((1 / 3 : ℝ)) ^ 2 := pow_le_pow_left₀ hq0 hq 2
    norm_num at h ⊢
    exact h
  linarith

end Qatlib.Papers.BQPMixSparse06.WitnessPair
