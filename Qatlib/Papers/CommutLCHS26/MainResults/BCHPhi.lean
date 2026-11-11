/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHMultilinear
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Data.List.FinRange

/-!
# The multilinear BCH phi expression

`phi` is the evaluation of the multilinear degree `n` component of the ordered word logarithm on
`Fin n`. Its explicit formulas sum right nested commutators over permutations with rational
weights determined by descent counts.

The Eulerian weight bound controls the norm by the sum of bracket norms divided by the squared
positive degree. These are the phi expressions used in the commutator expansion of
[AftabAnTrivisa2026].

## Main statements

* `phi_eq_perm`: expresses phi as a weighted permutation bracket sum.
* `phi_eq_original`: displays the common reciprocal squared degree factor.
* `phi_zero`: treats the empty family.
* `norm_phi_le_perm`: bounds the norm by the permutation bracket norm sum.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHPhi
open scoped BigOperators MonoidAlgebra Classical
open BCHDynkin BCHWordLie BCHWordCuts BCHCutCounts BCHEulerian BCHMultilinear

section Algebra
variable {B : Type} [Ring B] [Algebra ℚ B]

/-- The evaluated multilinear component of degree `n` in the logarithm of the ordered
exponential word on `Fin n`. -/
def phi {n : ℕ} (Y : Fin n → B) : B :=
  evaluateWords Y (selectWords (List.finRange n)
    (BCHWordLog.logCoefficient (wordSeries ((List.finRange n).map letter)) n))

/-- For positive degree, phi is the sum over permutation words of right nested brackets weighted
by their descent dependent phi weights. -/
theorem phi_eq {n : ℕ} (Y : Fin n → B) (hn : 0 < n) :
    phi Y = ∑ w ∈ permutationWords (List.finRange n),
      phiWeight n (descents w) • rightBracket (w.map Y) := by
  simpa only [phi, List.length_finRange] using
    evaluate_selected_log_phi Y (List.finRange n) (List.sortedLT_finRange n).pairwise
      (by simpa only [List.length_finRange] using hn)

/-- For positive degree, phi is the sum over permutations of the inputs of right nested brackets
with the corresponding phi weights. -/
theorem phi_eq_perm {n : ℕ} (Y : Fin n → B) (hn : 0 < n) :
    phi Y = ∑ σ : Equiv.Perm (Fin n), phiWeight n (descents (List.ofFn σ)) •
      rightBracket (List.ofFn (fun i => Y (σ i))) := by
  rw [phi_eq Y hn, sum_permutationWords]
  simp only [List.map_ofFn, Function.comp_def]

/-- For positive degree, phi equals the signed descent weighted permutation bracket sum with the
common factor `1 / n^2` displayed explicitly. -/
theorem phi_eq_original {n : ℕ} (Y : Fin n → B) (hn : 0 < n) :
    phi Y = (1 / (n : ℚ) ^ 2) • ∑ σ : Equiv.Perm (Fin n),
      ((-1 : ℚ) ^ descents (List.ofFn σ) /
        ((n - 1).choose (descents (List.ofFn σ)) : ℚ)) •
          rightBracket (List.ofFn (fun i => Y (σ i))) := by
  rw [phi_eq_perm Y hn, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [phiWeight, smul_smul, div_eq_mul_inv, mul_inv_rev, one_mul]
  congr 1
  ring

/-- Phi vanishes on an empty family. -/
theorem phi_zero (Y : Fin 0 → B) : phi Y = 0 := by
  simp only [phi, BCHWordLog.logCoefficient_finite, Finset.range_zero, Finset.sum_empty,
    map_zero]

end Algebra

section Norm
variable {B : Type} [NormedRing B] [NormedAlgebra ℝ B] [Algebra ℚ B]

/-- For positive degree and fewer descents than the degree, a phi weighted element has norm at
most its norm divided by the squared degree. -/
theorem norm_phi_term_le (n d : ℕ) (hn : 0 < n) (hd : d < n) (A : B) :
    ‖phiWeight n d • A‖ ≤ (1 / (n : ℝ) ^ 2) * ‖A‖ := by
  have hw : |(phiWeight n d : ℝ)| ≤ 1 / (n : ℝ) ^ 2 := by
    have hr : ((|phiWeight n d| : ℚ) : ℝ) ≤ ((1 / (n : ℚ) ^ 2 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (abs_phiWeight_le n d hn hd)
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast] using hr
  rw [← Rat.cast_smul_eq_qsmul ℝ, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hw (norm_nonneg A)

/-- For positive degree, the norm of phi is at most the sum of the permutation word bracket
norms divided by the squared degree. -/
theorem norm_phi_le {n : ℕ} (Y : Fin n → B) (hn : 0 < n) :
    ‖phi Y‖ ≤ (1 / (n : ℝ) ^ 2) *
      ∑ w ∈ permutationWords (List.finRange n), ‖rightBracket (w.map Y)‖ := by
  rw [phi_eq Y hn, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro w hw
  have hp : w.Perm (List.finRange n) := (mem_permutationWords w _).mp hw
  have hlen : w.length = n := by simpa only [List.length_finRange] using hp.length_eq
  have hwd : w.Nodup := hp.nodup_iff.mpr (List.nodup_finRange n)
  have hd : descents w < n := by
    cases w with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons a w => have h := gap_count a w hwd; omega
  exact norm_phi_term_le n (descents w) hn hd _

/-- For positive degree, the norm of phi is at most the sum of the bracket norms over all input
permutations divided by the squared degree. -/
theorem norm_phi_le_perm {n : ℕ} (Y : Fin n → B) (hn : 0 < n) :
    ‖phi Y‖ ≤ (1 / (n : ℝ) ^ 2) *
      ∑ σ : Equiv.Perm (Fin n), ‖rightBracket (List.ofFn (fun i => Y (σ i)))‖ := by
  simpa only [sum_permutationWords, List.map_ofFn, Function.comp_def] using norm_phi_le Y hn

end Norm
end Qatlib.Papers.CommutLCHS26.MainResults.BCHPhi
