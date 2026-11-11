/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Real.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3.2 — Frobenius-close approximations give few bad recommendations

Source: Iordanis Kerenidis, Anupam Prakash, *Quantum Recommendation Systems*,
fixed version arXiv:1603.08675v3 (22 Sep 2016), Lemma 3.2, printed p. 8
(Section 3.2 "Sampling an approximation of the preference matrix").

The preference matrix `T` has entries in `{0,1}`: `T i j = 1` means that product
`j` is a good recommendation for user `i`, and `T i j = 0` means it is bad.
Sampling a pair `(i,j)` from an approximation `T̃` assigns it probability
`T̃ i j ^ 2 / ‖T̃‖_F ^ 2` (the vector-state measurement rule). Lemma 3.2 claims
that if `‖T − T̃‖_F ≤ ε ‖T‖_F`, then

  `Pr_{(i,j)∼T̃}[(i,j) bad] ≤ (ε / (1 − ε)) ^ 2`.

We formalise the finite algebraic content: the bad mass
`badMass T T̃ = Σ_{(i,j) : T i j = 0} T̃ i j ^ 2` is at most
`(ε/(1−ε)) ^ 2 ‖T̃‖_F ^ 2`, and therefore the ratio by `‖T̃‖_F ^ 2` obeys the
stated bound.

The proof follows the paper verbatim:
* triangle inequality for the Frobenius norm gives `‖T̃‖_F ≥ (1 − ε) ‖T‖_F`;
* `‖T − T̃‖_F ^ 2` splits into `Σ_{(i,j):good} (1 − T̃ i j) ^ 2` plus
  `Σ_{(i,j):bad} T̃ i j ^ 2`, hence dominates `badMass`;
* `‖T − T̃‖_F ^ 2 ≤ ε ^ 2 ‖T‖_F ^ 2`.

Boundary: this is the finite mass inequality only. We do not build a
probability-space model of the sampler (the finite distribution is encoded by
the explicit ratio `badMass / frobSq`). The hypotheses `0 ≤ ε`, `ε < 1` and
`0 < frobSq T̃` are the paper's implicit nondegeneracy needed for the ratio;
they are not strengthening the sampled-probability conclusion.
-/

open scoped Matrix.Norms.Frobenius
open Matrix

namespace Qatlib.Papers.QRecommender16.MainResults.PreferenceSampling

set_option autoImplicit false

noncomputable section

variable {m n : ℕ}

/-- The squared Frobenius norm, written as the entrywise sum of squares. -/
def frobSq (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- The square of the Frobenius norm equals the entrywise sum of squares. -/
lemma frobSq_eq_norm_sq (A : Matrix (Fin m) (Fin n) ℝ) : frobSq A = ‖A‖ ^ 2 := by
  have hS : (0 : ℝ) ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (norm_nonneg _) 2
  rw [frobSq, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt hS]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]

/-- Total squared mass of entries that are bad recommendations for `T`, i.e.
entries with `T i j = 0`. -/
def badMass (T Tt : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, if T i j = 0 then Tt i j ^ 2 else 0

/-- The bad mass is nonnegative. -/
lemma badMass_nonneg (T Tt : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ badMass T Tt := by
  unfold badMass
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    split_ifs <;> positivity

/-- Source Lemma 3.2, splitting step (equation (1)): for a `{0,1}` preference
matrix, the squared Frobenius error dominates the bad mass because
`(T i j − T̃ i j)^2` equals `T̃ i j ^ 2` on bad entries and a square on good ones. -/
lemma badMass_le_frobSq_sub (T Tt : Matrix (Fin m) (Fin n) ℝ)
    (hT : ∀ i j, T i j = 0 ∨ T i j = 1) :
    badMass T Tt ≤ frobSq (T - Tt) := by
  unfold badMass frobSq
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hsub : (T - Tt) i j = T i j - Tt i j := rfl
  rw [hsub]
  by_cases h : T i j = 0
  · rw [if_pos h, h, zero_sub, neg_sq]
  · have h1 : T i j = 1 := (hT i j).resolve_left h
    rw [if_neg h, h1]
    exact sq_nonneg _

/-- Source Lemma 3.2, mass form (fixed arXiv:1603.08675v3, p. 8). If
`‖T − T̃‖_F ≤ ε ‖T‖_F` with `0 ≤ ε < 1`, then the total bad mass of `T̃` is at
most `(ε/(1−ε))^2 ‖T̃‖_F^2`. -/
theorem bad_mass_le (T Tt : Matrix (Fin m) (Fin n) ℝ) (ε : ℝ)
    (hT : ∀ i j, T i j = 0 ∨ T i j = 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hclose : ‖T - Tt‖ ≤ ε * ‖T‖) :
    badMass T Tt ≤ (ε / (1 - ε)) ^ 2 * ‖Tt‖ ^ 2 := by
  -- Triangle inequality in the form used by the paper: ‖T̃‖ ≥ ‖T‖ − ‖T − T̃‖.
  have htri : ‖T‖ - ‖Tt‖ ≤ ‖T - Tt‖ := norm_sub_norm_le T Tt
  have hlow : (1 - ε) * ‖T‖ ≤ ‖Tt‖ := by linarith
  have hlow0 : (0 : ℝ) ≤ (1 - ε) * ‖T‖ := by
    have := norm_nonneg (T : Matrix (Fin m) (Fin n) ℝ)
    nlinarith
  have hsq_low : ((1 - ε) * ‖T‖) ^ 2 ≤ ‖Tt‖ ^ 2 :=
    pow_le_pow_left₀ hlow0 hlow 2
  -- The bad mass is dominated by the squared error, which is at most ε²‖T‖².
  have hbad : badMass T Tt ≤ ‖T - Tt‖ ^ 2 := by
    rw [← frobSq_eq_norm_sq]
    exact badMass_le_frobSq_sub T Tt hT
  have hsub : ‖T - Tt‖ ^ 2 ≤ ε ^ 2 * ‖T‖ ^ 2 := by
    have hsq : ‖T - Tt‖ ^ 2 ≤ (ε * ‖T‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hclose 2
    have hεT : (0 : ℝ) ≤ ε * ‖T‖ :=
      mul_nonneg hε0 (norm_nonneg _)
    calc
      ‖T - Tt‖ ^ 2 ≤ (ε * ‖T‖) ^ 2 := hsq
      _ = ε ^ 2 * ‖T‖ ^ 2 := by ring
  -- Rewrite `ε²‖T‖²` as `(ε/(1−ε))² · ((1−ε)‖T‖)²`.
  have hfac0 : (0 : ℝ) ≤ (ε / (1 - ε)) ^ 2 := sq_nonneg _
  have hne : (1 - ε) ≠ 0 := by nlinarith
  calc
    badMass T Tt ≤ ε ^ 2 * ‖T‖ ^ 2 := le_trans hbad hsub
    _ = (ε / (1 - ε)) ^ 2 * (((1 - ε) * ‖T‖) ^ 2) := by
          field_simp
    _ ≤ (ε / (1 - ε)) ^ 2 * ‖Tt‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hsq_low hfac0

/-- Source Lemma 3.2, probability form (fixed arXiv:1603.08675v3, p. 8). Under the
same hypotheses, the probability that a sample drawn from `T̃` is a bad
recommendation, written as `badMass T T̃ / ‖T̃‖_F ^ 2`, is at most
`(ε/(1−ε))^2`. -/
theorem bad_recommendation_probability_le (T Tt : Matrix (Fin m) (Fin n) ℝ) (ε : ℝ)
    (hT : ∀ i j, T i j = 0 ∨ T i j = 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hclose : ‖T - Tt‖ ≤ ε * ‖T‖)
    (hpos : 0 < frobSq Tt) :
    badMass T Tt / frobSq Tt ≤ (ε / (1 - ε)) ^ 2 := by
  rw [div_le_iff₀ hpos, frobSq_eq_norm_sq]
  exact bad_mass_le T Tt ε hT hε0 hε1 hclose

end

end Qatlib.Papers.QRecommender16.MainResults.PreferenceSampling
