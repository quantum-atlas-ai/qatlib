/-
Copyright (c) 2026 qatlas-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.PreparedRelativeAeCertifiedStopping
public import Qatlib.Papers.QPatternMatch14.MainResults.Model.Instances

@[expose] public section

/-!
# Random-string bounds: Lemmas 6 and 7, Proposition 8, Theorem 1

Montanaro, *Quantum pattern matching fast on average* (arXiv:1408.1816v3),
Section 3 (pp. 9-10) and Section 1.1 (p. 2).

Lemma 7 is proved completely here from the finite Hoeffding bound for independent
bounded coordinates (`independent_weighted_hoeffding_signed`) plus the finite
union bound (`eventMass_exists_le_sum`), following the paper's Chernoff and
union-bound argument. The other legacy source targets are recorded separately
with their precise model gaps; no incomplete statement is imported here.
-/


set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Qatlib.Papers.QPatternMatch14.MainResults.UpperBounds.RandomInstances

open Qatlib.Papers.QPatternMatch14.MainResults.Model
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend

/-- Expectation of a point indicator under the uniform law (used in Lemma 7, arXiv:1408.1816v3, p. 9). -/
theorem uniform_expect_indicator {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (c : A) :
    (uniformFinDist A).expect (fun a => if a = c then (1 : ℝ) else 0) =
      (Fintype.card A : ℝ)⁻¹ := by
  unfold FinDist.expect uniformFinDist
  rw [← Finset.mul_sum]
  simp

/-- The number of matches equals the sum of the coordinate indicators (used in Lemma 7, arXiv:1408.1816v3, p. 9). -/
theorem sum_indicator_eq_matchCount {d m n : ℕ} {A : Type*} [DecidableEq A]
    (hmn : m ≤ n) (T : DStr d n A) (P : DStr d m A) (s : Coord d (n - m + 1)) :
    (∑ x : Coord d m, (if P x = T (shiftIdx hmn s x) then (1 : ℝ) else 0)) =
      (matchCount hmn T P s : ℝ) := by
  classical
  unfold matchCount
  rw [Fintype.card_subtype]
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : T (shiftIdx hmn s x) = P x
  · rw [ite_eq_left h.symm, ite_eq_left h]
  · rw [ite_eq_right (fun hp => h hp.symm), ite_eq_right h]

/-- For a fixed offset, the probability that uniformly random `P` agrees with `T`
in at least `(3/4) m^d` positions is at most `exp (-m^d/8)`.
This is the per-offset Chernoff step in the proof of Lemma 7. -/
theorem eventMass_matchCount_three_quarters_le {d m n : ℕ} {A : Type*}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (hmn : m ≤ n) (T : DStr d n A) (s : Coord d (n - m + 1))
    (hq : 2 ≤ Fintype.card A) (hm : 1 ≤ m) :
    eventMass (randomStringDist (d := d) (m := m) A)
        (fun P : DStr d m A =>
          (3 / 4 : ℝ) * (m : ℝ) ^ d ≤ (matchCount hmn T P s : ℝ)) ≤
      Real.exp (-((m : ℝ) ^ d / 8)) := by
  classical
  have hq0 : (0 : ℝ) < (Fintype.card A : ℝ) := by
    have : 0 < Fintype.card A := Fintype.card_pos
    exact_mod_cast this
  have hqR : (2 : ℝ) ≤ (Fintype.card A : ℝ) := by exact_mod_cast hq
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmd : (0 : ℝ) < (m : ℝ) ^ d := pow_pos hm0 d
  -- the per-coordinate law and the agreement indicator against the fixed text
  let p : Coord d m → FinDist A := fun _ => uniformFinDist A
  let f : ∀ _i : Coord d m, A → ℝ :=
    fun i a => if a = T (shiftIdx hmn s i) then (1 : ℝ) else 0
  have hfmem : ∀ i a, f i a ∈ Set.Icc (0 : ℝ) 1 := by
    intro i a
    dsimp only [f]
    split <;> norm_num
  have hab : ∀ i : Coord d m, (0 : ℝ) ≤ 1 := fun _ => by norm_num
  have hS : 0 < ∑ i : Coord d m, ((1 : ℝ)) ^ 2 * ((1 : ℝ) - 0) ^ 2 := by
    simp only [one_pow, sub_zero, mul_one]
    rw [Finset.sum_const, Finset.card_univ, card_coord, nsmul_eq_mul, Nat.cast_pow, mul_one]
    exact hmd
  -- exact expectation of the weighted sum
  have hE :
      (independent p).expect (weightedSum (fun _ => (1 : ℝ)) f) =
        (m : ℝ) ^ d / (Fintype.card A : ℝ) := by
    rw [Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_expectation]
    simp only [one_mul]
    have hcoord : ∀ i : Coord d m, (p i).expect (f i) = (Fintype.card A : ℝ)⁻¹ := by
      intro i
      dsimp only [p, f]
      exact uniform_expect_indicator _
    simp_rw [hcoord]
    rw [Finset.sum_const, Finset.card_univ, card_coord, nsmul_eq_mul, Nat.cast_pow]
    ring
  -- one-sided Hoeffding at deviation `m^d/4`
  have hu : 0 < (m : ℝ) ^ d / 4 := by
    have := hmd
    linarith
  have hH := independent_weighted_hoeffding_signed p (fun _ => (1 : ℝ)) f
    (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) ((m : ℝ) ^ d / 4) 1 hab hfmem hu
    (by norm_num) hS
  rw [hE] at hH
  have hExp :
      Real.exp (-2 * ((m : ℝ) ^ d / 4) ^ 2 /
          (∑ i : Coord d m, ((1 : ℝ)) ^ 2 * ((1 : ℝ) - 0) ^ 2)) =
        Real.exp (-((m : ℝ) ^ d / 8)) := by
    congr 1
    simp only [one_pow, sub_zero, mul_one]
    rw [Finset.sum_const, Finset.card_univ, card_coord, nsmul_eq_mul, Nat.cast_pow, mul_one]
    field_simp [hmd.ne']
    ring
  rw [hExp] at hH
  -- the threshold event implies the Hoeffding event
  have hinc : ∀ P : DStr d m A,
      (3 / 4 : ℝ) * (m : ℝ) ^ d ≤ (matchCount hmn T P s : ℝ) →
        ((m : ℝ) ^ d / 4 ≤
          1 * (weightedSum (fun _ => (1 : ℝ)) f P -
            (m : ℝ) ^ d / (Fintype.card A : ℝ))) := by
    intro P hP
    rw [one_mul]
    have hdiv : (m : ℝ) ^ d / (Fintype.card A : ℝ) ≤ (m : ℝ) ^ d / 2 := by
      exact div_le_div_of_nonneg_left hmd.le (by norm_num) hqR
    have hw : weightedSum (fun _ => (1 : ℝ)) f P = (matchCount hmn T P s : ℝ) := by
      dsimp only [weightedSum, f]
      simp only [one_mul]
      exact sum_indicator_eq_matchCount hmn T P s
    rw [hw]
    linarith
  have hmono := eventMass_mono (independent p)
    (fun P : DStr d m A => (3 / 4 : ℝ) * (m : ℝ) ^ d ≤ (matchCount hmn T P s : ℝ))
    (fun P => (m : ℝ) ^ d / 4 ≤
      1 * (weightedSum (fun _ => (1 : ℝ)) f P -
        (m : ℝ) ^ d / (Fintype.card A : ℝ))) hinc
  simpa only [randomStringDist, p] using le_trans hmono hH

/--
**Lemma 7** (arXiv:1408.1816v3, p. 9).  Let `T : [n]^d → Σ` be arbitrary and let
`P : [m]^d → Σ` be uniformly random.  Then the probability that there exists an
offset `s ∈ [n-m]^d` with `|{t : P(t) = T(s+t)}| ≥ (3/4) m^d` is at most
`n^d e^{-m^d/8}`.
-/
theorem source_lemma7 {d n m : ℕ} {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (hmn : m ≤ n) (hm : 1 ≤ m) (hq : 2 ≤ Fintype.card A) (T : DStr d n A) :
    eventMass (randomStringDist (d := d) (m := m) A)
        (fun P : DStr d m A => ∃ s : Coord d (n - m + 1),
          (3 / 4 : ℝ) * (m : ℝ) ^ d ≤ (matchCount hmn T P s : ℝ)) ≤
      (n : ℝ) ^ d * Real.exp (-((m : ℝ) ^ d / 8)) := by
  classical
  have hper := fun s : Coord d (n - m + 1) =>
    eventMass_matchCount_three_quarters_le hmn T s hq hm
  have hunion := eventMass_exists_le_sum (randomStringDist (d := d) (m := m) A)
    (fun (s : Coord d (n - m + 1)) (P : DStr d m A) =>
      (3 / 4 : ℝ) * (m : ℝ) ^ d ≤ (matchCount hmn T P s : ℝ))
  refine le_trans hunion ?_
  have hmd : (0 : ℝ) ≤ (m : ℝ) ^ d := by positivity
  have hle : ((n - m + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    have : n - m + 1 ≤ n := by omega
    exact_mod_cast this
  calc (∑ s : Coord d (n - m + 1),
          eventMass (randomStringDist (d := d) (m := m) A)
            (fun P : DStr d m A =>
              (3 / 4 : ℝ) * (m : ℝ) ^ d ≤ (matchCount hmn T P s : ℝ)))
      ≤ ∑ _s : Coord d (n - m + 1), Real.exp (-((m : ℝ) ^ d / 8)) :=
        Finset.sum_le_sum (fun s _ => hper s)
    _ = ((n - m + 1 : ℕ) : ℝ) ^ d * Real.exp (-((m : ℝ) ^ d / 8)) := by
        rw [Finset.sum_const, Finset.card_univ, card_coord, nsmul_eq_mul, Nat.cast_pow]
    _ ≤ (n : ℝ) ^ d * Real.exp (-((m : ℝ) ^ d / 8)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact pow_le_pow_left₀ (by positivity) hle d

end Qatlib.Papers.QPatternMatch14.MainResults.UpperBounds.RandomInstances
