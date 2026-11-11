/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JuntaLearning07.MainResults.FSOracleDefs
import Qatlib.Papers.JuntaLearning07.MainResults.InfluenceIdentification
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Sqrt
import Qatlib.Papers.JuntaLearning07.MainResults.ClassicalLearningLowerBound

/-!
# Ingredients for learning juntas

This module develops the probability model and error estimates used in the two-stage junta
learner of [AticiServedio2007]. `JointLearner`, `exampleProb`, and `jointProb` describe
hypotheses formed from Fourier samples and independent uniform examples, while
`highInfluenceSet` isolates coordinates above the influence threshold.

The second-stage construction `stage2Hypothesis` depends only on its selected coordinates. The
estimates `disagreement_flipList_le` and `fact_iv6_shift` control the effect of changing
low-influence coordinates, supplying the coordinate-shift estimate associated with Fact IV.6 and
ingredients for Theorem IV.5.

## Main statements

* `highInfluenceSet_subset_relevant` and `highInfluenceSet_card_le` place the high-influence
  coordinates inside any coordinate set determining the target.
* `stage2Hypothesis_isKJunta` bounds the number of coordinates used by the constructed
  hypothesis.
* `disagreement_flipList_le` bounds disagreement under distinct coordinate flips by their total
  influence.
* `fact_iv6_shift` gives an error below `ε / 10` for shifts on at most `k` coordinates of
  influence below `ε / (10 * k)`.
- `stage2_error_arithmetic` verifies the final scalar error inequality.

## References

* [Atici and Servedio, 2007][AticiServedio2007], Quantum Algorithms for Learning and Testing
  Juntas, Theorem IV.5 and Fact IV.6.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.JuntaLearning07.MainResults

open scoped BigOperators

variable {n : ℕ}

/-- The type of learners that map a transcript of `T` Fourier-sampled coordinate sets and `M`
Boolean-cube examples to a Boolean hypothesis on `n` coordinates. -/
def JointLearner (n T M : ℕ) : Type :=
  (Fin T → Finset (Fin n)) → (Fin M → (Fin n → Bool)) → ((Fin n → Bool) → Bool)

/-- The probability of an event under `M` independent uniform samples from the `n`-dimensional
Boolean cube. -/
def exampleProb (n M : ℕ) (E : (Fin M → (Fin n → Bool)) → Prop) : ℝ := by
  classical
  exact ∑ xs : Fin M → (Fin n → Bool), if E xs then (((2 : ℝ) ^ n)⁻¹) ^ M else 0

/-- The probability of an event involving `T` independent Fourier samples from `f` and `M`
independent uniform Boolean-cube examples, with the two transcripts sampled independently. -/
def jointProb (f : (Fin n → Bool) → Bool) (T M : ℕ)
    (E : (Fin T → Finset (Fin n)) → (Fin M → (Fin n → Bool)) → Prop) : ℝ := by
  classical
  exact ∑ s : Fin T → Finset (Fin n), (∏ t : Fin T, fsWeight f (s t)) *
    ∑ xs : Fin M → (Fin n → Bool), if E s xs then (((2 : ℝ) ^ n)⁻¹) ^ M else 0

/-- The set of coordinates whose Boolean influence on `f` is at least `ε / (10 * k)`. -/
def highInfluenceSet (f : (Fin n → Bool) → Bool) (ε : ℝ) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ε / (10 * (k : ℝ)) ≤ boolInfluence f i)

/-- If `f` depends only on `I` and `ε` and `k` are positive, every coordinate in
`highInfluenceSet f ε k` belongs to `I`. -/
theorem highInfluenceSet_subset_relevant {I : Finset (Fin n)}
    {f : (Fin n → Bool) → Bool} (hdep : dependsOnlyOn I f)
    {ε : ℝ} {k : ℕ} (hε : 0 < ε) (hk : 0 < k) :
    highInfluenceSet f ε k ⊆ I := by
  intro i hi
  rw [highInfluenceSet, Finset.mem_filter] at hi
  obtain ⟨-, hithresh⟩ := hi
  by_contra hni
  have hzero : boolInfluence f i = 0 := boolInfluence_eq_zero_of_not_depends hdep hni
  rw [hzero] at hithresh
  have hpos : 0 < ε / (10 * (k : ℝ)) := by positivity
  linarith

/-- If `f` depends only on `I` and `ε` and `k` are positive, the high-influence set has
cardinality at most `I.card`. -/
theorem highInfluenceSet_card_le {I : Finset (Fin n)}
    {f : (Fin n → Bool) → Bool} (hdep : dependsOnlyOn I f)
    {ε : ℝ} {k : ℕ} (hε : 0 < ε) (hk : 0 < k) :
    (highInfluenceSet f ε k).card ≤ I.card :=
  Finset.card_le_card (highInfluenceSet_subset_relevant hdep hε hk)

/-- The hypothesis obtained by evaluating `table` after retaining the input coordinates in `A`
and setting every other coordinate to `false`. -/
def stage2Hypothesis (A : Finset (Fin n)) (table : (Fin n → Bool) → Bool) :
    (Fin n → Bool) → Bool :=
  fun x => table (fun i => if i ∈ A then x i else false)

/-- The second-stage hypothesis depends only on the coordinates in `A`, for every choice of
`table`. -/
theorem stage2Hypothesis_dependsOnlyOn (A : Finset (Fin n))
    (table : (Fin n → Bool) → Bool) :
    dependsOnlyOn A (stage2Hypothesis A table) := by
  intro x y hxy
  unfold stage2Hypothesis
  congr 1
  funext i
  by_cases hi : i ∈ A
  · rw [if_pos hi, if_pos hi, hxy i hi]
  · rw [if_neg hi, if_neg hi]

/-- If `A` contains at most `k` coordinates, the second-stage hypothesis is a `k`-junta. -/
theorem stage2Hypothesis_isKJunta {k : ℕ} (A : Finset (Fin n))
    (table : (Fin n → Bool) → Bool) (hA : A.card ≤ k) :
    IsKJunta (n := n) k (stage2Hypothesis A table) :=
  ⟨A, hA, stage2Hypothesis_dependsOnlyOn A table⟩

open Qatlib.Concepts.ProbabilityCore.DistributionAA

open scoped BigOperators

variable {n : ℕ}

/-- Flips the coordinates of a Boolean-cube input successively in the order specified by a list. -/
def flipList {n : ℕ} : List (Fin n) → (Fin n → Bool) → (Fin n → Bool)
  | [], x => x
  | i :: l, x => flipList l (cubeFlip x i)

/-- Uniform disagreement is unchanged when the same coordinate flip is applied to the inputs of
both Boolean functions. -/
theorem disagreement_flip_comp {n : ℕ} (F G : (Fin n → Bool) → Bool) (i : Fin n) :
    disagreement (fun x => F (cubeFlip x i)) (fun x => G (cubeFlip x i)) =
      disagreement F G := by
  unfold disagreement uniformExpect
  congr 1
  exact Equiv.sum_comp (cubeFlipEquiv i)
    (fun x => if F x = G x then (0 : ℝ) else 1)

/-- Every Boolean function has zero uniform disagreement with itself. -/
theorem disagreement_self {n : ℕ} (f : (Fin n → Bool) → Bool) :
    disagreement f f = 0 := by
  unfold disagreement uniformExpect
  simp

/-- For a list of distinct coordinates, the disagreement between `f` and its coordinate-flipped
version is at most the sum of the influences of those coordinates. -/
theorem disagreement_flipList_le {n : ℕ} (f : (Fin n → Bool) → Bool)
    {l : List (Fin n)} (hnd : l.Nodup) :
    disagreement f (fun x => f (flipList l x)) ≤
      ∑ i ∈ l.toFinset, boolInfluence f i := by
  classical
  induction l with
  | nil =>
      simp only [flipList, List.toFinset_nil, Finset.sum_empty]
      have h : (fun x => f x) = f := rfl
      rw [h, disagreement_self]
  | cons i l ih =>
      obtain ⟨hil, hndl⟩ := List.nodup_cons.mp hnd
      have hih := ih hndl
      have hshift : (fun x => f (flipList (i :: l) x)) =
          fun x => (fun y => f (flipList l y)) (cubeFlip x i) := by
        funext x
        rfl
      rw [hshift]
      have htri := disagreement_triangle f (fun x => f (cubeFlip x i))
        (fun x => (fun y => f (flipList l y)) (cubeFlip x i))
      have hfirst : disagreement f (fun x => f (cubeFlip x i)) = boolInfluence f i := by
        unfold boolInfluence disagreement
        rfl
      have hsec : disagreement (fun x => f (cubeFlip x i))
            (fun x => (fun y => f (flipList l y)) (cubeFlip x i)) =
          disagreement f (fun y => f (flipList l y)) :=
        disagreement_flip_comp f (fun y => f (flipList l y)) i
      have hsum : (∑ j ∈ (i :: l).toFinset, boolInfluence f j) =
          boolInfluence f i + ∑ j ∈ l.toFinset, boolInfluence f j := by
        rw [List.toFinset_cons, Finset.sum_insert (by simpa using! hil)]
      calc disagreement f (fun x => (fun y => f (flipList l y)) (cubeFlip x i))
          ≤ disagreement f (fun x => f (cubeFlip x i)) +
              disagreement (fun x => f (cubeFlip x i))
                (fun x => (fun y => f (flipList l y)) (cubeFlip x i)) := htri
        _ = boolInfluence f i + disagreement f (fun y => f (flipList l y)) := by
            rw [hfirst, hsec]
        _ ≤ boolInfluence f i + ∑ j ∈ l.toFinset, boolInfluence f j := by linarith
        _ = ∑ j ∈ (i :: l).toFinset, boolInfluence f j := hsum.symm

/-- If `B` has at most `k` coordinates, each of influence below `ε / (10 * k)`, then flipping
any coordinates of `B` selected by `s` changes `f` on a fraction less than `ε / 10` of
inputs, for positive `k` and `ε`. This is the coordinate-shift estimate associated with Fact
IV.6 of [AticiServedio2007]. -/
theorem fact_iv6_shift {k : ℕ} {ε : ℝ} (hk : 0 < k) (hε : 0 < ε)
    {f : (Fin n → Bool) → Bool} {B : Finset (Fin n)} {s : Fin n → Bool}
    (hinf : ∀ i ∈ B, boolInfluence f i < ε / (10 * (k : ℝ)))
    (hB : B.card ≤ k) :
    disagreement f (fun x => f (flipList ((B.filter (fun i => s i = true)).toList) x))
      < ε / 10 := by
  classical
  set l : List (Fin n) := (B.filter (fun i => s i = true)).toList with hl
  have hnd : l.Nodup := Finset.nodup_toList _
  have hle := disagreement_flipList_le f hnd
  have hsub : l.toFinset ⊆ B := by
    intro i hi
    rw [hl, List.mem_toFinset] at hi
    exact (Finset.mem_filter.mp ((Finset.mem_toList).mp hi)).1
  have h2 : ∑ i ∈ l.toFinset, boolInfluence f i ≤ ∑ i ∈ B, boolInfluence f i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => boolInfluence_nonneg f i)
  have hsum_lt : ∑ i ∈ l.toFinset, boolInfluence f i < ε / 10 := by
    rcases Finset.eq_empty_or_nonempty l.toFinset with h0 | hne
    · rw [h0, Finset.sum_empty]
      linarith
    · have hlt : ∑ i ∈ l.toFinset, boolInfluence f i <
          ∑ i ∈ l.toFinset, ε / (10 * (k : ℝ)) := by
        apply Finset.sum_lt_sum (fun i hi => le_of_lt (hinf i (hsub hi)))
        obtain ⟨i, hi⟩ := hne
        exact ⟨i, hi, hinf i (hsub hi)⟩
      have hcard : ((l.toFinset).card : ℝ) ≤ (k : ℝ) := by
        have h1 : l.toFinset.card ≤ B.card := Finset.card_le_card hsub
        exact_mod_cast h1.trans hB
      have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hfac : (0 : ℝ) ≤ ε / (10 * (k : ℝ)) :=
        div_nonneg (le_of_lt hε) (mul_nonneg (by norm_num) (le_of_lt hkR))
      calc ∑ i ∈ l.toFinset, boolInfluence f i
          < ∑ i ∈ l.toFinset, ε / (10 * (k : ℝ)) := hlt
        _ = ((l.toFinset).card : ℝ) * (ε / (10 * (k : ℝ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (k : ℝ) * (ε / (10 * (k : ℝ))) :=
            mul_le_mul_of_nonneg_right hcard hfac
        _ = ε / 10 := by
            field_simp
  exact lt_of_le_of_lt hle hsum_lt

/-- For positive `ε`, the combined error expression `1 - (1 - ε / 3) ^ 2 + ε / 3` is strictly
less than `ε`. -/
theorem stage2_error_arithmetic {ε : ℝ} (hε : 0 < ε) :
    1 - (1 - ε / 3) ^ 2 + ε / 3 < ε := by
  have h3 : ε / 3 ≠ 0 := by linarith
  have hsq : 0 < (ε / 3) ^ 2 := by positivity
  nlinarith

end Qatlib.Papers.JuntaLearning07.MainResults
