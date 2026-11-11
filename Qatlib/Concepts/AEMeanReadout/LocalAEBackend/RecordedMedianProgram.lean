/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.NativeMean

/-!
# Recorded rational median programs and resource accounts

This module implements rational insertion sort with explicit comparison and peak-entry counters,
then extracts a median from the sorted list. `recordedMedianProgram` realizes numerical
repetition amplification as used in quantum counting [BrassardHoyerTapp1998Counting], with
uniform comparison, bit-time, and register-size accounts.

The program is also connected to signed rational mean-estimation trials in the setting of
[Montanaro2015]. Under the stated variance bound, the resulting theorem combines an
exponentially decreasing median failure estimate with rational-output size bounds and the
underlying AE query ledger.

## Main statements

* `recordedMedianProgram_correct`: identify the program output with the rational sample median.
* `recordedMedianProgram_uniform_accounts`: bound comparisons and bit time and compute peak
  register accounts.
* `output1.frontier1`: combine signed mean-estimation accuracy with the recorded median's
  resource accounts.

## References

* [Brassard, Høyer, and Tapp, 1998][BrassardHoyerTapp1998Counting]
* [Montanaro, 2015][Montanaro2015]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeSearch.NativeMean
open Qatlib.Concepts.MonteCarloMean.LayeredMean
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Qatlib
open Matrix
open scoped Classical BigOperators
set_option warningAsError false

/-- The binary length of a natural number, with zero assigned length zero. -/
def natBits (n : ℕ) : ℕ := if n = 0 then 0 else Nat.log2 n + 1

/-- The binary length of an integer's absolute value plus one sign bit. -/
def intBits (z : ℤ) : ℕ := natBits z.natAbs + 1

/-- The sum of the signed numerator length and denominator length of a rational number. -/
def ratBits (q : ℚ) : ℕ := intBits q.num + natBits q.den

/-- The maximum rational-output bit length over all finite records of a native signed trial. -/
def nativeTrialBits {I : Type} [Fintype I] (f : I → ℚ) (σ : ℚ) (k : ℕ) : ℕ :=
  Finset.univ.sup (fun ω : I × (LayerRecord k × LayerRecord k) =>
    ratBits (nativeSignedOutput f σ k ω))

/-- Every native signed trial output has rational bit length at most `nativeTrialBits`. -/
theorem ratBits_nativeSignedOutput_le {I : Type} [Fintype I]
    (f : I → ℚ) (σ : ℚ) (k : ℕ) (ω : I × (LayerRecord k × LayerRecord k)) :
    ratBits (nativeSignedOutput f σ k ω) ≤ nativeTrialBits f σ k :=
  Finset.le_sup (f := fun ω : I × (LayerRecord k × LayerRecord k) =>
    ratBits (nativeSignedOutput f σ k ω)) (Finset.mem_univ ω)

/-- Insert a rational into a list using ordered comparisons, recording the comparison count and
peak entry count. -/
def insertSortedCountedRat (x : ℚ) : List ℚ → List ℚ × ℕ × ℕ
  | [] => ([x], 0, 1)
  | y :: ys =>
      if x ≤ y then (x :: y :: ys, 1, 1 + (y :: ys).length)
      else
        let p := insertSortedCountedRat x ys
        (y :: p.1, p.2.1 + 1, max (1 + (y :: ys).length) p.2.2)

/-- Sort a rational list by insertion while accumulating comparison counts and the maximum peak
entry count. -/
def insertionSortCountedRat : List ℚ → List ℚ × ℕ × ℕ
  | [] => ([], 0, 0)
  | x :: xs =>
      let p := insertionSortCountedRat xs
      let q := insertSortedCountedRat x p.1
      (q.1, p.2.1 + q.2.1, max p.2.2 q.2.2)

/-- Counted insertion increases the output list length by one. -/
theorem insertSortedCountedRat_length (x : ℚ) (l : List ℚ) :
    (insertSortedCountedRat x l).1.length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
      simp only [insertSortedCountedRat]
      split
      · rfl
      · show ((insertSortedCountedRat x ys).1).length + 1 = (y :: ys).length + 1
        rw [ih]
        simp

/-- Counted insertion uses at most as many comparisons as the input list length. -/
theorem insertSortedCountedRat_cost_le (x : ℚ) (l : List ℚ) :
    (insertSortedCountedRat x l).2.1 ≤ l.length := by
  induction l with
  | nil => simp [insertSortedCountedRat]
  | cons y ys ih =>
      simp only [insertSortedCountedRat]
      split
      · simp
      · show (insertSortedCountedRat x ys).2.1 + 1 ≤ (y :: ys).length
        have hlen : (y :: ys).length = ys.length + 1 := rfl
        omega

/-- The list produced by counted insertion is a permutation of the inserted value followed by
the input list. -/
theorem insertSortedCountedRat_perm (x : ℚ) (l : List ℚ) :
    (insertSortedCountedRat x l).1.Perm (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
      simp only [insertSortedCountedRat]
      split
      · exact List.Perm.refl _
      · exact List.Perm.trans (List.Perm.cons y ih) (List.Perm.swap x y ys)

/-- Counted insertion preserves nondecreasing order when the input list is nondecreasing. -/
theorem insertSortedCountedRat_sorted {x : ℚ} {l : List ℚ} (hl : l.SortedLE) :
    (insertSortedCountedRat x l).1.SortedLE := by
  induction l with
  | nil =>
      exact List.sortedLE_iff_pairwise.mpr
        (List.Pairwise.cons (fun b hb => absurd hb (List.not_mem_nil (a := b))) List.Pairwise.nil)
  | cons y ys ih =>
      simp only [insertSortedCountedRat]
      rw [List.sortedLE_iff_pairwise] at hl ⊢
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hl
      split
      · next hxy =>
          refine List.Pairwise.cons (fun b hb => ?_) hl
          rcases List.mem_cons.mp hb with rfl | hbys
          · exact hxy
          · exact le_trans hxy (hhead b hbys)
      · next hnxy =>
          have hyx : y ≤ x := le_of_lt (lt_of_not_ge hnxy)
          refine List.Pairwise.cons (fun b hb => ?_)
            (List.sortedLE_iff_pairwise.mp (ih (List.sortedLE_iff_pairwise.mpr htail)))
          have hmem : b ∈ x :: ys := List.Perm.subset (insertSortedCountedRat_perm x ys) hb
          rcases List.mem_cons.mp hmem with rfl | hbys
          · exact hyx
          · exact hhead b hbys

/-- The peak entry counter of counted insertion equals one plus the input length. -/
theorem insertSortedCountedRat_peak (x : ℚ) (l : List ℚ) :
    (insertSortedCountedRat x l).2.2 = 1 + l.length := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
      simp only [insertSortedCountedRat]
      split
      · rfl
      · show max (1 + (y :: ys).length) (insertSortedCountedRat x ys).2.2
            = 1 + (y :: ys).length
        have hlen : (y :: ys).length = ys.length + 1 := rfl
        rw [ih]
        omega

/-- Counted insertion sort preserves the input list length. -/
theorem insertionSortCountedRat_length (l : List ℚ) :
    (insertionSortCountedRat l).1.length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      show ((insertSortedCountedRat x (insertionSortCountedRat xs).1).1).length
        = (x :: xs).length
      rw [insertSortedCountedRat_length, ih]
      simp

/-- Counted insertion sort produces a permutation of its input. -/
theorem insertionSortCountedRat_perm (l : List ℚ) :
    (insertionSortCountedRat l).1.Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      show ((insertSortedCountedRat x (insertionSortCountedRat xs).1).1).Perm (x :: xs)
      exact List.Perm.trans (insertSortedCountedRat_perm x _) (List.Perm.cons x ih)

/-- Counted insertion sort uses at most the square of the input length in comparisons. -/
theorem insertionSortCountedRat_cost_le (l : List ℚ) :
    (insertionSortCountedRat l).2.1 ≤ l.length * l.length := by
  induction l with
  | nil => simp [insertionSortCountedRat]
  | cons x xs ih =>
      show (insertionSortCountedRat xs).2.1
          + (insertSortedCountedRat x (insertionSortCountedRat xs).1).2.1
        ≤ (x :: xs).length * (x :: xs).length
      have h1 := insertSortedCountedRat_cost_le x (insertionSortCountedRat xs).1
      have h2 := insertionSortCountedRat_length xs
      have h3 : (x :: xs).length = xs.length + 1 := rfl
      have h4 : xs.length * xs.length + xs.length
          ≤ (x :: xs).length * (x :: xs).length := by
        rw [h3, Nat.succ_mul_succ]
        omega
      omega

/-- The output of counted insertion sort is nondecreasing. -/
theorem insertionSortCountedRat_sorted (l : List ℚ) :
    (insertionSortCountedRat l).1.SortedLE := by
  induction l with
  | nil => exact List.sortedLE_iff_pairwise.mpr List.Pairwise.nil
  | cons x xs ih =>
      show ((insertSortedCountedRat x (insertionSortCountedRat xs).1).1).SortedLE
      exact insertSortedCountedRat_sorted ih

/-- For a nonempty input list, the counted insertion sort peak entry counter equals the input
length. -/
theorem insertionSortCountedRat_peak (l : List ℚ) (hl : l ≠ []) :
    (insertionSortCountedRat l).2.2 = l.length := by
  induction l with
  | nil => exact absurd rfl hl
  | cons x xs ih =>
      by_cases hxs : xs = []
      · subst hxs
        show max (insertionSortCountedRat []).2.2
            (insertSortedCountedRat x (insertionSortCountedRat []).1).2.2 = 1
        simp only [insertionSortCountedRat, insertSortedCountedRat]
        omega
      · show max (insertionSortCountedRat xs).2.2
            (insertSortedCountedRat x (insertionSortCountedRat xs).1).2.2 = (x :: xs).length
        have hlen : (x :: xs).length = xs.length + 1 := rfl
        rw [insertSortedCountedRat_peak, insertionSortCountedRat_length]
        rw [ih hxs]
        omega

/-- Counted insertion sort produces the same rational list as merge sort with the nondecreasing
comparison. -/
theorem insertionSortCountedRat_eq_mergeSort (l : List ℚ) :
    (insertionSortCountedRat l).1 = l.mergeSort (fun a b => a ≤ b) := by
  have hp : ((insertionSortCountedRat l).1).Perm (l.mergeSort (fun a b => a ≤ b)) :=
    (insertionSortCountedRat_perm l).trans (List.mergeSort_perm l (fun a b => a ≤ b)).symm
  exact hp.eq_of_pairwise'
    (List.sortedLE_iff_pairwise.mp (insertionSortCountedRat_sorted l))
    (List.sortedLE_iff_pairwise.mp List.sortedLE_mergeSort)

/-- Sort a rational list and return its zero-based entry `r`, defaulting to zero if absent,
together with comparison and peak entry counters. -/
def recordedMedianProgram (r : ℕ) (l : List ℚ) : ℚ × ℕ × ℕ :=
  let p := insertionSortCountedRat l
  (p.1.getD r 0, p.2.1, p.2.2)

/-- The polynomial comparison bit-cost account `2(B + 2)² + 2B + 3` for rational inputs of bit
bound `B`. -/
def ratCompareBitCost (B : ℕ) : ℕ := 2*(B+2)*(B+2) + (2*B+3)

/-- The recorded median comparison count multiplied by the rational comparison bit-cost account. -/
def recordedMedianBitTime (r B : ℕ) (l : List ℚ) : ℕ :=
  (recordedMedianProgram r l).2.1 * ratCompareBitCost B

/-- The comparison workspace bit account `2(2B + 3)`. -/
def ratCompareRegisterBits (B : ℕ) : ℕ := 2*(2*B+3)

/-- The bit account for two counters, each of size `natBits n + 1`. -/
def ratCounterBits (n : ℕ) : ℕ := 2*(natBits n + 1)

/-- The peak bit account consisting of `n` rational entries of bound `B`, comparison workspace,
and two counters. -/
def recordedMedianPeakBits (n B : ℕ) : ℕ :=
  n*B + ratCompareRegisterBits B + ratCounterBits n

/-- On `2r + 1` rational samples, the recorded program returns `nativeRationalMedian`,
implementing numerical median repetition amplification [BrassardHoyerTapp1998Counting]. -/
theorem recordedMedianProgram_correct (r : ℕ) (v : Fin (2*r+1) → ℚ) :
    (recordedMedianProgram r (List.ofFn v)).1 = nativeRationalMedian r v := by
  show ((insertionSortCountedRat (List.ofFn v)).1).getD r 0 = nativeRationalMedian r v
  rw [insertionSortCountedRat_eq_mergeSort]
  rfl

/-- For `2r + 1` rational samples of bit length at most `B`, bound comparisons and bit time
quadratically and identify the peak entry and register accounts. -/
theorem recordedMedianProgram_uniform_accounts (r B : ℕ) :
    ∀ (w : Fin (2*r+1) → ℚ), (∀ z, ratBits (w z) ≤ B) →
      ((recordedMedianProgram r (List.ofFn w)).2.1 ≤ (2*r+1)*(2*r+1) ∧
        (recordedMedianProgram r (List.ofFn w)).2.2 = 2*r+1 ∧
        recordedMedianBitTime r B (List.ofFn w)
          ≤ (2*r+1)*(2*r+1)*ratCompareBitCost B ∧
        (recordedMedianProgram r (List.ofFn w)).2.2 * B
          + ratCompareRegisterBits B + ratCounterBits (2*r+1)
          = recordedMedianPeakBits (2*r+1) B) := by
  intro w _hB
  have hlen : (List.ofFn w).length = 2*r+1 := List.length_ofFn
  have hne : List.ofFn w ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  have hc := insertionSortCountedRat_cost_le (List.ofFn w)
  rw [hlen] at hc
  have hp := insertionSortCountedRat_peak (List.ofFn w) hne
  rw [hlen] at hp
  refine ⟨hc, hp, ?_, ?_⟩
  · show (insertionSortCountedRat (List.ofFn w)).2.1 * ratCompareBitCost B
        ≤ (2*r+1)*(2*r+1)*ratCompareBitCost B
    exact Nat.mul_le_mul_right _ hc
  · show (insertionSortCountedRat (List.ofFn w)).2.2 * B + ratCompareRegisterBits B
        + ratCounterBits (2*r+1)
        = (2*r+1)*B + ratCompareRegisterBits B + ratCounterBits (2*r+1)
    rw [hp]

namespace output1

/-- Under unitary preparation, `k ≥ 4`, positive `σ`, and variance at most `σ²`, the recorded
signed-trial median has error exceeding `9σ / 2^k` with probability at most `(143/144)^r`,
together with the stated bit-size, median-resource, and AE query accounts [Montanaro2015]. -/
theorem frontier1 :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
      (j : I) (f : I → ℚ) (σ : ℚ) (k r : ℕ)
      (hA : A ∈ Matrix.unitaryGroup I ℂ), 4 ≤ k → 0 < σ →
      (∑ i, BornProb (A *ᵥ Ket j) i*
          ((f i : ℝ)-(∑ i', BornProb (A *ᵥ Ket j) i'*(f i' : ℝ)))^2) ≤ (σ : ℝ)^2 →
      let hP : ∀ (x : I) (l : Fin (k+2)), nativeLayerPrepare A
          (fun i => max 0 ((f i-f x)/(4*σ))) k l ∈ Matrix.unitaryGroup (I×Bool) ℂ :=
        fun (x : I) (l : Fin (k+2)) => nativeLayerPrepare_unitary A
          (fun i => max 0 ((f i-f x)/(4*σ))) k l.val hA (fun _ => le_max_left _ _)
      let hN : ∀ (x : I) (l : Fin (k+2)), nativeLayerPrepare A
          (fun i => max 0 ((f x-f i)/(4*σ))) k l ∈ Matrix.unitaryGroup (I×Bool) ℂ :=
        fun (x : I) (l : Fin (k+2)) => nativeLayerPrepare_unitary A
          (fun i => max 0 ((f x-f i)/(4*σ))) k l.val hA (fun _ => le_max_left _ _)
      let law := nativeSignedLaw A j f σ k hA hP hN
      let B := nativeTrialBits f σ k
      law.probEvent (fun ω : Fin (2*r+1) → I × (LayerRecord k × LayerRecord k) =>
        9*(σ : ℝ)*(1/2 : ℝ)^k <
          |((recordedMedianProgram r
              (List.ofFn (fun z => nativeSignedOutput f σ k (ω z)))).1 : ℝ)
            -(∑ i', BornProb (A *ᵥ Ket j) i'*(f i' : ℝ))|) ≤ (143/144 : ℝ)^r ∧
      (∀ (ω : Fin (2*r+1) → I × (LayerRecord k × LayerRecord k)),
        (recordedMedianProgram r (List.ofFn (fun z => nativeSignedOutput f σ k (ω z)))).2.1
          ≤ (2*r+1)*(2*r+1) ∧
        (recordedMedianProgram r (List.ofFn (fun z => nativeSignedOutput f σ k (ω z)))).2.2
          = 2*r+1 ∧
        recordedMedianBitTime r B (List.ofFn (fun z => nativeSignedOutput f σ k (ω z)))
          ≤ (2*r+1)*(2*r+1)*ratCompareBitCost B ∧
        (recordedMedianProgram r (List.ofFn (fun z => nativeSignedOutput f σ k (ω z)))).2.2 * B
          + ratCompareRegisterBits B + ratCounterBits (2*r+1)
          = recordedMedianPeakBits (2*r+1) B) ∧
      (∀ z : I × (LayerRecord k × LayerRecord k),
        ratBits (nativeSignedOutput f σ k z) ≤ B) ∧
      (∀ x : I, ((nativeSignedAEPrograms A j f σ k x).map QueryCount).sum =
        2*(k+2)*(2*layerRepetitions k+1)*(layerGrid k-1)) := by
  intro I _ _ A j f σ k r hA hk hσ hvar hP hN law B
  obtain ⟨_hgood, hfail, hledger⟩ :=
    native_signed_rational_trial_and_median I A j f σ k r hA hk hσ hvar
  have hmed : ∀ (ω : Fin (2*r+1) → I × (LayerRecord k × LayerRecord k)),
      ((recordedMedianProgram r (List.ofFn (fun z => nativeSignedOutput f σ k (ω z)))).1 : ℝ)
        = (((List.ofFn (fun z => nativeSignedOutput f σ k (ω z))).mergeSort
            (fun a b => a ≤ b)).getD r 0 : ℝ) := by
    intro ω
    rw [recordedMedianProgram_correct]
    rfl
  have hfail' : law.probEvent (fun ω : Fin (2*r+1) → I × (LayerRecord k × LayerRecord k) =>
      9*(σ : ℝ)*(1/2 : ℝ)^k <
        |(((List.ofFn (fun z => nativeSignedOutput f σ k (ω z))).mergeSort
            (fun a b => a ≤ b)).getD r 0 : ℝ)
          -(∑ i', BornProb (A *ᵥ Ket j) i'*(f i' : ℝ))|) ≤ (143/144 : ℝ)^r := hfail
  refine ⟨?_, ?_, fun z => ratBits_nativeSignedOutput_le f σ k z, hledger⟩
  · simpa only [hmed] using! hfail'
  · intro ω
    exact (recordedMedianProgram_uniform_accounts r B
      (fun z => nativeSignedOutput f σ k (ω z))
      (fun z => ratBits_nativeSignedOutput_le f σ k (ω z)))

end output1

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
