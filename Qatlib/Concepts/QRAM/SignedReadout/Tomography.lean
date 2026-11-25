/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.AmplitudeAccess.Preparation
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.Count

@[expose] public section

/-!
# Signed readout from two batches of measurement outcomes

[KerenidisLandmanPrakash2020], Appendix G, Algorithm 3, estimates absolute
amplitudes from basis frequencies, stores their square roots in QRAM, and
uses interference outcomes to choose signs. [ChenXueChenEtAl2022], Section 3.3,
uses the sparse classical result for writeback. The functions below consume
the two observed batches and produce the empirical tree and sparse signed
estimate. Their deterministic guarantees hold for every observed batch.
-/

set_option autoImplicit false

namespace Qatlib.Concepts.QRAM.SignedReadout

open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Concepts.QRAM.AmplitudeAccess
open scoped BigOperators

variable {depth : ℕ}

/-- The empirical probability of an address in the basis-measurement batch. -/
noncomputable def frequency (samples : List (Address depth)) (address : Address depth) : ℝ :=
  (samples.count address : ℝ) / samples.length

/-- Store the square roots of the empirical probabilities at the observed addresses. -/
noncomputable def empiricalTree (samples : List (Address depth)) : Tree ℝ depth :=
  refresh (.vacant depth) samples (fun address => Real.sqrt (frequency samples address))

/-- Vacant intervals read as zero at every address. -/
private theorem vacant_read_zero (address : Address depth) :
    read (.vacant depth : Tree ℝ depth) address = 0 := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change read (.vacant depth : Tree ℝ depth) (Fin.tail address) = 0
      exact ih _

/-- Reading the empirical tree returns the square root of the full empirical frequency function. -/
theorem read_empirical_tree (samples : List (Address depth)) (address : Address depth) :
    read (empiricalTree samples) address = Real.sqrt (frequency samples address) := by
  rw [empiricalTree, read_refresh]
  by_cases h : address ∈ samples
  · simp [h]
  · simp [h, vacant_read_zero, frequency, List.count_eq_zero_of_not_mem h]

/-- Loading the empirical distribution maintains the square-sum invariant. -/
theorem valid_empirical_tree (samples : List (Address depth)) :
    Valid (empiricalTree samples) :=
  valid_refresh _ (by trivial) _ _

/-- Empirical basis frequencies sum to one when the measurement batch is nonempty. -/
theorem frequency_sum (samples : List (Address depth)) (h : samples ≠ []) :
    ∑ address, frequency samples address = 1 := by
  have hCount : (∑ address : Address depth, samples.count address) = samples.length := by
    calc
      _ = ∑ address ∈ samples.toFinset, samples.count address := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro address _ hAbsent
        exact List.count_eq_zero_of_not_mem (fun hMem => hAbsent (List.mem_toFinset.mpr hMem))
      _ = _ := List.sum_toFinset_count_eq_length _
  have hLength : (samples.length : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (fun hZero => h (List.length_eq_zero_iff.mp hZero))
  simp only [frequency, ← Finset.sum_div, ← Nat.cast_sum, hCount, div_self hLength]

/-- The empirical QRAM tree has unit root mass for a nonempty measurement batch. -/
theorem empirical_tree_mass (samples : List (Address depth)) (h : samples ≠ []) :
    mass (empiricalTree samples) = 1 := by
  rw [mass_eq_sum _ (valid_empirical_tree samples)]
  have hNonneg (address : Address depth) : 0 ≤ frequency samples address :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  simp_rw [read_empirical_tree, Real.sq_sqrt (hNonneg _)]
  exact frequency_sum samples h

/-- The interference branch amplitude on a clean flag after a Hadamard. -/
noncomputable def positiveAmplitude (state : Address depth → ℝ) (samples : List (Address depth))
    (address : Address depth) : ℝ :=
  (state address + pathAmplitude (empiricalTree samples) address) / 2

/-- Infer a coordinate's sign from the ancilla-zero count at its address. -/
noncomputable def signedCoordinate (samples : List (Address depth))
    (interference : List (Bool × Address depth)) (address : Address depth) : ℝ :=
  let weight := read (empiricalTree samples) address
  if (2 / 5 : ℝ) * interference.length * frequency samples address <
      (interference.count (false, address) : ℝ) then weight else -weight

/-- Return the signed coordinate estimates on the support observed in the first batch. -/
noncomputable def signedEstimates (samples : List (Address depth))
    (interference : List (Bool × Address depth)) : List (Address depth × ℝ) :=
  samples.dedup.map fun address => (address, signedCoordinate samples interference address)

/-- The estimated correction has support only at observed addresses. -/
theorem signed_estimates_support (samples : List (Address depth))
    (interference : List (Bool × Address depth)) :
    (signedEstimates samples interference).map Prod.fst = samples.dedup := by
  simp [signedEstimates, List.map_map, Function.comp_def]

/-- The number of written estimates is bounded by the number of basis measurements. -/
theorem signed_estimates_length_le (samples : List (Address depth))
    (interference : List (Bool × Address depth)) :
    (signedEstimates samples interference).length ≤ samples.length := by
  simpa [signedEstimates] using List.Sublist.length_le (List.dedup_sublist samples)

/-- The inferred sign changes only the sign of the square-root frequency. -/
theorem abs_signed_coordinate (samples : List (Address depth))
    (interference : List (Bool × Address depth)) (address : Address depth) :
    |signedCoordinate samples interference address| = Real.sqrt (frequency samples address) := by
  unfold signedCoordinate
  rw [read_empirical_tree]
  split_ifs <;> simp [abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Unobserved coordinates have zero estimate, the default of the sparse output. -/
theorem signed_coordinate_eq_zero_of_unobserved (samples : List (Address depth))
    (interference : List (Bool × Address depth)) (address : Address depth) (h : address ∉ samples) :
    signedCoordinate samples interference address = 0 := by
  have hFreq : frequency samples address = 0 := by
    simp [frequency, List.count_eq_zero_of_not_mem h]
  exact abs_eq_zero.mp (by rw [abs_signed_coordinate, hFreq, Real.sqrt_zero])

/-- Every readout coordinate has magnitude at most one. -/
theorem signed_coordinate_abs_le_one (samples : List (Address depth))
    (interference : List (Bool × Address depth)) (address : Address depth) :
    |signedCoordinate samples interference address| ≤ 1 := by
  rw [abs_signed_coordinate, ← Real.sqrt_one]
  apply Real.sqrt_le_sqrt
  by_cases h : samples = []
  · simp [h, frequency]
  · rw [← frequency_sum samples h]
    exact Finset.single_le_sum
      (fun i _ => div_nonneg (Nat.cast_nonneg (samples.count i)) (Nat.cast_nonneg samples.length))
      (Finset.mem_univ address)

/-- A coordinate appears at most once in a sparse list formed from distinct addresses. -/
private theorem sum_coordinate_on_nodup {A : Type*} [DecidableEq A] (addresses : List A)
    (hDistinct : addresses.Nodup) (value : A → ℝ) (address : A) :
    (addresses.map (fun i => if i = address then value i else 0)).sum =
      if address ∈ addresses then value address else 0 := by
  induction addresses with
  | nil => simp
  | cons i addresses ih =>
    obtain ⟨hFresh, hTail⟩ := List.nodup_cons.mp hDistinct
    by_cases h : i = address
    · subst i
      simp [ih hTail, hFresh]
    · simp [h, Ne.symm h, ih hTail]

/-- Aggregating the sparse output at one address gives the same estimate as direct
coordinate readout, including its default zero outside the sample support. -/
theorem sum_signed_estimates_at (samples : List (Address depth))
    (interference : List (Bool × Address depth)) (address : Address depth) :
    ((signedEstimates samples interference).map
      (fun pair => if pair.1 = address then pair.2 else 0)).sum =
        signedCoordinate samples interference address := by
  unfold signedEstimates
  rw [List.map_map]
  change (samples.dedup.map (fun i => if i = address then signedCoordinate samples interference i else 0)).sum = _
  rw [sum_coordinate_on_nodup _ (List.nodup_dedup _)]
  by_cases h : address ∈ samples
  · rw [ite_eq_left (List.mem_dedup.mpr h)]
  · rw [ite_eq_right (fun hMem => h (List.mem_dedup.mp hMem))]
    exact (signed_coordinate_eq_zero_of_unobserved samples interference address h).symm

/-- Correct threshold decisions preserve the unsigned error bound in the signed output. -/
theorem signed_coordinate_error_of_count_sign (samples : List (Address depth))
    (interference : List (Bool × Address depth)) (address : Address depth) (value tolerance : ℝ)
    (hMagnitude : |Real.sqrt (frequency samples address) - abs value| ≤ tolerance)
    (hPos : 0 < value → (2 / 5 : ℝ) * interference.length * frequency samples address <
      (interference.count (false, address) : ℝ))
    (hNeg : value < 0 → (interference.count (false, address) : ℝ) ≤
      (2 / 5 : ℝ) * interference.length * frequency samples address) :
    |signedCoordinate samples interference address - value| ≤ tolerance := by
  rcases lt_trichotomy value 0 with hNegative | hZero | hPositive
  · unfold signedCoordinate
    rw [ite_eq_right (not_lt_of_ge (hNeg hNegative)), read_empirical_tree]
    have hRewrite : -Real.sqrt (frequency samples address) - value =
        -(Real.sqrt (frequency samples address) - (-value)) := by ring
    rw [hRewrite, abs_neg, ← abs_of_neg hNegative]
    exact hMagnitude
  · simpa only [hZero, sub_zero, abs_zero, abs_signed_coordinate,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hMagnitude
  · simpa only [signedCoordinate, ite_eq_left (hPos hPositive), read_empirical_tree,
      abs_of_pos hPositive] using hMagnitude

/-- Small true amplitudes need no reliable sign decision. This gives the
`(1 + sqrt 2) * tolerance` bound from Appendix G.4 when the observed frequency is small. -/
theorem signed_coordinate_error_of_small_frequency (samples : List (Address depth))
    (interference : List (Bool × Address depth)) (address : Address depth) (value tolerance : ℝ)
    (hTolerance : 0 ≤ tolerance) (hSmall : |value| ≤ tolerance)
    (hFrequency : frequency samples address ≤ 2 * tolerance ^ 2) :
    |signedCoordinate samples interference address - value| ≤ (1 + Real.sqrt 2) * tolerance := by
  have hSqrt := Real.sqrt_le_sqrt hFrequency
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hTolerance] at hSqrt
  calc
    _ ≤ |signedCoordinate samples interference address| + |value| := by
      rw [sub_eq_add_neg]
      simpa only [abs_neg] using abs_add_le (signedCoordinate samples interference address) (-value)
    _ ≤ Real.sqrt 2 * tolerance + tolerance := by
      rw [abs_signed_coordinate]
      exact add_le_add hSqrt hSmall
    _ = _ := by ring

/-- Rescaling a signed coordinate incurs the magnitude error plus the coordinate error
multiplied by the true norm, provided the estimated coordinate has magnitude at most one. -/
theorem rescale_error (estimatedNorm trueNorm estimate value : ℝ)
    (hNorm : 0 ≤ trueNorm) (hEstimate : |estimate| ≤ 1) :
    |estimatedNorm * estimate - trueNorm * value| ≤
      |estimatedNorm - trueNorm| + trueNorm * |estimate - value| := by
  calc
    _ = |(estimatedNorm - trueNorm) * estimate + trueNorm * (estimate - value)| := by
      congr 1
      ring
    _ ≤ |(estimatedNorm - trueNorm) * estimate| + |trueNorm * (estimate - value)| :=
      abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hNorm]
      exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hEstimate) le_rfl

end Qatlib.Concepts.QRAM.SignedReadout
