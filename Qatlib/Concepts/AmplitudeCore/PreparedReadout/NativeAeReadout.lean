/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalPiApproximation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Order
set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

def nativeAESin (x : ℚ) (k : ℕ) : ℚ :=
  (List.range (8 * (k + 8))).foldl (fun z j =>
    z + (-1 : ℚ) ^ j * x ^ (2 * j + 1) / (Nat.factorial (2 * j + 1) : ℚ)) 0

def nativeAEDecode (M k : ℕ) (z : Fin M) : ℚ :=
  let x := piRatApprox (k + 8) * z.val / M
  max 0 (min 1 ((nativeAESin x k) ^ 2))

private theorem native_fold_sum {R : Type*} [AddCommMonoid R] (f : ℕ → R)
    (n : ℕ) : (List.range n).foldl (fun z j => z + f j) 0 =
      ∑ j ∈ Finset.range n, f j := by
  rw [← List.foldl_map, ← List.sum_eq_foldl]
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem nativeAESin_cast (x : ℚ) (k : ℕ) :
    (nativeAESin x k : ℝ) =
      ∑ j ∈ Finset.range (8 * (k + 8)),
        (-1 : ℝ) ^ j * (x : ℝ) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) := by
  unfold nativeAESin
  rw [native_fold_sum]
  push_cast
  rfl

private theorem native_factorial_block_bound (n : ℕ) :
    (4 : ℝ) ^ (7 + n) / ((7 + n).factorial : ℝ) ≤ 4 * ((2 : ℝ)⁻¹) ^ n := by
  have hf : (Nat.factorial 7 : ℝ) * (8 : ℝ) ^ n ≤ ((7 + n).factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_mul_pow_le_factorial (m := 7) (n := n))
  calc
    _ ≤ (4 : ℝ) ^ (7 + n) / ((Nat.factorial 7 : ℝ) * (8 : ℝ) ^ n) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hf
    _ = ((4 : ℝ) ^ 7 / (Nat.factorial 7 : ℝ)) * ((2 : ℝ)⁻¹) ^ n := by
      rw [pow_add, mul_div_mul_comm, ← div_pow]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num :
      (4 : ℝ) ^ 7 / (Nat.factorial 7 : ℝ) ≤ 4) (by positivity)

theorem nativeAESin_error (x : ℚ) (k : ℕ) (hx : |(x : ℝ)| ≤ 4) :
    |(nativeAESin x k : ℝ) - Real.sin (x : ℝ)| ≤ ((2 : ℝ)⁻¹) ^ (k + 5) := by
  let L := 8 * (k + 8)
  let b := 2 * L - 6
  let f := fun j : ℕ => (-1 : ℝ) ^ j * (x : ℝ) ^ (2 * j + 1) /
    ((2 * j + 1).factorial : ℝ)
  have hb : 7 + b = 2 * L + 1 := by dsimp [b, L]; omega
  have hmajorant : ∀ j : ℕ, ‖f (j + L)‖ ≤
      4 * ((2 : ℝ)⁻¹) ^ b * (1 / 4 : ℝ) ^ j := by
    intro j
    have hm : 2 * (j + L) + 1 = 7 + (b + 2 * j) := by omega
    calc
      _ = |(x : ℝ)| ^ (2 * (j + L) + 1) / ((2 * (j + L) + 1).factorial : ℝ) := by
        simp only [f, norm_div, norm_mul, norm_pow, Real.norm_eq_abs, abs_neg,
          abs_one, one_pow, one_mul,
          abs_of_nonneg (Nat.cast_nonneg ((2 * (j + L) + 1).factorial) :
            (0 : ℝ) ≤ ((2 * (j + L) + 1).factorial : ℝ))]
      _ ≤ (4 : ℝ) ^ (2 * (j + L) + 1) / ((2 * (j + L) + 1).factorial : ℝ) := by
        gcongr
      _ ≤ 4 * ((2 : ℝ)⁻¹) ^ (b + 2 * j) := by
        rw [hm]
        exact native_factorial_block_bound _
      _ = _ := by
        rw [pow_add, pow_mul]
        norm_num
        ring
  have hg : Summable (fun j : ℕ => 4 * ((2 : ℝ)⁻¹) ^ b * (1 / 4 : ℝ) ^ j) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left _
  have hn : Summable (fun j : ℕ => ‖f (j + L)‖) :=
    hg.of_nonneg_of_le (fun _ => norm_nonneg _) hmajorant
  have hs := Real.hasSum_sin (x : ℝ)
  have htail : (nativeAESin x k : ℝ) - Real.sin (x : ℝ) = -∑' j : ℕ, f (j + L) := by
    have hsum := hs.summable.sum_add_tsum_nat_add L
    rw [hs.tsum_eq] at hsum
    rw [nativeAESin_cast]
    change (∑ j ∈ Finset.range L, f j) - Real.sin (x : ℝ) = _
    rw [← hsum]
    abel
  rw [htail, ← Real.norm_eq_abs, norm_neg]
  calc
    _ ≤ ∑' j : ℕ, ‖f (j + L)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' j : ℕ, 4 * ((2 : ℝ)⁻¹) ^ b * (1 / 4 : ℝ) ^ j :=
      hn.tsum_le_tsum hmajorant hg
    _ = (16 / 3 : ℝ) * ((2 : ℝ)⁻¹) ^ b := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)]
      norm_num
      ring
    _ ≤ 8 * ((2 : ℝ)⁻¹) ^ (k + 8) := by
      have he : ((2 : ℝ)⁻¹) ^ b ≤ ((2 : ℝ)⁻¹) ^ (k + 8) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by dsimp [b, L]; omega)
      have hpos : 0 ≤ ((2 : ℝ)⁻¹) ^ b := by positivity
      nlinarith only [he, hpos]
    _ = _ := by
      have he : k + 8 = (k + 5) + 3 := by omega
      rw [he, pow_add]
      norm_num
      ring

private theorem native_clip_square_distance (p s : ℝ) (hs : s ^ 2 ≤ 1) :
    |max 0 (min 1 (p ^ 2)) - s ^ 2| ≤ |p ^ 2 - s ^ 2| := by
  rw [max_eq_right (le_min zero_le_one (sq_nonneg p))]
  by_cases hp : p ^ 2 ≤ 1
  · rw [min_eq_right hp]
  · rw [min_eq_left (by linarith : 1 ≤ p ^ 2),
      abs_of_nonneg (by linarith : 0 ≤ 1 - s ^ 2),
      abs_of_nonneg (by linarith : 0 ≤ p ^ 2 - s ^ 2)]
    linarith

theorem native_ae_computed_scalar_precision :
    ∀ (M k : ℕ) (z : Fin M), 0 ≤ nativeAEDecode M k z ∧
      nativeAEDecode M k z ≤ 1 ∧
      |(nativeAEDecode M k z : ℝ) - aeEstimate M z| ≤ ((2 : ℝ)⁻¹) ^ k := by
  intro M k z
  have hM : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M from by have := z.isLt; omega)
  let r : ℝ := (z.val : ℝ) / M
  let x : ℚ := piRatApprox (k + 8) * z.val / M
  let θ : ℝ := Real.pi * r
  let p : ℝ := nativeAESin x k
  let e : ℝ := ((2 : ℝ)⁻¹) ^ (k + 4)
  have hr0 : 0 ≤ r := div_nonneg (Nat.cast_nonneg _) hM.le
  have hr1 : r ≤ 1 := by
    apply (div_le_iff₀ hM).mpr
    have hz : (z.val : ℝ) < M := by exact_mod_cast z.isLt
    simp only [one_mul]
    exact hz.le
  obtain ⟨hπ0, hπ4, hπerror⟩ := rational_machin_pi_computed_precision.2 (k + 8)
  have hπ0' : 0 ≤ (piRatApprox (k + 8) : ℝ) := by exact_mod_cast hπ0.le
  have hπ4' : (piRatApprox (k + 8) : ℝ) ≤ 4 := by exact_mod_cast hπ4.le
  have hx : (x : ℝ) = (piRatApprox (k + 8) : ℝ) * r := by
    dsimp [x, r]
    push_cast
    ring
  have hx0 : 0 ≤ (x : ℝ) := by rw [hx]; positivity
  have hx4 : |(x : ℝ)| ≤ 4 := by
    rw [abs_of_nonneg hx0, hx]
    have h := mul_le_mul hπ4' hr1 hr0 (by norm_num : (0 : ℝ) ≤ 4)
    simpa using h
  have hθ : |(x : ℝ) - θ| ≤ ((2 : ℝ)⁻¹) ^ (k + 10) := by
    have hπ : |(piRatApprox (k + 8) : ℝ) - Real.pi| ≤
        ((2 : ℝ)⁻¹) ^ (k + 10) := by
      convert hπerror using 1
    calc
      _ = |(piRatApprox (k + 8) : ℝ) - Real.pi| * r := by
        rw [hx]
        dsimp [θ]
        rw [← sub_mul, abs_mul, abs_of_nonneg hr0]
      _ ≤ ((2 : ℝ)⁻¹) ^ (k + 10) * 1 :=
        mul_le_mul hπ hr1 hr0 (by positivity)
      _ = _ := mul_one _
  have hsin : |p - Real.sin θ| ≤ e := by
    have hpert := (Real.abs_sin_sub_sin_le (x : ℝ) θ).trans hθ
    have hsmall : ((2 : ℝ)⁻¹) ^ (k + 10) ≤ ((2 : ℝ)⁻¹) ^ (k + 5) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    calc
      _ ≤ |p - Real.sin (x : ℝ)| + |Real.sin (x : ℝ) - Real.sin θ| := abs_sub_le _ _ _
      _ ≤ ((2 : ℝ)⁻¹) ^ (k + 5) + ((2 : ℝ)⁻¹) ^ (k + 5) :=
        add_le_add (nativeAESin_error x k hx4) (hpert.trans hsmall)
      _ = e := by
        have he : k + 5 = (k + 4) + 1 := by omega
        rw [he, pow_succ]
        dsimp [e]
        ring
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hsabs := Real.abs_sin_le_one θ
  have hpabs : |p| ≤ 1 + e := by
    have h := abs_sub_le p (Real.sin θ) 0
    simp only [sub_zero] at h
    linarith
  have hplus : |p + Real.sin θ| ≤ 2 + e := by
    have h := abs_add_le p (Real.sin θ)
    linarith
  have hsquare : |p ^ 2 - (Real.sin θ) ^ 2| ≤ ((2 : ℝ)⁻¹) ^ k := by
    calc
      _ = |p - Real.sin θ| * |p + Real.sin θ| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ e * (2 + e) := mul_le_mul hsin hplus (abs_nonneg _) he0
      _ ≤ 3 * e := by nlinarith
      _ ≤ _ := by
        dsimp [e]
        rw [pow_add]
        norm_num
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) k]
  refine ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _), ?_⟩
  have hcast : (nativeAEDecode M k z : ℝ) = max 0 (min 1 (p ^ 2)) := by
    simp only [nativeAEDecode, Rat.cast_max, Rat.cast_min, Rat.cast_zero,
      Rat.cast_one, Rat.cast_pow]
    rfl
  have heq : aeEstimate M z = (Real.sin θ) ^ 2 := by
    dsimp [aeEstimate, θ, r]
    rw [mul_div_assoc]
  rw [hcast, heq]
  exact (native_clip_square_distance p (Real.sin θ) (Real.sin_sq_le_one θ)).trans hsquare

def nativeAESinCounted (x : ℚ) (k : ℕ) : ℚ × ℕ :=
  (List.range (8 * (k + 8))).foldl (fun z j =>
    (z.1 + (-1 : ℚ) ^ j * x ^ (2 * j + 1) / (Nat.factorial (2 * j + 1) : ℚ),
      z.2 + 1)) (0, 0)

private theorem native_fold_counter (f : ℕ → ℚ) (xs : List ℕ) (v : ℚ) (c : ℕ) :
    xs.foldl (fun z j => (z.1 + f j, z.2 + 1)) (v, c) =
      (xs.foldl (fun z j => z + f j) v, c + xs.length) := by
  induction xs generalizing v c with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    congr 1
    omega

theorem nativeAESin_value_and_terms (x : ℚ) (k : ℕ) :
    nativeAESinCounted x k = (nativeAESin x k, 8 * (k + 8)) := by
  unfold nativeAESinCounted nativeAESin
  rw [native_fold_counter]
  simp

theorem nativeAESin_counted_zero (k : ℕ) : nativeAESinCounted 0 k = (0, 8 * (k + 8)) := by
  rw [nativeAESin_value_and_terms]
  have hs : nativeAESin 0 k = 0 := by
    unfold nativeAESin
    rw [native_fold_sum]
    apply Finset.sum_eq_zero
    intro j _
    simp
  rw [hs]

theorem native_ae_same_record_bhmt_success :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M k : ℕ) (hM : 2 ≤ M)
      (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ),
      let a := MeasureProb (preparedAAState A j) S
      (∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |(nativeAEDecode M k z : ℝ) - a| ≤
          2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) +
            Real.pi ^ 2 / (M : ℝ) ^ 2 + ((2 : ℝ)⁻¹) ^ k),
        (aeLaw M A j S hA hM).prob z) ≥ 8 / Real.pi ^ 2 := by
  intro I _ _ M k hM A j S hA
  (try dsimp only)
  let a := MeasureProb (preparedAAState A j) S
  let B := 2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) +
    Real.pi ^ 2 / (M : ℝ) ^ 2
  have hsub : (Finset.univ.filter (fun z : Fin M => |aeEstimate M z - a| ≤ B)) ⊆
      (Finset.univ.filter (fun z : Fin M =>
        |(nativeAEDecode M k z : ℝ) - a| ≤ B + ((2 : ℝ)⁻¹) ^ k)) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hold := (Finset.mem_filter.mp hz).2
    have hnative := (native_ae_computed_scalar_precision M k z).2.2
    have htri := abs_sub_le (nativeAEDecode M k z : ℝ) (aeEstimate M z) a
    linarith only [hold, hnative, htri]
  have hmass := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun z _ _ => (aeLaw M A j S hA hM).nonneg z)
  exact (prepared_ae_bhmt_error_and_endpoints M hM A j S hA).1.trans hmass

end Qatlib.Concepts.AmplitudeCore.PreparedReadout
