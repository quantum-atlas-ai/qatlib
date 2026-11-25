/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamEfficiency10.SuzukiWord.SourceDefinitions
public import Qatlib.Papers.HamEfficiency10.SuzukiWord.SourceRecursive
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

/-!
# The printed Suzuki coefficient-mass constants

Equations (6) and (30) of arXiv:1005.1318v3 include a factor linear in
the order parameter. Compare the pinned constants with those printed in
the paper and expose a counterexample to the proposed uniform comparison.
-/

set_option autoImplicit false

open Qatlib.Papers.HamEfficiency10.SuzukiWord
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.HamEfficiency10.SuzukiWord

/-- The two-term constant of Eq. (6) at order `2k`. -/
noncomputable def sourceTwoMass (k : ℕ) : ℝ :=
  (8 / 3 : ℝ) * (k : ℝ) * (5 / 3 : ℝ) ^ (k - 1)

/-- The `m`-term constant of Eq. (30) at order `2k`. -/
noncomputable def sourceManyMass (m k : ℕ) : ℝ :=
  (m : ℝ) * (4 / 3 : ℝ) * (k : ℝ) * (5 / 3 : ℝ) ^ (k - 1)

/-- The pinned two-term coefficient assumption is stronger than Eq. (6) for positive order. -/
theorem twoMass_le_source {k : ℕ} (hk : 1 ≤ k) : scalingConstant k ≤ sourceTwoMass k := by
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  unfold scalingConstant sourceTwoMass
  gcongr
  exact (mul_one (8 / 3 : ℝ)).symm.le.trans
    (mul_le_mul_of_nonneg_left hk' (by norm_num))

/-- At order parameter nine the pinned many-term constant exceeds Eq. (30) already
for one term. A uniform comparison in the other direction would fail. -/
theorem sourceManyMass_lt_pinned_nine :
    sourceManyMass 1 9 < manyTermScalingConstant 1 9 := by
  norm_num [sourceManyMass, manyTermScalingConstant]

/-- The printed two-term constant is the two-summand case of Eq. (30). -/
theorem sourceManyMass_two (k : ℕ) : sourceManyMass 2 k = sourceTwoMass k := by
  unfold sourceManyMass sourceTwoMass
  norm_num

private theorem recursion_factor_bound (level : ℕ) :
    let u := recursiveSuzukiScale level
    (4 * |u| + |1 - 4 * u|) * ((level : ℝ) + 1) ≤ (5 / 3 : ℝ) * ((level : ℝ) + 2) := by
  dsimp only
  let x := (level : ℝ) + 1
  let y := 1 / (2 * x + 1)
  have hx : 0 < x := by dsimp [x]; positivity
  have hx1 : 1 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) level]
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hy1 : y ≤ 1 := by
    dsimp [y]
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have hp : (4 : ℝ) ^ y ≤ 1 + 3 * y := by
    have h := (convexOn_rpow_left (b := 4) (by norm_num)).2
      (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
      (sub_nonneg.mpr hy1) hy0 (sub_add_cancel 1 y)
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.rpow_zero, Real.rpow_one] at h
    linarith
  have hlow : 6 * x / (2 * x + 1) ≤ 4 - (4 : ℝ) ^ y := by
    have he : 6 * x / (2 * x + 1) = 3 - 3 * y := by
      dsimp [y]
      field_simp
      ring
    rw [he]
    linarith
  have hz : 0 < 4 - (4 : ℝ) ^ y := (by positivity : 0 < 6 * x / (2 * x + 1)).trans_le hlow
  have hu : recursiveSuzukiScale level ≤ (2 * x + 1) / (6 * x) := by
    have hy : 1 / (2 * level + 3 : ℝ) = y := by
      dsimp [y, x]
      congr 1
      ring
    rw [recursiveSuzukiScale, hy]
    rw [← one_div]
    apply (div_le_iff₀ hz).2
    have hm := mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ (2 * x + 1) / (6 * x))
    have he : ((2 * x + 1) / (6 * x)) * (6 * x / (2 * x + 1)) = 1 := by
      field_simp
    simpa only [he] using hm
  have hscale := (recursiveSuzukiScale_bounds level).1
  have hu0 : 0 ≤ recursiveSuzukiScale level := by linarith
  have huneg : 1 - 4 * recursiveSuzukiScale level ≤ 0 := by linarith
  have hsucc : ((level : ℝ) + 2) = x + 1 := by dsimp [x]; ring
  rw [abs_of_nonneg hu0, abs_of_nonpos huneg, hsucc]
  change (4 * recursiveSuzukiScale level + -(1 - 4 * recursiveSuzukiScale level)) * x ≤
    (5 / 3 : ℝ) * (x + 1)
  have hm := mul_le_mul_of_nonneg_right hu hx.le
  have he : ((2 * x + 1) / (6 * x)) * x = (2 * x + 1) / 6 := by field_simp
  rw [he] at hm
  nlinarith only [hm]

private theorem mass_append {I : Type} [Fintype I] [DecidableEq I]
    (xs ys : List (Matrix I I ℂ)) :
    suzukiMass (xs ++ ys) = suzukiMass xs + suzukiMass ys := by
  simp only [suzukiMass, List.map_append, List.sum_append]

private theorem mass_scale {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (a : ℝ) :
    suzukiMass (xs.map (fun X => a • X)) = |a| * suzukiMass xs := by
  induction xs with
  | nil => simp [suzukiMass]
  | cons X xs ih =>
      simpa [suzukiMass, norm_smul, Real.norm_eq_abs, mul_add] using
        congrArg (fun s => |a| * ‖X‖ + s) ih

/-- The actual recursive product's generator norm sum is at most the base norm sum times
the order parameter and the geometric factor in the paper's coefficient bound. -/
theorem recursive_mass_linear {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (level : ℕ) :
    suzukiMass (recursiveSuzukiGenerators xs level) ≤
      ((level : ℝ) + 1) * (5 / 3 : ℝ) ^ level * suzukiMass xs := by
  have hbase : 0 ≤ suzukiMass xs := by
    unfold suzukiMass
    exact List.sum_nonneg (by simp)
  induction level with
  | zero =>
      have hrev : suzukiMass xs.reverse = suzukiMass xs := by
        simp only [suzukiMass, List.map_reverse, List.sum_reverse]
      simp only [recursiveSuzukiGenerators, mass_append, mass_scale, hrev, Nat.cast_zero,
        zero_add, pow_zero, mul_one, one_mul]
      linarith [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  | succ level ih =>
      let u := recursiveSuzukiScale level
      let b := (5 / 3 : ℝ) ^ level * suzukiMass xs
      have hb : 0 ≤ b := by dsimp [b]; positivity
      let a := 4 * |u| + |1 - 4 * u|
      have ha : 0 ≤ a := by dsimp [a]; positivity
      calc
        _ = a * suzukiMass (recursiveSuzukiGenerators xs level) := by
          simp only [recursiveSuzukiGenerators, mass_append, mass_scale, a, u]
          ring
        _ ≤ a * (((level : ℝ) + 1) * b) := by
          apply mul_le_mul_of_nonneg_left _ ha
          simpa only [b, mul_assoc] using ih
        _ = (a * ((level : ℝ) + 1)) * b := (mul_assoc _ _ _).symm
        _ ≤ ((5 / 3 : ℝ) * ((level : ℝ) + 2)) * b :=
          mul_le_mul_of_nonneg_right (recursion_factor_bound level) hb
        _ = _ := by
          simp only [b, Nat.cast_succ, pow_succ]
          ring

/-- With normalized input mass, the actual source word obeys the printed many-term constant. -/
theorem sourceWord_mass_le {I : Type} [Fintype I] [DecidableEq I]
    (H : List (Matrix I I ℂ)) {k : ℕ} (hk : 0 < k)
    (h : suzukiMass (SourceRecursive.signed H) ≤ (H.length : ℝ)) :
    suzukiMass (SourceRecursive.sourceWord H k) ≤ sourceManyMass H.length k := by
  have hcast : (((k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel hk : k - 1 + 1 = k)
  have hcoeff : 0 ≤ (k : ℝ) * (5 / 3 : ℝ) ^ (k - 1) := by positivity
  calc
    _ ≤ (k : ℝ) * (5 / 3 : ℝ) ^ (k - 1) * suzukiMass (SourceRecursive.signed H) := by
      simpa only [SourceRecursive.sourceWord, hcast] using
        recursive_mass_linear (SourceRecursive.signed H) (k - 1)
    _ ≤ (k : ℝ) * (5 / 3 : ℝ) ^ (k - 1) * (H.length : ℝ) :=
      mul_le_mul_of_nonneg_left h hcoeff
    _ ≤ _ := by
      unfold sourceManyMass
      have hn : 0 ≤ (H.length : ℝ) := Nat.cast_nonneg _
      nlinarith only [mul_nonneg hcoeff hn]

end Qatlib.Papers.HamEfficiency10.SuzukiWord
