/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtLinearSolve.Waterfill

/-!
# Rational bisection for water-fill optimization

This module computes rational water-fill energies and bisects a level bracket to approach a
prescribed energy. It proves exact bracket widths and quantitative bounds for energy, fill
increments, and normalized target overlap in the water-fill optimization setting of
[OzolsRoettelerRoland2013].

## Main statements

* `computed_waterlevel_actual_bracket_and_work`: Verify the bisection bracket and its width.
* `computed_waterlevel_fixed_energy_optimal_precision`: Bound the normalized overlap deficit at
  the computed level.

## References

* [Ozols et al., 2013][OzolsRoettelerRoland2013]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError

open Qatlib.Concepts.NativeNumerics.WaterFilling

namespace Qatlib.Concepts.Waterfill.LevelSearch
open scoped Classical BigOperators

/-- The rational sum of squares of the filled coordinates at a given level. -/
def computedWaterEnergy {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) : ℚ :=
  ∑ j, (waterFill π σ γ j)^2

/-- The rational level one plus the sum of source-to-target ratios. -/
def computedWaterHigh {m : ℕ} (π σ : Fin m → ℚ) : ℚ := 1+∑ j, π j/σ j

/-- The interval obtained by repeatedly bisecting the initial level bracket according to whether
the midpoint energy is below `q`. -/
def computedWaterBracket {m : ℕ} (π σ : Fin m → ℚ) (q : ℚ) : ℕ → ℚ×ℚ
  | 0 => (0,computedWaterHigh π σ)
  | k+1 => let b := computedWaterBracket π σ q k
           let mid := (b.1+b.2)/2
           if computedWaterEnergy π σ mid < q then (mid,b.2) else (b.1,mid)

/-- The upper endpoint of the rational bisection bracket after `k` steps. -/
def computedWaterLevel {m : ℕ} (π σ : Fin m → ℚ) (q : ℚ) (k : ℕ) : ℚ :=
  (computedWaterBracket π σ q k).2

/-- The real cast of the computed rational energy equals `waterMass`. -/
theorem computedWaterEnergy_cast {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    (computedWaterEnergy π σ γ : ℝ) = waterMass π σ γ := by
  simp [computedWaterEnergy, waterMass]

/-- For nonnegative source and target, computed energy is monotone between nonnegative levels. -/
theorem computedWaterEnergy_mono {m : ℕ} (π σ : Fin m → ℚ)
    (h : ∀ j, 0 ≤ π j ∧ 0 ≤ σ j) {a b : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) :
    computedWaterEnergy π σ a ≤ computedWaterEnergy π σ b := by
  apply Finset.sum_le_sum
  intro j _
  have h0 : 0 ≤ waterFill π σ a j := le_min (h j).1 (mul_nonneg ha (h j).2)
  have hle : waterFill π σ a j ≤ waterFill π σ b j :=
    min_le_min_left _ (mul_le_mul_of_nonneg_right hab (h j).2)
  nlinarith

/-- For a nonnegative source and strictly positive target, `computedWaterHigh` is positive and
its fill energy equals the full source energy. -/
theorem computedWaterHigh_saturates {m : ℕ} (π σ : Fin m → ℚ)
    (h : ∀ j, 0 ≤ π j ∧ 0 < σ j) :
    0 < computedWaterHigh π σ ∧
      computedWaterEnergy π σ (computedWaterHigh π σ) = ∑ j, (π j)^2 := by
  have hn (j : Fin m) : 0 ≤ π j / σ j := div_nonneg (h j).1 (h j).2.le
  have hs : (0:ℚ) ≤ ∑ j, π j / σ j := Finset.sum_nonneg fun j _ => hn j
  refine ⟨by unfold computedWaterHigh; linarith, ?_⟩
  apply Finset.sum_congr rfl
  intro j _
  have hj : π j / σ j ≤ ∑ i, π i / σ i :=
    Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ j)
  have hb : π j ≤ computedWaterHigh π σ * σ j :=
    (div_le_iff₀ (h j).2).mp (by unfold computedWaterHigh; linarith)
  rw [waterFill, min_eq_left hb]

/-- For a feasible target energy, the `k`th bisection interval has nonnegative ordered
endpoints, brackets the target energy, and has width `computedWaterHigh π σ / 2 ^ k`; see
[OzolsRoettelerRoland2013]. -/
theorem computed_waterlevel_actual_bracket_and_work
    (m k : ℕ) (π σ : Fin m → ℚ) (q : ℚ)
    (h : ∀ j, 0 ≤ π j ∧ 0 < σ j) (hq : 0 ≤ q) (hqmax : q ≤ ∑ j, (π j)^2) :
    let b := computedWaterBracket π σ q k
    0 ≤ b.1 ∧ b.1 ≤ b.2 ∧ computedWaterEnergy π σ b.1 ≤ q ∧
      q ≤ computedWaterEnergy π σ b.2 ∧
      b.2-b.1 = computedWaterHigh π σ/(2:ℚ)^k := by
  have hn : ∀ j, 0 ≤ π j ∧ 0 ≤ σ j := fun j => ⟨(h j).1, (h j).2.le⟩
  induction k with
  | zero =>
    dsimp [computedWaterBracket]
    have hh := computedWaterHigh_saturates π σ h
    refine ⟨le_refl _, hh.1.le, ?_, by rw [hh.2]; exact hqmax, by simp⟩
    simpa [computedWaterEnergy, waterFill, min_eq_right (h _).1] using! hq
  | succ k ih =>
    (try dsimp only at ih)
    obtain ⟨hl, hlh, hel, heh, hw⟩ := ih
    dsimp only [computedWaterBracket]
    split_ifs with hm
    · refine ⟨by linarith, by linarith, hm.le, heh, ?_⟩
      rw [pow_succ, div_mul_eq_div_div, ← hw]
      ring
    · refine ⟨hl, by linarith, hel, le_of_not_gt hm, ?_⟩
      rw [pow_succ, div_mul_eq_div_div, ← hw]
      ring

/-- With a nonnegative target, each filled-coordinate increment lies between zero and the level
increment times its target coordinate. -/
theorem computedWaterFill_increment {m : ℕ} (π σ : Fin m → ℚ)
    (hσ : ∀ j, 0 ≤ σ j) {a b : ℚ} (hab : a ≤ b) (j : Fin m) :
    0 ≤ waterFill π σ b j - waterFill π σ a j ∧
      waterFill π σ b j - waterFill π σ a j ≤ (b-a)*σ j := by
  have habs := mul_le_mul_of_nonneg_right hab (hσ j)
  dsimp only [waterFill]
  by_cases ha : π j ≤ a*σ j
  · rw [min_eq_left ha, min_eq_left (ha.trans habs)]
    exact ⟨by simp, by nlinarith⟩
  · rw [min_eq_right (le_of_not_ge ha)]
    by_cases hb : π j ≤ b*σ j
    · rw [min_eq_left hb]
      constructor <;> linarith
    · rw [min_eq_right (le_of_not_ge hb)]
      constructor <;> linarith

/-- For nonnegative source and target, the energy increment is at most twice the source-target
overlap times the nonnegative level increment. -/
theorem computedWaterEnergy_increment {m : ℕ} (π σ : Fin m → ℚ)
    (h : ∀ j, 0 ≤ π j ∧ 0 ≤ σ j) {a b : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) :
    computedWaterEnergy π σ b - computedWaterEnergy π σ a ≤
      2*(∑ j, π j*σ j)*(b-a) := by
  rw [computedWaterEnergy, computedWaterEnergy, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, 2*(π j*σ j)*(b-a) := by
      apply Finset.sum_le_sum
      intro j _
      have hi := computedWaterFill_increment π σ (fun i => (h i).2) hab j
      have hx : 0 ≤ waterFill π σ a j := le_min (h j).1 (mul_nonneg ha (h j).2)
      have hy : waterFill π σ b j ≤ π j := min_le_left _ _
      have hxπ : waterFill π σ a j ≤ π j := min_le_left _ _
      have hp := mul_le_mul hi.2 (show waterFill π σ b j + waterFill π σ a j ≤ 2*π j by linarith)
        (by linarith : 0 ≤ waterFill π σ b j + waterFill π σ a j)
        (mul_nonneg (sub_nonneg.mpr hab) (h j).2)
      nlinarith
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- For a nonnegative target, the Euclidean norm of the fill increment is at most the level
increment times the Euclidean norm of the target. -/
theorem computedWaterFill_norm_increment {m : ℕ} (π σ : Fin m → ℚ)
    (hσ : ∀ j, 0 ≤ σ j) {a b : ℚ} (hab : a ≤ b) :
    ‖(WithLp.toLp 2 (fun j => (waterFill π σ b j : ℝ)) : EuclideanSpace ℝ (Fin m)) -
      WithLp.toLp 2 (fun j => (waterFill π σ a j : ℝ))‖ ≤
      ((b-a : ℚ) : ℝ) * ‖(WithLp.toLp 2 (fun j => (σ j : ℝ)) : EuclideanSpace ℝ (Fin m))‖ := by
  let x : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun j => (waterFill π σ b j : ℝ))
  let y : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun j => (waterFill π σ a j : ℝ))
  let s : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun j => (σ j : ℝ))
  have hd : (0:ℝ) ≤ ((b-a : ℚ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hab
  have hs : ‖x-y‖^2 ≤ (((b-a : ℚ) : ℝ)*‖s‖)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ j, (((b-a : ℚ) : ℝ)*(σ j : ℝ))^2 := by
        apply Finset.sum_le_sum
        intro j _
        have hi := computedWaterFill_increment π σ hσ hab j
        have hi0 : (0:ℝ) ≤ (waterFill π σ b j : ℝ)-(waterFill π σ a j : ℝ) := by exact_mod_cast hi.1
        have hi1 : (waterFill π σ b j : ℝ)-(waterFill π σ a j : ℝ) ≤ ((b-a : ℚ) : ℝ)*(σ j : ℝ) := by
          exact_mod_cast hi.2
        change ((waterFill π σ b j : ℝ)-(waterFill π σ a j : ℝ))^2 ≤ _
        nlinarith
      _ = _ := by simp_rw [mul_pow]; rw [← Finset.mul_sum, EuclideanSpace.real_norm_sq_eq]
  have hn : 0 ≤ ((b-a : ℚ) : ℝ)*‖s‖ := mul_nonneg hd (norm_nonneg _)
  change ‖x-y‖ ≤ ((b-a : ℚ) : ℝ)*‖s‖
  nlinarith [norm_nonneg (x-y)]

/-- At a positive level, the water fill maximizes target overlap among nonnegative
source-bounded vectors with no greater squared norm. -/
theorem computedWaterFill_overlap_le {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ)
    (v : Fin m → ℝ) (hγ : 0 < γ)
    (hv : ∀ j, 0 ≤ v j ∧ v j ≤ (π j : ℝ))
    (he : (∑ j, (v j)^2) ≤ waterMass π σ γ) :
    (∑ j, (σ j : ℝ)*v j) ≤ ∑ j, (σ j : ℝ)*(waterFill π σ γ j : ℝ) := by
  have hg : (0:ℝ) < γ := by exact_mod_cast hγ
  have hi (j : Fin m) :
      2*(γ : ℝ)*((σ j : ℝ)*v j-(σ j : ℝ)*(waterFill π σ γ j : ℝ)) ≤
        (v j)^2-(waterFill π σ γ j : ℝ)^2 := by
    by_cases hs : π j ≤ γ*σ j
    · have hs' : (π j : ℝ) ≤ (γ : ℝ)*(σ j : ℝ) := by exact_mod_cast hs
      rw [waterFill, min_eq_left hs]
      nlinarith [mul_nonneg (sub_nonneg.mpr (hv j).2)
        (show 0 ≤ 2*(γ : ℝ)*(σ j : ℝ)-(π j : ℝ)-v j by linarith [(hv j).2])]
    · rw [waterFill, min_eq_right (le_of_not_ge hs), Rat.cast_mul]
      nlinarith [sq_nonneg (v j-(γ : ℝ)*(σ j : ℝ))]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hi j)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hh
  change (∑ j, (v j)^2) ≤ ∑ j, (waterFill π σ γ j : ℝ)^2 at he
  nlinarith

/-- For a source-bounded vector of feasible positive energy `q`, its normalized target overlap
exceeds that of the computed fill by at most `2 * (∑ j, σ j ^ 2) * computedWaterHigh π σ /
(2 ^ k * √q)`, with rational quantities cast to the reals; see [OzolsRoettelerRoland2013]. -/
theorem computed_waterlevel_fixed_energy_optimal_precision
    (m k : ℕ) (π σ : Fin m → ℚ) (q : ℚ) (v : Fin m → ℝ)
    (h : ∀ j, 0 ≤ π j ∧ 0 < σ j) (hq : 0 < q) (hqmax : q ≤ ∑ j, (π j)^2)
    (hv : ∀ j, 0 ≤ v j ∧ v j ≤ (π j : ℝ)) (he : (∑ j, (v j)^2) = (q : ℝ)) :
    let γ := computedWaterLevel π σ q k
    (∑ j, (σ j : ℝ)*v j)/Real.sqrt (q : ℝ) -
      (∑ j, (σ j : ℝ)*(waterFill π σ γ j : ℝ))/Real.sqrt (waterMass π σ γ) ≤
      2*(∑ j, (σ j : ℝ)^2)*(computedWaterHigh π σ : ℝ)/
        ((2:ℝ)^k*Real.sqrt (q : ℝ)) := by
  (try dsimp only)
  let a := (computedWaterBracket π σ q k).1
  let γ := computedWaterLevel π σ q k
  let x : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun j => (waterFill π σ γ j : ℝ))
  let y : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun j => (waterFill π σ a j : ℝ))
  let s : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun j => (σ j : ℝ))
  let R := Real.sqrt (q : ℝ)
  have hb := computed_waterlevel_actual_bracket_and_work m k π σ q h hq.le hqmax
  (try dsimp only at hb)
  have ha : 0 ≤ a := hb.1
  have hag : a ≤ γ := hb.2.1
  have hg0 : 0 ≤ γ := ha.trans hag
  have hlow : waterMass π σ a ≤ (q : ℝ) := by
    rw [← computedWaterEnergy_cast]; exact_mod_cast hb.2.2.1
  have hhigh : (q : ℝ) ≤ waterMass π σ γ := by
    rw [← computedWaterEnergy_cast]; exact_mod_cast hb.2.2.2.1
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  have hR : 0 < R := Real.sqrt_pos.mpr hqr
  have hR2 : R^2 = (q : ℝ) := Real.sq_sqrt hqr.le
  have hg : 0 < γ := by
    by_contra hh
    have hz : γ = 0 := le_antisymm (le_of_not_gt hh) hg0
    have hm : waterMass π σ γ = 0 := by
      rw [hz]; simp [waterMass, waterFill, min_eq_right (h _).1]
    rw [hm] at hhigh
    linarith
  have hx2 : ‖x‖^2 = waterMass π σ γ := by
    rw [EuclideanSpace.real_norm_sq_eq]; rfl
  have hy2 : ‖y‖^2 = waterMass π σ a := by
    rw [EuclideanSpace.real_norm_sq_eq]; rfl
  have hRx : R ≤ ‖x‖ := by nlinarith [norm_nonneg x]
  have hyR : ‖y‖ ≤ R := by nlinarith [norm_nonneg y]
  have hx : 0 < ‖x‖ := hR.trans_le hRx
  have hnx : Real.sqrt (waterMass π σ γ) = ‖x‖ := by
    rw [← hx2, Real.sqrt_sq (norm_nonneg x)]
  have hinc := computedWaterFill_norm_increment π σ (fun j => (h j).2.le) hag
  have hgap : ‖x‖-R ≤ (((γ-a : ℚ) : ℝ))*‖s‖ := by
    have ht := norm_sub_norm_le x y
    change ‖x-y‖ ≤ (((γ-a : ℚ) : ℝ))*‖s‖ at hinc
    linarith
  have hov := computedWaterFill_overlap_le π σ γ v hg hv
    (by rw [he]; exact hhigh)
  have hcs : (∑ j, (σ j : ℝ)*(waterFill π σ γ j : ℝ)) ≤ ‖s‖*‖x‖ := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, x, s,
      WithLp.ofLp_toLp, Pi.star_apply, star_trivial, mul_comm] using! real_inner_le_norm s x
  let C := ∑ j, (σ j : ℝ)*(waterFill π σ γ j : ℝ)
  have hCN : C/‖x‖ ≤ ‖s‖ := (div_le_iff₀ hx).mpr hcs
  have hd : (0:ℝ) ≤ ((γ-a : ℚ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hag
  have hprod : C/‖x‖*(‖x‖-R) ≤ ‖s‖^2*((γ-a : ℚ) : ℝ) := by
    calc
      _ ≤ ‖s‖*(‖x‖-R) := mul_le_mul_of_nonneg_right hCN (sub_nonneg.mpr hRx)
      _ ≤ ‖s‖*(((γ-a : ℚ) : ℝ)*‖s‖) := mul_le_mul_of_nonneg_left hgap (norm_nonneg _)
      _ = _ := by ring
  have hwidth : ((γ-a : ℚ) : ℝ) = (computedWaterHigh π σ : ℝ)/(2:ℝ)^k := by
    exact_mod_cast hb.2.2.2.2
  have hs2 : ‖s‖^2 = ∑ j, (σ j : ℝ)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  rw [hnx]
  change (∑ j, (σ j : ℝ)*v j)/R - C/‖x‖ ≤ _
  have hloss : (∑ j, (σ j : ℝ)*v j)/R - C/‖x‖ ≤
      ‖s‖^2*((γ-a : ℚ) : ℝ)/R := by
    apply (le_div_iff₀ hR).mpr
    have hid : ((∑ j, (σ j : ℝ)*v j)/R-C/‖x‖)*R =
        (∑ j, (σ j : ℝ)*v j)-C+C/‖x‖*(‖x‖-R) := by
      field_simp; ring
    rw [hid]
    change (∑ j, (σ j : ℝ)*v j) ≤ C at hov
    linarith
  calc
    _ ≤ ‖s‖^2*((γ-a : ℚ) : ℝ)/R := hloss
    _ ≤ 2*(‖s‖^2*((γ-a : ℚ) : ℝ)/R) := by
      have hn : 0 ≤ ‖s‖^2*((γ-a : ℚ) : ℝ)/R := by positivity
      linarith
    _ = _ := by rw [hwidth, hs2]; dsimp [R]; ring

end Qatlib.Concepts.Waterfill.LevelSearch
