/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MultivarMean21.MainResults.SourceModel
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Data.Fin.Rev

@[expose] public section

/-!
# Directional-Mean Concentration Over the Uniform Grid (Lemma 3.1)

This module formalizes Lemma 3.1 (Section 3.1, p. 9) of Cornelissen and Jerbi
establishing a sub-Gaussian Hoeffding tail bound for `|<u, x>|` and a
Markov/Cauchy--Schwarz tail bound for `E[|<u, X>|]` when `u` is drawn uniformly
from the centered `d`-dimensional grid `G`.

## Main statements

* `lemma3_1_first`: Lemma 3.1 (first bound),
  `Pr_{u ~ G}[alpha |<u, x>| >= ||x||_2] <= 2 exp(-2 / alpha^2)`.
* `lemma3_1_second`: Lemma 3.1 (second bound),
  `Pr_{u ~ G}[alpha E|<u, X>| >= E||X||_2] <= alpha / 2`.

## References

* Cornelissen and Jerbi, 2021, Section 3.1,
  Lemma 3.1, p. 9.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.MultivarMean21.MainResults.BoundedBinary
open Qatlib.Papers.MultivarMean21.MainResults

/-- Each centered grid coordinate lies between `-1/2` and `1/2`. -/
private theorem gridCoord_mem_Icc (m : ℕ) (hm : 0 < m) (j : Fin m) :
    -1 / 2 ≤ gridCoord m j ∧ gridCoord m j ≤ 1 / 2 := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hj : (j : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt j.isLt
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have hcoord : gridCoord m j = ((j : ℝ) + 1 / 2) / (m : ℝ) - 1 / 2 := by
    unfold gridCoord
    field_simp
    ring
  rw [hcoord]
  constructor
  · have hquot : 0 ≤ ((j : ℝ) + 1 / 2) / (m : ℝ) :=
      div_nonneg (by linarith) hmR.le
    linarith
  · have hquot : ((j : ℝ) + 1 / 2) / (m : ℝ) ≤ 1 :=
      (div_le_iff₀ hmR).mpr (by linarith)
    linarith

/-- A centered grid coordinate has square at most `1/4`. -/
private theorem gridCoord_sq_le (m : ℕ) (hm : 0 < m) (j : Fin m) :
    (gridCoord m j) ^ 2 ≤ 1 / 4 := by
  obtain ⟨hl, hu⟩ := gridCoord_mem_Icc m hm j
  nlinarith

/-- Reversing the grid index negates its coordinate. -/
private theorem gridCoord_rev (m : ℕ) (j : Fin m) :
    gridCoord m j.rev = -gridCoord m j := by
  have hm : 0 < m := Nat.pos_of_ne_zero (by intro h; subst m; exact Fin.elim0 j)
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hrev : ((j.rev : Fin m) : ℝ) = (m : ℝ) - 1 - (j : ℝ) := by
    have hnat : j.rev.val + j.val + 1 = m := by simp only [Fin.val_rev]; omega
    have hreal : (j.rev : ℝ) + (j : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hnat
    linarith
  unfold gridCoord
  rw [hrev]
  field_simp
  ring

/-- Centered grid coordinates sum to zero. -/
private theorem sum_gridCoord_eq_zero (m : ℕ) :
    ∑ j : Fin m, gridCoord m j = 0 := by
  have h := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin m)) (gridCoord m)
  simp only [Fin.revPerm_apply, gridCoord_rev, Finset.sum_neg_distrib] at h
  linarith

/-- The uniform weight of a nonempty grid is positive. -/
private theorem gridWeight_pos (d m : ℕ) (hm : 0 < m) : 0 < gridWeight d m := by
  unfold gridWeight
  positivity

/-- Uniform grid weights sum to one. -/
private theorem sum_gridWeight_eq_one (d m : ℕ) (hm : 0 < m) :
    ∑ _j : Fin d → Fin m, gridWeight d m = 1 := by
  simp only [gridWeight, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  exact mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr hm.ne'))

/-- The squared Euclidean norm is the sum of coordinate squares. -/
private theorem l2Nat_sq {d : ℕ} (y : Vec d) :
    (l2Nat y) ^ 2 = ∑ i, (y i) ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (y i))

/-- A uniform centered grid coordinate satisfies a Gaussian exponential bound. -/
private theorem avg_exp_gridCoord_le (m : ℕ) (hm : 0 < m) (s : ℝ) :
    (m : ℝ)⁻¹ * ∑ j : Fin m, Real.exp (s * gridCoord m j) ≤ Real.exp (s ^ 2 / 8) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hpoint (j : Fin m) : Real.exp (s * gridCoord m j) ≤
      (gridCoord m j + 1 / 2) * Real.exp (s / 2) +
        (1 / 2 - gridCoord m j) * Real.exp (-s / 2) := by
    obtain ⟨hl, hu⟩ := gridCoord_mem_Icc m hm j
    have h := convexOn_exp.2 (Set.mem_univ (s / 2)) (Set.mem_univ (-s / 2))
      (by linarith : 0 ≤ gridCoord m j + 1 / 2)
      (by linarith : 0 ≤ 1 / 2 - gridCoord m j)
      (by ring : (gridCoord m j + 1 / 2) + (1 / 2 - gridCoord m j) = 1)
    calc
      _ = Real.exp ((gridCoord m j + 1 / 2) * (s / 2) +
          (1 / 2 - gridCoord m j) * (-s / 2)) := by congr 1; ring
      _ ≤ _ := by simpa only [smul_eq_mul] using h
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ j : Fin m,
        ((gridCoord m j + 1 / 2) * Real.exp (s / 2) +
          (1 / 2 - gridCoord m j) * Real.exp (-s / 2)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hpoint j) (by positivity)
    _ = Real.cosh (s / 2) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        sum_gridCoord_eq_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, zero_add, sub_zero, Real.cosh_eq]
      field_simp
    _ ≤ Real.exp ((s / 2) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
    _ = _ := by congr 1; ring

/-- The directional exponential moment factors over independent grid coordinates. -/
private theorem mgf_gridPoint_le {d : ℕ} (m : ℕ) (hm : 0 < m) (t : ℝ) (y : Vec d) :
    ∑ j : Fin d → Fin m, gridWeight d m *
      Real.exp (t * ∑ i : Fin d, gridPoint d m j i * y i) ≤
        Real.exp (t ^ 2 * (∑ i : Fin d, (y i) ^ 2) / 8) := by
  have hfactor (j : Fin d → Fin m) : gridWeight d m *
      Real.exp (t * ∑ i : Fin d, gridPoint d m j i * y i) =
        ∏ i : Fin d, ((m : ℝ)⁻¹ * Real.exp ((t * y i) * gridCoord m (j i))) := by
    have hexp : t * ∑ i : Fin d, gridPoint d m j i * y i =
        ∑ i : Fin d, (t * y i) * gridCoord m (j i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [gridPoint]
      ring
    rw [hexp, Real.exp_sum, Finset.prod_mul_distrib]
    simp [gridWeight]
  simp_rw [hfactor]
  rw [← Fintype.prod_sum (fun (i : Fin d) (k : Fin m) =>
    (m : ℝ)⁻¹ * Real.exp ((t * y i) * gridCoord m k))]
  calc
    _ ≤ ∏ i : Fin d, Real.exp ((t * y i) ^ 2 / 8) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (Real.exp_nonneg _)
      · intro i hi
        simpa only [← Finset.mul_sum] using avg_exp_gridCoord_le m hm (t * y i)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [mul_pow]
      rw [← Finset.sum_div, ← Finset.mul_sum]

/-- Exponential Markov bounds give the one-sided directional tail estimate. -/
private theorem grid_one_sided_le {d : ℕ} (α : ℝ) (hα : 0 < α) (m : ℕ) (hm : 0 < m)
    (x y : Vec d) (hx : 0 < l2Nat x) (hy : ∑ i, (y i) ^ 2 = (l2Nat x) ^ 2) :
    gridProb d m (fun u => l2Nat x ≤ α * ∑ i, u i * y i) ≤
      Real.exp (-2 / α ^ 2) := by
  classical
  let t : ℝ := 4 / (α * l2Nat x)
  have ht : 0 < t := by dsimp [t]; positivity
  have hpoint (j : Fin d → Fin m) :
      (if l2Nat x ≤ α * ∑ i, gridPoint d m j i * y i then 1 else 0 : ℝ) ≤
        Real.exp (-4 / α ^ 2) * Real.exp (t * ∑ i, gridPoint d m j i * y i) := by
    split_ifs with h
    · have hdiv : l2Nat x / α ≤ ∑ i, gridPoint d m j i * y i :=
        (div_le_iff₀ hα).mpr (by simpa only [mul_comm] using h)
      have hmul := mul_le_mul_of_nonneg_left hdiv ht.le
      have heq : t * (l2Nat x / α) = 4 / α ^ 2 := by
        dsimp [t]
        field_simp
      rw [heq] at hmul
      rw [← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by
        simpa only [neg_div, sub_eq_add_neg, add_comm] using sub_nonneg.mpr hmul)
    · positivity
  calc
    _ ≤ ∑ j : Fin d → Fin m, gridWeight d m *
        (Real.exp (-4 / α ^ 2) * Real.exp (t * ∑ i, gridPoint d m j i * y i)) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpoint j)
        (gridWeight_pos d m hm).le
    _ = Real.exp (-4 / α ^ 2) * ∑ j : Fin d → Fin m, gridWeight d m *
        Real.exp (t * ∑ i, gridPoint d m j i * y i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ Real.exp (-4 / α ^ 2) *
        Real.exp (t ^ 2 * (∑ i, (y i) ^ 2) / 8) :=
      mul_le_mul_of_nonneg_left (mgf_gridPoint_le m hm t y) (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add, hy]
      congr 1
      dsimp [t]
      field_simp
      ring

/-- Fixed arXiv:2111.09787, Lemma 3.1 (p. 9), first inequality.  For `α > 0`, `m ≥ 1` and a
nonzero vector `x`, a uniform grid point `u ∼ G` satisfies
`Pr[α · |⟨u,x⟩| ≥ ‖x‖₂] ≤ 2·exp(−2/α²)`.

The hypothesis `0 < ‖x‖₂` is necessary: at `x = 0` the event has probability `1`, and the paper's
bound `2e^{−2/α²}` is smaller than `1` for `α² < 2/log 2`.  The paper's proof divides by
`∑ⱼ |α xⱼ|² = α²‖x‖₂²`, so the hypothesis is implicit in the source. -/
theorem lemma3_1_first {d : ℕ} (α : ℝ) (hα : 0 < α) (m : ℕ) (hm : 0 < m)
    (x : Vec d) (hx : 0 < l2Nat x) :
    gridProb d m (fun u => l2Nat x ≤ α * |∑ i, u i * x i|) ≤ 2 * Real.exp (-2 / α ^ 2) := by
  classical
  have hpos := grid_one_sided_le α hα m hm x x hx (l2Nat_sq x).symm
  have hneg := grid_one_sided_le α hα m hm x (fun i => -x i) hx
    (by simp only [neg_sq]; exact (l2Nat_sq x).symm)
  have hpoint (j : Fin d → Fin m) :
      (if l2Nat x ≤ α * |∑ i, gridPoint d m j i * x i| then 1 else 0 : ℝ) ≤
        (if l2Nat x ≤ α * ∑ i, gridPoint d m j i * x i then 1 else 0) +
        (if l2Nat x ≤ α * ∑ i, gridPoint d m j i * (-x i) then 1 else 0) := by
    have hcover : l2Nat x ≤ α * |∑ i, gridPoint d m j i * x i| →
        (l2Nat x ≤ α * ∑ i, gridPoint d m j i * x i) ∨
          (l2Nat x ≤ α * ∑ i, gridPoint d m j i * (-x i)) := by
      intro h
      by_cases hs : 0 ≤ ∑ i, gridPoint d m j i * x i
      · exact Or.inl (by rwa [abs_of_nonneg hs] at h)
      · right
        simpa only [abs_of_neg (lt_of_not_ge hs), mul_neg, Finset.sum_neg_distrib] using h
    split_ifs <;> norm_num
    tauto
  have hunion : gridProb d m (fun u => l2Nat x ≤ α * |∑ i, u i * x i|) ≤
      gridProb d m (fun u => l2Nat x ≤ α * ∑ i, u i * x i) +
        gridProb d m (fun u => l2Nat x ≤ α * ∑ i, u i * (-x i)) := by
    unfold gridProb
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [mul_add] using
      mul_le_mul_of_nonneg_left (hpoint j) (gridWeight_pos d m hm).le
  linarith

/-- Reverse one coordinate index, preserving the uniform grid. -/
private def flipCoord {d : ℕ} (m : ℕ) (i : Fin d) : Equiv.Perm (Fin d → Fin m) where
  toFun j := Function.update j i (j i).rev
  invFun j := Function.update j i (j i).rev
  left_inv j := by
    funext k
    by_cases h : k = i
    · subst k
      simp
    · simp [Function.update_of_ne h]
  right_inv j := by
    funext k
    by_cases h : k = i
    · subst k
      simp
    · simp [Function.update_of_ne h]

/-- Distinct centered grid coordinates have zero cross moment. -/
private theorem gridCoord_orthogonal {d : ℕ} (m : ℕ) (i k : Fin d) (hik : i ≠ k) :
    ∑ j : Fin d → Fin m, gridCoord m (j i) * gridCoord m (j k) = 0 := by
  have h := Equiv.sum_comp (flipCoord m i)
    (fun j : Fin d → Fin m => gridCoord m (j i) * gridCoord m (j k))
  simp only [flipCoord, Equiv.coe_fn_mk, Function.update_self,
    Function.update_of_ne hik.symm, gridCoord_rev, neg_mul, Finset.sum_neg_distrib] at h
  linarith

/-- The directional second moment is at most one quarter of the squared norm. -/
private theorem grid_second_moment_le {d : ℕ} (m : ℕ) (hm : 0 < m) (y : Vec d) :
    ∑ j : Fin d → Fin m, gridWeight d m * (∑ i, gridPoint d m j i * y i) ^ 2 ≤
      (l2Nat y) ^ 2 / 4 := by
  have hdiag (i : Fin d) :
      ∑ j : Fin d → Fin m, gridWeight d m * (gridCoord m (j i)) ^ 2 ≤ 1 / 4 := by
    calc
      _ ≤ ∑ _j : Fin d → Fin m, gridWeight d m * (1 / 4) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (gridCoord_sq_le m hm (j i)) (gridWeight_pos d m hm).le
      _ = 1 / 4 := by rw [← Finset.sum_mul, sum_gridWeight_eq_one d m hm, one_mul]
  have hcross (i k : Fin d) (hik : i ≠ k) :
      ∑ j : Fin d → Fin m, gridWeight d m *
        ((gridPoint d m j i * y i) * (gridPoint d m j k * y k)) = 0 := by
    calc
      _ = (gridWeight d m * (y i * y k)) *
          ∑ j : Fin d → Fin m, gridCoord m (j i) * gridCoord m (j k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [gridPoint]
        ring
      _ = 0 := by rw [gridCoord_orthogonal m i k hik, mul_zero]
  calc
    _ = ∑ i : Fin d, ∑ k : Fin d, ∑ j : Fin d → Fin m,
        gridWeight d m * ((gridPoint d m j i * y i) * (gridPoint d m j k * y k)) := by
      simp_rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i : Fin d, (y i) ^ 2 *
        ∑ j : Fin d → Fin m, gridWeight d m * (gridCoord m (j i)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [gridPoint]
        ring
      · intro k hk hki
        exact hcross i k hki.symm
      · simp
    _ ≤ ∑ i : Fin d, (y i) ^ 2 * (1 / 4) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hdiag i) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, l2Nat_sq]; ring

/-- Cauchy--Schwarz bounds the absolute directional mean by half the norm. -/
private theorem grid_first_moment_le {d : ℕ} (m : ℕ) (hm : 0 < m) (y : Vec d) :
    ∑ j : Fin d → Fin m, gridWeight d m * |∑ i, gridPoint d m j i * y i| ≤
      l2Nat y / 2 := by
  have hw : 0 ≤ gridWeight d m := (gridWeight_pos d m hm).le
  have hsqrt : Real.sqrt (gridWeight d m) ^ 2 = gridWeight d m := Real.sq_sqrt hw
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d → Fin m))
    (fun _ => Real.sqrt (gridWeight d m))
    (fun j => Real.sqrt (gridWeight d m) * |∑ i, gridPoint d m j i * y i|)
  simp only [mul_pow, sq_abs, hsqrt] at hcs
  have hleft : (∑ j : Fin d → Fin m, Real.sqrt (gridWeight d m) *
      (Real.sqrt (gridWeight d m) * |∑ i, gridPoint d m j i * y i|)) =
        ∑ j : Fin d → Fin m, gridWeight d m * |∑ i, gridPoint d m j i * y i| := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_assoc, ← pow_two, hsqrt]
  rw [hleft, sum_gridWeight_eq_one d m hm, one_mul] at hcs
  have hsecond := grid_second_moment_le m hm y
  have hn : 0 ≤ l2Nat y := Real.sqrt_nonneg _
  nlinarith

/-- Fixed arXiv:2111.09787, Lemma 3.1 (p. 9), second inequality.  For `α > 0`, `m ≥ 1` and a
random variable `X` with `E[‖X‖₂] > 0`, a uniform grid point satisfies
`Pr[α · E|⟨u,X⟩| ≥ E‖X‖₂] ≤ α/2`.

The hypothesis `0 < E[‖X‖₂]` is necessary: for `X ≡ 0` the event has probability `1`, exceeding
`α/2` when `α < 2`; the paper's proof divides by `E[‖X‖₂]`. -/
theorem lemma3_1_second {d : ℕ} (α : ℝ) (hα : 0 < α) (m : ℕ) (hm : 0 < m)
    (r : FinRV d) (hX : 0 < r.expectedNorm) :
    gridProb d m (fun u => r.expectedNorm ≤ α * r.absDirectionalMean u) ≤ α / 2 := by
  classical
  have hmean (u : Vec d) : 0 ≤ r.absDirectionalMean u :=
    Finset.sum_nonneg fun ω _ => mul_nonneg (r.P_nonneg ω) (abs_nonneg _)
  have hpoint (j : Fin d → Fin m) :
      (if r.expectedNorm ≤ α * r.absDirectionalMean (gridPoint d m j) then 1 else 0 : ℝ) ≤
        (α / r.expectedNorm) * r.absDirectionalMean (gridPoint d m j) := by
    split_ifs with h
    · rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hX).mpr (by simpa only [one_mul] using h)
    · exact mul_nonneg (div_nonneg hα.le hX.le) (hmean _)
  calc
    _ ≤ ∑ j : Fin d → Fin m, gridWeight d m *
        ((α / r.expectedNorm) * r.absDirectionalMean (gridPoint d m j)) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpoint j)
        (gridWeight_pos d m hm).le
    _ = (α / r.expectedNorm) * ∑ ω, r.P ω *
        ∑ j : Fin d → Fin m, gridWeight d m *
          |∑ i, gridPoint d m j i * r.X ω i| := by
      simp only [FinRV.absDirectionalMean, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω hω
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ (α / r.expectedNorm) * ∑ ω, r.P ω * (l2Nat (r.X ω) / 2) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hα.le hX.le)
      exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
        (grid_first_moment_le m hm (r.X ω)) (r.P_nonneg ω)
    _ = α / 2 := by
      simp only [← mul_div_assoc]
      rw [← Finset.sum_div]
      rw [← FinRV.expectedNorm]
      field_simp

end Qatlib.Papers.MultivarMean21.MainResults.BoundedBinary
