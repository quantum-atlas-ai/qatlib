/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Papers.QConvexOpt18.MainResults.HullBound.SourceHullBound
import Qatlib.Papers.QConvexOpt18.MainResults.SubgradientGap.SourceSubgradientGap

set_option backward.isDefEq.respectTransparency false

/-!
# QConvexOpt18 Lemma 17: the finite-difference gradient is a uniform linear approximator

van Apeldoorn--Gilyén--Gribling--de Wolf, fixed arXiv:1809.00643v4
(accepted in Quantum 2019-12-03), Lemma 17.

Lemma 17. If `r2 > 0`, `z ∈ ℝ^n` and `f : B₁(z, r2) → ℝ` is convex, then
`sup_{y ∈ B₁(0, r2)} |f (z + y) - f z - ⟨y, ∇^(r2) f (z)⟩| ≤ r2^2 Δ^(r2) f (z) / 2`.

The proof is the source's. Write `d(y) := f (z + y) - f z - ⟨y, ∇^(r2) f (z)⟩`. Then `d` is convex
on `B₁(0, r2)` (a translate of `f` minus an affine functional), `d 0 = 0`, and on the generating
set `S = {± r2 eᵢ}` one computes `d (r2 eᵢ) = d (-(r2 eᵢ)) = r2^2 Δᵢ^(r2) f (z) / 2`. Hence
`|d s| ≤ r2^2 Δ^(r2) f (z) / 2` on `S`, and Lemma 16 (`source_convexHull_symmetric_bound`)
extends the bound to `conv(S)`, which is the `ℓ₁` ball `B₁(0, r2)`.

The two ingredients that make this paper-level statement rather than a restatement of Lemma 16 are
`convex_l1Ball` / `l1Ball_subset_convexHull_symCoordSet` (the `ℓ₁` ball is the convex hull of the
signed coordinate vectors of Definition 8) and `gradDot`, the linear functional `⟨·, ∇^(r2) f z⟩`
built from Mathlib's `LinearMap.proj` so that convexity of the affine part is
`LinearMap.convexOn` rather than a fresh computation.

Boundary: a pointwise sup bound on the `ℓ₁` ball. It does not involve the hypergrid discretisation,
the approximate function `f̃`, or any query model; those belong to Lemmas 12 and 18.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QConvexOpt18.MainResults

open scoped BigOperators

/-- The linear functional `⟨y, g⟩ = ∑ᵢ yᵢ gᵢ`, assembled from the coordinate projections so that its
convexity is `LinearMap.convexOn`. -/
def gradDot {n : ℕ} (g : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i, g i • (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ)

/-- `gradDot g` is the coordinate functional `y ↦ ∑ᵢ yᵢ gᵢ`. -/
theorem gradDot_apply {n : ℕ} (g y : Fin n → ℝ) : gradDot g y = ∑ i, y i * g i := by
  simp only [gradDot, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm (g i) (y i)

/-- The `ℓ₁` ball of radius `r` is convex. -/
theorem convex_l1Ball {n : ℕ} (r : ℝ) : Convex ℝ {v : Fin n → ℝ | l1Norm v ≤ r} := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  show l1Norm (a • x + b • y) ≤ r
  have h1 : l1Norm (a • x + b • y) ≤ l1Norm (a • x) + l1Norm (b • y) := l1Norm_add_le _ _
  have h2 : l1Norm (a • x) = a * l1Norm x := by
    rw [l1Norm_smul, abs_of_pos ha]
  have h3 : l1Norm (b • y) = b * l1Norm y := by
    rw [l1Norm_smul, abs_of_pos hb]
  have h4 : a * l1Norm x ≤ a * r := mul_le_mul_of_nonneg_left hx ha.le
  have h5 : b * l1Norm y ≤ b * r := mul_le_mul_of_nonneg_left hy hb.le
  have h6 : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  linarith

/-- Every point of the `ℓ₁` ball of radius `r` lies in the convex hull of the signed coordinate
vectors `± r eᵢ`. -/
theorem l1Ball_subset_convexHull_symCoordSet {n : ℕ} (i0 : Fin n) (r : ℝ) (hr : 0 < r) :
    {v : Fin n → ℝ | l1Norm v ≤ r} ⊆ convexHull ℝ (symCoordSet (n := n) r) := by
  intro v hv
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hC : Convex ℝ (convexHull ℝ (symCoordSet (n := n) r)) := convex_convexHull ℝ _
  have hpos : r • coordVec i0 ∈ symCoordSet (n := n) r := ⟨i0, Or.inl rfl⟩
  have hneg : -(r • coordVec i0) ∈ symCoordSet (n := n) r := ⟨i0, Or.inr rfl⟩
  have hzero_eq : (1 / 2 : ℝ) • (r • coordVec i0) + (1 / 2 : ℝ) • (-(r • coordVec i0)) = 0 := by
    ext j
    by_cases h : j = i0
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, coordVec,
        Pi.single_apply, h, if_true, smul_eq_mul]
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, coordVec,
        Pi.single_apply, h, if_false, smul_eq_mul]
      ring
  have h0C : (0 : Fin n → ℝ) ∈ convexHull ℝ (symCoordSet (n := n) r) := by
    have hmem := hC (subset_convexHull ℝ _ hpos) (subset_convexHull ℝ _ hneg)
      (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    rwa [hzero_eq] at hmem
  set w : Option (Fin n) → ℝ := fun o => match o with
    | none => 1 - l1Norm v / r
    | some i => |v i| / r with hwdef
  set p : Option (Fin n) → (Fin n → ℝ) := fun o => match o with
    | none => 0
    | some i => if 0 ≤ v i then r • coordVec i else -(r • coordVec i) with hpdef
  have hwr : ∑ i : Fin n, |v i| / r = l1Norm v / r := by
    rw [l1Norm, Finset.sum_div]
  have hw0 : ∀ o ∈ (Finset.univ : Finset (Option (Fin n))), 0 ≤ w o := by
    intro o _
    cases o with
    | none =>
      simp only [hwdef]
      have hle : l1Norm v / r ≤ 1 := (div_le_one hr).mpr hv
      linarith
    | some i =>
      simp only [hwdef]
      positivity
  have hw1 : ∑ o, w o = 1 := by
    rw [Fintype.sum_option]
    simp only [hwdef]
    rw [hwr]
    ring
  have hsum : ∑ o, w o • p o = v := by
    rw [Fintype.sum_option]
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    have hterm : ∀ i : Fin n, (w (some i)) * (p (some i)) j =
        (if i = j then v j else 0) := by
      intro i
      have hw_i : w (some i) = |v i| / r := by simp [hwdef]
      have hp_i : p (some i) = if 0 ≤ v i then r • coordVec i else -(r • coordVec i) := by
        simp [hpdef]
      rw [hw_i, hp_i]
      by_cases hij : i = j
      · rw [hij]
        by_cases hvj : 0 ≤ v j
        · simp only [if_pos hvj, Pi.smul_apply, coordVec_apply_self, smul_eq_mul,
            abs_of_nonneg hvj]
          field_simp
          simp
        · simp only [if_neg hvj, Pi.neg_apply, Pi.smul_apply, coordVec_apply_self,
            smul_eq_mul, abs_of_neg (lt_of_not_ge hvj)]
          field_simp
          simp
      · rw [if_neg hij]
        have hz : (coordVec i) j = 0 := coordVec_apply_ne (Ne.symm hij)
        by_cases hvj : 0 ≤ v i
        · simp only [if_pos hvj, Pi.smul_apply, hz, smul_eq_mul, mul_zero]
        · simp only [if_neg hvj, Pi.neg_apply, Pi.smul_apply, hz, smul_eq_mul, mul_zero,
            neg_zero]
    have hp0 : (w none) * (p none) j = 0 := by simp [hpdef]
    rw [hp0, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq',
      if_pos (Finset.mem_univ j)]
    simp
  have hmem : Finset.univ.centerMass w p ∈ convexHull ℝ (Set.range p) :=
    Finset.centerMass_mem_convexHull (t := Finset.univ) (w := w) hw0
      (by rw [hw1]; exact one_pos) (fun o _ => Set.mem_range_self o)
  have hsub : convexHull ℝ (Set.range p) ⊆ convexHull ℝ (symCoordSet (n := n) r) := by
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    rintro _ ⟨o, rfl⟩
    cases o with
    | none => simpa [hpdef] using h0C
    | some i =>
      simp only [hpdef]
      by_cases h : 0 ≤ v i
      · rw [if_pos h]
        exact subset_convexHull ℝ _ ⟨i, Or.inl rfl⟩
      · rw [if_neg h]
        exact subset_convexHull ℝ _ ⟨i, Or.inr rfl⟩
  have hcm : Finset.univ.centerMass w p = v := by
    rw [Finset.centerMass_eq_of_sum_1 (t := Finset.univ) (w := w) (z := p) (by simpa using hw1)]
    simpa using hsum
  rw [hcm] at hmem
  exact hsub hmem

/-- Lemma 17 of arXiv:1809.00643v4. On the `ℓ₁` ball `B₁(0, r2)`, the finite-difference gradient
`∇^(r2) f (z)` gives a uniform linear approximation of `f` up to `r2^2 Δ^(r2) f (z) / 2`. -/
theorem source_linearApprox_error {n : ℕ} (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) (r2 : ℝ)
    (hr : 0 < r2) (hconv : ConvexOn ℝ (Metric.closedBall z r2) f) :
    ∀ y : Fin n → ℝ, l1Norm y ≤ r2 →
      |f (z + y) - f z - ∑ i, y i * finDiffGradCoord f z r2 i| ≤
        r2 ^ 2 * finDiffLaplace f z r2 / 2 := by
  rcases n with _ | k
  · intro y hy
    have hlap : finDiffLaplace f z r2 = 0 := by simp [finDiffLaplace]
    have hzy : z + y = z := by funext i; exact i.elim0
    have hsum0 : (∑ i : Fin 0, y i * finDiffGradCoord f z r2 i) = 0 := by simp
    rw [hlap, hzy, hsum0]
    simp
  · intro y hy
    have hnn : ∀ i : Fin (k + 1), 0 ≤ finDiffLaplaceCoord f z r2 i := by
      intro i
      obtain ⟨hmem₂, hmem₁⟩ := coordVec_smul_mem_closedBall z hr.le i
      exact finDiffLaplaceCoord_nonneg hconv i hmem₂ hmem₁ hr
    set s0 : Set (Fin (k + 1) → ℝ) := (fun w => z + w) ⁻¹' Metric.closedBall z r2 with hs0
    have htransl : ConvexOn ℝ s0 (fun w => f (z + w)) := hconv.translate_right z
    have hlin : ConvexOn ℝ s0 (fun w : Fin (k + 1) → ℝ => -(gradDot (finDiffGrad f z r2) w)) :=
      (LinearMap.convexOn (-(gradDot (finDiffGrad f z r2))) htransl.1)
    have hd : ConvexOn ℝ s0
        (fun w => f (z + w) - f z - ∑ i, w i * finDiffGradCoord f z r2 i) := by
      have h := (htransl.add hlin).add_const (- f z)
      convert h using 1 <;> first
      | rfl
      | (funext w
         simp [Pi.add_apply, LinearMap.neg_apply, gradDot_apply, finDiffGrad,
           sub_eq_add_neg, add_comm, add_left_comm, add_assoc])
    have hst : convexHull ℝ (symCoordSet (n := k + 1) r2) ⊆ s0 := by
      have hgen : symCoordSet (n := k + 1) r2 ⊆ {v : Fin (k + 1) → ℝ | l1Norm v ≤ r2} := by
        rintro v ⟨i, rfl | rfl⟩
        · show l1Norm (r2 • coordVec i) ≤ r2
          rw [l1Norm_smul, l1Norm_coordVec, abs_of_pos hr]
          simp
        · show l1Norm (-(r2 • coordVec i)) ≤ r2
          rw [← neg_smul, l1Norm_smul, l1Norm_coordVec, abs_neg, abs_of_pos hr]
          simp
      have hball : {v : Fin (k + 1) → ℝ | l1Norm v ≤ r2} ⊆ s0 := by
        intro v hv
        rw [hs0, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
        have hzv : z + v - z = v := by abel
        rw [hzv]
        exact (norm_le_l1Norm v).trans hv
      exact subset_trans (convexHull_min hgen (convex_l1Ball r2)) hball
    have hconvD : ConvexOn ℝ (convexHull ℝ (symCoordSet (n := k + 1) r2))
        (fun w => f (z + w) - f z - ∑ i, w i * finDiffGradCoord f z r2 i) :=
      hd.subset hst (convex_convexHull ℝ _)
    have h0d : f (z + 0) - f z -
        ∑ i, (0 : Fin (k + 1) → ℝ) i * finDiffGradCoord f z r2 i = 0 := by
      simp
    have hr0 : r2 ≠ 0 := ne_of_gt hr
    have hval : ∀ i : Fin (k + 1),
        f (z + r2 • coordVec i) - f z -
            ∑ j, (r2 • coordVec i) j * finDiffGradCoord f z r2 j =
          r2 ^ 2 * finDiffLaplaceCoord f z r2 i / 2 := by
      intro i
      have hsum₁ : ∑ j, (r2 • coordVec i) j * finDiffGradCoord f z r2 j =
          r2 * finDiffGradCoord f z r2 i := by
        have hterm : ∀ j, (r2 • coordVec i) j = r2 * coordVec i j := fun j => by simp
        have hfac : ∀ j, r2 * coordVec i j * finDiffGradCoord f z r2 j =
            r2 * (finDiffGradCoord f z r2 j * coordVec i j) := fun j => by ring
        simp only [hterm, hfac, ← Finset.mul_sum]
        rw [sum_mul_coordVec (fun j => finDiffGradCoord f z r2 j) i]
      have hgrad : r2 * finDiffGradCoord f z r2 i =
          (f (z + r2 • coordVec i) - f (z - r2 • coordVec i)) / 2 := by
        rw [finDiffGradCoord]
        field_simp
      have hlap : r2 ^ 2 * finDiffLaplaceCoord f z r2 i / 2 =
          (f (z + r2 • coordVec i) - 2 * f z + f (z - r2 • coordVec i)) / 2 := by
        rw [finDiffLaplaceCoord]
        field_simp
      rw [hsum₁, hgrad, hlap]
      ring
    have hval_neg : ∀ i : Fin (k + 1),
        f (z + -(r2 • coordVec i)) - f z -
            ∑ j, (-(r2 • coordVec i)) j * finDiffGradCoord f z r2 j =
          r2 ^ 2 * finDiffLaplaceCoord f z r2 i / 2 := by
      intro i
      have hsum₂ : ∑ j, (-(r2 • coordVec i)) j * finDiffGradCoord f z r2 j =
          -(r2 * finDiffGradCoord f z r2 i) := by
        have hterm : ∀ j, (-(r2 • coordVec i)) j = -(r2 * coordVec i j) := fun j => by simp
        have hfac : ∀ j, -(r2 * coordVec i j) * finDiffGradCoord f z r2 j =
            -(r2 * (finDiffGradCoord f z r2 j * coordVec i j)) := fun j => by ring
        simp only [hterm, hfac, Finset.sum_neg_distrib, ← Finset.mul_sum]
        rw [sum_mul_coordVec (fun j => finDiffGradCoord f z r2 j) i]
      have hgrad : r2 * finDiffGradCoord f z r2 i =
          (f (z + r2 • coordVec i) - f (z - r2 • coordVec i)) / 2 := by
        rw [finDiffGradCoord]
        field_simp
      have hlap : r2 ^ 2 * finDiffLaplaceCoord f z r2 i / 2 =
          (f (z + r2 • coordVec i) - 2 * f z + f (z - r2 • coordVec i)) / 2 := by
        rw [finDiffLaplaceCoord]
        field_simp
      rw [hsum₂, hgrad, hlap]
      ring
    have hbd : ∀ s ∈ symCoordSet (n := k + 1) r2,
        |f (z + s) - f z - ∑ i, s i * finDiffGradCoord f z r2 i| ≤
          r2 ^ 2 * finDiffLaplace f z r2 / 2 := by
      rintro s ⟨i, rfl | rfl⟩
      · rw [hval i, abs_of_nonneg (by have := hnn i; positivity)]
        have hle := finDiffLaplaceCoord_le_sum hnn i
        nlinarith [sq_nonneg r2]
      · rw [hval_neg i, abs_of_nonneg (by have := hnn i; positivity)]
        have hle := finDiffLaplaceCoord_le_sum hnn i
        nlinarith [sq_nonneg r2]
    have hyC : y ∈ convexHull ℝ (symCoordSet (n := k + 1) r2) :=
      l1Ball_subset_convexHull_symCoordSet ⟨0, Nat.succ_pos k⟩ r2 hr hy
    exact source_convexHull_symmetric_bound (symCoordSet (n := k + 1) r2)
      (symCoordSet_eq_neg (n := k + 1) r2)
      (fun w => f (z + w) - f z - ∑ i, w i * finDiffGradCoord f z r2 i)
      (r2 ^ 2 * finDiffLaplace f z r2 / 2) hconvD h0d hbd y hyC

end Qatlib.Papers.QConvexOpt18.MainResults
