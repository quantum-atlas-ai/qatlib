/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MacaulayHHL21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4.4 — ℓ2 lower bound in a convex hull

Fixed paper: arXiv:2111.00405, Lemma 4.4 on p.8.

Statement (verbatim): *Suppose `y₁, y₂, …, y_t` are 0/1 vectors and `y₁` has the minimum
Hamming weight. Then every vector in their convex hull `A` has length (ℓ2 norm) at least
`‖y₁‖ / √t`.*

Model choice: the convex hull is a real object and the generators are 0/1, so we model the
generators and their convex combinations over `ℝ` (a 0/1 complex vector is its real
counterpart).  The proof follows the paper: for `y = Σ wᵢ yᵢ` with `wᵢ ≥ 0`, `Σ wᵢ = 1`,
pointwise `(Σᵢ wᵢ yᵢ(k))² ≥ Σᵢ wᵢ² yᵢ(k)` (cross terms are nonnegative), hence
`‖y‖₂² ≥ Σᵢ wᵢ² hᵢ ≥ h·Σᵢ wᵢ² ≥ h/t`, where `h = ‖y₁‖₂²` and `Σᵢ wᵢ² ≥ 1/t` by Cauchy–Schwarz.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.MacaulayHHL21.MainResults.Lemma44

open Qatlib.Papers.MacaulayHHL21.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Squared ℓ2 norm of a real vector. -/
def l2NormSqR (v : ι → ℝ) : ℝ := ∑ i, v i ^ 2

/-- ℓ2 norm of a real vector. -/
def l2NormR (v : ι → ℝ) : ℝ := Real.sqrt (l2NormSqR v)

/-- Real-valued 0/1 vector. -/
def IsZeroOneR (v : ι → ℝ) : Prop := ∀ i, v i = 0 ∨ v i = 1

/-- Hamming weight of a real 0/1 vector. -/
def hammingWeightR (v : ι → ℝ) : ℕ := (univ.filter (fun i => v i = 1)).card

/-- The real convex hull `{Σᵢ wᵢ yᵢ : wᵢ ≥ 0, Σᵢ wᵢ = 1}`. -/
def convexHullR {t : ℕ} (Y : Fin t → ι → ℝ) : Set (ι → ℝ) :=
  {y | ∃ w : Fin t → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ y = fun k => ∑ i, w i * Y i k}

/-- A 0/1 real entry squares to itself. -/
theorem zeroOneR_sq (v : ι → ℝ) (h : IsZeroOneR v) (i : ι) :
    v i ^ 2 = if v i = 1 then (1 : ℝ) else 0 := by
  rcases h i with h0 | h1 <;> simp_all

/-- The squared ℓ2 norm of a real 0/1 vector equals its Hamming weight. -/
theorem zeroOneR_l2NormSq_eq (v : ι → ℝ) (h : IsZeroOneR v) :
    l2NormSqR v = (hammingWeightR v : ℝ) := by
  unfold l2NormSqR hammingWeightR
  simp only [zeroOneR_sq v h, Finset.sum_boole]

/-- The entry sum of a real 0/1 vector equals its Hamming weight. -/
theorem zeroOneR_sum_eq (v : ι → ℝ) (h : IsZeroOneR v) :
    (∑ i, v i) = (hammingWeightR v : ℝ) := by
  unfold hammingWeightR
  have hstep : ∀ i : ι, v i = if v i = 1 then (1 : ℝ) else 0 := by
    intro i; rcases h i with h0 | h1 <;> simp_all
  calc (∑ i, v i) = ∑ i, (if v i = 1 then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl (fun i _ => hstep i)
    _ = ((univ.filter (fun i => v i = 1)).card : ℝ) :=
        Finset.sum_boole (fun i => v i = 1) univ

/-- A real 0/1 entry is nonnegative. -/
theorem zeroOneR_nonneg (v : ι → ℝ) (h : IsZeroOneR v) (i : ι) : 0 ≤ v i := by
  rcases h i with h0 | h1 <;> simp_all

/-- **Lemma 4.4** (arXiv:2111.00405, p.8): a convex combination of 0/1 vectors, one of which
(`Y 0`) has minimum Hamming weight, has ℓ2 norm at least `‖Y 0‖ / √t`. -/
theorem lemma44_convexHull_l2_lowerBound
    {t : ℕ} [NeZero t] (Y : Fin t → ι → ℝ)
    (hZ : ∀ i, IsZeroOneR (Y i))
    (hMin : ∀ i, hammingWeightR (Y 0) ≤ hammingWeightR (Y i))
    {y : ι → ℝ} (hy : y ∈ convexHullR Y) :
    l2NormR (Y 0) ≤ Real.sqrt (t : ℝ) * l2NormR y := by
  classical
  have ht : 0 < t := Nat.pos_of_neZero t
  obtain ⟨w, hw_nonneg, hw_sum, hyeq⟩ := hy
  have hyk : ∀ k, y k = ∑ i, w i * Y i k := fun k => congrFun hyeq k
  set h : ℕ := hammingWeightR (Y 0) with hh
  have hY0sq : l2NormSqR (Y 0) = (h : ℝ) := by
    rw [zeroOneR_l2NormSq_eq (Y 0) (hZ 0), ← hh]
  -- expansion of the squared norm
  have hexp : l2NormSqR y = ∑ k, (∑ i, w i * Y i k) * (∑ i, w i * Y i k) := by
    unfold l2NormSqR
    refine Finset.sum_congr rfl ?_; intro k _
    rw [hyk k, sq]
  -- pointwise lower bound
  have hpoint : ∀ k, (∑ i, w i ^ 2 * Y i k) ≤ (∑ i, w i * Y i k) * (∑ i, w i * Y i k) := by
    intro k
    have ha : ∀ i, 0 ≤ w i * Y i k := fun i =>
      mul_nonneg (hw_nonneg i) (zeroOneR_nonneg (Y i) (hZ i) k)
    have hkey : ∀ i : Fin t,
        (w i * Y i k) * (w i * Y i k) ≤ ∑ j, (w i * Y i k) * (w j * Y j k) := by
      intro i
      refine Finset.single_le_sum (f := fun j => (w i * Y i k) * (w j * Y j k)) ?_ (mem_univ i)
      intro j _
      exact mul_nonneg (ha i) (ha j)
    calc (∑ i, w i ^ 2 * Y i k)
        = ∑ i, (w i * Y i k) * (w i * Y i k) := by
          apply Finset.sum_congr rfl
          intro i _
          have hsq : Y i k * Y i k = Y i k := by
            rcases (hZ i) k with h0 | h1 <;> simp_all
          calc w i ^ 2 * Y i k = w i * w i * (Y i k * Y i k) := by rw [hsq]; ring
            _ = (w i * Y i k) * (w i * Y i k) := by ring
      _ ≤ ∑ i, ∑ j, (w i * Y i k) * (w j * Y j k) :=
            Finset.sum_le_sum (fun i _ => hkey i)
      _ = (∑ i, w i * Y i k) * (∑ j, w j * Y j k) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.mul_sum]
      _ = (∑ i, w i * Y i k) * (∑ i, w i * Y i k) := rfl
  -- accumulate the lower bound
  have hge : (∑ i, w i ^ 2 * (hammingWeightR (Y i) : ℝ)) ≤ l2NormSqR y := by
    calc (∑ i, w i ^ 2 * (hammingWeightR (Y i) : ℝ))
        = ∑ i, w i ^ 2 * (∑ k, Y i k) := by
          refine Finset.sum_congr rfl ?_; intro i _
          rw [zeroOneR_sum_eq (Y i) (hZ i)]
      _ = ∑ i, ∑ k, w i ^ 2 * Y i k := by
          refine Finset.sum_congr rfl ?_; intro i _
          rw [Finset.mul_sum]
      _ = ∑ k, ∑ i, w i ^ 2 * Y i k := Finset.sum_comm
      _ ≤ ∑ k, (∑ i, w i * Y i k) * (∑ i, w i * Y i k) :=
            Finset.sum_le_sum (fun k _ => hpoint k)
      _ = l2NormSqR y := hexp.symm
  -- minimum weight controls every weight
  have hh_min : (h : ℝ) * (∑ i, w i ^ 2) ≤ ∑ i, w i ^ 2 * (hammingWeightR (Y i) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i _
    have hi_nat : h ≤ hammingWeightR (Y i) := by
      rw [hh]; exact hMin i
    have hi : (h : ℝ) ≤ (hammingWeightR (Y i) : ℝ) := by exact_mod_cast hi_nat
    calc (h : ℝ) * w i ^ 2 ≤ (hammingWeightR (Y i) : ℝ) * w i ^ 2 :=
          mul_le_mul_of_nonneg_right hi (sq_nonneg _)
      _ = w i ^ 2 * (hammingWeightR (Y i) : ℝ) := by ring
  -- Cauchy–Schwarz on the convex weights
  have hCSw : (1 : ℝ) ≤ (t : ℝ) * (∑ i, w i ^ 2) := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin t))) (f := fun i => w i)
    rw [Finset.card_univ, Fintype.card_fin, hw_sum] at hcs
    simpa using hcs
  have hsumw2 : 1 / (t : ℝ) ≤ ∑ i, w i ^ 2 := by
    rw [div_le_iff₀ (by exact_mod_cast ht)]
    nlinarith [hCSw]
  -- final chain
  have hlower : (h : ℝ) / (t : ℝ) ≤ l2NormSqR y := by
    calc (h : ℝ) / (t : ℝ) = (h : ℝ) * (1 / (t : ℝ)) := by rw [mul_one_div]
      _ ≤ (h : ℝ) * (∑ i, w i ^ 2) :=
            mul_le_mul_of_nonneg_left hsumw2 (by positivity)
      _ ≤ ∑ i, w i ^ 2 * (hammingWeightR (Y i) : ℝ) := hh_min
      _ ≤ l2NormSqR y := hge
  rcases Nat.eq_zero_or_pos h with hzero | hpos
  · have hY00 : l2NormR (Y 0) = 0 := by
      rw [l2NormR, hY0sq, hzero]; simp
    rw [hY00]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hpos
    have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    have hratio : (h : ℝ) / (t : ℝ) ≤ l2NormSqR y := hlower
    have hsqrt_le : Real.sqrt ((h : ℝ) / (t : ℝ)) ≤ l2NormR y := by
      rw [l2NormR]
      exact Real.sqrt_le_sqrt hratio
    have hnormY0 : l2NormR (Y 0) = Real.sqrt (h : ℝ) := by
      rw [l2NormR, hY0sq]
    calc l2NormR (Y 0) = Real.sqrt (h : ℝ) := hnormY0
      _ = Real.sqrt (t : ℝ) * Real.sqrt ((h : ℝ) / (t : ℝ)) := by
            rw [← Real.sqrt_mul htpos.le]
            congr 1
            field_simp
      _ ≤ Real.sqrt (t : ℝ) * l2NormR y :=
            mul_le_mul_of_nonneg_left hsqrt_le (Real.sqrt_nonneg _)

end Qatlib.Papers.MacaulayHHL21.MainResults.Lemma44
