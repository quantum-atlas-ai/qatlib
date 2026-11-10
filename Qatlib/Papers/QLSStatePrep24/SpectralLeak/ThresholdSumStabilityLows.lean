/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLSStatePrep24.SpectralLeak.ThresholdSumStabilityStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Papers.QLSStatePrep24.SpectralLeak
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace Qatlib.Papers.QLSStatePrep24.SpectralLeak

open Matrix Qatlib.Concepts.QlsReadoutSpec.Amplification Qatlib.Papers.QLSStatePrep24.SpectralLeak
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open scoped Classical BigOperators

private theorem normVec_sq_eq {H : Type} [Fintype H] (v : QState H) :
    normVec v ^ 2 = ∑ i, ‖v i‖ ^ 2 :=
  norm_toEuclidean_fromVec_sq v

private theorem toEuclidean_fromVec_sub {H : Type} [Fintype H] (x y : QState H) :
    toEuclidean_fromVec (x - y) = toEuclidean_fromVec x - toEuclidean_fromVec y := by
  rfl

private theorem normVec_abs_sub {H : Type} [Fintype H] (x y : QState H) :
    |normVec x - normVec y| ≤ normVec (x - y) := by
  have h := abs_norm_sub_norm_le (toEuclidean_fromVec x) (toEuclidean_fromVec y)
  rw [← toEuclidean_fromVec_sub] at h
  simpa [normVec] using! h

private theorem normVec_sq_diff {H : Type} [Fintype H] (x y : QState H)
    (hx : normVec x ≤ 1) (hy : normVec y ≤ 1) :
    |(normVec x) ^ 2 - (normVec y) ^ 2| ≤ 2 * normVec (x - y) := by
  have hnnx : 0 ≤ normVec x := norm_nonneg _
  have hnny : 0 ≤ normVec y := norm_nonneg _
  have hkey : |(normVec x) ^ 2 - (normVec y) ^ 2|
      = |normVec x - normVec y| * (normVec x + normVec y) := by
    rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg hnnx hnny), mul_comm]
  rw [hkey]
  have hsub : |normVec x - normVec y| ≤ normVec (x - y) := normVec_abs_sub x y
  have hsum : normVec x + normVec y ≤ 2 := by linarith
  have hnn : 0 ≤ normVec (x - y) := norm_nonneg _
  have h1 : |normVec x - normVec y| * (normVec x + normVec y)
      ≤ normVec (x - y) * (normVec x + normVec y) :=
    mul_le_mul_of_nonneg_right hsub (add_nonneg hnnx hnny)
  have h2 : normVec (x - y) * (normVec x + normVec y)
      ≤ normVec (x - y) * 2 :=
    mul_le_mul_of_nonneg_left hsum hnn
  linarith

private theorem geom_sum_9 (n : ℕ) : (∑ i ∈ Finset.range n, (9 : ℝ) ^ i) = ((9 : ℝ) ^ n - 1) / 8 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h8 : (8 : ℝ) ≠ 0 := by norm_num
    field_simp
    ring

private theorem geom_sum_9_Icc (a b : ℕ) (hab : a ≤ b) :
    (∑ s ∈ Finset.Icc a b, (9 : ℝ) ^ s) = ((9 : ℝ) ^ (b + 1) - (9 : ℝ) ^ a) / 8 := by
  have hsum : (∑ i ∈ Finset.range (b - a + 1), (9 : ℝ) ^ (a + i))
      = ∑ s ∈ Finset.Icc a b, (9 : ℝ) ^ s := by
    refine Finset.sum_bij (fun i _ => a + i) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢
      omega
    · intro i₁ _ i₂ _ h
      exact Nat.add_left_cancel h
    · intro s hs
      simp only [Finset.mem_Icc] at hs
      refine ⟨s - a, by simp only [Finset.mem_range]; omega, ?_⟩
      show a + (s - a) = s
      omega
    · intro i hi
      rfl
  have hpt : ∀ i ∈ Finset.range (b - a + 1),
      (9 : ℝ) ^ (a + i) = (9 : ℝ) ^ a * (9 : ℝ) ^ i :=
    fun i _ => pow_add (9 : ℝ) a i
  rw [← hsum, Finset.sum_congr rfl hpt, ← Finset.mul_sum, geom_sum_9]
  have h9 : (9 : ℝ) ^ (b + 1) = (9 : ℝ) ^ a * (9 : ℝ) ^ (b - a + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h9]
  have h8 : (8 : ℝ) ≠ 0 := by norm_num
  field_simp

private theorem sum_range_add_one {α : Type} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    (∑ i ∈ Finset.range n, f (i + 1)) = ∑ l ∈ Finset.Icc 1 n, f l := by
  refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢
    omega
  · intro i₁ _ i₂ _ h
    exact Nat.succ.inj h
  · intro l hl
    simp only [Finset.mem_Icc] at hl
    refine ⟨l - 1, by simp only [Finset.mem_range]; omega, ?_⟩
    show (l - 1) + 1 = l
    omega
  · intro i hi
    rfl

private theorem sum_fin_add_one {α : Type} [AddCommMonoid α] (m : ℕ) (f : ℕ → α) :
    (∑ j : Fin m, f (j.val + 1)) = ∑ l ∈ Finset.Icc 1 m, f l :=
  (Fin.sum_univ_eq_sum_range (fun k : ℕ => f (k + 1)) m).trans (sum_range_add_one m f)

private theorem double_sum_scale {I : Type} [Fintype I] {m : ℕ}
    (w : I → Fin m → ℝ) (X : Fin m → ℝ) (c : ℝ) :
    (∑ u, ∑ h, w u h * X h) * c = ∑ u, ∑ h, w u h * (X h * c) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  ring

private theorem double_sum_le {I : Type} [Fintype I] {m : ℕ}
    (w : I → Fin m → ℝ) (X Y : Fin m → ℝ)
    (hw : ∀ u h, 0 ≤ w u h) (hle : ∀ h, X h ≤ Y h) :
    (∑ u, ∑ h, w u h * X h) ≤ ∑ u, ∑ h, w u h * Y h := by
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro h _
  exact mul_le_mul_of_nonneg_left (hle h) (hw u h)

private theorem three_pow_div_sq (a b : ℕ) :
    ((3 : ℝ) ^ a / (3 : ℝ) ^ b) ^ 2 = (9 : ℝ) ^ a / (9 : ℝ) ^ b := by
  rw [div_pow, pow_two, pow_two, ← mul_pow, ← mul_pow]
  norm_num

private theorem weightedBandState_sq {I : Type} [Fintype I] (m : ℕ)
    (γ : I → ℂ) (ζ : ℕ → I → ℂ) :
    (normVec (weightedBandState m γ ζ)) ^ 2
      = ∑ u : I, ∑ h : Fin m, (‖γ u‖ ^ 2 * ‖ζ (h.val + 1) u‖ ^ 2)
          * ((9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m) := by
  rw [normVec_sq_eq]
  show ∑ p : Fin m × I, ‖γ p.2 * ζ (p.1.val + 1) p.2
      * ((3 : ℝ) ^ (p.1.val + 1) / (3 : ℝ) ^ m)‖ ^ 2 = _
  have hpt : ∀ p : Fin m × I,
      ‖γ p.2 * ζ (p.1.val + 1) p.2 * ((3 : ℝ) ^ (p.1.val + 1) / (3 : ℝ) ^ m)‖ ^ 2
        = ‖γ p.2‖ ^ 2 * ‖ζ (p.1.val + 1) p.2‖ ^ 2
            * ((3 : ℝ) ^ (p.1.val + 1) / (3 : ℝ) ^ m) ^ 2 := by
    intro p
    rw [norm_mul, mul_pow, norm_mul, mul_pow]
    rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have h3 : (0 : ℝ) ≤ 3 := by norm_num
    rw [abs_of_nonneg h3]
  rw [Finset.sum_congr rfl fun p _ => hpt p]
  rw [Fintype.sum_prod_type]
  show ∑ x : Fin m, ∑ u : I,
      ‖γ u‖ ^ 2 * ‖ζ (x.val + 1) u‖ ^ 2 * ((3 : ℝ) ^ (x.val + 1) / (3 : ℝ) ^ m) ^ 2 = _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have hre : ∀ x : Fin m,
      ‖γ u‖ ^ 2 * ‖ζ (x.val + 1) u‖ ^ 2 * ((3 : ℝ) ^ (x.val + 1) / (3 : ℝ) ^ m) ^ 2
        = ‖γ u‖ ^ 2 * (‖ζ (x.val + 1) u‖ ^ 2 * ((3 : ℝ) ^ (x.val + 1) / (3 : ℝ) ^ m) ^ 2) :=
    fun x => mul_assoc _ _ _
  rw [Finset.sum_congr rfl (fun x _ => hre x), ← Finset.mul_sum]
  have hR : (∑ h : Fin m, ‖γ u‖ ^ 2 * ‖ζ (h.val + 1) u‖ ^ 2
        * ((9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m))
      = ‖γ u‖ ^ 2 * ∑ h : Fin m, ‖ζ (h.val + 1) u‖ ^ 2 * ((9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m) := by
    have hmul : ∀ h : Fin m, ‖γ u‖ ^ 2 * ‖ζ (h.val + 1) u‖ ^ 2
          * ((9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m)
        = ‖γ u‖ ^ 2 * (‖ζ (h.val + 1) u‖ ^ 2 * ((9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m)) :=
      fun h => mul_assoc _ _ _
    rw [Finset.sum_congr rfl (fun h _ => hmul h), ← Finset.mul_sum]
  rw [hR]
  refine congrArg (‖γ u‖ ^ 2 * ·) ?_
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [three_pow_div_sq]

private theorem thresholdSum_eq {I : Type} [Fintype I] (m l : ℕ)
    (γ : I → ℂ) (ζ : ℕ → I → ℂ) :
    thresholdSum m l γ ζ
      = ∑ u : I, ∑ h : Fin m, (‖γ u‖ ^ 2 * ‖ζ (h.val + 1) u‖ ^ 2)
          * (∑ t : Fin l, (9 : ℝ) ^ (t.val + 1) *
              (if m - l + t.val + 1 < h.val + 1 then (1 : ℝ)
                else (9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m)) := by

  have hBP : ∀ t : Fin l,
      bandPotentialProbability m γ ζ (m - l + t.val + 1) * (9 : ℝ) ^ (t.val + 1)
        = ∑ u : I, ∑ h : Fin m,
            (‖γ u‖ ^ 2 * ‖ζ (h.val + 1) u‖ ^ 2)
              * ((9 : ℝ) ^ (t.val + 1)
                  * (if m - l + t.val + 1 < h.val + 1 then (1 : ℝ)
                      else (9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m)) := by
    intro t
    show (∑ u : I, ‖γ u‖ ^ 2 * ∑ h : Fin m, ‖ζ (h.val + 1) u‖ ^ 2
        * (if m - l + t.val + 1 < h.val + 1 then (1 : ℝ)
            else (9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m)) * (9 : ℝ) ^ (t.val + 1) = _
    have h1 : (∑ u : I, ‖γ u‖ ^ 2 * ∑ h : Fin m, ‖ζ (h.val + 1) u‖ ^ 2
        * (if m - l + t.val + 1 < h.val + 1 then (1 : ℝ)
            else (9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m)) * (9 : ℝ) ^ (t.val + 1)
        = ∑ u : I, (‖γ u‖ ^ 2 * ∑ h : Fin m, ‖ζ (h.val + 1) u‖ ^ 2
            * (if m - l + t.val + 1 < h.val + 1 then (1 : ℝ)
                else (9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m)) * (9 : ℝ) ^ (t.val + 1) :=
      Finset.sum_mul _ _ _
    rw [h1]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    have h2 : (‖γ u‖ ^ 2 * ∑ h : Fin m, ‖ζ (h.val + 1) u‖ ^ 2
        * (if m - l + t.val + 1 < h.val + 1 then (1 : ℝ)
            else (9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m)) * (9 : ℝ) ^ (t.val + 1)
        = ∑ h : Fin m, (‖γ u‖ ^ 2 * ‖ζ (h.val + 1) u‖ ^ 2)
            * ((9 : ℝ) ^ (t.val + 1)
                * (if m - l + t.val + 1 < h.val + 1 then (1 : ℝ)
                    else (9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      by_cases hcond : m - l + t.val + 1 < h.val + 1 <;> simp [hcond]; ring
    exact h2
  show (∑ t : Fin l, bandPotentialProbability m γ ζ (m - l + t.val + 1)
      * (9 : ℝ) ^ (t.val + 1)) = _
  rw [Finset.sum_congr rfl (fun t _ => hBP t)]

  have hcomm : (∑ t : Fin l, ∑ u : I, ∑ h : Fin m,
        (‖γ u‖ ^ 2 * ‖ζ (h.val + 1) u‖ ^ 2)
          * ((9 : ℝ) ^ (t.val + 1)
              * (if m - l + t.val + 1 < h.val + 1 then (1 : ℝ)
                  else (9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m)))
      = ∑ u : I, ∑ h : Fin m, (‖γ u‖ ^ 2 * ‖ζ (h.val + 1) u‖ ^ 2)
          * (∑ t : Fin l, (9 : ℝ) ^ (t.val + 1)
              * (if m - l + t.val + 1 < h.val + 1 then (1 : ℝ)
                  else (9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m)) := by
    have h1 : (∑ t : Fin l, ∑ u : I, ∑ h : Fin m,
          (‖γ u‖ ^ 2 * ‖ζ (h.val + 1) u‖ ^ 2)
            * ((9 : ℝ) ^ (t.val + 1)
                * (if m - l + t.val + 1 < h.val + 1 then (1 : ℝ)
                    else (9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m)))
        = ∑ u : I, ∑ t : Fin l, ∑ h : Fin m,
            (‖γ u‖ ^ 2 * ‖ζ (h.val + 1) u‖ ^ 2)
              * ((9 : ℝ) ^ (t.val + 1)
                  * (if m - l + t.val + 1 < h.val + 1 then (1 : ℝ)
                      else (9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m)) :=
      Finset.sum_comm (s := (Finset.univ : Finset (Fin l))) (t := (Finset.univ : Finset I))
    rw [h1]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    have h2 : (∑ t : Fin l, ∑ h : Fin m,
          (‖γ u‖ ^ 2 * ‖ζ (h.val + 1) u‖ ^ 2)
            * ((9 : ℝ) ^ (t.val + 1)
                * (if m - l + t.val + 1 < h.val + 1 then (1 : ℝ)
                    else (9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m)))
        = ∑ h : Fin m, ∑ t : Fin l,
            (‖γ u‖ ^ 2 * ‖ζ (h.val + 1) u‖ ^ 2)
              * ((9 : ℝ) ^ (t.val + 1)
                  * (if m - l + t.val + 1 < h.val + 1 then (1 : ℝ)
                      else (9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m)) :=
      Finset.sum_comm (s := (Finset.univ : Finset (Fin l))) (t := (Finset.univ : Finset (Fin m)))
    rw [h2]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [← Finset.mul_sum]
  exact hcomm

private theorem threshold_weight_bound (m l : ℕ) (hlm : l ≤ m) (hl : 0 < l)
    (k : ℕ) (_hk1 : 1 ≤ k) (hkm : k ≤ m) :
    let A : ℝ := (9 : ℝ) ^ k / (9 : ℝ) ^ m
    let C : ℝ := ∑ t : Fin l, (9 : ℝ) ^ (t.val + 1) *
      (if m - l + t.val + 1 < k then (1 : ℝ) else A)
    A * (9 : ℝ) ^ l ≤ C ∧ C ≤ (5 / 4) * (A * (9 : ℝ) ^ l) := by
  (try dsimp only)
  set A : ℝ := (9 : ℝ) ^ k / (9 : ℝ) ^ m
  set C : ℝ := ∑ t : Fin l, (9 : ℝ) ^ (t.val + 1) *
    (if m - l + t.val + 1 < k then (1 : ℝ) else A)
  have hApos : 0 < A :=
    div_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)
  have hA : 0 ≤ A := le_of_lt hApos
  have hA1 : A ≤ 1 :=
    div_le_one_of_le₀ (pow_le_pow_right₀ (by norm_num) hkm) (pow_nonneg (by norm_num) _)
  have h9pos : ∀ n : ℕ, 0 < (9 : ℝ) ^ n := fun n => pow_pos (by norm_num) n
  have h9nn : ∀ n : ℕ, 0 ≤ (9 : ℝ) ^ n := fun n => le_of_lt (h9pos n)

  have hcond : ∀ t : Fin l, (m - l + t.val + 1 < k) ↔ (t.val + 1 < k - (m - l)) := by
    intro t
    omega

  have hC : C = ∑ s ∈ Finset.Icc 1 l, (9 : ℝ) ^ s * (if s < (k - (m - l)) then (1 : ℝ) else A) := by
    have hre : C = ∑ t : Fin l, (9 : ℝ) ^ (t.val + 1)
        * (if t.val + 1 < (k - (m - l)) then (1 : ℝ) else A) := by
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have hif : (if m - l + t.val + 1 < k then (1 : ℝ) else A)
          = (if t.val + 1 < (k - (m - l)) then (1 : ℝ) else A) := by
        by_cases h : t.val + 1 < (k - (m - l))
        · have hk : m - l + t.val + 1 < k := (hcond t).2 h
          simp [h, hk]
        · have hk : ¬ m - l + t.val + 1 < k := fun hh => h ((hcond t).1 hh)
          simp [h, hk]
      rw [hif]
    rw [hre]
    exact (sum_fin_add_one l (fun s => (9 : ℝ) ^ s * (if s < (k - (m - l)) then (1 : ℝ) else A)))

  have hsplit : (∑ s ∈ Finset.Icc 1 l, (9 : ℝ) ^ s * (if s < (k - (m - l)) then (1 : ℝ) else A))
      = (∑ s ∈ Finset.Icc 1 l, (if s < (k - (m - l)) then (9 : ℝ) ^ s else 0))
        + (∑ s ∈ Finset.Icc 1 l, (if s < (k - (m - l)) then 0 else A * (9 : ℝ) ^ s)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    by_cases h : s < (k - (m - l)) <;> simp [h, mul_comm]
  have hloweq' : (∑ s ∈ Finset.Icc 1 l, (if s < (k - (m - l)) then (9 : ℝ) ^ s else 0))
      = ∑ s ∈ (Finset.Icc 1 l).filter (fun s => s < (k - (m - l))), (9 : ℝ) ^ s := by
    rw [← Finset.sum_filter]
  have hhigh' : (∑ s ∈ Finset.Icc 1 l, (if s < (k - (m - l)) then 0 else A * (9 : ℝ) ^ s))
      = ∑ s ∈ (Finset.Icc 1 l).filter (fun s => ¬ s < (k - (m - l))), A * (9 : ℝ) ^ s := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun s _ => by by_cases h : s < (k - (m - l)) <;> simp [h])

  have hfilter_low : (Finset.Icc 1 l).filter (fun s => s < (k - (m - l))) = Finset.Icc 1 ((k - (m - l)) - 1) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, by omega⟩
    · intro ⟨h1, h2⟩
      exact ⟨⟨h1, by omega⟩, by omega⟩
  have hlowsum : (∑ s ∈ Finset.Icc 1 l, (if s < (k - (m - l)) then (9 : ℝ) ^ s else 0))
      = ∑ s ∈ Finset.Icc 1 ((k - (m - l)) - 1), (9 : ℝ) ^ s := by
    rw [hloweq', hfilter_low]

  have hgeo_all : (∑ s ∈ Finset.Icc 1 l, (9 : ℝ) ^ s) = ((9 : ℝ) ^ (l + 1) - 9) / 8 := by
    rw [geom_sum_9_Icc 1 l (by omega), pow_one]
  by_cases hr : k - (m - l) ≤ 1
  · have hinner : ∀ s ∈ Finset.Icc 1 l, (9 : ℝ) ^ s * (if s < (k - (m - l)) then (1 : ℝ) else A)
        = A * (9 : ℝ) ^ s := by
      intro s hs
      have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
      have hns : ¬ s < (k - (m - l)) := by omega
      simp [hns, mul_comm]
    have hCeq : C = A * ∑ s ∈ Finset.Icc 1 l, (9 : ℝ) ^ s := by
      rw [hC, Finset.sum_congr rfl hinner, Finset.mul_sum]
    rw [hCeq, hgeo_all]
    refine ⟨?_, ?_⟩
    · have h9l : (9 : ℝ) ^ l ≤ ((9 : ℝ) ^ (l + 1) - 9) / 8 := by
        have h : (8 : ℝ) * (9 : ℝ) ^ l ≤ (9 : ℝ) ^ (l + 1) - 9 := by
          have hpow : (9 : ℝ) ^ (l + 1) = 9 * (9 : ℝ) ^ l := by
            rw [pow_succ]
            ring
          have h9l' : (9 : ℝ) ^ 1 ≤ (9 : ℝ) ^ l := pow_le_pow_right₀ (by norm_num) (by omega)
          have h9l'' : (9 : ℝ) ≤ (9 : ℝ) ^ l := by simpa using! h9l'
          nlinarith [h9pos l, h9l'']
        have h8 : (0 : ℝ) < 8 := by norm_num
        have := (div_le_div_iff_of_pos_right h8).mpr h
        rwa [show (8 : ℝ) * (9 : ℝ) ^ l / 8 = (9 : ℝ) ^ l by ring] at this
      exact mul_le_mul_of_nonneg_left h9l hA
    · have h9l : ((9 : ℝ) ^ (l + 1) - 9) / 8 ≤ (5 / 4) * (9 : ℝ) ^ l := by
        have h : (9 : ℝ) ^ (l + 1) - 9 ≤ 10 * (9 : ℝ) ^ l := by
          have hpow : (9 : ℝ) ^ (l + 1) = 9 * (9 : ℝ) ^ l := by
            rw [pow_succ]
            ring
          nlinarith [h9pos l]
        have h8 : (0 : ℝ) < 8 := by norm_num
        have := (div_le_div_iff_of_pos_right h8).mpr h
        rw [show (5 / 4 : ℝ) * (9 : ℝ) ^ l = 10 * (9 : ℝ) ^ l / 8 by field_simp; ring]
        exact this
      have h1 : A * (((9 : ℝ) ^ (l + 1) - 9) / 8) ≤ (5 / 4) * (A * (9 : ℝ) ^ l) := by
        have h1' : A * (((9 : ℝ) ^ (l + 1) - 9) / 8) ≤ A * ((5 / 4) * (9 : ℝ) ^ l) :=
          mul_le_mul_of_nonneg_left h9l hA
        have h3 : A * ((5 / 4) * (9 : ℝ) ^ l) = (5 / 4) * (A * (9 : ℝ) ^ l) := by ring
        exact h1'.trans h3.le
      exact h1
  · have hr2 : 2 ≤ (k - (m - l)) := by omega
    have hrl : (k - (m - l)) ≤ l := by omega

    have hAkey : A * (9 : ℝ) ^ l = (9 : ℝ) ^ (k - (m - l)) := by
      have hkl : m ≤ k + l := by omega
      have hre : k + l - m = k - (m - l) := by omega
      have h9 : (9 : ℝ) ≠ 0 := by norm_num
      calc A * (9 : ℝ) ^ l
          = ((9 : ℝ) ^ k / (9 : ℝ) ^ m) * (9 : ℝ) ^ l := rfl
        _ = (9 : ℝ) ^ k * (9 : ℝ) ^ l / (9 : ℝ) ^ m := by ring
        _ = (9 : ℝ) ^ (k + l) / (9 : ℝ) ^ m := by rw [← pow_add]
        _ = (9 : ℝ) ^ (k + l - m) := by
            rw [div_eq_mul_inv, ← pow_sub₀ (9 : ℝ) h9 hkl]
        _ = (9 : ℝ) ^ (k - (m - l)) := by rw [hre]

    have hfilter_high : (Finset.Icc 1 l).filter (fun s => ¬ s < (k - (m - l))) = Finset.Icc (k - (m - l)) l := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · intro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨by omega, h2⟩
      · intro ⟨h1, h2⟩
        exact ⟨⟨by omega, h2⟩, by omega⟩
    have hhighsum : (∑ s ∈ Finset.Icc 1 l, (if s < (k - (m - l)) then 0 else A * (9 : ℝ) ^ s))
        = A * ∑ s ∈ Finset.Icc (k - (m - l)) l, (9 : ℝ) ^ s := by
      rw [hhigh', hfilter_high, ← Finset.mul_sum]
    have hCeq : C = (∑ s ∈ Finset.Icc 1 ((k - (m - l)) - 1), (9 : ℝ) ^ s)
        + A * ∑ s ∈ Finset.Icc (k - (m - l)) l, (9 : ℝ) ^ s := by
      rw [hC, hsplit, hlowsum, hhighsum]
    have hgeo1 : (∑ s ∈ Finset.Icc 1 ((k - (m - l)) - 1), (9 : ℝ) ^ s) = ((9 : ℝ) ^ (k - (m - l)) - 9) / 8 := by
      have h := geom_sum_9_Icc 1 ((k - (m - l)) - 1) (by omega)
      rw [h]
      have hexp : ((k - (m - l)) - 1) + 1 = (k - (m - l)) := by omega
      rw [hexp, pow_one]
    have hgeo2 : (∑ s ∈ Finset.Icc (k - (m - l)) l, (9 : ℝ) ^ s)
        = ((9 : ℝ) ^ (l + 1) - (9 : ℝ) ^ (k - (m - l))) / 8 :=
      geom_sum_9_Icc (k - (m - l)) l hrl
    refine ⟨?_, ?_⟩
    · have hmem : l ∈ Finset.Icc (k - (m - l)) l := Finset.mem_Icc.mpr ⟨hrl, le_refl _⟩
      have hterm : (9 : ℝ) ^ l ≤ ∑ s ∈ Finset.Icc (k - (m - l)) l, (9 : ℝ) ^ s :=
        Finset.single_le_sum (fun s _ => h9nn s) hmem
      have hstep : A * (9 : ℝ) ^ l ≤ A * ∑ s ∈ Finset.Icc (k - (m - l)) l, (9 : ℝ) ^ s :=
        mul_le_mul_of_nonneg_left hterm hA
      have hnonneg : 0 ≤ ∑ s ∈ Finset.Icc 1 ((k - (m - l)) - 1), (9 : ℝ) ^ s :=
        Finset.sum_nonneg (fun s _ => h9nn s)
      rw [hCeq]
      nlinarith
    · rw [hCeq, hgeo1, hgeo2]
      have hA9 : A * (9 : ℝ) ^ (l + 1) = 9 * (9 : ℝ) ^ (k - (m - l)) := by
        have hpow : (9 : ℝ) ^ (l + 1) = 9 * (9 : ℝ) ^ l := by
          rw [pow_succ]
          ring
        rw [hpow]
        have hkey : A * (9 * (9 : ℝ) ^ l) = 9 * (A * (9 : ℝ) ^ l) := by ring
        rw [hkey, hAkey]
      have hrew : (5 / 4) * (A * (9 : ℝ) ^ l) = (5 / 4) * (9 : ℝ) ^ (k - (m - l)) := by
        rw [hAkey]
      rw [hrew]

      have h2 : ((9 : ℝ) ^ (k - (m - l)) - 9) / 8 + A * (((9 : ℝ) ^ (l + 1) - (9 : ℝ) ^ (k - (m - l))) / 8)
          = (((9 : ℝ) ^ (k - (m - l)) - 9) + (A * (9 : ℝ) ^ (l + 1) - A * (9 : ℝ) ^ (k - (m - l)))) / 8 := by
        ring
      rw [h2]
      have hA2 : 0 ≤ A * (9 : ℝ) ^ (k - (m - l)) :=
        mul_nonneg hA (h9nn _)
      have h8 : (0 : ℝ) < 8 := by norm_num
      rw [div_le_iff₀ h8]
      nlinarith [h9pos (k - (m - l)), hA1, hA9, hA2]

theorem Clause32ThresholdSumStability_answer : Clause32ThresholdSumStability := by
  constructor
  · intro I _ m l γ ζ hlm
    show (l = 0 → thresholdSum m l γ ζ = 0) ∧
      (0 < l → (normVec (weightedBandState m γ ζ)) ^ 2 * (9 : ℝ) ^ l ≤ thresholdSum m l γ ζ ∧
        thresholdSum m l γ ζ ≤ (5 / 4) * (normVec (weightedBandState m γ ζ)) ^ 2 * (9 : ℝ) ^ l)
    have hw : ∀ (u : I) (h : Fin m), 0 ≤ (‖γ u‖ ^ 2 * ‖ζ (h.val + 1) u‖ ^ 2) :=
      fun u h => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    constructor
    · intro hl
      subst hl
      show (∑ t : Fin 0, _) = 0
      simp
    · intro hl
      set w : I → Fin m → ℝ := fun u h => ‖γ u‖ ^ 2 * ‖ζ (h.val + 1) u‖ ^ 2
      set A : Fin m → ℝ := fun h => (9 : ℝ) ^ (h.val + 1) / (9 : ℝ) ^ m
      set S : Fin m → ℝ := fun h => ∑ t : Fin l, (9 : ℝ) ^ (t.val + 1) *
        (if m - l + t.val + 1 < h.val + 1 then (1 : ℝ) else A h)
      have hp : (normVec (weightedBandState m γ ζ)) ^ 2 = ∑ u, ∑ h, w u h * A h := by
        rw [weightedBandState_sq]
      have hts : thresholdSum m l γ ζ = ∑ u, ∑ h, w u h * S h := by
        rw [thresholdSum_eq]
      have hbound : ∀ h : Fin m,
          A h * (9 : ℝ) ^ l ≤ S h ∧ S h ≤ (5 / 4) * (A h * (9 : ℝ) ^ l) := by
        intro h
        exact threshold_weight_bound m l hlm hl (h.val + 1)
          (by omega) (by omega)
      refine ⟨?_, ?_⟩
      · have h1 : (∑ u, ∑ h, w u h * A h) * (9 : ℝ) ^ l = ∑ u, ∑ h, w u h * (A h * (9 : ℝ) ^ l) :=
          double_sum_scale w A ((9 : ℝ) ^ l)
        rw [hp, hts, h1]
        exact double_sum_le w _ _ hw (fun h => (hbound h).1)
      · have h2a : (5 / 4) * (normVec (weightedBandState m γ ζ)) ^ 2 * (9 : ℝ) ^ l
            = (5 / 4) * ((normVec (weightedBandState m γ ζ)) ^ 2 * (9 : ℝ) ^ l) := by
          ring
        have h2b : (5 / 4) * ((∑ u, ∑ h, w u h * A h) * (9 : ℝ) ^ l)
            = (5 / 4) * (∑ u, ∑ h, w u h * (A h * (9 : ℝ) ^ l)) := by
          rw [double_sum_scale]
        have h2 : (5 / 4) * (∑ u, ∑ h, w u h * (A h * (9 : ℝ) ^ l))
            = ∑ u, ∑ h, w u h * ((5 / 4) * (A h * (9 : ℝ) ^ l)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun u _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun h _ => ?_)
          ring
        have h3 : (5 / 4) * ((normVec (weightedBandState m γ ζ)) ^ 2 * (9 : ℝ) ^ l)
            = (5 / 4) * ((∑ u, ∑ h, w u h * A h) * (9 : ℝ) ^ l) := by
          rw [hp]
        rw [h2a, h3, h2b, h2, hts]
        exact double_sum_le w _ _ hw (fun h => (hbound h).2)
  · intro H _ l εbm ψ φ hε hdist
    have hpt : ∀ j : Fin l,
        |(normVec (ψ j)) ^ 2 - (normVec (φ j)) ^ 2| * (9 : ℝ) ^ (j.val + 1)
          ≤ 4 * εbm * (9 : ℝ) ^ (j.val + 1) := by
      intro j
      obtain ⟨hψ, hφ, hd⟩ := hdist j
      have h1 : |(normVec (ψ j)) ^ 2 - (normVec (φ j)) ^ 2| ≤ 4 * εbm := by
        have h2 := normVec_sq_diff (ψ j) (φ j) hψ hφ
        nlinarith [hd]
      have hpow : 0 ≤ (9 : ℝ) ^ (j.val + 1) := pow_nonneg (by norm_num) _
      exact mul_le_mul_of_nonneg_right h1 hpow
    have hrew : |(∑ j : Fin l, (normVec (ψ j)) ^ 2 * (9 : ℝ) ^ (j.val + 1))
        - (∑ j : Fin l, (normVec (φ j)) ^ 2 * (9 : ℝ) ^ (j.val + 1))|
        = |∑ j : Fin l, ((normVec (ψ j)) ^ 2 - (normVec (φ j)) ^ 2) * (9 : ℝ) ^ (j.val + 1)| := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hrew]
    have htri : |∑ j : Fin l, ((normVec (ψ j)) ^ 2 - (normVec (φ j)) ^ 2) * (9 : ℝ) ^ (j.val + 1)|
        ≤ ∑ j : Fin l, |((normVec (ψ j)) ^ 2 - (normVec (φ j)) ^ 2) * (9 : ℝ) ^ (j.val + 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    have habs2 : ∀ j : Fin l,
        |((normVec (ψ j)) ^ 2 - (normVec (φ j)) ^ 2) * (9 : ℝ) ^ (j.val + 1)|
          = |(normVec (ψ j)) ^ 2 - (normVec (φ j)) ^ 2| * (9 : ℝ) ^ (j.val + 1) := by
      intro j
      rw [abs_mul, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 9) _)]
    have hsumle : (∑ j : Fin l, |((normVec (ψ j)) ^ 2 - (normVec (φ j)) ^ 2) * (9 : ℝ) ^ (j.val + 1)|)
        ≤ ∑ j : Fin l, 4 * εbm * (9 : ℝ) ^ (j.val + 1) := by
      apply Finset.sum_le_sum
      intro j _
      rw [habs2 j]
      exact hpt j
    have hfac : (∑ j : Fin l, 4 * εbm * (9 : ℝ) ^ (j.val + 1))
        = 4 * εbm * ∑ j : Fin l, (9 : ℝ) ^ (j.val + 1) := by
      rw [Finset.mul_sum]

    have hgeo : (∑ j : Fin l, (9 : ℝ) ^ (j.val + 1)) = ((9 : ℝ) ^ (l + 1) - 9) / 8 := by
      have h1 : (∑ j : Fin l, (9 : ℝ) ^ (j.val + 1)) = ∑ i ∈ Finset.range l, (9 : ℝ) ^ (i + 1) :=
        Fin.sum_univ_eq_sum_range (fun j : ℕ => (9 : ℝ) ^ (j + 1)) l
      have h2 : (∑ i ∈ Finset.range l, (9 : ℝ) ^ (i + 1))
          = (9 : ℝ) * ∑ i ∈ Finset.range l, (9 : ℝ) ^ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [pow_succ]; ring)
      rw [h1, h2, geom_sum_9]
      have h8 : (8 : ℝ) ≠ 0 := by norm_num
      field_simp
      ring
    have h9pos : 0 < (9 : ℝ) ^ l := pow_pos (by norm_num) _
    have hfinal : ((9 : ℝ) ^ (l + 1) - 9) / 8 ≤ (9 / 8) * (9 : ℝ) ^ l := by
      have h : (9 : ℝ) ^ (l + 1) - 9 ≤ 9 * (9 : ℝ) ^ l := by
        have hpow : (9 : ℝ) ^ (l + 1) = 9 * (9 : ℝ) ^ l := by
          rw [pow_succ]
          ring
        nlinarith [h9pos]
      have h8 : (0 : ℝ) < 8 := by norm_num
      have hthis := (div_le_div_iff_of_pos_right h8).mpr h
      rw [show (9 / 8 : ℝ) * (9 : ℝ) ^ l = 9 * (9 : ℝ) ^ l / 8 by field_simp]
      exact hthis
    have hε0 : 0 ≤ 4 * εbm := by nlinarith
    have hstep : 4 * εbm * (((9 : ℝ) ^ (l + 1) - 9) / 8)
        ≤ 4 * εbm * ((9 / 8) * (9 : ℝ) ^ l) :=
      mul_le_mul_of_nonneg_left hfinal hε0
    calc |∑ j : Fin l, ((normVec (ψ j)) ^ 2 - (normVec (φ j)) ^ 2) * (9 : ℝ) ^ (j.val + 1)|
        ≤ ∑ j : Fin l, |((normVec (ψ j)) ^ 2 - (normVec (φ j)) ^ 2) * (9 : ℝ) ^ (j.val + 1)| := htri
      _ ≤ ∑ j : Fin l, 4 * εbm * (9 : ℝ) ^ (j.val + 1) := hsumle
      _ = 4 * εbm * ∑ j : Fin l, (9 : ℝ) ^ (j.val + 1) := hfac
      _ = 4 * εbm * (((9 : ℝ) ^ (l + 1) - 9) / 8) := by rw [hgeo]
      _ ≤ 4 * εbm * ((9 / 8) * (9 : ℝ) ^ l) := hstep
      _ = (9 / 8) * 4 * εbm * (9 : ℝ) ^ l := by ring

end Qatlib.Papers.QLSStatePrep24.SpectralLeak
