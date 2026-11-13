/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GevreyGrad19.MainResults.Model.GevreyGradDefinitions
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option backward.isDefEq.respectTransparency false

/-!
# Gevrey Regularity of Hypercube Test Functions

This module proves Lemma 4.2: for `c > 0` and `0 < ε < c / 146`, every trigonometric
test function in `testClass d c ε` belongs to the analytic Gevrey class
`Gevrey d c 0 Set.univ`.

## Main statements

* `testClass_subset_gevrey`: `testClass d c ε ⊆ Gevrey d c 0 Set.univ`.

## References

* [Cornelissen, 2019][Cornelissen2019], Lemma 4.2, pp. 36-37.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace Qatlib.Papers.GevreyGrad19.MainResults.LowerBound

open Qatlib.Papers.GevreyGrad19.MainResults

private def prodFun {d : ℕ} (h : Fin d → ℝ → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∏ m, h m (x m)

private lemma prodFun_contDiff {d : ℕ} {h : Fin d → ℝ → ℝ}
    (hh : ∀ m, ContDiff ℝ ⊤ (h m)) : ContDiff ℝ ⊤ (prodFun h) := by
  unfold prodFun
  apply contDiff_prod
  intro m _
  exact (hh m).comp (contDiff_apply ℝ (fun _ : Fin d => ℝ) m)

private lemma prodFun_split {d : ℕ} (h : Fin d → ℝ → ℝ)
    (i : Fin d) (x : Fin d → ℝ) :
    prodFun h x = h i (x i) * ∏ m ∈ Finset.univ.erase i, h m (x m) := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

private lemma prodFun_fderiv_single {d : ℕ} {h : Fin d → ℝ → ℝ}
    (hh : ∀ m, ContDiff ℝ ⊤ (h m)) (i : Fin d) (x : Fin d → ℝ) :
    fderiv ℝ (prodFun h) x (Pi.single i 1) =
      prodFun (Function.update h i (deriv (h i))) x := by
  have hline : (fun t : ℝ => prodFun h (x + t • Pi.single i 1)) =
      (fun t : ℝ => h i (x i + t) * ∏ m ∈ Finset.univ.erase i, h m (x m)) := by
    funext t
    rw [prodFun_split h i]
    congr 1
    · simp
    · apply Finset.prod_congr rfl
      intro m hm
      simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hm)]
  have hf : DifferentiableAt ℝ (prodFun h)
      (x + (0 : ℝ) • (Pi.single i 1 : Fin d → ℝ)) :=
    ((prodFun_contDiff hh).differentiable (by simp)).differentiableAt
  have hderiv := (hf.hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_const (0 : ℝ) x).add
      ((hasDerivAt_id (0 : ℝ)).smul_const
        (Pi.single i (1 : ℝ) : Fin d → ℝ)))).deriv
  simp only [zero_smul, add_zero, one_smul, zero_add] at hderiv
  change deriv (fun t : ℝ => prodFun h (x + t • Pi.single i 1)) 0 =
    fderiv ℝ (prodFun h) x (Pi.single i 1) at hderiv
  rw [← hderiv, hline]
  have hi : HasDerivAt (h i) (deriv (h i) (x i)) (x i + id (0 : ℝ)) := by
    simpa using ((hh i).differentiable (by simp) (x i)).hasDerivAt
  have ht := (hi.comp 0 ((hasDerivAt_id (0 : ℝ)).const_add (x i))).mul_const
    (∏ m ∈ Finset.univ.erase i, h m (x m))
  simp only [Function.comp_apply, mul_one] at ht
  rw [ht.deriv, prodFun_split _ i]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro m hm
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)]

private def applyDirs {d : ℕ} : {k : ℕ} → (Fin k → Fin d) →
    (Fin d → ℝ → ℝ) → (Fin d → ℝ → ℝ)
  | 0, _, h => h
  | _ + 1, α, h => Function.update (applyDirs (Fin.tail α) h) (α 0)
      (deriv (applyDirs (Fin.tail α) h (α 0)))

private lemma applyDirs_contDiff {d k : ℕ} (α : Fin k → Fin d)
    {h : Fin d → ℝ → ℝ} (hh : ∀ m, ContDiff ℝ ⊤ (h m)) :
    ∀ m, ContDiff ℝ ⊤ (applyDirs α h m) := by
  induction k with
  | zero => exact hh
  | succ k ih =>
    intro m
    by_cases hm : m = α 0
    · subst m
      simpa only [applyDirs, Function.update_self] using
        ContDiff.deriv' (n := ⊤) (by simpa using ih (Fin.tail α) (α 0))
    · simpa only [applyDirs, Function.update_of_ne hm] using ih (Fin.tail α) m

private lemma prodFun_iteratedFDeriv {d k : ℕ} (α : Fin k → Fin d)
    {h : Fin d → ℝ → ℝ} (hh : ∀ m, ContDiff ℝ ⊤ (h m)) (x : Fin d → ℝ) :
    iteratedFDeriv ℝ k (prodFun h) x (fun r => Pi.single (α r) 1) =
      prodFun (applyDirs α h) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    have hf := (prodFun_contDiff hh).differentiable_iteratedFDeriv
      (m := k) (by simp)
    rw [hf.differentiableAt.iteratedFDeriv_succ_apply_left']
    have heq : (fun y => iteratedFDeriv ℝ k (prodFun h) y
        (Fin.tail (fun r => (Pi.single (α r) (1 : ℝ) : Fin d → ℝ)))) =
        prodFun (applyDirs (Fin.tail α) h) := by
      funext y
      exact ih (Fin.tail α) y
    rw [heq, prodFun_fderiv_single (applyDirs_contDiff (Fin.tail α) hh)]
    rfl

private def TrigScaled (c : ℝ) (r : ℕ) (u : ℝ → ℝ) : Prop :=
  u = (fun t => c ^ r * Real.sin (c * t)) ∨
  u = (fun t => c ^ r * Real.cos (c * t)) ∨
  u = (fun t => -(c ^ r * Real.sin (c * t))) ∨
  u = (fun t => -(c ^ r * Real.cos (c * t)))

private lemma TrigScaled.contDiff {c : ℝ} {r : ℕ} {u : ℝ → ℝ}
    (hu : TrigScaled c r u) : ContDiff ℝ ⊤ u := by
  rcases hu with rfl | rfl | rfl | rfl <;> fun_prop

private lemma TrigScaled.abs_le {c : ℝ} (hc : 0 ≤ c) {r : ℕ} {u : ℝ → ℝ}
    (hu : TrigScaled c r u) (t : ℝ) : |u t| ≤ c ^ r := by
  rcases hu with rfl | rfl | rfl | rfl
  · simpa [abs_mul, abs_of_nonneg (pow_nonneg hc r)] using
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (c * t)) (pow_nonneg hc r)
  · simpa [abs_mul, abs_of_nonneg (pow_nonneg hc r)] using
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (c * t)) (pow_nonneg hc r)
  · simpa [abs_mul, abs_of_nonneg (pow_nonneg hc r)] using
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (c * t)) (pow_nonneg hc r)
  · simpa [abs_mul, abs_of_nonneg (pow_nonneg hc r)] using
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (c * t)) (pow_nonneg hc r)

private lemma TrigScaled.deriv_scaled {c : ℝ} {r : ℕ} {u : ℝ → ℝ}
    (hu : TrigScaled c r u) : TrigScaled c (r + 1) (deriv u) := by
  have hs : deriv (fun t => c ^ r * Real.sin (c * t)) =
      (fun t => c ^ (r + 1) * Real.cos (c * t)) := by
    funext t
    have ht := (((hasDerivAt_id t).const_mul c).sin.const_mul (c ^ r)).deriv
    simp only [id_eq] at ht
    rw [ht, pow_succ]
    ring
  have hcos : deriv (fun t => c ^ r * Real.cos (c * t)) =
      (fun t => -(c ^ (r + 1) * Real.sin (c * t))) := by
    funext t
    have ht := (((hasDerivAt_id t).const_mul c).cos.const_mul (c ^ r)).deriv
    simp only [id_eq] at ht
    rw [ht, pow_succ]
    ring
  rcases hu with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr (Or.inl hcos))
  · right; right; right
    funext t
    simpa only [deriv.fun_neg] using congrArg Neg.neg (congrFun hs t)
  · left
    funext t
    simpa only [deriv.fun_neg, neg_neg] using congrArg Neg.neg (congrFun hcos t)

private lemma applyDirs_trig {d k : ℕ} {c : ℝ} (α : Fin k → Fin d)
    {h : Fin d → ℝ → ℝ} {deg : Fin d → ℕ}
    (hh : ∀ m, TrigScaled c (deg m) (h m)) :
    ∃ deg' : Fin d → ℕ, (∑ m, deg' m) = (∑ m, deg m) + k ∧
      ∀ m, TrigScaled c (deg' m) (applyDirs α h m) := by
  induction k with
  | zero => exact ⟨deg, by simp, hh⟩
  | succ k ih =>
    obtain ⟨deg', hsum, htrig⟩ := ih (Fin.tail α)
    refine ⟨Function.update deg' (α 0) (deg' (α 0) + 1), ?_, ?_⟩
    · rw [Finset.sum_update_of_mem (Finset.mem_univ (α 0))]
      have hsplit := Finset.sum_erase_add Finset.univ deg' (Finset.mem_univ (α 0))
      rw [Finset.sdiff_singleton_eq_erase] at *
      omega
    · intro m
      by_cases hm : m = α 0
      · subst m
        simpa only [Function.update_self, applyDirs] using (htrig (α 0)).deriv_scaled
      · simpa only [applyDirs, Function.update_of_ne hm] using htrig m

private lemma prodFun_trig_bound {d k : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (α : Fin k → Fin d) {h : Fin d → ℝ → ℝ}
    (hh : ∀ m, TrigScaled c 0 (h m)) (x : Fin d → ℝ) :
    |iteratedFDeriv ℝ k (prodFun h) x (fun r => Pi.single (α r) 1)| ≤ c ^ k := by
  rw [prodFun_iteratedFDeriv α (fun m => (hh m).contDiff)]
  obtain ⟨deg, hsum, htrig⟩ := applyDirs_trig α hh
  simp only [Finset.sum_const_zero, zero_add] at hsum
  calc
    |prodFun (applyDirs α h) x| = ∏ m, |applyDirs α h m (x m)| := by
      simp only [prodFun, Finset.abs_prod]
    _ ≤ ∏ m, c ^ deg m := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      (fun m _ => (htrig m).abs_le hc (x m))
    _ = c ^ k := by rw [Finset.prod_pow_eq_pow_sum, hsum]

private def trigFactors {d : ℕ} (c : ℝ) (j m : Fin d) (t : ℝ) : ℝ :=
  if m = j then Real.sin (c * t) else Real.cos (c * t)

private lemma trigFactors_scaled {d : ℕ} (c : ℝ) (j m : Fin d) :
    TrigScaled c 0 (trigFactors c j m) := by
  by_cases hm : m = j
  · left
    funext t
    simp [trigFactors, hm]
  · right; left
    funext t
    simp [trigFactors, hm]

private lemma testFunction_sum_prodFun (d : ℕ) (c ε : ℝ) (b : Fin d → ℝ) :
    testFunction d c ε b = fun x =>
      ∑ j, (73 * ε * b j / (c * (d : ℝ))) * prodFun (trigFactors c j) x := by
  funext x
  apply Finset.sum_congr rfl
  intro j _
  rw [prodFun_split _ j]
  simp only [trigFactors, ite_true]
  have hp : (∏ m ∈ Finset.univ.erase j,
      if m = j then Real.sin (c * x m) else Real.cos (c * x m)) =
      ∏ m ∈ Finset.univ.erase j, Real.cos (c * x m) := by
    apply Finset.prod_congr rfl
    intro m hm
    simp [Finset.ne_of_mem_erase hm]
  rw [hp, mul_assoc]

/-- **Lemma 4.2**: for `d : ℕ`, `c > 0`, and `ε ∈ (0, c / 146)`, every test function
in `testClass d c ε` belongs to `Gevrey d c 0 Set.univ`. -/
theorem testClass_subset_gevrey (d : ℕ) {c ε : ℝ} (hc : 0 < c) (hε0 : 0 < ε)
    (hεc : ε < c / 146) :
    testClass d c ε ⊆ Gevrey d c 0 Set.univ := by
  rintro f ⟨b, hb, rfl⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hz : testFunction 0 c ε b = fun _ => 0 := by
      funext x
      simp [testFunction]
    rw [hz]
    refine ⟨contDiff_const.contDiffOn, ?_⟩
    intro x _ k α
    change |iteratedFDeriv ℝ k (fun _ : Fin 0 → ℝ => 0) x
      (fun r => Pi.single (α r) 1)| ≤ _
    rw [iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, zero_apply, abs_zero, Real.rpow_zero, mul_one]
    positivity
  have hdc : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hcd (j : Fin d) : ContDiff ℝ ⊤ (prodFun (trigFactors c j)) :=
    prodFun_contDiff fun m => (trigFactors_scaled c j m).contDiff
  have hcoeff (j : Fin d) : |73 * ε * b j / (c * (d : ℝ))| =
      73 * ε / (c * (d : ℝ)) := by
    have hbabs : |b j| = 1 := by
      rcases hb j with hj | hj <;> simp [hj]
    rw [abs_div, abs_mul, hbabs, abs_of_pos (by positivity : 0 < 73 * ε),
      abs_of_pos (mul_pos hc hdc), mul_one]
  have hsmall : 73 * ε / c ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hc).mpr
    linarith
  rw [testFunction_sum_prodFun]
  refine ⟨(ContDiff.sum (fun j _ => contDiff_const.mul (hcd j))).contDiffOn, ?_⟩
  intro x _ k α
  have hderiv : iteratedFDeriv ℝ k
      (fun y => ∑ j, (73 * ε * b j / (c * (d : ℝ))) *
        prodFun (trigFactors c j) y) x (fun r => Pi.single (α r) 1) =
      ∑ j, (73 * ε * b j / (c * (d : ℝ))) *
        iteratedFDeriv ℝ k (prodFun (trigFactors c j)) x
          (fun r => Pi.single (α r) 1) := by
    rw [iteratedFDeriv_fun_sum_apply
      (fun j _ => ((contDiff_const.mul (hcd j)).of_le le_top).contDiffAt)]
    rw [_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    change iteratedFDeriv ℝ k
      (fun y => (73 * ε * b j / (c * (d : ℝ))) • prodFun (trigFactors c j) y)
        x (fun r => Pi.single (α r) 1) = _
    rw [iteratedFDeriv_const_smul_apply' ((hcd j).of_le le_top).contDiffAt]
    rfl
  rw [hderiv, Real.rpow_zero, mul_one]
  calc
    |∑ j, (73 * ε * b j / (c * (d : ℝ))) *
        iteratedFDeriv ℝ k (prodFun (trigFactors c j)) x
          (fun r => Pi.single (α r) 1)|
        ≤ ∑ j, |(73 * ε * b j / (c * (d : ℝ))) *
          iteratedFDeriv ℝ k (prodFun (trigFactors c j)) x
            (fun r => Pi.single (α r) 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, (73 * ε / (c * (d : ℝ))) * c ^ k := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, hcoeff]
      exact mul_le_mul_of_nonneg_left
        (prodFun_trig_bound hc.le α (trigFactors_scaled c j) x) (by positivity)
    _ = (73 * ε / c) * c ^ k := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    _ ≤ (1 / 2 : ℝ) * c ^ k :=
      mul_le_mul_of_nonneg_right hsmall (pow_nonneg hc.le k)

end Qatlib.Papers.GevreyGrad19.MainResults.LowerBound
