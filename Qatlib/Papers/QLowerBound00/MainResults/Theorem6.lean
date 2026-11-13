/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLowerBound00.MainResults.Model.AdversaryD

/-!
# Finite-alphabet adversary lower bound

`source_theorem6` gives a value-query lower bound using local mismatch degrees whose products
are bounded by `lmax`. The statement includes the query trajectory, normalization, output
success, and relation degree conditions for finite-alphabet inputs and a general output type.
See [Ambainis2002] for the paper's setting.

## Main statements

* `source_theorem6`: For a value-query trajectory satisfying the stated initialization,
  normalization, output-error, and relation-degree conditions, `(1 - 2*sqrt (ε*(1-ε))) * sqrt
  (m*m') / 2 ≤ T * sqrt lmax`.

## References

* [Ambainis, 2002][Ambainis2002]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QLowerBound00.MainResults.Theorem6

open Qatlib.Papers.QLowerBound00.MainResults.Model
open Qatlib.Papers.QLowerBound00.MainResults.AdversaryCore

/-- For a value-query trajectory satisfying the stated initialization, normalization,
output-error, and relation-degree conditions, `(1 - 2*sqrt (ε*(1-ε))) * sqrt (m*m') / 2 ≤ T
* sqrt lmax`. See [Ambainis2002]. -/
theorem source_theorem6 {n d Z : ℕ} (hd : 0 < d) {β : Type*} [DecidableEq β]
    (f : InputD n d → β)
    (X Y : Finset (InputD n d)) (R : Finset (InputD n d × InputD n d))
    (m m' lmax : ℕ) (ε : ℝ) (T : ℕ)
    (lx ly : InputD n d → Fin n → ℕ) (bit : ℕ → Fin n)
    (ψ : ℕ → ((Fin n × Fin d) × Fin Z) → InputD n d → ℂ)
    (ans : ((Fin n × Fin d) × Fin Z) → β)
    (iw0 : (Fin n × Fin d) × Fin Z)
    (hinit : ∀ iw x, ψ 0 iw x = if iw = iw0 then 1 else 0)
    (hquery : ∀ k < T, ψ (k + 1) = valueQuery hd (bit k) (ψ k))
    (hnorm : ∀ k x, (∑ iw, ‖ψ k iw x‖ ^ 2) = 1)
    (hfXY : ∀ x ∈ X, ∀ y ∈ Y, f x ≠ f y)
    (hRsub : ∀ p ∈ R, p.1 ∈ X ∧ p.2 ∈ Y)
    (hm : ∀ x ∈ X, m ≤ (R.filter (fun p => p.1 = x)).card)
    (hm' : ∀ y ∈ Y, m' ≤ (R.filter (fun p => p.2 = y)).card)
    (hlx : ∀ x ∈ X, ∀ i : Fin n,
      (R.filter (fun p => p.1 = x ∧ p.2 i ≠ x i)).card = lx x i)
    (hly : ∀ y ∈ Y, ∀ i : Fin n,
      (R.filter (fun p => p.2 = y ∧ p.1 i ≠ y i)).card = ly y i)
    (hlmax : ∀ p ∈ R, ∀ i : Fin n, p.1 i ≠ p.2 i → lx p.1 i * ly p.2 i ≤ lmax)
    (hsucc : ∀ x : InputD n d,
      1 - ε ≤ ∑ iw ∈ univ.filter (fun iw => ans iw = f x), ‖ψ T iw x‖ ^ 2)
    (hX : 0 < X.card) (hY : 0 < Y.card)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    (1 - 2 * Real.sqrt (ε * (1 - ε))) * Real.sqrt ((m : ℝ) * (m' : ℝ)) / 2 ≤
      (T : ℝ) * Real.sqrt (lmax : ℝ) := by
  classical

  have hdisj : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro z hzX hzY
    exact hfXY z hzX z hzY rfl

  let α : InputD n d → ℝ := fun x => initialAmplitude X Y x
  let φ : ℕ → ((Fin n × Fin d) × Fin Z) → InputD n d → ℂ :=
    fun k iw x => (α x : ℂ) * ψ k iw x

  have hφ0 : ∀ x y, rhoEntry (φ 0) x y = initialState X Y x * initialState X Y y := by
    intro x y
    have hsum1 : (∑ iw, star (ψ 0 iw x) * ψ 0 iw y) = 1 := by
      have hterm : ∀ iw, star (ψ 0 iw x) * ψ 0 iw y =
          (if iw = iw0 then (1 : ℂ) else 0) := by
        intro iw
        rw [hinit iw x, hinit iw y]
        by_cases h : iw = iw0 <;> simp [h]
      rw [Finset.sum_congr rfl (fun iw _ => hterm iw), Finset.sum_ite_eq']
      simp
    rw [rhoEntry_eq_of_factor (ψ := φ 0) (a := ψ 0)
      (α := fun x => initialAmplitude X Y x) (fun iw x => rfl), hsum1, mul_one]
    rfl

  let S : ℕ → ℝ := fun k => progress R (rhoEntry (φ k))
  have hS0 : S 0 = progress R (fun x y => initialState X Y x * initialState X Y y) := by
    unfold S
    congr 1
    funext x y
    exact hφ0 x y
  have hS0card : S 0 =
      (R.card : ℝ) * (2 * Real.sqrt (X.card : ℝ) * Real.sqrt (Y.card : ℝ))⁻¹ := by
    rw [hS0]
    exact progress_initial X Y R hdisj hRsub hX hY

  have hcard := card_relation_ge X Y R m m' hRsub hm hm'
  have hsqrtXpos : 0 < Real.sqrt (X.card : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hX)
  have hsqrtYpos : 0 < Real.sqrt (Y.card : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hY)
  have hBpos : 0 < 2 * Real.sqrt (X.card : ℝ) * Real.sqrt (Y.card : ℝ) :=
    mul_pos (mul_pos (by norm_num) hsqrtXpos) hsqrtYpos
  have hmm0 : (0 : ℝ) ≤ (m : ℝ) * (m' : ℝ) := by positivity
  have hX0 : (0 : ℝ) ≤ (X.card : ℝ) := by positivity
  have hY0 : (0 : ℝ) ≤ (Y.card : ℝ) := by positivity
  have hAB : Real.sqrt ((m : ℝ) * (m' : ℝ) * (X.card : ℝ) * (Y.card : ℝ)) =
      Real.sqrt ((m : ℝ) * (m' : ℝ)) *
        (2 * Real.sqrt (X.card : ℝ) * Real.sqrt (Y.card : ℝ)) / 2 := by
    rw [show (m : ℝ) * (m' : ℝ) * (X.card : ℝ) * (Y.card : ℝ) =
      ((m : ℝ) * (m' : ℝ)) * ((X.card : ℝ) * (Y.card : ℝ)) by ring]
    rw [Real.sqrt_mul hmm0, Real.sqrt_mul hX0]
    ring
  have hS0lower : Real.sqrt ((m : ℝ) * (m' : ℝ)) / 2 ≤ S 0 := by
    rw [hS0card]
    have hval : Real.sqrt ((m : ℝ) * (m' : ℝ)) / 2 =
        Real.sqrt ((m : ℝ) * (m' : ℝ) * (X.card : ℝ) * (Y.card : ℝ)) /
          (2 * Real.sqrt (X.card : ℝ) * Real.sqrt (Y.card : ℝ)) := by
      rw [hAB]
      have hxne : Real.sqrt (X.card : ℝ) ≠ 0 := hsqrtXpos.ne'
      have hyne : Real.sqrt (Y.card : ℝ) ≠ 0 := hsqrtYpos.ne'
      field_simp
    rw [hval]
    exact div_le_div_of_nonneg_right hcard hBpos.le

  have hmassφ : ∀ k x, mass (φ k) x = α x ^ 2 := by
    intro k x
    unfold mass
    have hterm : ∀ iw, ‖φ k iw x‖ ^ 2 = (α x) ^ 2 * ‖ψ k iw x‖ ^ 2 := by
      intro iw
      unfold φ
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [Finset.sum_congr rfl (fun iw _ => hterm iw), ← Finset.mul_sum, hnorm k x, mul_one]
  have hαX : ∀ x ∈ X, α x ^ 2 = (2 * (X.card : ℝ))⁻¹ := by
    intro x hx
    simp only [α, initialAmplitude, if_pos hx]
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  have hαY : ∀ y ∈ Y, α y ^ 2 = (2 * (Y.card : ℝ))⁻¹ := by
    intro y hy
    have hyX : y ∉ X := fun h => (Finset.disjoint_left.mp hdisj) h hy
    simp only [α, initialAmplitude, if_neg hyX, if_pos hy]
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  have hmass_le : ∀ k, (∑ iw, ∑ x ∈ X, ‖φ k iw x‖ ^ 2) +
      (∑ iw, ∑ y ∈ Y, ‖φ k iw y‖ ^ 2) ≤ 1 := by
    intro k
    have hXsum : (∑ iw, ∑ x ∈ X, ‖φ k iw x‖ ^ 2) = ∑ x ∈ X, α x ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun x _ => hmassφ k x)
    have hYsum : (∑ iw, ∑ y ∈ Y, ‖φ k iw y‖ ^ 2) = ∑ y ∈ Y, α y ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun y _ => hmassφ k y)
    rw [hXsum, hYsum, Finset.sum_congr rfl hαX, Finset.sum_congr rfl hαY,
      Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hxcalc : (X.card : ℝ) * (2 * (X.card : ℝ))⁻¹ = 1 / 2 := by
      have hXne : (X.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hX)
      field_simp
    have hycalc : (Y.card : ℝ) * (2 * (Y.card : ℝ))⁻¹ = 1 / 2 := by
      have hYne : (Y.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hY)
      field_simp
    rw [hxcalc, hycalc]
    norm_num

  have hφq : ∀ k < T, φ (k + 1) = valueQuery hd (bit k) (φ k) := by
    intro k hk
    funext iw x
    have hs := congrFun (congrFun (valueQuery_smul (fun x => (α x : ℂ)) hd (bit k) (ψ k)) iw) x
    show (α x : ℂ) * ψ (k + 1) iw x =
      valueQuery hd (bit k) (fun iw x => (α x : ℂ) * ψ k iw x) iw x
    rw [hs, hquery k hk]

  have hwrongX : ∀ x ∈ X,
      (∑ iw ∈ univ.filter (fun iw => ans iw ≠ f x), ‖ψ T iw x‖ ^ 2) ≤ ε := by
    intro x hx
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := (univ : Finset ((Fin n × Fin d) × Fin Z)))
      (p := fun iw => ans iw = f x) (f := fun iw => ‖ψ T iw x‖ ^ 2)
    have htotal := hnorm T x
    have hsuccx := hsucc x
    linarith
  have hrightY : ∀ x ∈ X, ∀ y ∈ Y,
      (∑ iw ∈ univ.filter (fun iw => ans iw = f x), ‖ψ T iw y‖ ^ 2) ≤ ε := by
    intro x hx y hy
    have hfne : f x ≠ f y := hfXY x hx y hy
    have hsub : univ.filter (fun iw => ans iw = f x) ⊆
        univ.filter (fun iw => ans iw ≠ f y) := by
      intro iw hiw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiw ⊢
      intro h
      exact hfne (hiw.symm.trans h)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun iw => ‖ψ T iw y‖ ^ 2)
      (fun iw _ _ => by positivity)
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := (univ : Finset ((Fin n × Fin d) × Fin Z)))
      (p := fun iw => ans iw = f y) (f := fun iw => ‖ψ T iw y‖ ^ 2)
    have htotal := hnorm T y
    have hsuccy := hsucc y
    have hne : (∑ iw ∈ univ.filter (fun iw => ans iw ≠ f y), ‖ψ T iw y‖ ^ 2) ≤ ε := by
      linarith
    linarith

  have hSupper : S T ≤ 2 * Real.sqrt (ε * (1 - ε)) * S 0 := by
    rw [hS0]
    refine final_progress_le R ε (fun x y => rhoEntry (φ T) x y)
      (fun x y => initialState X Y x * initialState X Y y) ?_
    intro p hp
    obtain ⟨hxX, hyY⟩ := hRsub p hp
    have hpair := lemma1_density_entry
      (ZW := ((Fin n × Fin d) × Fin Z)) ans (f p.1)
      (fun iw => ψ T iw p.1) (fun iw => ψ T iw p.2)
      (initialAmplitude X Y p.1 : ℂ) (initialAmplitude X Y p.2 : ℂ) ε hε0 hε
      (hnorm T p.1) (hnorm T p.2) (hwrongX p.1 hxX) (hrightY p.1 hxX p.2 hyY)
    calc ‖rhoEntry (φ T) p.1 p.2‖
        = ‖(initialAmplitude X Y p.1 : ℂ) * (initialAmplitude X Y p.2 : ℂ) *
            ∑ iw, star (ψ T iw p.1) * ψ T iw p.2‖ := by
            rw [rhoEntry_eq_of_factor (ψ := φ T) (a := ψ T)
              (α := fun x => initialAmplitude X Y x) (fun iw x => rfl)]
      _ ≤ 2 * Real.sqrt (ε * (1 - ε)) * ‖(initialAmplitude X Y p.1 : ℂ)‖ *
            ‖(initialAmplitude X Y p.2 : ℂ)‖ := hpair
      _ = 2 * Real.sqrt (ε * (1 - ε)) *
            ‖initialState X Y p.1 * initialState X Y p.2‖ := by
            simp only [initialState, norm_mul]
            ring

  have hstep : ∀ k < T, S k - S (k + 1) ≤ Real.sqrt (lmax : ℝ) := by
    intro k hk
    have hsub := progress_sub_le R (rhoEntry (φ k)) (rhoEntry (φ (k + 1)))
    have hnorm2 : (∑ p ∈ R,
        ‖rhoEntry (φ k) p.1 p.2 - rhoEntry (φ (k + 1)) p.1 p.2‖) =
        ∑ p ∈ R, ‖rhoEntry (φ (k + 1)) p.1 p.2 - rhoEntry (φ k) p.1 p.2‖ := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [norm_sub_rev]
    have hbound : (∑ p ∈ R,
        ‖rhoEntry (φ (k + 1)) p.1 p.2 - rhoEntry (φ k) p.1 p.2‖) ≤
        Real.sqrt (lmax : ℝ) := by
      rw [hφq k hk]
      exact progress_valueQuery_step_le_lmax hd X Y R lmax (bit k) (φ k)
        (fun x => lx x (bit k)) (fun y => ly y (bit k)) hRsub
        (fun x hx => hlx x hx (bit k)) (fun y hy => hly y hy (bit k))
        (fun p hp => hlmax p hp (bit k)) (hmass_le k)
    unfold S
    refine hsub.trans ?_
    rw [hnorm2]
    exact hbound
  rw [mul_div_assoc]
  exact adversary_lower_bound (S := S) (T := T) (B := Real.sqrt (lmax : ℝ))
    (S0 := Real.sqrt ((m : ℝ) * (m' : ℝ)) / 2) hε0 hε hstep hS0lower hSupper

end Qatlib.Papers.QLowerBound00.MainResults.Theorem6
