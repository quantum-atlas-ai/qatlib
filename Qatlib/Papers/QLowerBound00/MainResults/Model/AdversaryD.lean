/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLowerBound00.MainResults.Model.ValueOracle
import Qatlib.Papers.QLowerBound00.MainResults.AdversaryCore

/-!
# Adversary progress under finite-alphabet value queries

Modular-shift invariance gives `mass_valueQuery` and preservation of Gram entries when queried
symbols agree. A general overlap-change bound yields `progress_valueQuery_step_le_lmax`,
extending the local-degree adversary estimate to the value-query model. See [Ambainis2002] for
the paper's setting.

## Main statements

* `addFin_eq_add`: The explicit modular addition `addFin` agrees with addition in `Fin d` for
  positive `d`.
* `valueQuery_smul`: A value query commutes with multiplication by a complex amplitude depending
  only on the input.

## References

* [Ambainis, 2002][Ambainis2002]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QLowerBound00.MainResults.Model

open Qatlib.Papers.QLowerBound00.MainResults.AdversaryCore

/-- The explicit modular addition `addFin` agrees with addition in `Fin d` for positive `d`. -/
theorem addFin_eq_add {d : ℕ} (hd : 0 < d) (a b : Fin d) : addFin hd a b = a + b := by
  haveI : NeZero d := ⟨Nat.pos_iff_ne_zero.mp hd⟩
  rw [Fin.ext_iff, addFin, Fin.val_add]

/-- A finite sum is unchanged by a modular translation of its index. -/
theorem sum_addFin_shift {d : ℕ} {M : Type*} [AddCommMonoid M]
    (hd : 0 < d) (G : Fin d → M) (c : Fin d) :
    (∑ a : Fin d, G (addFin hd a c)) = ∑ a : Fin d, G a := by
  haveI : NeZero d := ⟨Nat.pos_iff_ne_zero.mp hd⟩
  have h : ∀ a : Fin d, addFin hd a c = a + c := fun a => addFin_eq_add hd a c
  simp_rw [h]
  exact Equiv.sum_comp (Equiv.addRight c) G

/-- A sum over query index, response register, and workspace splits into the corresponding three
iterated sums. -/
theorem sum_iw_split {n d Z : ℕ} {M : Type*} [AddCommMonoid M]
    (F : ((Fin n × Fin d) × Fin Z) → M) :
    (∑ iw, F iw) = ∑ i' : Fin n, ∑ a : Fin d, ∑ z : Fin Z, F ((i', a), z) := by
  rw [Fintype.sum_prod_type]
  exact Fintype.sum_prod_type (fun p : Fin n × Fin d => ∑ z : Fin Z, F (p, z))

/-- A value query preserves the squared workspace mass of every input column. -/
theorem mass_valueQuery {n d Z : ℕ} (hd : 0 < d) (i : Fin n)
    (ψ : ((Fin n × Fin d) × Fin Z) → InputD n d → ℂ) (x : InputD n d) :
    mass (valueQuery hd i ψ) x = mass ψ x := by
  classical
  unfold mass
  rw [sum_iw_split (F := fun iw => ‖valueQuery hd i ψ iw x‖ ^ 2)]
  rw [sum_iw_split (F := fun iw => ‖ψ iw x‖ ^ 2)]
  refine Finset.sum_congr rfl (fun i' _ => ?_)
  by_cases hi : i' = i
  · subst i'
    have hval : ∀ (a : Fin d) (z : Fin Z),
        valueQuery hd i ψ ((i, a), z) x = ψ ((i, addFin hd a (x i)), z) x := by
      intro a z
      simp [valueQuery]
    simp only [hval]
    exact sum_addFin_shift hd (fun a => ∑ z : Fin Z, ‖ψ ((i, a), z) x‖ ^ 2) (x i)
  · have hval : ∀ (a : Fin d) (z : Fin Z),
        valueQuery hd i ψ ((i', a), z) x = ψ ((i', a), z) x := by
      intro a z
      simp [valueQuery, hi]
    simp only [hval]

/-- A value query preserves the Gram entry between inputs agreeing at the queried coordinate. -/
theorem rhoEntry_valueQuery_same {n d Z : ℕ} (hd : 0 < d) (i : Fin n)
    (ψ : ((Fin n × Fin d) × Fin Z) → InputD n d → ℂ) (x y : InputD n d)
    (hxy : x i = y i) :
    rhoEntry (valueQuery hd i ψ) x y = rhoEntry ψ x y := by
  classical
  unfold rhoEntry
  rw [sum_iw_split (F := fun iw => star (valueQuery hd i ψ iw x) * valueQuery hd i ψ iw y)]
  rw [sum_iw_split (F := fun iw => star (ψ iw x) * ψ iw y)]
  refine Finset.sum_congr rfl (fun i' _ => ?_)
  by_cases hi : i' = i
  · subst i'
    have hval : ∀ (a : Fin d) (z : Fin Z),
        star (valueQuery hd i ψ ((i, a), z) x) * valueQuery hd i ψ ((i, a), z) y
          = star (ψ ((i, addFin hd a (x i)), z) x) * ψ ((i, addFin hd a (x i)), z) y := by
      intro a z
      simp [valueQuery, hxy]
    simp only [hval]
    exact sum_addFin_shift hd
      (fun a => ∑ z : Fin Z, star (ψ ((i, a), z) x) * ψ ((i, a), z) y) (x i)
  · have hval : ∀ (a : Fin d) (z : Fin Z),
        star (valueQuery hd i ψ ((i', a), z) x) * valueQuery hd i ψ ((i', a), z) y
          = star (ψ ((i', a), z) x) * ψ ((i', a), z) y := by
      intro a z
      simp [valueQuery, hi]
    simp only [hval]

/-- The norm of the Gram-entry change under a value query is at most twice the product of the
square roots of the two input-column masses. -/
theorem rhoEntry_valueQuery_diff_le {n d Z : ℕ} (hd : 0 < d) (i : Fin n)
    (ψ : ((Fin n × Fin d) × Fin Z) → InputD n d → ℂ) (x y : InputD n d) :
    ‖rhoEntry (valueQuery hd i ψ) x y - rhoEntry ψ x y‖ ≤
      2 * (Real.sqrt (mass ψ x) * Real.sqrt (mass ψ y)) := by
  have h1 := rhoEntry_norm_le (valueQuery hd i ψ) x y
  have h2 := rhoEntry_norm_le ψ x y
  have hm1 : (∑ iw, ‖valueQuery hd i ψ iw x‖ ^ 2) = mass ψ x := mass_valueQuery hd i ψ x
  have hm2 : (∑ iw, ‖valueQuery hd i ψ iw y‖ ^ 2) = mass ψ y := mass_valueQuery hd i ψ y
  rw [hm1, hm2] at h1
  rw [show (∑ iw, ‖ψ iw x‖ ^ 2) = mass ψ x from rfl,
    show (∑ iw, ‖ψ iw y‖ ^ 2) = mass ψ y from rfl] at h2
  calc ‖rhoEntry (valueQuery hd i ψ) x y - rhoEntry ψ x y‖
      ≤ ‖rhoEntry (valueQuery hd i ψ) x y‖ + ‖rhoEntry ψ x y‖ := norm_sub_le _ _
    _ ≤ Real.sqrt (mass ψ x) * Real.sqrt (mass ψ y) +
          Real.sqrt (mass ψ x) * Real.sqrt (mass ψ y) := add_le_add h1 h2
    _ = 2 * (Real.sqrt (mass ψ x) * Real.sqrt (mass ψ y)) := by ring

/-- Under the stated local mismatch-degree product bound and total-mass bound, the sum of
Gram-entry changes from one value query is at most `sqrt lmax`. See [Ambainis2002]. -/
theorem progress_valueQuery_step_le_lmax {n d Z : ℕ} (hd : 0 < d)
    (X Y : Finset (InputD n d)) (R : Finset (InputD n d × InputD n d)) (lmax : ℕ)
    (i : Fin n) (ψ : ((Fin n × Fin d) × Fin Z) → InputD n d → ℂ)
    (lx ly : InputD n d → ℕ)
    (hRsub : ∀ p ∈ R, p.1 ∈ X ∧ p.2 ∈ Y)
    (hxcard : ∀ x ∈ X, (R.filter (fun p => p.1 = x ∧ p.2 i ≠ x i)).card = lx x)
    (hycard : ∀ y ∈ Y, (R.filter (fun p => p.2 = y ∧ p.1 i ≠ y i)).card = ly y)
    (hlmax : ∀ p ∈ R, p.1 i ≠ p.2 i → lx p.1 * ly p.2 ≤ lmax)
    (hmass : (∑ iw, ∑ x ∈ X, ‖ψ iw x‖ ^ 2) + (∑ iw, ∑ y ∈ Y, ‖ψ iw y‖ ^ 2) ≤ 1) :
    ∑ p ∈ R, ‖rhoEntry (valueQuery hd i ψ) p.1 p.2 - rhoEntry ψ p.1 p.2‖ ≤
      Real.sqrt (lmax : ℝ) := by
  classical
  let A : InputD n d → ℝ := fun x => ∑ iw, ‖ψ iw x‖ ^ 2
  have hAnonneg : ∀ x, 0 ≤ A x := fun x => Finset.sum_nonneg (fun iw _ => by positivity)
  set R' : Finset (InputD n d × InputD n d) := R.filter (fun p => p.1 i ≠ p.2 i) with hR'def

  have hterm : ∀ p ∈ R, ‖rhoEntry (valueQuery hd i ψ) p.1 p.2 - rhoEntry ψ p.1 p.2‖ =
      if p.1 i = p.2 i then 0
        else ‖rhoEntry (valueQuery hd i ψ) p.1 p.2 - rhoEntry ψ p.1 p.2‖ := by
    intro p hp
    by_cases h : p.1 i = p.2 i
    · rw [if_pos h, rhoEntry_valueQuery_same hd i ψ p.1 p.2 h, sub_self, norm_zero]
    · rw [if_neg h]
  rw [Finset.sum_congr rfl hterm]
  have hfilt : (∑ p ∈ R, if p.1 i = p.2 i then 0
        else ‖rhoEntry (valueQuery hd i ψ) p.1 p.2 - rhoEntry ψ p.1 p.2‖)
      = ∑ p ∈ R', ‖rhoEntry (valueQuery hd i ψ) p.1 p.2 - rhoEntry ψ p.1 p.2‖ := by
    rw [hR'def, Finset.sum_filter (s := R) (p := fun p => p.1 i ≠ p.2 i)
      (f := fun p => ‖rhoEntry (valueQuery hd i ψ) p.1 p.2 - rhoEntry ψ p.1 p.2‖)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : p.1 i = p.2 i <;> simp [h]
  rw [hfilt]

  have hlxpos : ∀ p ∈ R', 0 < lx p.1 := by
    intro p hp
    have hpR : p ∈ R := (Finset.mem_filter.mp hp).1
    have hdiff : p.1 i ≠ p.2 i := (Finset.mem_filter.mp hp).2
    have hc : (R.filter (fun q => q.1 = p.1 ∧ q.2 i ≠ p.1 i)).card = lx p.1 :=
      hxcard p.1 (hRsub p hpR).1
    have hpos : 0 < (R.filter (fun q => q.1 = p.1 ∧ q.2 i ≠ p.1 i)).card :=
      Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hpR, rfl, Ne.symm hdiff⟩⟩
    rwa [hc] at hpos
  have hlypos : ∀ p ∈ R', 0 < ly p.2 := by
    intro p hp
    have hpR : p ∈ R := (Finset.mem_filter.mp hp).1
    have hdiff : p.1 i ≠ p.2 i := (Finset.mem_filter.mp hp).2
    have hc : (R.filter (fun q => q.2 = p.2 ∧ q.1 i ≠ p.2 i)).card = ly p.2 :=
      hycard p.2 (hRsub p hpR).2
    have hpos : 0 < (R.filter (fun q => q.2 = p.2 ∧ q.1 i ≠ p.2 i)).card :=
      Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hpR, rfl, hdiff⟩⟩
    rwa [hc] at hpos
  have hpoint : ∀ p ∈ R', ‖rhoEntry (valueQuery hd i ψ) p.1 p.2 - rhoEntry ψ p.1 p.2‖ ≤
      Real.sqrt ((ly p.2 : ℝ) / (lx p.1 : ℝ)) * A p.1 +
        Real.sqrt ((lx p.1 : ℝ) / (ly p.2 : ℝ)) * A p.2 := by
    intro p hp
    have hαnn : 0 ≤ Real.sqrt ((ly p.2 : ℝ) / (lx p.1 : ℝ)) := Real.sqrt_nonneg _
    have hβnn : 0 ≤ Real.sqrt ((lx p.1 : ℝ) / (ly p.2 : ℝ)) := Real.sqrt_nonneg _
    have hαβ : Real.sqrt ((ly p.2 : ℝ) / (lx p.1 : ℝ)) *
        Real.sqrt ((lx p.1 : ℝ) / (ly p.2 : ℝ)) = 1 := by
      have hmul : Real.sqrt (((ly p.2 : ℝ) / (lx p.1 : ℝ)) *
            ((lx p.1 : ℝ) / (ly p.2 : ℝ))) =
          Real.sqrt ((ly p.2 : ℝ) / (lx p.1 : ℝ)) *
            Real.sqrt ((lx p.1 : ℝ) / (ly p.2 : ℝ)) :=
        Real.sqrt_mul (x := (ly p.2 : ℝ) / (lx p.1 : ℝ)) (by positivity) ((lx p.1 : ℝ) / (ly p.2 : ℝ))
      rw [← hmul]
      rw [show ((ly p.2 : ℝ) / (lx p.1 : ℝ)) * ((lx p.1 : ℝ) / (ly p.2 : ℝ)) = 1 by
        have h1 : (lx p.1 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hlxpos p hp))
        have h2 : (ly p.2 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hlypos p hp))
        field_simp]
      exact Real.sqrt_one
    have hρ := rhoEntry_valueQuery_diff_le hd i ψ p.1 p.2
    have hρ' : ‖rhoEntry (valueQuery hd i ψ) p.1 p.2 - rhoEntry ψ p.1 p.2‖ ≤
        2 * (Real.sqrt (A p.1) * Real.sqrt (A p.2)) := hρ
    have h2 := amgm_two (A := A p.1) (B := A p.2) (hAnonneg p.1) (hAnonneg p.2)
      hαnn hβnn hαβ
    linarith [hρ', h2]
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [Finset.sum_add_distrib]

  have hfilteqX : ∀ x, R'.filter (fun p => p.1 = x)
      = R.filter (fun p => p.1 = x ∧ p.2 i ≠ x i) := by
    intro x
    rw [hR'def, Finset.filter_filter]
    apply Finset.filter_congr
    intro p hp
    constructor
    · rintro ⟨hne, hpx⟩
      exact ⟨hpx, fun h2 => hne (by rw [hpx, h2])⟩
    · rintro ⟨hpx, hne⟩
      exact ⟨fun h2 => hne (by rw [← hpx]; exact h2.symm), hpx⟩
  have hfilteqY : ∀ y, R'.filter (fun p => p.2 = y)
      = R.filter (fun p => p.2 = y ∧ p.1 i ≠ y i) := by
    intro y
    rw [hR'def, Finset.filter_filter]
    apply Finset.filter_congr
    intro p hp
    constructor
    · rintro ⟨hne, hpy⟩
      exact ⟨hpy, fun h2 => hne (by rw [h2, hpy])⟩
    · rintro ⟨hpy, hne⟩
      exact ⟨fun h2 => hne (by rw [h2, ← hpy]), hpy⟩
  have hcardX : ∀ x ∈ X, (R'.filter (fun p => p.1 = x)).card = lx x := by
    intro x hx; rw [hfilteqX x]; exact hxcard x hx
  have hcardY : ∀ y ∈ Y, (R'.filter (fun p => p.2 = y)).card = ly y := by
    intro y hy; rw [hfilteqY y]; exact hycard y hy

  have hfiberX : ∑ p ∈ R', Real.sqrt ((ly p.2 : ℝ) / (lx p.1 : ℝ)) * A p.1
      = ∑ x ∈ X, A x * ∑ p ∈ R'.filter (fun p => p.1 = x),
          Real.sqrt ((ly p.2 : ℝ) / (lx x : ℝ)) := by
    have h := Finset.sum_fiberwise_of_maps_to
      (s := R') (t := X) (g := fun p => p.1)
      (h := fun p hp => (hRsub p (Finset.mem_filter.mp hp).1).1)
      (f := fun p => Real.sqrt ((ly p.2 : ℝ) / (lx p.1 : ℝ)) * A p.1)
    rw [← h]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hpx : p.1 = x := (Finset.mem_filter.mp hp).2
    rw [hpx]; ring
  have hfiberY : ∑ p ∈ R', Real.sqrt ((lx p.1 : ℝ) / (ly p.2 : ℝ)) * A p.2
      = ∑ y ∈ Y, A y * ∑ p ∈ R'.filter (fun p => p.2 = y),
          Real.sqrt ((lx p.1 : ℝ) / (ly y : ℝ)) := by
    have h := Finset.sum_fiberwise_of_maps_to
      (s := R') (t := Y) (g := fun p => p.2)
      (h := fun p hp => (hRsub p (Finset.mem_filter.mp hp).1).2)
      (f := fun p => Real.sqrt ((lx p.1 : ℝ) / (ly p.2 : ℝ)) * A p.2)
    rw [← h]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hpy : p.2 = y := (Finset.mem_filter.mp hp).2
    rw [hpy]; ring
  have hinnerX : ∀ x ∈ X, ∑ p ∈ R'.filter (fun p => p.1 = x),
      Real.sqrt ((ly p.2 : ℝ) / (lx x : ℝ)) ≤ Real.sqrt (lmax : ℝ) := by
    intro x hx
    have hcard : (R'.filter (fun p => p.1 = x)).card = lx x := hcardX x hx
    rcases Nat.eq_zero_or_pos (lx x) with h0 | hpos
    · have hz : (R'.filter (fun p => p.1 = x)).card = 0 := by rw [hcard, h0]
      rw [Finset.card_eq_zero.mp hz]; simp
    · calc ∑ p ∈ R'.filter (fun p => p.1 = x), Real.sqrt ((ly p.2 : ℝ) / (lx x : ℝ))
          ≤ ∑ p ∈ R'.filter (fun p => p.1 = x), Real.sqrt (lmax : ℝ) / (lx x : ℝ) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hpR : p ∈ R' := (Finset.mem_filter.mp hp).1
            have hpRsubR : p ∈ R := (Finset.mem_filter.mp hpR).1
            have hdiff : p.1 i ≠ p.2 i := (Finset.mem_filter.mp hpR).2
            have hlyp : 0 < ly p.2 := hlypos p hpR
            have hprod : lx x * ly p.2 ≤ lmax := by
              have := hlmax p hpRsubR hdiff
              rwa [(Finset.mem_filter.mp hp).2] at this
            exact sqrt_div_le hpos hlyp hprod
        _ = ((R'.filter (fun p => p.1 = x)).card : ℝ) *
              (Real.sqrt (lmax : ℝ) / (lx x : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = (lx x : ℝ) * (Real.sqrt (lmax : ℝ) / (lx x : ℝ)) := by rw [hcard]
        _ = Real.sqrt (lmax : ℝ) := by
              rw [mul_div_cancel₀ _ (by exact_mod_cast (ne_of_gt hpos))]
  have hinnerY : ∀ y ∈ Y, ∑ p ∈ R'.filter (fun p => p.2 = y),
      Real.sqrt ((lx p.1 : ℝ) / (ly y : ℝ)) ≤ Real.sqrt (lmax : ℝ) := by
    intro y hy
    have hcard : (R'.filter (fun p => p.2 = y)).card = ly y := hcardY y hy
    rcases Nat.eq_zero_or_pos (ly y) with h0 | hpos
    · have hz : (R'.filter (fun p => p.2 = y)).card = 0 := by rw [hcard, h0]
      rw [Finset.card_eq_zero.mp hz]; simp
    · calc ∑ p ∈ R'.filter (fun p => p.2 = y), Real.sqrt ((lx p.1 : ℝ) / (ly y : ℝ))
          ≤ ∑ p ∈ R'.filter (fun p => p.2 = y), Real.sqrt (lmax : ℝ) / (ly y : ℝ) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hpR : p ∈ R' := (Finset.mem_filter.mp hp).1
            have hpRsubR : p ∈ R := (Finset.mem_filter.mp hpR).1
            have hdiff : p.1 i ≠ p.2 i := (Finset.mem_filter.mp hpR).2
            have hlxp : 0 < lx p.1 := hlxpos p hpR
            have hprod : ly y * lx p.1 ≤ lmax := by
              have := hlmax p hpRsubR hdiff
              rw [(Finset.mem_filter.mp hp).2] at this
              rwa [mul_comm]
            exact sqrt_div_le hpos hlxp hprod
        _ = ((R'.filter (fun p => p.2 = y)).card : ℝ) *
              (Real.sqrt (lmax : ℝ) / (ly y : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = (ly y : ℝ) * (Real.sqrt (lmax : ℝ) / (ly y : ℝ)) := by rw [hcard]
        _ = Real.sqrt (lmax : ℝ) := by
              rw [mul_div_cancel₀ _ (by exact_mod_cast (ne_of_gt hpos))]
  have hXbound : ∑ p ∈ R', Real.sqrt ((ly p.2 : ℝ) / (lx p.1 : ℝ)) * A p.1
      ≤ Real.sqrt (lmax : ℝ) * ∑ x ∈ X, A x := by
    rw [hfiberX]
    calc ∑ x ∈ X, A x * ∑ p ∈ R'.filter (fun p => p.1 = x),
            Real.sqrt ((ly p.2 : ℝ) / (lx x : ℝ))
        ≤ ∑ x ∈ X, A x * Real.sqrt (lmax : ℝ) := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          exact mul_le_mul_of_nonneg_left (hinnerX x hx) (hAnonneg x)
      _ = Real.sqrt (lmax : ℝ) * ∑ x ∈ X, A x := by rw [← Finset.sum_mul, mul_comm]
  have hYbound : ∑ p ∈ R', Real.sqrt ((lx p.1 : ℝ) / (ly p.2 : ℝ)) * A p.2
      ≤ Real.sqrt (lmax : ℝ) * ∑ y ∈ Y, A y := by
    rw [hfiberY]
    calc ∑ y ∈ Y, A y * ∑ p ∈ R'.filter (fun p => p.2 = y),
            Real.sqrt ((lx p.1 : ℝ) / (ly y : ℝ))
        ≤ ∑ y ∈ Y, A y * Real.sqrt (lmax : ℝ) := by
          refine Finset.sum_le_sum (fun y hy => ?_)
          exact mul_le_mul_of_nonneg_left (hinnerY y hy) (hAnonneg y)
      _ = Real.sqrt (lmax : ℝ) * ∑ y ∈ Y, A y := by rw [← Finset.sum_mul, mul_comm]
  refine (add_le_add hXbound hYbound).trans ?_
  have hmassA : (∑ x ∈ X, A x) + (∑ y ∈ Y, A y) ≤ 1 := by
    have hAX : ∑ x ∈ X, A x = ∑ iw, ∑ x ∈ X, ‖ψ iw x‖ ^ 2 := by
      rw [show A = fun x => ∑ iw, ‖ψ iw x‖ ^ 2 from rfl]; exact Finset.sum_comm
    have hAY : ∑ y ∈ Y, A y = ∑ iw, ∑ y ∈ Y, ‖ψ iw y‖ ^ 2 := by
      rw [show A = fun y => ∑ iw, ‖ψ iw y‖ ^ 2 from rfl]; exact Finset.sum_comm
    rw [hAX, hAY]; exact hmass
  calc Real.sqrt (lmax : ℝ) * ∑ x ∈ X, A x + Real.sqrt (lmax : ℝ) * ∑ y ∈ Y, A y
      = Real.sqrt (lmax : ℝ) * ((∑ x ∈ X, A x) + (∑ y ∈ Y, A y)) := by ring
    _ ≤ Real.sqrt (lmax : ℝ) * 1 := by
        refine mul_le_mul_of_nonneg_left hmassA (Real.sqrt_nonneg _)
    _ = Real.sqrt (lmax : ℝ) := by ring

/-- A value query commutes with multiplication by a complex amplitude depending only on the
input. See [Ambainis2002]. -/
theorem valueQuery_smul {n d Z : ℕ} (β : InputD n d → ℂ) (hd : 0 < d) (i : Fin n)
    (f : ((Fin n × Fin d) × Fin Z) → InputD n d → ℂ) :
    valueQuery hd i (fun iw x => β x * f iw x) =
      (fun iw x => β x * valueQuery hd i f iw x) := by
  funext iw x
  unfold valueQuery
  by_cases h : iw.1.1 = i <;> simp [h]

end Qatlib.Papers.QLowerBound00.MainResults.Model
