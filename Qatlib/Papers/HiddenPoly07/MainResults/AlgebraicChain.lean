/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic
import Qatlib.Papers.HiddenPoly07.MainResults.CountingLemmas
import Qatlib.Papers.HiddenPoly07.MainResults.GoodSetCardinality
import Qatlib.Papers.HiddenPoly07.MainResults.MeasurementSuccessBound
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HiddenPoly07.MainResults

open scoped BigOperators

theorem image_card_ge_of_fiber_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (hn : 1 ≤ n) (φ : (Fin n → F) → (Fin n → F))
    (q : MvPolynomial (Fin n) F) (hq : q ≠ 0) (D : ℕ) (hD : 0 < D)
    (hfib : ∀ b, MvPolynomial.eval b q ≠ 0 →
      (Finset.univ.filter (fun b' => φ b' = φ b)).card ≤ D) :
    ((Fintype.card F : ℝ) ^ n - (q.totalDegree : ℝ) * (Fintype.card F : ℝ) ^ (n - 1)) / D
      ≤ ((Finset.univ.image φ).card : ℝ) := by
  classical
  set good : Finset (Fin n → F) :=
    Finset.univ.filter (fun b => MvPolynomial.eval b q ≠ 0) with hgood
  have hgood_ge : (Fintype.card F : ℝ) ^ n
      - (q.totalDegree : ℝ) * (Fintype.card F : ℝ) ^ (n - 1) ≤ (good.card : ℝ) := by
    have h := good_set_card_ge_raw (F := F) hn q hq
    simpa only [← hgood] using h
  have hfib_good : ∀ b ∈ good.image φ, (good.filter (fun a => φ a = b)).card ≤ D := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    have hqa : MvPolynomial.eval a q ≠ 0 := by
      simpa only [hgood, Finset.mem_filter, Finset.mem_univ, true_and] using ha
    have hsub : good.filter (fun a' => φ a' = φ a)
        ⊆ Finset.univ.filter (fun a' => φ a' = φ a) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx.2
    exact le_trans (Finset.card_le_card hsub) (hfib a hqa)
  have hcount := card_le_mul_card_image good φ D hfib_good
  have hsub2 : good.image φ ⊆ Finset.univ.image φ := by
    intro b hb
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
  have hle_img : (good.image φ).card ≤ (Finset.univ.image φ).card :=
    Finset.card_le_card hsub2
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hcountR : (good.card : ℝ) ≤ (D : ℝ) * ((Finset.univ.image φ).card : ℝ) := by
    have h1 : (good.card : ℝ) ≤ (D : ℝ) * ((good.image φ).card : ℝ) := by exact_mod_cast hcount
    have h2 : (D : ℝ) * ((good.image φ).card : ℝ) ≤ (D : ℝ) * ((Finset.univ.image φ).card : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast hle_img
    linarith
  rw [div_le_iff₀ hDpos]
  nlinarith [hgood_ge, hcountR]

theorem image_card_ge_of_big_field {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (hn : 1 ≤ n) (φ : (Fin n → F) → (Fin n → F))
    (q : MvPolynomial (Fin n) F) (hq : q ≠ 0) (D : ℕ) (hD : 0 < D)
    (hfib : ∀ b, MvPolynomial.eval b q ≠ 0 →
      (Finset.univ.filter (fun b' => φ b' = φ b)).card ≤ D)
    (hbig : 2 * q.totalDegree ≤ Fintype.card F) :
    (1 / (2 * (D : ℝ))) * (Fintype.card F : ℝ) ^ n
      ≤ ((Finset.univ.image φ).card : ℝ) := by
  classical
  set d : ℕ := Fintype.card F with hd
  set e : ℕ := q.totalDegree with he
  have hdpos : 0 < d := Fintype.card_pos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hmain := image_card_ge_of_fiber_bound (F := F) hn φ q hq D hD hfib
  have hbigR : (2 : ℝ) * (e : ℝ) ≤ (d : ℝ) := by exact_mod_cast hbig

  have h1 : (d : ℝ) ^ n - (e : ℝ) * (d : ℝ) ^ (n - 1) = (d : ℝ) ^ (n - 1) * ((d : ℝ) - (e : ℝ)) := by
    have hsplit : (d : ℝ) ^ n = (d : ℝ) ^ (n - 1) * (d : ℝ) := by
      rw [← pow_succ, Nat.sub_add_cancel hn]
    rw [hsplit]; ring
  have h2 : (d : ℝ) ^ n / 2 ≤ (d : ℝ) ^ n - (e : ℝ) * (d : ℝ) ^ (n - 1) := by
    rw [h1]
    have h3 : (d : ℝ) ^ (n - 1) * ((d : ℝ) / 2) = (d : ℝ) ^ n / 2 := by
      have hsplit : (d : ℝ) ^ n = (d : ℝ) ^ (n - 1) * (d : ℝ) := by
        rw [← pow_succ, Nat.sub_add_cancel hn]
      rw [hsplit]; ring
    rw [← h3]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have hfrac : (d : ℝ) ^ n / (2 * (D : ℝ))
      ≤ ((d : ℝ) ^ n - (e : ℝ) * (d : ℝ) ^ (n - 1)) / (D : ℝ) := by
    have hsplit : (d : ℝ) ^ n / (2 * (D : ℝ)) = ((d : ℝ) ^ n / 2) / (D : ℝ) := by
      field_simp
    rw [hsplit]
    apply div_le_div_of_nonneg_right _ (le_of_lt hDpos)
    exact h2
  have heq : (1 / (2 * (D : ℝ))) * (d : ℝ) ^ n = (d : ℝ) ^ n / (2 * (D : ℝ)) := by ring
  rw [heq]
  exact le_trans hfrac hmain

theorem prop43_image_lower_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {m n : ℕ} (hn : 1 ≤ n) (f : (Fin m → F) → (Fin n → F) → (Fin n → F))
    (x : Fin m → F) (q : MvPolynomial (Fin n) F) (hq : q ≠ 0) (D : ℕ) (hD : 0 < D)
    (hfib : ∀ b, MvPolynomial.eval b q ≠ 0 →
      (Finset.univ.filter (fun b' => f x b' = f x b)).card ≤ D)
    (hbig : 2 * q.totalDegree ≤ Fintype.card F) :
    (1 / (2 * (D : ℝ))) * (Fintype.card F : ℝ) ^ n
      ≤ ((Finset.univ.image (fun b => f x b)).card : ℝ) :=
  image_card_ge_of_big_field (F := F) hn (fun b => f x b) q hq D hD hfib hbig

theorem Wgood_card_ge_of_fiber_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (φ : (Fin n → F) → (Fin n → F))
    (U : Finset (Fin n → F)) (hU : U.card = (Fintype.card F).descFactorial n)
    (Ix : Finset (Fin n → F)) (κ : ℕ)
    (hIx : Ix.card ≤ κ * (Fintype.card F) ^ (n - 1))
    (D : ℕ) (hD : 0 < D)
    (hfib : ∀ b ∈ U, (U.filter (fun b' => φ b' = φ b)).card ≤ D) :
    ((Fintype.card F).descFactorial n : ℝ) / D
        - (κ : ℝ) * (Fintype.card F : ℝ) ^ (n - 1)
      ≤ ((U.image φ \ Ix).card : ℝ) := by
  classical
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hfib' : ∀ b ∈ U.image φ, (U.filter (fun a => φ a = b)).card ≤ D := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact hfib a ha
  have hcount := card_le_mul_card_image U φ D hfib'
  have hcountR : (U.card : ℝ) / (D : ℝ) ≤ ((U.image φ).card : ℝ) := by
    rw [div_le_iff₀ hDpos]
    have h1 : (U.card : ℝ) ≤ (D : ℝ) * ((U.image φ).card : ℝ) := by exact_mod_cast hcount
    nlinarith [h1]

  have hcover : (U.image φ).card ≤ (U.image φ \ Ix).card + Ix.card := by
    have hsub : U.image φ ⊆ (U.image φ \ Ix) ∪ Ix := by
      intro a ha
      by_cases h : a ∈ Ix
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha, h⟩)
    calc (U.image φ).card ≤ ((U.image φ \ Ix) ∪ Ix).card := Finset.card_le_card hsub
      _ ≤ (U.image φ \ Ix).card + Ix.card := Finset.card_union_le _ _
  have hcoverR : ((U.image φ).card : ℝ)
      ≤ ((U.image φ \ Ix).card : ℝ) + (Ix.card : ℝ) := by exact_mod_cast hcover
  have hIxR : (Ix.card : ℝ) ≤ (κ : ℝ) * (Fintype.card F : ℝ) ^ (n - 1) := by
    exact_mod_cast hIx
  have hUeq : (U.card : ℝ) = ((Fintype.card F).descFactorial n : ℝ) := by rw [hU]
  have hc : ((Fintype.card F).descFactorial n : ℝ) / (D : ℝ)
      ≤ ((U.image φ).card : ℝ) := by rw [← hUeq]; exact hcountR
  have hstep : ((Fintype.card F).descFactorial n : ℝ) / (D : ℝ)
      - (κ : ℝ) * (Fintype.card F : ℝ) ^ (n - 1)
      ≤ ((U.image φ).card : ℝ) - (Ix.card : ℝ) := by
    linarith [hc, hIxR]
  have hstep2 : ((U.image φ).card : ℝ) - (Ix.card : ℝ)
      ≤ ((U.image φ \ Ix).card : ℝ) := by linarith [hcoverR]
  linarith [hstep, hstep2]

theorem WgoodMin_ge {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (X : Finset (Fin n → F)) (W : (Fin n → F) → Finset (Fin n → F)) {c : ℝ}
    (hne : X.Nonempty) (h : ∀ x ∈ X, c ≤ ((W x).card : ℝ)) :
    c ≤ ((WgoodMin X W : ℕ) : ℝ) := by
  classical
  unfold WgoodMin
  rw [dif_pos hne]
  obtain ⟨x, hx, hxe⟩ :=
    Finset.mem_image.mp (Finset.min'_mem (X.image fun x => (W x).card) (hne.image _))
  rw [← hxe]
  exact h x hx

theorem success_constant_of_good_counts {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (X : Finset (Fin n → F)) (W : (Fin n → F) → Finset (Fin n → F))
    (eta : (Fin n → F) → (Fin n → F) → ℕ)
    (hη : ∀ x ∈ X, ∀ w ∈ W x, 1 ≤ eta x w)
    (hXc : (Fintype.card F : ℝ) ^ n / 2 ^ n ≤ (X.card : ℝ))
    (hWc : ∀ x ∈ X, (Fintype.card F : ℝ) ^ n / 2 ^ n ≤ ((W x).card : ℝ)) :
    ((2 : ℝ) ^ (3 * n))⁻¹
      ≤ ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ *
          ∑ x ∈ X, (∑ w ∈ W x, Real.sqrt (eta x w)) ^ 2 := by
  classical
  have hd : 0 < Fintype.card F := Fintype.card_pos
  have hpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ n / 2 ^ n := by positivity
  have hXpos : (0 : ℝ) < (X.card : ℝ) := lt_of_lt_of_le hpos hXc
  have hXne : X.Nonempty := Finset.card_pos.mp (by exact_mod_cast hXpos)
  have hWmin : (Fintype.card F : ℝ) ^ n / 2 ^ n ≤ ((WgoodMin X W : ℕ) : ℝ) :=
    WgoodMin_ge X W hXne hWc
  exact success_probability_constant_of_good_counts X W eta hη hd hXc hWmin

theorem prop46_success_of_nonvanishing {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (hn : 1 ≤ n)
    (g : MvPolynomial (Fin n) F) (hg : g ≠ 0)
    (hW : (Fin n → F) → MvPolynomial (Fin n) F)
    (hhW : ∀ x, MvPolynomial.eval x g ≠ 0 → hW x ≠ 0)
    (degW : ℕ)
    (hdegW : ∀ x, MvPolynomial.eval x g ≠ 0 → (hW x).totalDegree ≤ degW)
    (eta : (Fin n → F) → (Fin n → F) → ℕ)
    (hη : ∀ x, MvPolynomial.eval x g ≠ 0 →
      ∀ w, MvPolynomial.eval w (hW x) ≠ 0 → 1 ≤ eta x w)
    (hbigG : 2 * g.totalDegree ≤ Fintype.card F)
    (hbigW : 2 * degW ≤ Fintype.card F) :
    ((2 : ℝ) ^ (3 * n))⁻¹
      ≤ ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ *
          ∑ x ∈ Finset.univ.filter (fun x => MvPolynomial.eval x g ≠ 0),
            (∑ w ∈ Finset.univ.filter (fun w => MvPolynomial.eval w (hW x) ≠ 0),
              Real.sqrt (eta x w)) ^ 2 := by
  classical
  have hXc : (Fintype.card F : ℝ) ^ n / 2 ^ n
      ≤ ((Finset.univ.filter (fun x => MvPolynomial.eval x g ≠ 0)).card : ℝ) :=
    good_set_card_ge (F := F) hn g hg hbigG
  have hWc : ∀ x ∈ Finset.univ.filter (fun x => MvPolynomial.eval x g ≠ 0),
      (Fintype.card F : ℝ) ^ n / 2 ^ n
        ≤ ((Finset.univ.filter (fun w => MvPolynomial.eval w (hW x) ≠ 0)).card : ℝ) := by
    intro x hx
    have hgx : MvPolynomial.eval x g ≠ 0 := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx
    have hbigx : 2 * (hW x).totalDegree ≤ Fintype.card F :=
      le_trans (Nat.mul_le_mul_left 2 (hdegW x hgx)) hbigW
    exact good_set_card_ge (F := F) hn (hW x) (hhW x hgx) hbigx
  have hη' : ∀ x ∈ Finset.univ.filter (fun x => MvPolynomial.eval x g ≠ 0),
      ∀ w ∈ Finset.univ.filter (fun w => MvPolynomial.eval w (hW x) ≠ 0), 1 ≤ eta x w := by
    intro x hx w hw
    have hgx : MvPolynomial.eval x g ≠ 0 := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx
    have hwx : MvPolynomial.eval w (hW x) ≠ 0 := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hw
    exact hη x hgx w hwx
  exact success_constant_of_good_counts _ _ eta hη' hXc hWc

theorem cor42_arith {d n D : ℕ} (hd : 0 < d) (hD : 0 < D) :
    (1 : ℝ) / (2 ^ (3 * n + 2) * (D : ℝ) ^ 2)
      ≤ ((d : ℝ) ^ (3 * n))⁻¹
          * (((d : ℝ) ^ n / 2 ^ n) * (((d : ℝ) ^ n / (2 ^ (n + 1) * (D : ℝ))) ^ 2)) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hd3 : (0 : ℝ) < (d : ℝ) ^ (3 * n) := pow_pos hdR _
  have hden : (0 : ℝ) < 2 ^ (3 * n + 2) * (D : ℝ) ^ 2 := by positivity
  rw [le_iff_eq_or_lt]
  left
  have hd0 : (d : ℝ) ≠ 0 := hdR.ne'
  have hD0 : (D : ℝ) ≠ 0 := hDR.ne'
  have h2 : (2 : ℝ) ^ n * 2 ^ (2 * n + 2) = 2 ^ (3 * n + 2) := by
    rw [← pow_add]; congr 1; omega
  rw [eq_comm]
  field_simp
  ring_nf

theorem cor42_constant_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n D : ℕ} (_hn : 1 ≤ n) (hD : 0 < D)
    (X : Finset (Fin n → F)) (W : (Fin n → F) → Finset (Fin n → F))
    (eta : (Fin n → F) → (Fin n → F) → ℕ)
    (hη : ∀ x ∈ X, ∀ w ∈ W x, 1 ≤ eta x w)
    (hXc : (Fintype.card F : ℝ) ^ n / 2 ^ n ≤ (X.card : ℝ))
    (hWc : ∀ x ∈ X, (Fintype.card F : ℝ) ^ n / (2 ^ (n + 1) * (D : ℝ))
      ≤ ((W x).card : ℝ)) :
    (1 : ℝ) / (2 ^ (3 * n + 2) * (D : ℝ) ^ 2)
      ≤ ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ *
          ∑ x ∈ X, (∑ w ∈ W x, Real.sqrt (eta x w)) ^ 2 := by
  classical
  have hd : 0 < Fintype.card F := Fintype.card_pos
  have hdR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hd
  have hpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ n / 2 ^ n := by positivity
  have hXpos : (0 : ℝ) < (X.card : ℝ) := lt_of_lt_of_le hpos hXc
  have hXne : X.Nonempty := Finset.card_pos.mp (by exact_mod_cast hXpos)
  have hWmin : (Fintype.card F : ℝ) ^ n / (2 ^ (n + 1) * (D : ℝ))
      ≤ ((WgoodMin X W : ℕ) : ℝ) := WgoodMin_ge X W hXne hWc
  have hmain := lemma31_success_lower_bound X W eta hη

  have hX0 : (0 : ℝ) ≤ (X.card : ℝ) := by positivity
  have hW0 : (0 : ℝ) ≤ ((WgoodMin X W : ℕ) : ℝ) := by positivity
  have hprod : ((Fintype.card F : ℝ) ^ n / 2 ^ n)
        * (((Fintype.card F : ℝ) ^ n / (2 ^ (n + 1) * (D : ℝ))) ^ 2)
      ≤ ((X.card : ℝ) * ((WgoodMin X W : ℕ) : ℝ) ^ 2) := by
    apply mul_le_mul hXc _ _ hX0
    · exact pow_le_pow_left₀ (by positivity) hWmin 2
    · positivity
  have harith := cor42_arith (d := Fintype.card F) (n := n) (D := D) hd hD
  have hnonneg : (0 : ℝ) ≤ ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ := by positivity
  calc (1 : ℝ) / (2 ^ (3 * n + 2) * (D : ℝ) ^ 2)
      ≤ ((Fintype.card F : ℝ) ^ (3 * n))⁻¹
          * (((Fintype.card F : ℝ) ^ n / 2 ^ n)
            * (((Fintype.card F : ℝ) ^ n / (2 ^ (n + 1) * (D : ℝ))) ^ 2)) := harith
    _ ≤ ((Fintype.card F : ℝ) ^ (3 * n))⁻¹
          * ((X.card : ℝ) * ((WgoodMin X W : ℕ) : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hprod hnonneg
    _ ≤ _ := hmain

theorem cor42_source_chain {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n D κ : ℕ} (_hD : 0 < D)
    (W : (Fin n → F) → Finset (Fin n → F))
    (eta : (Fin n → F) → (Fin n → F) → ℕ)
    (hη : ∀ x ∈ Xgood F n, ∀ w ∈ W x, 1 ≤ eta x w)
    (hc : 0 ≤ ((Fintype.card F).descFactorial n : ℝ) / (D : ℝ)
      - (κ : ℝ) * (Fintype.card F : ℝ) ^ (n - 1))
    (hW : ∀ x ∈ Xgood F n,
      ((Fintype.card F).descFactorial n : ℝ) / (D : ℝ)
        - (κ : ℝ) * (Fintype.card F : ℝ) ^ (n - 1) ≤ ((W x).card : ℝ)) :
    ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ *
        (((Xgood F n).card : ℝ) *
          (((Fintype.card F).descFactorial n : ℝ) / (D : ℝ)
            - (κ : ℝ) * (Fintype.card F : ℝ) ^ (n - 1)) ^ 2)
      ≤ ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ *
          ∑ x ∈ Xgood F n, (∑ w ∈ W x, Real.sqrt (eta x w)) ^ 2 := by
  classical
  set c : ℝ := ((Fintype.card F).descFactorial n : ℝ) / (D : ℝ)
    - (κ : ℝ) * (Fintype.card F : ℝ) ^ (n - 1) with hcdef
  have hper : ∀ x ∈ Xgood F n, c ^ 2 ≤ (∑ w ∈ W x, Real.sqrt (eta x w)) ^ 2 := by
    intro x hx
    have hcard : c ≤ ((W x).card : ℝ) := hW x hx
    have h1 : c ^ 2 ≤ ((W x).card : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ hc hcard 2
      simpa [pow_two] using this
    exact h1.trans (goodBlock_success_le (W x) (eta x) (hη x hx))
  have hsum : ((Xgood F n).card : ℝ) * c ^ 2
      ≤ ∑ x ∈ Xgood F n, (∑ w ∈ W x, Real.sqrt (eta x w)) ^ 2 := by
    have := Finset.sum_le_sum hper
    rwa [Finset.sum_const, nsmul_eq_mul] at this
  have hnonneg : (0 : ℝ) ≤ ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left hsum hnonneg

end Qatlib.Papers.HiddenPoly07.MainResults
