/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BornMetrics.FiniteStats.MetricCore
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
open Qatlib.Foundations.BornMetrics.FiniteStats

namespace Qatlib.Papers.QCircApprox95.MainResults

abbrev DecisionProblem (ι : Type*) := ι → Fin 2

def decides {ι : Type*} {N : ℕ} (p : Fin N → Fin 2) (q : ℝ)
    (u : ι → Fin N → ℂ) (f : ι → Fin 2) : Prop :=
  ∀ b, 1 / 2 * (1 + 1 / q) ≤ fiberProb p (u b) (f b)

def StateNorm {ι : Type*} {N : ℕ} (u : ι → Fin N → ℂ) : Prop :=
  ∀ b, ∑ i, ‖u b i‖ ^ 2 = 1

theorem fiberProb_nonneg {N A : ℕ} (p : Fin N → Fin A) (u : Fin N → ℂ) (a : Fin A) :
    0 ≤ fiberProb p u a := by
  unfold fiberProb
  exact Finset.sum_nonneg fun i _ => by split_ifs <;> positivity

theorem fin_two_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  have hlt := i.isLt
  have hval : i.val = 0 ∨ i.val = 1 := by omega
  rcases hval with h0 | h1
  · left; exact Fin.ext (by simpa using h0)
  · right; exact Fin.ext (by simpa using h1)

theorem fiberProb_zero_add_one {N : ℕ} (p : Fin N → Fin 2) (u : Fin N → ℂ) :
    fiberProb p u 0 + fiberProb p u 1 = ∑ i, ‖u i‖ ^ 2 := by
  unfold fiberProb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rcases fin_two_eq_zero_or_one (p i) with h | h <;> simp [h]

theorem sqrt_fiberProb_eq_l2norm_mask {N A : ℕ} (p : Fin N → Fin A) (u : Fin N → ℂ)
    (c : Fin A) :
    Real.sqrt (fiberProb p u c) =
      l2norm (fun i => if p i = c then u i else 0) := by
  rw [l2norm, fiberProb]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : p i = c <;> simp [h]

theorem abs_sqrt_fiberProb_sub_le {N A : ℕ} (p : Fin N → Fin A)
    (u v : Fin N → ℂ) (c : Fin A) :
    |Real.sqrt (fiberProb p u c) - Real.sqrt (fiberProb p v c)| ≤ l2norm (u - v) := by
  let um : Fin N → ℂ := fun i => if p i = c then u i else 0
  let vm : Fin N → ℂ := fun i => if p i = c then v i else 0
  have hum : l2norm um = Real.sqrt (fiberProb p u c) :=
    (sqrt_fiberProb_eq_l2norm_mask p u c).symm
  have hvm : l2norm vm = Real.sqrt (fiberProb p v c) :=
    (sqrt_fiberProb_eq_l2norm_mask p v c).symm
  have hmm : l2norm (um - vm) ≤ l2norm (u - v) := by
    rw [l2norm, l2norm]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    have hpt : ‖um i - vm i‖ ≤ ‖u i - v i‖ := by
      by_cases h : p i = c <;> simp [um, vm, h]
    have hpt' : ‖(um - vm) i‖ ≤ ‖(u - v) i‖ := by simpa using hpt
    nlinarith [hpt', norm_nonneg ((um - vm) i), norm_nonneg ((u - v) i)]
  have htri : l2norm um ≤ l2norm (um - vm) + l2norm vm := by
    have h := l2norm_add_le (um - vm) vm
    have he : (um - vm) + vm = um := by funext i; simp
    rwa [he] at h
  have htri' : l2norm vm ≤ l2norm (um - vm) + l2norm um := by
    have h := l2norm_add_le (vm - um) um
    have he : (vm - um) + um = vm := by funext i; simp
    have hvm' : l2norm (um - vm) = l2norm (vm - um) := by
      rw [l2norm, l2norm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.sub_apply, norm_sub_rev]
    rw [← hvm', he] at h
    exact h
  rw [← hum, ← hvm]
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem decides_eq_of_close {N : ℕ} {ι : Type*} (p : Fin N → Fin 2) {q : ℝ}
    (hq : 0 < q) {u v : ι → Fin N → ℂ} {f g : ι → Fin 2}
    (hu : StateNorm u) (hv : StateNorm v)
    (hf : decides p q u f) (hg : decides p q v g)
    (hnear : ∀ b, l2norm (u b - v b) < 1 / q) :
    f = g := by
  funext b
  by_contra hne

  have hsumu := fiberProb_zero_add_one p (u b)
  have hsumv := fiberProb_zero_add_one p (v b)
  rw [hu b] at hsumu
  rw [hv b] at hsumv
  have happ : 1 / 2 * (1 + 1 / q) ≤ fiberProb p (u b) (f b) := hf b
  have hbpp : 1 / 2 * (1 + 1 / q) ≤ fiberProb p (v b) (g b) := hg b
  have htv : 2 / q ≤ measDist p (u b) (v b) := by
    have hm : measDist p (u b) (v b)
        = 2 * |fiberProb p (u b) 0 - fiberProb p (v b) 0| := by
      unfold measDist
      rw [Fin.sum_univ_two]
      have h1 : fiberProb p (u b) 1 = 1 - fiberProb p (u b) 0 := by linarith
      have h2 : fiberProb p (v b) 1 = 1 - fiberProb p (v b) 0 := by linarith
      rw [h1, h2]
      have h3 : |(1 - fiberProb p (u b) 0) - (1 - fiberProb p (v b) 0)|
          = |fiberProb p (u b) 0 - fiberProb p (v b) 0| := by
        rw [show (1 - fiberProb p (u b) 0) - (1 - fiberProb p (v b) 0)
              = -(fiberProb p (u b) 0 - fiberProb p (v b) 0) by ring, abs_neg]
      rw [h3]
      ring
    rw [hm]
    have hlow : 1 / q ≤ |fiberProb p (u b) 0 - fiberProb p (v b) 0| := by
      rcases fin_two_eq_zero_or_one (f b) with hf0 | hf1
      · have hg1 : g b = 1 := by
          rcases fin_two_eq_zero_or_one (g b) with hg0 | hg1
          · exact absurd (hf0.trans hg0.symm) hne
          · exact hg1
        rw [hf0] at happ
        rw [hg1] at hbpp
        have h1 : fiberProb p (v b) 0 = 1 - fiberProb p (v b) 1 := by linarith
        rw [h1]
        have : 1 / q ≤ fiberProb p (u b) 0 - (1 - fiberProb p (v b) 1) := by linarith
        refine this.trans (le_abs_self _)
      · have hg0 : g b = 0 := by
          rcases fin_two_eq_zero_or_one (g b) with hg0 | hg1
          · exact hg0
          · exact absurd (hf1.trans hg1.symm) hne
        rw [hf1] at happ
        rw [hg0] at hbpp
        have h2 : 1 / q ≤ fiberProb p (v b) 0 - fiberProb p (u b) 0 := by linarith
        have h2' : 1 / q ≤ -(fiberProb p (u b) 0 - fiberProb p (v b) 0) := by
          rw [neg_sub]
          linarith
        exact h2'.trans (neg_le_abs _)
    have h2q : 2 / q = 2 * (1 / q) := by ring
    rw [h2q]
    linarith
  have hle : measDist p (u b) (v b) ≤ 2 * l2norm (u b - v b) :=
    measDist_le_two_l2 p (u b) (v b) (hu b) (hv b)
  have hstrict : 2 * l2norm (u b - v b) < 2 / q := by
    have h := hnear b
    have : 2 * l2norm (u b - v b) < 2 * (1 / q) := by linarith
    rwa [mul_one_div] at this
  linarith

theorem decides_eq_of_ball {N : ℕ} {ι : Type*} {p : Fin N → Fin 2} {q δ : ℝ}
    (hq : 0 < q) {u w v : ι → Fin N → ℂ} {f g : ι → Fin 2}
    (hu : StateNorm u) (hw : StateNorm w)
    (hδ : 2 * δ < 1 / q)
    (huv : ∀ b, l2norm (u b - v b) < δ)
    (hwv : ∀ b, l2norm (w b - v b) < δ)
    (hf : decides p q u f) (hg : decides p q w g) :
    f = g := by
  apply decides_eq_of_close p hq hu hw hf hg
  intro b
  have htri : l2norm (u b - w b) ≤ l2norm (u b - v b) + l2norm (w b - v b) := by
    have h := l2norm_add_le (u b - v b) (v b - w b)
    have he : (u b - v b) + (v b - w b) = u b - w b := by funext i; simp
    have hsym : l2norm (v b - w b) = l2norm (w b - v b) := by
      rw [l2norm, l2norm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.sub_apply, norm_sub_rev]
    rw [he, hsym] at h
    exact h
  linarith [huv b, hwv b, hδ]

theorem decision_card_le_centres {N : ℕ} {ι : Type*} [Fintype ι]
    (p : Fin N → Fin 2) {q δ : ℝ} (hq : 0 < q) (hδ : 2 * δ < 1 / q)
    {m : ℕ} (c : Fin m → ι → Fin N → ℂ)
    (F : Finset (ι → Fin 2))
    (hF : ∀ f ∈ F, ∃ u, StateNorm u ∧ decides p q u f ∧
      ∃ i, ∀ b, l2norm (u b - c i b) < δ) :
    F.card ≤ m := by
  classical
  have hex : ∀ f : ↥F, ∃ i : Fin m, ∃ u : ι → Fin N → ℂ,
      StateNorm u ∧ decides p q u f.1 ∧ ∀ b, l2norm (u b - c i b) < δ := by
    intro f
    obtain ⟨u, hnorm, hdec, i, hnear⟩ := hF f.1 f.2
    exact ⟨i, u, hnorm, hdec, hnear⟩
  let g : ↥F → Fin m := fun f => Classical.choose (hex f)
  have hg_inj : Function.Injective g := by
    intro f1 f2 hEq
    obtain ⟨u1, hn1, hd1, hnear1⟩ := Classical.choose_spec (hex f1)
    obtain ⟨u2, hn2, hd2, hnear2⟩ := Classical.choose_spec (hex f2)
    have hmain : (f1 : ι → Fin 2) = (f2 : ι → Fin 2) := by
      apply decides_eq_of_ball (v := c (g f1)) (δ := δ) hq hn1 hn2 hδ
      · intro b
        exact hnear1 b
      · intro b
        have hEq' : g f1 = Classical.choose (hex f2) := hEq
        rw [← hEq'] at hnear2
        exact hnear2 b
      · exact hd1
      · exact hd2
    exact Subtype.ext hmain
  calc F.card = Fintype.card ↥F := (Fintype.card_coe F).symm
    _ ≤ Fintype.card (Fin m) := Fintype.card_le_of_injective g hg_inj
    _ = m := Fintype.card_fin m

theorem decision_card_le_indexed {N : ℕ} {ι : Type*} [Fintype ι]
    {τ : Type*} [Fintype τ]
    (p : Fin N → Fin 2) {q δ : ℝ} (hq : 0 < q) (hδ : 2 * δ < 1 / q)
    (c : τ → ι → Fin N → ℂ)
    (F : Finset (ι → Fin 2))
    (hF : ∀ f ∈ F, ∃ u, StateNorm u ∧ decides p q u f ∧
      ∃ i, ∀ b, l2norm (u b - c i b) < δ) :
    F.card ≤ Fintype.card τ := by
  classical
  have hex : ∀ f : ↥F, ∃ i : τ, ∃ u : ι → Fin N → ℂ,
      StateNorm u ∧ decides p q u f.1 ∧ ∀ b, l2norm (u b - c i b) < δ := by
    intro f
    obtain ⟨u, hnorm, hdec, i, hnear⟩ := hF f.1 f.2
    exact ⟨i, u, hnorm, hdec, hnear⟩
  let g : ↥F → τ := fun f => Classical.choose (hex f)
  have hg_inj : Function.Injective g := by
    intro f1 f2 hEq
    obtain ⟨u1, hn1, hd1, hnear1⟩ := Classical.choose_spec (hex f1)
    obtain ⟨u2, hn2, hd2, hnear2⟩ := Classical.choose_spec (hex f2)
    have hmain : (f1 : ι → Fin 2) = (f2 : ι → Fin 2) := by
      apply decides_eq_of_ball (v := c (g f1)) (δ := δ) hq hn1 hn2 hδ
      · intro b
        exact hnear1 b
      · intro b
        have hEq' : g f1 = Classical.choose (hex f2) := hEq
        rw [← hEq'] at hnear2
        exact hnear2 b
      · exact hd1
      · exact hd2
    exact Subtype.ext hmain
  calc F.card = Fintype.card ↥F := (Fintype.card_coe F).symm
    _ ≤ Fintype.card τ := Fintype.card_le_of_injective g hg_inj

def guesses {ι : Type*} {N A : ℕ} (p : Fin N → Fin A) (q : ℝ)
    (u : ι → Fin N → ℂ) (f : ι → Fin A) : Prop :=
  ∀ b, 1 / q ≤ fiberProb p (u b) (f b)

theorem fiberProb_ge_quarter_of_close {N A : ℕ} {ι : Type*} (p : Fin N → Fin A)
    {q δ : ℝ} (hq : 0 < q) {u v : ι → Fin N → ℂ} {f : ι → Fin A}
    (hg : guesses p q u f)
    (hnear : ∀ b, l2norm (u b - v b) < δ)
    (hδ : δ ≤ 1 / (2 * Real.sqrt q)) :
    ∀ b, 1 / (4 * q) ≤ fiberProb p (v b) (f b) := by
  intro b
  have hv := hg b
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hs := abs_sqrt_fiberProb_sub_le p (u b) (v b) (f b)
  have hP : (1 : ℝ) / Real.sqrt q ≤ Real.sqrt (fiberProb p (u b) (f b)) := by
    have h1 : Real.sqrt (1 / q) ≤ Real.sqrt (fiberProb p (u b) (f b)) :=
      Real.sqrt_le_sqrt hv
    rwa [Real.sqrt_div' (1 : ℝ) (le_of_lt hq), Real.sqrt_one] at h1
  have hlow : (1 : ℝ) / Real.sqrt q - l2norm (u b - v b) ≤
      Real.sqrt (fiberProb p (v b) (f b)) := by
    have h2 := (abs_sub_le_iff.mp hs).1
    linarith
  have hstrict : (1 : ℝ) / (2 * Real.sqrt q) <
      Real.sqrt (fiberProb p (v b) (f b)) := by
    have hd : l2norm (u b - v b) < 1 / (2 * Real.sqrt q) :=
      lt_of_lt_of_le (hnear b) hδ
    have hgap : (1 : ℝ) / Real.sqrt q - 1 / (2 * Real.sqrt q) =
        1 / (2 * Real.sqrt q) := by
      field_simp
      ring
    linarith
  have hsqr : (1 / (2 * Real.sqrt q)) ^ 2 <
      (Real.sqrt (fiberProb p (v b) (f b))) ^ 2 := by
    have hx : 0 < (1 : ℝ) / (2 * Real.sqrt q) := by positivity
    nlinarith [hstrict]
  rw [Real.sq_sqrt (fiberProb_nonneg p (v b) (f b))] at hsqr
  have hcalc : (1 / (2 * Real.sqrt q)) ^ 2 = 1 / (4 * q) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt hq)]
    norm_num
  linarith

theorem card_threshold_mass_le {N A : ℕ} (p : Fin N → Fin A) (u : Fin N → ℂ)
    (hn : ∑ i, ‖u i‖ ^ 2 = 1) {α : ℝ} (hα : 0 < α) :
    ((Finset.univ.filter (fun c : Fin A => α ≤ fiberProb p u c)).card : ℝ) * α ≤ 1 := by
  classical
  have hsum : ∑ c, fiberProb p u c = 1 := by
    rw [sum_fiberProb, hn]
  have hconst : ((Finset.univ.filter (fun c : Fin A => α ≤ fiberProb p u c)).card : ℝ) * α
      = ∑ c ∈ Finset.univ.filter (fun c : Fin A => α ≤ fiberProb p u c), α := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hconst]
  calc
    ∑ c ∈ Finset.univ.filter (fun c : Fin A => α ≤ fiberProb p u c), α
        ≤ ∑ c ∈ Finset.univ.filter (fun c : Fin A => α ≤ fiberProb p u c),
            fiberProb p u c := by
      apply Finset.sum_le_sum
      intro c hc
      exact (Finset.mem_filter.mp hc).2
    _ ≤ ∑ c, fiberProb p u c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro c _ _
      exact fiberProb_nonneg p u c
    _ = 1 := hsum

theorem card_functions_mem_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ℕ}
    (S : ι → Finset (Fin A)) :
    (Finset.univ.filter (fun f : ι → Fin A => ∀ b, f b ∈ S b)).card
      = ∏ b, (S b).card := by
  classical
  calc
    (Finset.univ.filter (fun f : ι → Fin A => ∀ b, f b ∈ S b)).card
        = Fintype.card {f : ι → Fin A // ∀ b, f b ∈ S b} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card (∀ b : ι, ↥(S b)) :=
      Fintype.card_congr Equiv.subtypePiEquivPi
    _ = ∏ b, (S b).card := by
      rw [Fintype.card_pi]
      apply Finset.prod_congr rfl
      intro b _
      exact Fintype.card_coe (S b)

theorem guess_card_le_centres {N A : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin N → Fin A) {q δ : ℝ} (hq : 0 < q) (hδ : δ < 1 / (2 * Real.sqrt q))
    {m : ℕ} (c : Fin m → ι → Fin N → ℂ)
    (hc : ∀ i b, ∑ k, ‖c i b k‖ ^ 2 = 1)
    (F : Finset (ι → Fin A))
    (hF : ∀ f ∈ F, ∃ u, StateNorm u ∧ guesses p q u f ∧
      ∃ i, ∀ b, l2norm (u b - c i b) < δ) :
    (F.card : ℝ) ≤ (m : ℝ) * (4 * q) ^ (Fintype.card ι) := by
  classical
  let S : Fin m → ι → Finset (Fin A) := fun i b =>
    Finset.univ.filter (fun a : Fin A => 1 / (4 * q) ≤ fiberProb p (c i b) a)
  let T : Fin m → Finset (ι → Fin A) := fun i =>
    Finset.univ.filter (fun f : ι → Fin A => ∀ b, f b ∈ S i b)
  have hsub : F ⊆ Finset.univ.biUnion T := by
    intro f hf
    obtain ⟨u, _, hg, i, hnear⟩ := hF f hf
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ f, ?_⟩
    intro b
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fiberProb_ge_quarter_of_close p hq hg hnear (le_of_lt hδ) b⟩
  have hcard : F.card ≤ (Finset.univ.biUnion T).card := Finset.card_le_card hsub
  have hb : (Finset.univ.biUnion T).card ≤ ∑ i : Fin m, (T i).card := by
    have := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin m))) (t := T)
    simpa using this
  have hT : ∀ i, (T i).card = ∏ b, (S i b).card := fun i =>
    card_functions_mem_pi (S i)
  have hS : ∀ i b, ((S i b).card : ℝ) ≤ 4 * q := by
    intro i b
    have hpos : (0 : ℝ) < 1 / (4 * q) := by positivity
    have h := card_threshold_mass_le p (c i b) (hc i b) hpos
    have h4 : (0 : ℝ) < 4 * q := by positivity
    have h' : ((S i b).card : ℝ) / (4 * q) ≤ 1 := by
      have heq : ((S i b).card : ℝ) * (1 / (4 * q)) = ((S i b).card : ℝ) / (4 * q) := by
        ring
      linarith
    exact (div_le_one h4).mp h'
  have hprod : ∀ i, ((T i).card : ℝ) ≤ (4 * q) ^ (Fintype.card ι) := by
    intro i
    rw [hT i]
    have hcast : ((∏ b, (S i b).card : ℕ) : ℝ) = ∏ b, ((S i b).card : ℝ) := by
      push_cast
      rfl
    rw [hcast]
    calc
      ∏ b, ((S i b).card : ℝ) ≤ ∏ b, (4 * q) :=
        Finset.prod_le_prod₀ (fun b _ => by positivity) (fun b _ => hS i b)
      _ = (4 * q) ^ (Fintype.card ι) := by
        rw [Finset.prod_const, Finset.card_univ]
  calc
    (F.card : ℝ) ≤ ((Finset.univ.biUnion T).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ((∑ i : Fin m, (T i).card : ℕ) : ℝ) := by exact_mod_cast hb
    _ = ∑ i : Fin m, ((T i).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ _i : Fin m, (4 * q) ^ (Fintype.card ι) :=
      Finset.sum_le_sum fun i _ => hprod i
    _ = (m : ℝ) * (4 * q) ^ (Fintype.card ι) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem guess_card_le_indexed {N A : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : Type*} [Fintype τ]
    (p : Fin N → Fin A) {q δ : ℝ} (hq : 0 < q) (hδ : δ < 1 / (2 * Real.sqrt q))
    (c : τ → ι → Fin N → ℂ)
    (hc : ∀ i b, ∑ k, ‖c i b k‖ ^ 2 = 1)
    (F : Finset (ι → Fin A))
    (hF : ∀ f ∈ F, ∃ u, StateNorm u ∧ guesses p q u f ∧
      ∃ i, ∀ b, l2norm (u b - c i b) < δ) :
    (F.card : ℝ) ≤ (Fintype.card τ : ℝ) * (4 * q) ^ (Fintype.card ι) := by
  classical
  let S : τ → ι → Finset (Fin A) := fun i b =>
    Finset.univ.filter (fun a : Fin A => 1 / (4 * q) ≤ fiberProb p (c i b) a)
  let T : τ → Finset (ι → Fin A) := fun i =>
    Finset.univ.filter (fun f : ι → Fin A => ∀ b, f b ∈ S i b)
  have hsub : F ⊆ Finset.univ.biUnion T := by
    intro f hf
    obtain ⟨u, _, hg, i, hnear⟩ := hF f hf
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ f, ?_⟩
    intro b
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fiberProb_ge_quarter_of_close p hq hg hnear (le_of_lt hδ) b⟩
  have hcard : F.card ≤ (Finset.univ.biUnion T).card := Finset.card_le_card hsub
  have hb : (Finset.univ.biUnion T).card ≤ ∑ i : τ, (T i).card := by
    have := Finset.card_biUnion_le (s := (Finset.univ : Finset τ)) (t := T)
    simpa using this
  have hT : ∀ i, (T i).card = ∏ b, (S i b).card := fun i =>
    card_functions_mem_pi (S i)
  have hS : ∀ i b, ((S i b).card : ℝ) ≤ 4 * q := by
    intro i b
    have hpos : (0 : ℝ) < 1 / (4 * q) := by positivity
    have h := card_threshold_mass_le p (c i b) (hc i b) hpos
    have h4 : (0 : ℝ) < 4 * q := by positivity
    have h' : ((S i b).card : ℝ) / (4 * q) ≤ 1 := by
      have heq : ((S i b).card : ℝ) * (1 / (4 * q)) = ((S i b).card : ℝ) / (4 * q) := by
        ring
      linarith
    exact (div_le_one h4).mp h'
  have hprod : ∀ i, ((T i).card : ℝ) ≤ (4 * q) ^ (Fintype.card ι) := by
    intro i
    rw [hT i]
    have hcast : ((∏ b, (S i b).card : ℕ) : ℝ) = ∏ b, ((S i b).card : ℝ) := by
      push_cast
      rfl
    rw [hcast]
    calc
      ∏ b, ((S i b).card : ℝ) ≤ ∏ b, (4 * q) :=
        Finset.prod_le_prod₀ (fun b _ => by positivity) (fun b _ => hS i b)
      _ = (4 * q) ^ (Fintype.card ι) := by
        rw [Finset.prod_const, Finset.card_univ]
  calc
    (F.card : ℝ) ≤ ((Finset.univ.biUnion T).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ((∑ i : τ, (T i).card : ℕ) : ℝ) := by exact_mod_cast hb
    _ = ∑ i : τ, ((T i).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ _i : τ, (4 * q) ^ (Fintype.card ι) :=
      Finset.sum_le_sum fun i _ => hprod i
    _ = (Fintype.card τ : ℝ) * (4 * q) ^ (Fintype.card ι) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Qatlib.Papers.QCircApprox95.MainResults
