/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ModularFunct00.MainResults.Setup
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Approximation

open Matrix
open scoped Matrix.Norms.L2Operator

lemma braidWord_one {G : Type*} [Group G] {m : ℕ} (σ : Fin m → G) :
    BraidWord σ 0 1 := by
  refine ⟨[], by simp, by simp⟩

lemma braidWord_mono {G : Type*} [Group G] {m : ℕ} {σ : Fin m → G} {l l' : ℕ}
    {b : G} (h : BraidWord σ l b) (hll : l ≤ l') : BraidWord σ l' b := by
  rcases h with ⟨w, hw, hprod⟩
  exact ⟨w, le_trans hw hll, hprod⟩

lemma braidWord_mul {G : Type*} [Group G] {m : ℕ} {σ : Fin m → G} {l l' : ℕ}
    {a b : G} (ha : BraidWord σ l a) (hb : BraidWord σ l' b) :
    BraidWord σ (l + l') (a * b) := by
  rcases ha with ⟨u, hu, rfl⟩
  rcases hb with ⟨v, hv, rfl⟩
  refine ⟨u ++ v, by simp only [List.length_append]; omega, ?_⟩
  rw [List.map_append, List.prod_append]

lemma braidWord_gen {G : Type*} [Group G] {m : ℕ} (σ : Fin m → G) (i : Fin m) :
    BraidWord σ 1 (σ i) := by
  refine ⟨[⟨i, true⟩], by simp, by simp⟩

lemma braidWord_inv_gen {G : Type*} [Group G] {m : ℕ} (σ : Fin m → G) (i : Fin m) :
    BraidWord σ 1 (σ i)⁻¹ := by
  refine ⟨[⟨i, false⟩], by simp, by simp⟩

lemma braidWord_list_prod {G : Type*} [Group G] {m : ℕ} {σ : Fin m → G} {l : ℕ}
    {bs : List G} (hbs : ∀ b ∈ bs, BraidWord σ l b) :
    BraidWord σ (bs.length * l) bs.prod := by
  induction bs with
  | nil => simpa using braidWord_one (σ := σ)
  | cons b bs ih =>
    rw [List.prod_cons, List.length_cons, Nat.succ_mul]
    have h := braidWord_mul (l := l) (l' := bs.length * l)
      (hbs b List.mem_cons_self) (ih (fun x hx => hbs x (List.mem_cons_of_mem _ hx)))
    simpa [Nat.add_comm] using h

lemma norm_list_prod_le_one {R : Type*} [NormedRing R] [NormOneClass R] :
    ∀ (l : List R), (∀ x ∈ l, ‖x‖ ≤ 1) → ‖l.prod‖ ≤ 1
  | [], _ => by simp [norm_one]
  | a :: t, h => by
    rw [List.prod_cons]
    calc ‖a * t.prod‖ ≤ ‖a‖ * ‖t.prod‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := by
            gcongr
            · exact h a List.mem_cons_self
            · exact norm_list_prod_le_one t (fun x hx => h x (List.mem_cons_of_mem _ hx))
      _ = 1 := by norm_num

lemma norm_list_prod_sub_prod_le {R : Type*} [NormedRing R] [NormOneClass R] :
    ∀ (u v : List R), u.length = v.length →
      (∀ x ∈ u, ‖x‖ ≤ 1) → (∀ x ∈ v, ‖x‖ ≤ 1) →
      ‖u.prod - v.prod‖ ≤ (u.zipWith (fun a b => ‖a - b‖) v).sum
  | [], [], _, _, _ => by simp
  | [], _ :: _, hlen, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _ => by simp at hlen
  | a :: t, b :: s, hlen, hu, hv => by
    simp only [List.length_cons] at hlen
    have hlen' : t.length = s.length := Nat.succ.inj hlen
    rw [List.prod_cons, List.prod_cons, List.zipWith_cons_cons, List.sum_cons]
    have e : a * t.prod - b * s.prod = a * (t.prod - s.prod) + (a - b) * s.prod := by
      noncomm_ring
    rw [e]
    have hS : ‖s.prod‖ ≤ 1 :=
      norm_list_prod_le_one s (fun x hx => hv x (List.mem_cons_of_mem _ hx))
    have ih := norm_list_prod_sub_prod_le t s hlen'
      (fun x hx => hu x (List.mem_cons_of_mem _ hx))
      (fun x hx => hv x (List.mem_cons_of_mem _ hx))
    calc ‖a * (t.prod - s.prod) + (a - b) * s.prod‖
        ≤ ‖a * (t.prod - s.prod)‖ + ‖(a - b) * s.prod‖ := norm_add_le _ _
      _ ≤ ‖a‖ * ‖t.prod - s.prod‖ + ‖a - b‖ * ‖s.prod‖ := by
            gcongr <;> exact norm_mul_le _ _
      _ ≤ 1 * (t.zipWith (fun a b => ‖a - b‖) s).sum + ‖a - b‖ * 1 := by
            have h1 : ‖a‖ * ‖t.prod - s.prod‖ ≤ 1 * ‖t.prod - s.prod‖ := by
              gcongr
              exact hu a List.mem_cons_self
            have h2 : ‖a - b‖ * ‖s.prod‖ ≤ ‖a - b‖ * 1 := by gcongr
            linarith
      _ = ‖a - b‖ + (t.zipWith (fun a b => ‖a - b‖) s).sum := by ring

lemma sum_uniform_inv_ten_le_tenth (n : ℕ) (hn : 1 ≤ n) :
    (Finset.range n).sum (fun _ => 1 / (10 * (n : ℝ))) ≤ 1 / 10 := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h : (n : ℝ) * (1 / (10 * (n : ℝ))) = 1 / 10 := by
    field_simp
  exact le_of_eq h

lemma total_length_quadratic (n : ℕ) (C : ℝ) :
    (n : ℝ) * (C * (1 / (1 / (10 * (n : ℝ)))) ^ 2) =
      C * (10 * (n : ℝ)) ^ 2 * (n : ℝ) := by
  have h : (1 : ℝ) / (1 / (10 * (n : ℝ))) = 10 * (n : ℝ) := by
    field_simp
  rw [h]
  ring

lemma list_sum_le_length_mul {l : List ℝ} {c : ℝ} (h : ∀ x ∈ l, x ≤ c) :
    l.sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    have ha := h a List.mem_cons_self
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    linarith

lemma nat_mul_inv_ten (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * (1 / (10 * (n : ℝ))) = 1 / 10 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp

lemma success_ge_three_quarters {err : ℝ} (h : err ≤ 1 / 10) :
    3 / 4 ≤ 1 - err := by
  linarith

lemma polyLogOverhead_mul {f g : ℕ → ℕ}
    (hf : PolyLogOverhead f) (hg : PolyLogOverhead g) :
    PolyLogOverhead (fun L => f L * g L) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨a + b, fun L => ?_⟩
  calc f L * g L
      ≤ (Nat.log 2 (L + 1) + 1) ^ a * (Nat.log 2 (L + 1) + 1) ^ b :=
        Nat.mul_le_mul (ha L) (hb L)
    _ = (Nat.log 2 (L + 1) + 1) ^ (a + b) := (pow_add _ _ _).symm

lemma polyLogOverhead_const_one : PolyLogOverhead (fun _ => 1) := by
  refine ⟨0, fun L => ?_⟩
  simp

end Qatlib.Papers.ModularFunct00.MainResults.Approximation
