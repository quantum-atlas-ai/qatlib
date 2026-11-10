/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HiddenPoly07.MainResults

open scoped BigOperators

theorem card_le_mul_card_image {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β)
    (D : ℕ) (hD : ∀ b ∈ s.image f, (s.filter (fun a => f a = b)).card ≤ D) :
    s.card ≤ D * (s.image f).card := by
  classical
  rw [Finset.card_eq_sum_card_image f s]
  calc ∑ b ∈ s.image f, (s.filter (fun a => f a = b)).card
      ≤ ∑ _b ∈ s.image f, D := Finset.sum_le_sum (fun b hb => hD b hb)
    _ = (s.image f).card * D := by rw [Finset.sum_const, Nat.nsmul_eq_mul]
    _ = D * (s.image f).card := by rw [mul_comm]

theorem card_injective_tuples (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (Finset.univ.filter (fun b : Fin n → F => Function.Injective b)).card
      = (Fintype.card F).descFactorial n := by
  classical
  rw [← Fintype.card_subtype]
  have e : {b : Fin n → F // Function.Injective b} ≃ (Fin n ↪ F) :=
    Equiv.subtypeInjectiveEquivEmbedding (Fin n) F
  rw [Fintype.card_congr e, Fintype.card_embedding_eq, Fintype.card_fin]

theorem descFactorial_ge_half_pow {d n : ℕ} (hn : 2 * n ≤ d) :
    (d : ℝ) ^ n / 2 ^ n ≤ (d.descFactorial n : ℝ) := by
  have hnd : n ≤ d := by omega
  have h := Nat.pow_sub_le_descFactorial d n
  have hcast : (((d + 1 - n : ℕ) : ℝ)) ^ n ≤ (d.descFactorial n : ℝ) := by
    exact_mod_cast h
  have hbase : (d : ℝ) / 2 ≤ ((d + 1 - n : ℕ) : ℝ) := by
    have hsub : (d + 1 - n : ℕ) = d + 1 - n := rfl
    rw [hsub, Nat.cast_sub (by omega : n ≤ d + 1)]
    push_cast
    have hnR : (2 : ℝ) * (n : ℝ) ≤ (d : ℝ) := by exact_mod_cast hn
    linarith
  calc (d : ℝ) ^ n / 2 ^ n = ((d : ℝ) / 2) ^ n := by rw [div_pow]
    _ ≤ (((d + 1 - n : ℕ) : ℝ)) ^ n := by
        exact pow_le_pow_left₀ (by positivity) hbase n
    _ ≤ (d.descFactorial n : ℝ) := hcast

theorem card_zeros_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (hn : 1 ≤ n) (p : MvPolynomial (Fin n) F) (hp : p ≠ 0) :
    ((Finset.univ.filter (fun b : Fin n → F => MvPolynomial.eval b p = 0)).card : ℝ)
      ≤ (p.totalDegree : ℝ) * (Fintype.card F : ℝ) ^ (n - 1) := by
  classical
  set d : ℕ := Fintype.card F with hd
  have hdpos : 0 < d := Fintype.card_pos
  have h := MvPolynomial.schwartz_zippel_totalDegree (R := F) hp (Finset.univ : Finset F)
  rw [Fintype.piFinset_univ] at h
  have hcard : (Finset.univ : Finset F).card = d := by rw [Finset.card_univ]
  rw [hcard] at h
  set z : ℕ := (Finset.univ.filter (fun b : Fin n → F => MvPolynomial.eval b p = 0)).card with hz'
  set e : ℕ := p.totalDegree with he
  have hR : (z : ℝ) / (d : ℝ) ^ n ≤ (e : ℝ) / (d : ℝ) := by
    rw [← Nat.cast_pow] at h
    have hcast : (((z : ℚ≥0) / ((d ^ n : ℕ) : ℚ≥0) : ℚ≥0) : ℝ) ≤ (((e : ℚ≥0) / (d : ℚ≥0) : ℚ≥0) : ℝ) := by
      exact_mod_cast h
    rw [NNRat.cast_div, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast, NNRat.cast_natCast,
      NNRat.cast_natCast, Nat.cast_pow] at hcast
    exact hcast
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hdpow : (0 : ℝ) < (d : ℝ) ^ n := pow_pos hdR n
  have hdn : (d : ℝ) ^ n / (d : ℝ) = (d : ℝ) ^ (n - 1) := by
    rw [div_eq_iff hdR.ne']
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hz : (z : ℝ) ≤ (e : ℝ) / (d : ℝ) * (d : ℝ) ^ n := by
    rw [div_le_iff₀ hdpow] at hR
    linarith [hR]
  have hstep : (e : ℝ) / (d : ℝ) * (d : ℝ) ^ n = (e : ℝ) * (d : ℝ) ^ (n - 1) := by
    have h1 : (e : ℝ) / (d : ℝ) * (d : ℝ) ^ n = (e : ℝ) * ((d : ℝ) ^ n / (d : ℝ)) := by ring
    rw [h1, hdn]
  rw [hstep] at hz
  simpa [z, e] using hz

theorem good_set_card_ge_raw {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (hn : 1 ≤ n) (g : MvPolynomial (Fin n) F) (hg : g ≠ 0) :
    (Fintype.card F : ℝ) ^ n - (g.totalDegree : ℝ) * (Fintype.card F : ℝ) ^ (n - 1)
      ≤ ((Finset.univ.filter (fun x : Fin n → F => MvPolynomial.eval x g ≠ 0)).card : ℝ) := by
  classical
  set d : ℕ := Fintype.card F with hd
  set e : ℕ := g.totalDegree with he
  set zeros : Finset (Fin n → F) := Finset.univ.filter (fun x => MvPolynomial.eval x g = 0) with hzeros
  set good : Finset (Fin n → F) := Finset.univ.filter (fun x => MvPolynomial.eval x g ≠ 0) with hgood
  have hpart : zeros.card + good.card = d ^ n := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n → F))) (p := fun x => MvPolynomial.eval x g = 0)
    have hgood' : good = Finset.univ.filter (fun x => ¬ (MvPolynomial.eval x g = 0)) := by
      ext x; simp only [hgood, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
    have hunivcard : (Finset.univ : Finset (Fin n → F)).card = d ^ n := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    rw [← hgood', hunivcard] at h
    have hz : (Finset.univ.filter (fun x : Fin n → F => MvPolynomial.eval x g = 0)) = zeros := rfl
    rw [hz] at h
    exact h
  have hz_le : (zeros.card : ℝ) ≤ (e : ℝ) * (d : ℝ) ^ (n - 1) := by
    have h := card_zeros_le (F := F) hn g hg
    simpa [zeros, hzeros, d, e, hd, he] using h
  have hgood_eq : (good.card : ℝ) = (d : ℝ) ^ n - (zeros.card : ℝ) := by
    have hle : zeros.card ≤ d ^ n := by rw [← hpart]; exact Nat.le_add_right _ _
    have hnn : good.card = d ^ n - zeros.card := by omega
    rw [hnn, Nat.cast_sub hle]; push_cast; ring
  rw [hgood_eq]
  linarith [hz_le]

theorem good_set_card_ge {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (hn : 1 ≤ n) (g : MvPolynomial (Fin n) F) (hg : g ≠ 0)
    (hbig : 2 * g.totalDegree ≤ Fintype.card F) :
    (Fintype.card F : ℝ) ^ n / 2 ^ n
      ≤ ((Finset.univ.filter (fun x : Fin n → F => MvPolynomial.eval x g ≠ 0)).card : ℝ) := by
  classical
  set d : ℕ := Fintype.card F with hd
  set e : ℕ := g.totalDegree with he
  have hdpos : 0 < d := Fintype.card_pos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hraw := good_set_card_ge_raw (F := F) hn g hg
  have hbigR : (2 : ℝ) * (e : ℝ) ≤ (d : ℝ) := by exact_mod_cast hbig
  have h1 : (d : ℝ) ^ n - (e : ℝ) * (d : ℝ) ^ (n - 1) = (d : ℝ) ^ (n - 1) * ((d : ℝ) - (e : ℝ)) := by
    have hsplit : (d : ℝ) ^ n = (d : ℝ) ^ (n - 1) * (d : ℝ) := by
      rw [← pow_succ, Nat.sub_add_cancel hn]
    rw [hsplit]; ring
  have h2 : (d : ℝ) ^ (n - 1) * ((d : ℝ) / 2) ≤ (d : ℝ) ^ (n - 1) * ((d : ℝ) - (e : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have h3 : (d : ℝ) ^ (n - 1) * ((d : ℝ) / 2) = (d : ℝ) ^ n / 2 := by
    have hsplit : (d : ℝ) ^ n = (d : ℝ) ^ (n - 1) * (d : ℝ) := by
      rw [← pow_succ, Nat.sub_add_cancel hn]
    rw [hsplit]; ring
  have hpow2 : (2 : ℝ) ≤ 2 ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := by ring
      _ ≤ 2 ^ n := by apply pow_le_pow_right₀ (by norm_num) hn
  have hfinal : (d : ℝ) ^ n / 2 ^ n ≤ (d : ℝ) ^ n / 2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hpow2

  have hfil : (Finset.univ.filter (fun x : Fin n → F => MvPolynomial.eval x g ≠ 0))
      = (Finset.univ.filter (fun x : Fin n → F => ¬ (MvPolynomial.eval x g = 0))) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
  rw [hfil]
  linarith [hraw, h1, h2, h3, hfinal]

end Qatlib.Papers.HiddenPoly07.MainResults
