/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Sum
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Classical BigOperators

namespace Qatlib.Papers.QLattice03.MainResults

variable {N : ℕ} [NeZero N]

def ssum {n : ℕ} (B : Finset (Fin n)) (a : Fin n → ZMod N) : ZMod N := ∑ j ∈ B, a j

theorem sum_update_add {n : ℕ} (B : Finset (Fin n)) (a : Fin n → ZMod N) (i : Fin n)
    (c : ZMod N) :
    ∑ j ∈ B, Function.update a i (a i + c) j
      = (∑ j ∈ B, a j) + if i ∈ B then c else 0 := by
  classical
  have h : ∀ j ∈ B, Function.update a i (a i + c) j = a j + if j = i then c else 0 := by
    intro j _
    rw [Function.update_apply]
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hji]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib]
  congr 1
  simpa using Finset.sum_ite_eq' (s := B) (a := i) (b := fun _ => c)

theorem card_fiber_le_shift {n : ℕ} (B : Finset (Fin n)) {i : Fin n} (hi : i ∈ B)
    (t c : ZMod N) :
    Fintype.card {a : Fin n → ZMod N // ssum B a = t} ≤
      Fintype.card {a : Fin n → ZMod N // ssum B a = t + c} := by
  classical
  refine Fintype.card_le_of_injective
    (fun a : {a : Fin n → ZMod N // ssum B a = t} =>
      (⟨Function.update a.1 i (a.1 i + c), ?_⟩ :
        {a : Fin n → ZMod N // ssum B a = t + c})) ?_
  · show ssum B (Function.update a.1 i (a.1 i + c)) = t + c
    unfold ssum
    rw [sum_update_add, if_pos hi]
    have h := a.2
    unfold ssum at h
    rw [h]
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ heq
    have h1 : Function.update a i (a i + c) = Function.update b i (b i + c) := by
      simpa using congrArg Subtype.val heq
    apply Subtype.ext
    funext j
    by_cases hj : j = i
    · rw [hj]
      have h := congrFun h1 i
      simp only [Function.update_self] at h
      exact add_right_cancel h
    · have h := congrFun h1 j
      rw [Function.update_of_ne hj, Function.update_of_ne hj] at h
      exact h

theorem card_fiber_eq {n : ℕ} (B : Finset (Fin n)) (hB : B.Nonempty) (t : ZMod N) :
    Fintype.card {a : Fin n → ZMod N // ssum B a = t} =
      Fintype.card {a : Fin n → ZMod N // ssum B a = 0} := by
  classical
  obtain ⟨i, hi⟩ := hB
  have h1 : Fintype.card {a : Fin n → ZMod N // ssum B a = t} ≤
      Fintype.card {a : Fin n → ZMod N // ssum B a = 0} := by
    have h := card_fiber_le_shift (N := N) B hi t (-t)
    rwa [add_neg_cancel] at h
  have h2 : Fintype.card {a : Fin n → ZMod N // ssum B a = 0} ≤
      Fintype.card {a : Fin n → ZMod N // ssum B a = t} := by
    have h := card_fiber_le_shift (N := N) B hi 0 t
    rwa [zero_add] at h
  exact le_antisymm h1 h2

theorem sum_card_fiber {n : ℕ} (B : Finset (Fin n)) :
    ∑ t : ZMod N, Fintype.card {a : Fin n → ZMod N // ssum B a = t} = N ^ n := by
  classical
  rw [← Fintype.card_sigma]
  rw [Fintype.card_congr (Equiv.sigmaFiberEquiv (fun a : Fin n → ZMod N => ssum B a))]
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem card_fiber {n : ℕ} (B : Finset (Fin n)) (hB : B.Nonempty) (t : ZMod N) :
    Fintype.card {a : Fin n → ZMod N // ssum B a = t} = N ^ (n - 1) := by
  classical
  have hN : 0 < N := NeZero.pos N
  obtain ⟨i, hi⟩ := hB
  have hn : 0 < n := by
    have := i.isLt
    omega
  have hconst : ∀ t' : ZMod N,
      Fintype.card {a : Fin n → ZMod N // ssum B a = t'} =
        Fintype.card {a : Fin n → ZMod N // ssum B a = 0} :=
    fun t' => card_fiber_eq B ⟨i, hi⟩ t'
  have hsum := sum_card_fiber (N := N) B
  simp_rw [hconst] at hsum
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul] at hsum
  have hpow : N ^ n = N * N ^ (n - 1) := by
    rw [show n = (n - 1) + 1 by omega, pow_succ']
    have h' : (n - 1) + 1 - 1 = n - 1 := by omega
    rw [h']
  rw [hpow] at hsum
  have hc : Fintype.card {a : Fin n → ZMod N // ssum B a = 0} = N ^ (n - 1) :=
    Nat.eq_of_mul_eq_mul_left hN hsum
  exact (hconst t).trans hc

theorem card_nonempty_finset (n : ℕ) :
    Fintype.card {B : Finset (Fin n) // B.Nonempty} = 2 ^ n - 1 := by
  classical
  have htotal : Fintype.card (Finset (Fin n)) = 2 ^ n := by
    rw [Fintype.card_finset, Fintype.card_fin]
  have hsub : Subsingleton {B : Finset (Fin n) // ¬ B.Nonempty} := by
    constructor
    intro a b
    have ha : a.1 = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      exact a.2
    have hb : b.1 = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      exact b.2
    exact Subtype.ext (ha.trans hb.symm)
  have hempty : Fintype.card {B : Finset (Fin n) // ¬ B.Nonempty} = 1 := by
    have hle : Fintype.card {B : Finset (Fin n) // ¬ B.Nonempty} ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr hsub
    have hpos : 0 < Fintype.card {B : Finset (Fin n) // ¬ B.Nonempty} :=
      Fintype.card_pos_iff.mpr ⟨⟨∅, by simp⟩⟩
    omega
  have hsplit := Fintype.card_subtype_compl (fun B : Finset (Fin n) => B.Nonempty)
  rw [hempty, htotal] at hsplit
  omega

def countNonempty {n : ℕ} (a : Fin n → ZMod N) (t : ZMod N) : ℕ :=
  (Finset.univ.filter (fun B : Finset (Fin n) => B.Nonempty ∧ ssum B a = t)).card

theorem countNonempty_pos_of_nonempty_subset {n : ℕ} {a : Fin n → ZMod N} {t : ZMod N}
    {B : Finset (Fin n)} (hB : B.Nonempty) (h : ssum B a = t) : 0 < countNonempty a t := by
  classical
  unfold countNonempty
  rw [Finset.card_pos]
  exact ⟨B, by simp [hB, h]⟩

theorem sum_countNonempty {n : ℕ} (t : ZMod N) :
    ∑ a : Fin n → ZMod N, countNonempty a t = (2 ^ n - 1) * N ^ (n - 1) := by
  classical
  have hstep : ∀ B : Finset (Fin n),
      (∑ a : Fin n → ZMod N,
          (if B.Nonempty ∧ ssum B a = t then (1 : ℕ) else 0)) =
        if B.Nonempty then N ^ (n - 1) else 0 := by
    intro B
    by_cases hB : B.Nonempty
    · rw [if_pos hB]
      have hset : (Finset.univ.filter (fun a : Fin n → ZMod N => B.Nonempty ∧ ssum B a = t))
          = Finset.univ.filter (fun a : Fin n → ZMod N => ssum B a = t) := by
        ext a
        simp [hB]
      have hcard :
          (Finset.univ.filter (fun a : Fin n → ZMod N => ssum B a = t)).card =
            Fintype.card {a : Fin n → ZMod N // ssum B a = t} :=
        (Fintype.card_of_subtype (p := fun a : Fin n → ZMod N => ssum B a = t) _
          (fun a => by simp)).symm
      rw [← Finset.card_filter, hset, hcard]
      exact card_fiber B hB t
    · rw [if_neg hB]
      have hset : (Finset.univ.filter (fun a : Fin n → ZMod N => B.Nonempty ∧ ssum B a = t))
          = ∅ := by
        ext a
        simp [hB]
      rw [← Finset.card_filter, hset]
      simp
  calc ∑ a : Fin n → ZMod N, countNonempty a t
      = ∑ a : Fin n → ZMod N, ∑ B : Finset (Fin n),
          (if B.Nonempty ∧ ssum B a = t then (1 : ℕ) else 0) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        unfold countNonempty
        rw [Finset.card_filter]
    _ = ∑ B : Finset (Fin n), ∑ a : Fin n → ZMod N,
          (if B.Nonempty ∧ ssum B a = t then (1 : ℕ) else 0) := Finset.sum_comm
    _ = ∑ B : Finset (Fin n), (if B.Nonempty then N ^ (n - 1) else 0) := by
        exact Finset.sum_congr rfl (fun B _ => hstep B)
    _ = (2 ^ n - 1) * N ^ (n - 1) := by
        rw [← Finset.sum_filter]
        rw [Finset.sum_const, smul_eq_mul]
        congr 1
        have hcard :
            (Finset.univ.filter (fun B : Finset (Fin n) => B.Nonempty)).card =
              Fintype.card {B : Finset (Fin n) // B.Nonempty} :=
          (Fintype.card_of_subtype (p := fun B : Finset (Fin n) => B.Nonempty) _
            (fun B => by simp)).symm
        rw [hcard, card_nonempty_finset n]

def noSubsetSum_prob_le_half (N r : ℕ) [NeZero N] (_hr : 8 * N < 2 ^ r) : Prop := by
  classical
  exact (Fintype.card {p : (Fin r → ZMod N) × ZMod N // ¬ SubsetSumLegal N r p.1 p.2} : ℝ) * 2
    ≤ (Fintype.card ((Fin r → ZMod N) × ZMod N) : ℝ)

end Qatlib.Papers.QLattice03.MainResults
