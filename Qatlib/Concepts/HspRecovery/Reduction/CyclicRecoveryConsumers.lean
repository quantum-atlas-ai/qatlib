/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.CyclicRecovery.CyclicGcdDecoder
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open scoped Classical

variable {R : Type} [Fintype R] [DecidableEq R] [AddCommGroup R]

theorem cyclic_constant_and_injective_consumer (N m : ℕ) (hN : 0 < N) :
    (cyclicSampleDist N hN (fun _ : Fin N => (0 : ZMod 1))).probEvent
        (fun ω : Fin m → Fin N =>
          cyclicVerifiedDecode N hN (fun _ => (0 : ZMod 1)) ω = some 1) = 1 ∧
    (∀ f : Fin N → R, Function.Injective f → ∀ y : Fin N,
      (cyclicSampleDist N hN f).prob y = 1 / (N : ℝ)) := by
  constructor
  · have hcol : ∀ x y : Fin N,
        (fun _ : Fin N => (0 : ZMod 1)) x = (fun _ : Fin N => (0 : ZMod 1)) y ↔
          x.val % 1 = y.val % 1 := by
      intro x y
      simp [Nat.mod_one]
    have hω0 : ∀ ω : Fin m → Fin N, (∀ i, (N / 1) ∣ (ω i).val) →
        cyclicVerifiedDecode N hN (fun _ : Fin N => (0 : ZMod 1)) ω = some 1 := by
      intro ω hsupp
      rw [Nat.div_one] at hsupp
      have hzero : ∀ i, (ω i).val = 0 := fun i =>
        Nat.eq_zero_of_dvd_of_lt (hsupp i) (ω i).isLt
      have hdecode : cyclicPeriodDecode N ω = 1 := by
        show N / (cyclicGcdCounted N (List.ofFn fun i => (ω i).val)).1 = 1
        rw [(cyclic_counted_euclidean_gcd N _).1]
        have hlist : List.ofFn (fun i => (ω i).val) = List.replicate m 0 := by
          rw [← List.ofFn_const]
          exact congrArg List.ofFn (funext fun i => hzero i)
        rw [hlist]
        have hfold : ∀ n : ℕ, (List.replicate n (0 : ℕ)).foldl Nat.gcd N = N := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih =>
            rw [List.replicate_succ, List.foldl_cons, Nat.gcd_zero_right]
            exact ih
        rw [hfold, Nat.div_self hN]
      rw [cyclicVerifiedDecode_def, hdecode, if_pos rfl]
    have htotal : ∀ ω : Fin m → Fin N,
        (cyclicSampleDist N hN (fun _ : Fin N => (0 : ZMod 1))).probOf ω
          = if (∀ i, (ω i).val = 0) then (1 : ℝ) else 0 := by
      intro ω
      rw [cyclicSampleDist_probOf N 1 hN _ (by norm_num) (one_dvd N) hcol m ω,
        Nat.div_one]
      have hone : (1 / ((1 : ℕ) : ℝ)) ^ m = 1 := by
        rw [Nat.cast_one, one_div, inv_one, one_pow]
      rw [hone]
      by_cases h : ∀ i, N ∣ (ω i).val
      · rw [if_pos h, if_pos (fun i => Nat.eq_zero_of_dvd_of_lt (h i) (ω i).isLt)]
      · rw [if_neg h, if_neg (fun hz => h fun i => by rw [hz i]; exact dvd_zero _)]
    show ∑ ω ∈ Finset.univ.filter (fun ω : Fin m → Fin N =>
        cyclicVerifiedDecode N hN (fun _ : Fin N => (0 : ZMod 1)) ω = some 1),
        (cyclicSampleDist N hN (fun _ : Fin N => (0 : ZMod 1))).probOf ω = 1
    apply le_antisymm
    · calc ∑ ω ∈ Finset.univ.filter (fun ω : Fin m → Fin N =>
              cyclicVerifiedDecode N hN (fun _ : Fin N => (0 : ZMod 1)) ω = some 1),
              (cyclicSampleDist N hN (fun _ : Fin N => (0 : ZMod 1))).probOf ω
          ≤ ∑ ω : Fin m → Fin N,
              (cyclicSampleDist N hN (fun _ : Fin N => (0 : ZMod 1))).probOf ω :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun ω _ _ => FinDist.probOf_nonneg _ ω)
        _ = 1 := (cyclicSampleDist N hN _).sum_probOf m
    · have hmem : (fun _ : Fin m => (⟨0, hN⟩ : Fin N)) ∈ Finset.univ.filter
          (fun ω : Fin m → Fin N =>
            cyclicVerifiedDecode N hN (fun _ : Fin N => (0 : ZMod 1)) ω = some 1) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hω0 _ fun i => by
          rw [Nat.div_one]
          exact dvd_zero _⟩
      have h1 : (cyclicSampleDist N hN (fun _ : Fin N => (0 : ZMod 1))).probOf
            (fun _ : Fin m => (⟨0, hN⟩ : Fin N)) = 1 := by
        rw [htotal]
        exact if_pos fun i => rfl
      calc (1 : ℝ) = (cyclicSampleDist N hN (fun _ : Fin N => (0 : ZMod 1))).probOf
              (fun _ : Fin m => (⟨0, hN⟩ : Fin N)) := h1.symm
        _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin m → Fin N =>
              cyclicVerifiedDecode N hN (fun _ : Fin N => (0 : ZMod 1)) ω = some 1),
              (cyclicSampleDist N hN (fun _ : Fin N => (0 : ZMod 1))).probOf ω :=
            Finset.single_le_sum (fun ω _ => FinDist.probOf_nonneg _ ω) hmem
  · intro f hf y
    have hcol : ∀ a b : Fin N, f a = f b ↔ a.val % N = b.val % N := by
      intro a b
      rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt]
      exact ⟨fun h => Fin.ext_iff.mp (hf h), fun h => congrArg f (Fin.ext h)⟩
    have h := cyclic_period_born_uniform_multiples N N hN f hN (dvd_refl N) hcol y
    rw [Nat.div_self hN] at h
    simpa using h

theorem cyclic_mod_twelve_actual_consumer :
    (∀ y : Fin 12, (cyclicSampleDist 12 (by omega) (fun x : Fin 12 => (x.val : ZMod 4))).prob y =
      if 3 ∣ y.val then 1 / 4 else 0) ∧
    cyclicPeriodDecode 12 (![3, 6] : Fin 2 → Fin 12) = 4 ∧
    cyclicVerifiedDecode 12 (by omega) (fun x : Fin 12 => (x.val : ZMod 4))
        (![3, 6] : Fin 2 → Fin 12) = some 4 ∧
    cyclicVerifiedDecode 12 (by omega) (fun x : Fin 12 => (x.val : ZMod 4))
        (![0, 6] : Fin 2 → Fin 12) = none := by
  have hcol : ∀ x y : Fin 12,
      (x.val : ZMod 4) = (y.val : ZMod 4) ↔ x.val % 4 = y.val % 4 :=
    fun x y => ZMod.natCast_eq_natCast_iff x.val y.val 4
  refine ⟨?_, by decide, by decide, by decide⟩
  intro y
  exact cyclic_period_born_uniform_multiples 12 4 (by omega)
    (fun x : Fin 12 => (x.val : ZMod 4)) (by norm_num) (by norm_num) hcol y

end Qatlib.Concepts.HspRecovery.ReductionCore
