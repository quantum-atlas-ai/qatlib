/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic
import Qatlib.Papers.AffineHSP02.MainResults.AffineGroup

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.AffineHSP02.MainResults

noncomputable section

variable {p q : ℕ} [NeZero p]

def affProj (q : ℕ) (a : (ZMod p)ˣ) (b : ZMod p) :
    Matrix (ZMod p)ˣ (ZMod p)ˣ ℂ :=
  fun j k => (q : ℂ)⁻¹ * ∑ t ∈ Finset.range q,
    if ((a : ZMod p) ^ t) * (j : ZMod p) = (k : ZMod p)
    then (ZMod.stdAddChar ((1 - (a : ZMod p) ^ t) * b * (j : ZMod p)) : ℂ)
    else 0

theorem affProj_diag (q : ℕ) (a : (ZMod p)ˣ) (b : ZMod p) (hq : orderOf a = q)
    (j : (ZMod p)ˣ) :
    affProj q a b j j = (q : ℂ)⁻¹ := by
  have hqpos : 0 < q := by rw [← hq]; exact orderOf_pos a
  unfold affProj
  have hsum : ∑ t ∈ Finset.range q,
      (if ((a : ZMod p) ^ t) * (j : ZMod p) = (j : ZMod p)
       then (ZMod.stdAddChar ((1 - (a : ZMod p) ^ t) * b * (j : ZMod p)) : ℂ)
       else 0) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro t ht hne
      rw [if_neg]
      intro h
      apply hne
      have ht' : t < orderOf a := by rw [hq]; exact Finset.mem_range.mp ht
      have h0 : (0 : ℕ) < orderOf a := orderOf_pos a
      have h1 : (a ^ t : (ZMod p)ˣ) * j = (1 : (ZMod p)ˣ) * j := by
        apply Units.ext
        simpa [Units.val_mul] using h
      have hpoweq : a ^ t = a ^ 0 := by
        have hc := mul_right_cancel h1
        simpa using hc
      exact pow_injOn_Iio_orderOf ht' h0 hpoweq
    · intro hnot
      exact absurd (Finset.mem_range.mpr hqpos) hnot
  rw [hsum, mul_one]

theorem affProj_apply_of_mem (q : ℕ) (a : (ZMod p)ˣ) (b : ZMod p)
    (hq : orderOf a = q) (j k : (ZMod p)ˣ) (t₀ : ℕ) (ht₀ : t₀ < q)
    (hk : ((a : ZMod p) ^ t₀) * (j : ZMod p) = (k : ZMod p)) :
    affProj q a b j k
      = (q : ℂ)⁻¹ * (ZMod.stdAddChar (b * ((j : ZMod p) - (k : ZMod p))) : ℂ) := by
  unfold affProj
  have huniq : ∀ t ∈ Finset.range q,
      ((a : ZMod p) ^ t) * (j : ZMod p) = (k : ZMod p) → t = t₀ := by
    intro t ht htk
    have ht' : t < orderOf a := by rw [hq]; exact Finset.mem_range.mp ht
    have ht₀' : t₀ < orderOf a := by rw [hq]; exact ht₀
    have h1 : (a ^ t : (ZMod p)ˣ) * j = k := by
      apply Units.ext
      simpa [Units.val_mul] using htk
    have h2 : (a ^ t₀ : (ZMod p)ˣ) * j = k := by
      apply Units.ext
      simpa [Units.val_mul] using hk
    have hpoweq : a ^ t = a ^ t₀ := mul_right_cancel (h1.trans h2.symm)
    exact pow_injOn_Iio_orderOf ht' ht₀' hpoweq
  rw [Finset.sum_eq_single t₀]
  · rw [if_pos hk]
    congr 1
    have hphase : (1 - (a : ZMod p) ^ t₀) * b * (j : ZMod p)
        = b * ((j : ZMod p) - (k : ZMod p)) := by
      rw [← hk]
      ring
    rw [hphase]
  · intro t ht hne
    rw [if_neg]
    exact fun h => hne (huniq t ht h)
  · intro hnot
    exact absurd (Finset.mem_range.mpr ht₀) hnot

theorem affProj_apply_of_not_mem (q : ℕ) (a : (ZMod p)ˣ) (b : ZMod p)
    (j k : (ZMod p)ˣ)
    (h : ∀ t, t < q → ((a : ZMod p) ^ t) * (j : ZMod p) ≠ (k : ZMod p)) :
    affProj q a b j k = 0 := by
  unfold affProj
  rw [Finset.sum_eq_zero]
  · simp
  · intro t ht
    rw [if_neg]
    exact h t (Finset.mem_range.mp ht)

theorem affProj_trace [Fact p.Prime] (q : ℕ) (a : (ZMod p)ˣ) (b : ZMod p)
    (hq : orderOf a = q) :
    Matrix.trace (affProj q a b) = ((p : ℂ) - 1) * (q : ℂ)⁻¹ := by
  rw [Matrix.trace]
  change ∑ i : (ZMod p)ˣ, affProj q a b i i = ((p : ℂ) - 1) * (q : ℂ)⁻¹
  rw [Finset.sum_congr rfl (fun j _ => affProj_diag q a b hq j)]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_units, ZMod.card]
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [Nat.cast_sub hp1]
  push_cast
  ring

theorem affProj_trace_eq_index [Fact p.Prime] (q : ℕ) (a : (ZMod p)ˣ) (b : ZMod p)
    (hq : orderOf a = q) (hdvd : q ∣ p - 1) :
    Matrix.trace (affProj q a b) = (((p - 1) / q : ℕ) : ℂ) := by
  have hqpos : 0 < q := by rw [← hq]; exact orderOf_pos a
  have hqne : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
  rw [affProj_trace q a b hq]
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [Nat.cast_div hdvd hqne, Nat.cast_sub hp1]
  push_cast
  rw [div_eq_mul_inv]

end

end Qatlib.Papers.AffineHSP02.MainResults
