/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.HiddenSubgrp04.MainResults.Defs
import Qatlib.Papers.HiddenSubgrp04.MainResults.AppendixASets

/-!
# Injectivity and range bounds for rounded coordinates

This module proves monotonicity and elementary bounds for `nearInt`, then applies them to the
coordinate map `deltaMap`. The results `lemma_A5_injective` and `lemma_A5_image_subset`
establish injectivity on the input register and an outer interval bound for its
second-coordinate fibers.

The development follows [Lomont2004].

## Main statements

* `kappa_bounds`: For positive N, N ≤ M, and k < M, the rounded value Nk/M lies between zero and
  N, inclusive.
* `lemma_A5_injective`: For positive N and N ≤ M, `deltaMap M N` is injective on `Fin M`.
* `lemma_A5_image_subset`: For positive N and N ≤ M, every second-coordinate fiber `Cs M N s`
  lies in the integer interval from −alpha to alpha.

## References

* [Lomont, 2004][Lomont2004]
-/

set_option warningAsError false

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.HiddenSubgrp04.MainResults

noncomputable section

/-- Nearest-integer rounding is monotone on the real numbers. -/
theorem nearInt_mono {x y : ℝ} (h : x ≤ y) : nearInt x ≤ nearInt y := by
  unfold nearInt
  exact Int.floor_mono (by linarith)

/-- Subtracting one half from the rounded integer gives a lower bound on the original real
number. -/
theorem nearInt_sub_half_le (x : ℝ) : (nearInt x : ℝ) - 1 / 2 ≤ x := by
  have h := (abs_le.mp (abs_nearInt_sub_le x)).2
  linarith

/-- Adding one half to the rounded integer gives an upper bound on the original real number. -/
theorem le_nearInt_add_half (x : ℝ) : x ≤ (nearInt x : ℝ) + 1 / 2 := by
  have h := (abs_le.mp (abs_nearInt_sub_le x)).1
  linarith

/-- Nearest-integer rounding sends zero to zero. -/
theorem nearInt_zero : nearInt (0 : ℝ) = 0 := by
  unfold nearInt
  norm_num

/-- Nearest-integer rounding fixes every integer cast to the reals. -/
theorem nearInt_intCast (z : ℤ) : nearInt (z : ℝ) = z := by
  unfold nearInt
  rw [show (z : ℝ) + 1 / 2 = (1 / 2 : ℝ) + (z : ℝ) by ring,
    Int.floor_add_intCast]
  norm_num

/-- For positive N, N ≤ M, and k < M, the rounded value Nk/M lies between zero and N, inclusive. -/
theorem kappa_bounds (M N k : ℕ) (hN : 0 < N) (_hM : N ≤ M) (hk : k < M) :
    0 ≤ nearInt ((N : ℝ) / (M : ℝ) * (k : ℝ)) ∧
      nearInt ((N : ℝ) / (M : ℝ) * (k : ℝ)) ≤ (N : ℤ) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  set k' : ℤ := nearInt ((N : ℝ) / (M : ℝ) * (k : ℝ)) with hk'
  have hxnonneg : (0 : ℝ) ≤ (N : ℝ) / (M : ℝ) * (k : ℝ) := by positivity
  have hklt : (k : ℝ) < (M : ℝ) := by exact_mod_cast hk
  have hxlt : (N : ℝ) / (M : ℝ) * (k : ℝ) < (N : ℝ) := by
    calc (N : ℝ) / (M : ℝ) * (k : ℝ)
        < (N : ℝ) / (M : ℝ) * (M : ℝ) :=
          mul_lt_mul_of_pos_left hklt (by positivity)
      _ = (N : ℝ) := by field_simp
  constructor
  · have h1 : (N : ℝ) / (M : ℝ) * (k : ℝ) ≤ (k' : ℝ) + 1 / 2 := by
      rw [hk']; exact le_nearInt_add_half _
    have h2 : (-1 : ℝ) < (k' : ℝ) := by linarith
    have h3 : (-1 : ℤ) < k' := by exact_mod_cast h2
    omega
  · have h1 : (k' : ℝ) - 1 / 2 ≤ (N : ℝ) / (M : ℝ) * (k : ℝ) := by
      rw [hk']; exact nearInt_sub_half_le _
    have h2 : (k' : ℝ) < (N : ℝ) + 1 := by linarith
    have h3 : k' < (N : ℤ) + 1 := by exact_mod_cast h2
    omega

/-- For positive N and N ≤ M, `deltaMap M N` is injective on `Fin M` ([Lemma A.5][Lomont2004]). -/
theorem lemma_A5_injective (M N : ℕ) (hN : 0 < N) (hM : N ≤ M) :
    Function.Injective (fun k : Fin M => deltaMap M N k.val) := by
  intro k1 k2 h
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  unfold deltaMap at h
  dsimp only at h
  set k1' : ℤ := nearInt ((N : ℝ) / (M : ℝ) * (k1.val : ℝ)) with hk1'
  set k2' : ℤ := nearInt ((N : ℝ) / (M : ℝ) * (k2.val : ℝ)) with hk2'
  have hs : k1' % (N : ℤ) = k2' % (N : ℤ) := congrArg Prod.fst h
  have ht : (k1.val : ℤ) - nearInt ((M : ℝ) / (N : ℝ) * (k1' : ℝ))
      = (k2.val : ℤ) - nearInt ((M : ℝ) / (N : ℝ) * (k2' : ℝ)) :=
    congrArg Prod.snd h
  have hb1 : 0 ≤ k1' ∧ k1' ≤ (N : ℤ) := by
    rw [hk1']; exact kappa_bounds M N k1.val hN hM k1.isLt
  have hb2 : 0 ≤ k2' ∧ k2' ≤ (N : ℤ) := by
    rw [hk2']; exact kappa_bounds M N k2.val hN hM k2.isLt

  have hdvd : (N : ℤ) ∣ (k2' - k1') := Int.modEq_iff_dvd.mp hs
  obtain ⟨m, hm⟩ := hdvd
  have hNposZ : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hbb1 : (N : ℤ) * m ≤ (N : ℤ) := by rw [← hm]; omega
  have hbb2 : -((N : ℤ)) ≤ (N : ℤ) * m := by rw [← hm]; omega
  have hNposR' : (0 : ℝ) < ((N : ℤ) : ℝ) := by exact_mod_cast hNposZ
  have hmle : m ≤ 1 := by
    have hc : ((N : ℤ) : ℝ) * (m : ℝ) ≤ ((N : ℤ) : ℝ) := by
      have h : (((N : ℤ) * m : ℤ) : ℝ) ≤ ((N : ℤ) : ℝ) := by exact_mod_cast hbb1
      simpa only [Int.cast_mul] using h
    have h' : (m : ℝ) ≤ 1 := by nlinarith
    exact_mod_cast h'
  have hmge : -1 ≤ m := by
    have hc : -((N : ℤ) : ℝ) ≤ ((N : ℤ) : ℝ) * (m : ℝ) := by
      have h : (((-(N : ℤ)) : ℤ) : ℝ) ≤ (((N : ℤ) * m : ℤ) : ℝ) := by
        exact_mod_cast hbb2
      simpa only [Int.cast_mul, Int.cast_neg] using h
    have h' : (-1 : ℝ) ≤ (m : ℝ) := by nlinarith
    exact_mod_cast h'
  have hmcases : m = -1 ∨ m = 0 ∨ m = 1 := by omega

  have hN0 : nearInt ((M : ℝ) / (N : ℝ) * ((0 : ℤ) : ℝ)) = 0 := by
    have : (M : ℝ) / (N : ℝ) * ((0 : ℤ) : ℝ) = 0 := by simp
    rw [this, nearInt_zero]
  have hNN : nearInt ((M : ℝ) / (N : ℝ) * ((N : ℤ) : ℝ)) = (M : ℤ) := by
    have hcast : ((N : ℤ) : ℝ) = (N : ℝ) := by simp
    rw [hcast]
    have hMN : (M : ℝ) / (N : ℝ) * (N : ℝ) = (M : ℝ) := by field_simp
    rw [hMN, show (M : ℝ) = ((M : ℤ) : ℝ) by simp, nearInt_intCast]
  rcases hmcases with hm1 | hm0 | hp1
  · have hk1N : k1' = (N : ℤ) := by
      have : k2' - k1' = -((N : ℤ)) := by rw [hm, hm1]; ring
      omega
    have hk20 : k2' = 0 := by
      have : k2' - k1' = -((N : ℤ)) := by rw [hm, hm1]; ring
      omega
    rw [hk1N, hk20] at ht
    rw [hNN, hN0] at ht
    have hk1lt : (k1.val : ℤ) < (M : ℤ) := by exact_mod_cast k1.isLt
    have hk2ge : (0 : ℤ) ≤ (k2.val : ℤ) := by positivity

    have : (k1.val : ℤ) = (k2.val : ℤ) + (M : ℤ) := by linarith
    omega
  · have hk' : k1' = k2' := by
      have : k2' - k1' = 0 := by rw [hm, hm0]; ring
      omega
    rw [hk'] at ht
    have : (k1.val : ℤ) = (k2.val : ℤ) := by linarith
    exact Fin.ext (by exact_mod_cast this)
  · have hk10 : k1' = 0 := by
      have : k2' - k1' = (N : ℤ) := by rw [hm, hp1]; ring
      omega
    have hk2N : k2' = (N : ℤ) := by
      have : k2' - k1' = (N : ℤ) := by rw [hm, hp1]; ring
      omega
    rw [hk10, hk2N] at ht
    rw [hN0, hNN] at ht
    have hk2lt : (k2.val : ℤ) < (M : ℤ) := by exact_mod_cast k2.isLt
    have hk1ge : (0 : ℤ) ≤ (k1.val : ℤ) := by positivity
    have : (k2.val : ℤ) = (k1.val : ℤ) + (M : ℤ) := by linarith
    omega

/-- For positive N and N ≤ M, every second-coordinate fiber `Cs M N s` lies in the integer
interval from −alpha to alpha ([Lemma A.5][Lomont2004]). -/
theorem lemma_A5_image_subset (M N : ℕ) (hN : 0 < N) (_hM : N ≤ M) :
    ∀ s : ℤ, Cs M N s ⊆ Set.Icc (-(alpha M N)) (alpha M N) := by
  intro s t ht
  obtain ⟨k, hk, -, htk⟩ := ht

  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set k' : ℤ := nearInt ((N : ℝ) / (M : ℝ) * (k : ℝ)) with hk'
  have ht' : t = (k : ℤ) - nearInt ((M : ℝ) / (N : ℝ) * (k' : ℝ)) := by
    rw [← htk]
    rfl

  have hgap1 : |(k' : ℝ) - (N : ℝ) / (M : ℝ) * (k : ℝ)| ≤ 1 / 2 := by
    have := abs_nearInt_sub_le ((N : ℝ) / (M : ℝ) * (k : ℝ))
    simpa only [hk'] using this
  have hgap2 : |nearInt ((M : ℝ) / (N : ℝ) * (k' : ℝ))
      - (M : ℝ) / (N : ℝ) * (k' : ℝ)| ≤ 1 / 2 :=
    abs_nearInt_sub_le _
  have hkey : (t : ℝ) = -((M : ℝ) / (N : ℝ)) * ((k' : ℝ) - (N : ℝ) / (M : ℝ) * (k : ℝ))
      - (nearInt ((M : ℝ) / (N : ℝ) * (k' : ℝ)) - (M : ℝ) / (N : ℝ) * (k' : ℝ)) := by
    rw [ht']
    push_cast
    field_simp
    ring
  have hMNo : (0 : ℝ) ≤ (M : ℝ) / (N : ℝ) := by positivity
  have habs : |(t : ℝ)| ≤ (M : ℝ) / (2 * (N : ℝ)) + 1 / 2 := by
    have htri : |(t : ℝ)| ≤
        |(-((M : ℝ) / (N : ℝ)) * ((k' : ℝ) - (N : ℝ) / (M : ℝ) * (k : ℝ)))|
          + |(M : ℝ) / (N : ℝ) * (k' : ℝ)
              - nearInt ((M : ℝ) / (N : ℝ) * (k' : ℝ))| := by
      rw [hkey]
      have := abs_add_le
        (-((M : ℝ) / (N : ℝ)) * ((k' : ℝ) - (N : ℝ) / (M : ℝ) * (k : ℝ)))
        (-(nearInt ((M : ℝ) / (N : ℝ) * (k' : ℝ)) - (M : ℝ) / (N : ℝ) * (k' : ℝ)))
      simpa [sub_eq_add_neg, abs_neg] using this
    calc |(t : ℝ)| ≤
          |(-((M : ℝ) / (N : ℝ)) * ((k' : ℝ) - (N : ℝ) / (M : ℝ) * (k : ℝ)))|
            + |(M : ℝ) / (N : ℝ) * (k' : ℝ)
                - nearInt ((M : ℝ) / (N : ℝ) * (k' : ℝ))| := htri
      _ = (M : ℝ) / (N : ℝ) * |(k' : ℝ) - (N : ℝ) / (M : ℝ) * (k : ℝ)|
            + |(M : ℝ) / (N : ℝ) * (k' : ℝ)
                - nearInt ((M : ℝ) / (N : ℝ) * (k' : ℝ))| := by
            rw [abs_mul, abs_neg, abs_of_nonneg hMNo]
      _ ≤ (M : ℝ) / (N : ℝ) * (1 / 2) + 1 / 2 := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hgap1 hMNo
            · rw [abs_sub_comm]; exact hgap2
      _ = (M : ℝ) / (2 * (N : ℝ)) + 1 / 2 := by field_simp
  have hle : (t : ℝ) ≤ (M : ℝ) / (2 * (N : ℝ)) + 1 / 2 := (abs_le.mp habs).2
  have hge : -((M : ℝ) / (2 * (N : ℝ)) + 1 / 2) ≤ (t : ℝ) := (abs_le.mp habs).1
  constructor
  · have : (-t : ℤ) ≤ alpha M N := by
      apply Int.le_floor.mpr
      push_cast
      linarith
    omega
  · apply Int.le_floor.mpr
    linarith

end

end Qatlib.Papers.HiddenSubgrp04.MainResults
