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
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Disjoint
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Qatlib.Papers.HiddenSubgrp04.MainResults.Defs

/-!
# Rounded cells and modular-distance estimates

This module proves nearest-integer estimates for `nearInt` and a Lipschitz estimate for
`distMod`. It defines the cell and coordinate-map propositions `lemma_A4Statement` and
`lemma_A5Statement`, and proves the modular-distance lower bound `lemma_A6` outside a cell.

The development follows [Lomont2004].

## Main statements

* `abs_distMod_sub_le`: For positive modulus M, the absolute difference of the modular distances
  of `x` and `y` is at most |x − y|.
* `lemma_A4Statement`: The proposition that the two specified distinct cells have equal
  cardinality and are disjoint, under N > 2, M ≥ 2N, and valid index hypotheses.
* `lemma_A6`: If `k` is outside the i-th cell and the size and index hypotheses hold, its
  modular distance from Mi/N is at least M/(2N) − 1.

## References

* [Lomont, 2004][Lomont2004]
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.HiddenSubgrp04.MainResults

noncomputable section

/-- The integer `nearInt x` is at distance at most one half from `x`. -/
theorem abs_nearInt_sub_le (x : ℝ) : |(nearInt x : ℝ) - x| ≤ 1 / 2 := by
  have h1 : (nearInt x : ℝ) ≤ x + 1 / 2 := by
    unfold nearInt
    exact Int.floor_le (x + 1 / 2)
  have h2 : x + 1 / 2 < (nearInt x : ℝ) + 1 := by
    unfold nearInt
    exact Int.lt_floor_add_one (x + 1 / 2)
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The integer `nearInt x` is at least as close to `x` as any other integer. -/
theorem abs_nearInt_sub_le_any (x : ℝ) (n : ℤ) :
    |(nearInt x : ℝ) - x| ≤ |(n : ℝ) - x| := by
  set f : ℤ := nearInt x with hf
  have hx : |(f : ℝ) - x| ≤ 1 / 2 := abs_nearInt_sub_le x
  have hx1 : (f : ℝ) - x ≤ 1 / 2 := (abs_sub_le_iff.mp hx).1
  have hx2 : x - (f : ℝ) ≤ 1 / 2 := (abs_sub_le_iff.mp hx).2
  rcases lt_trichotomy n f with hlt | heq | hgt
  · have hn : (n : ℝ) ≤ (f : ℝ) - 1 := by
      have hz : n ≤ f - 1 := by omega
      exact_mod_cast hz
    have hnx : (n : ℝ) - x < 0 := by linarith
    rw [abs_of_neg hnx]
    linarith [abs_nonneg ((f : ℝ) - x)]
  · subst heq
    simp
  · have hn : (f : ℝ) + 1 ≤ (n : ℝ) := by
      have hz : f + 1 ≤ n := by omega
      exact_mod_cast hz
    have hnx : 0 < (n : ℝ) - x := by linarith
    rw [abs_of_pos hnx]
    linarith [abs_nonneg ((f : ℝ) - x)]

/-- For positive modulus M, the absolute difference of the modular distances of `x` and `y` is
at most |x − y|. -/
theorem abs_distMod_sub_le {M : ℝ} (hM : 0 < M) (x y : ℝ) :
    |distMod M x - distMod M y| ≤ |x - y| := by
  have hmin : ∀ a b : ℝ,
      |a - M * (nearInt (a / M) : ℝ)| ≤ |a - M * (nearInt (b / M) : ℝ)| := by
    intro a b
    have h := abs_nearInt_sub_le_any (a / M) (nearInt (b / M))
    have hscale : ∀ z : ℝ, |a - M * z| = M * |a / M - z| := by
      intro z
      rw [show a - M * z = M * (a / M - z) by field_simp]
      rw [abs_mul, abs_of_pos hM]
    calc |a - M * (nearInt (a / M) : ℝ)|
        = M * |a / M - (nearInt (a / M) : ℝ)| := hscale _
      _ = M * |(nearInt (a / M) : ℝ) - a / M| := by rw [abs_sub_comm]
      _ ≤ M * |(nearInt (b / M) : ℝ) - a / M| :=
          mul_le_mul_of_nonneg_left h (le_of_lt hM)
      _ = M * |a / M - (nearInt (b / M) : ℝ)| := by rw [abs_sub_comm]
      _ = |a - M * (nearInt (b / M) : ℝ)| := (hscale _).symm
  have key : ∀ a b : ℝ, distMod M a ≤ |a - b| + distMod M b := by
    intro a b
    have h1 : distMod M a = |a - M * (nearInt (a / M) : ℝ)| := rfl
    have h2 : distMod M b = |b - M * (nearInt (b / M) : ℝ)| := rfl
    calc distMod M a = |a - M * (nearInt (a / M) : ℝ)| := h1
      _ ≤ |a - M * (nearInt (b / M) : ℝ)| := hmin a b
      _ = |(a - b) + (b - M * (nearInt (b / M) : ℝ))| := by ring_nf
      _ ≤ |a - b| + |b - M * (nearInt (b / M) : ℝ)| := abs_add_le _ _
      _ = |a - b| + distMod M b := by rw [h2]
  have hyx : |y - x| = |x - y| := abs_sub_comm y x
  rw [abs_sub_le_iff]
  constructor <;> linarith [key x y, key y x]

/-- The proposition that the two specified distinct cells have equal cardinality and are
disjoint, under N > 2, M ≥ 2N, and valid index hypotheses. -/
def lemma_A4Statement (M N : ℕ) (hN : 2 < N) (hM : 2 * N ≤ M)
    (i1 i2 : ℕ) (h1 : i1 < N) (h2 : i2 < N) (hne : i1 ≠ i2) : Prop :=
    (cell M N i1).card = (cell M N i2).card ∧
      Disjoint (cell M N i1) (cell M N i2)

/-- The proposition asserting injectivity of `deltaMap` on `Fin M`, the equality `alpha = beta +
1`, and the stated inner and outer interval inclusions for each coordinate fiber `Cs`. -/
def lemma_A5Statement (M N : ℕ) : Prop :=
    Function.Injective (fun k : Fin M => deltaMap M N k.val) ∧
      alpha M N = beta M N + 1 ∧
      (∀ s : ℤ, 0 ≤ s → s < (N : ℤ) →
        Set.Icc (-(beta M N)) (beta M N) ⊆ Cs M N s ∧
          Cs M N s ⊆ Set.Icc (-(alpha M N)) (alpha M N))

/-- If `k` is outside the i-th cell and the size and index hypotheses hold, its modular distance
from Mi/N is at least M/(2N) − 1 ([Lemma A.6][Lomont2004]). -/
theorem lemma_A6 (M N i k : ℕ) (hN : 2 < N) (hM : 2 * N ≤ M)
    (hi : i < N) (hk : k < M) (hnot : k ∉ cell M N i) :
    (M : ℝ) / (2 * (N : ℝ)) - 1 ≤
      distMod (M : ℝ) ((k : ℝ) - (M : ℝ) / (N : ℝ) * (i : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hmem : (k ∈ cell M N i) ↔
      distMod (M : ℝ) ((k : ℝ) - (nearInt ((M : ℝ) / (N : ℝ) * (i : ℝ)) : ℝ)) <
        (M : ℝ) / (2 * (N : ℝ)) - 1 / 2 := by
    simp only [cell, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨hk, h⟩⟩
  have hge : (M : ℝ) / (2 * (N : ℝ)) - 1 / 2 ≤
      distMod (M : ℝ) ((k : ℝ) - (nearInt ((M : ℝ) / (N : ℝ) * (i : ℝ)) : ℝ)) := by
    rw [hmem] at hnot
    exact not_lt.mp hnot
  have hbound : |(nearInt ((M : ℝ) / (N : ℝ) * (i : ℝ)) : ℝ) - (M : ℝ) / (N : ℝ) * (i : ℝ)| ≤ 1 / 2 :=
    abs_nearInt_sub_le _
  have hdiff : ((k : ℝ) - (M : ℝ) / (N : ℝ) * (i : ℝ)) -
        ((k : ℝ) - (nearInt ((M : ℝ) / (N : ℝ) * (i : ℝ)) : ℝ)) =
      (nearInt ((M : ℝ) / (N : ℝ) * (i : ℝ)) : ℝ) - (M : ℝ) / (N : ℝ) * (i : ℝ) := by
    ring
  have hlip : |distMod (M : ℝ) ((k : ℝ) - (M : ℝ) / (N : ℝ) * (i : ℝ)) -
      distMod (M : ℝ) ((k : ℝ) - (nearInt ((M : ℝ) / (N : ℝ) * (i : ℝ)) : ℝ))| ≤ 1 / 2 := by
    calc |distMod (M : ℝ) ((k : ℝ) - (M : ℝ) / (N : ℝ) * (i : ℝ)) -
          distMod (M : ℝ) ((k : ℝ) - (nearInt ((M : ℝ) / (N : ℝ) * (i : ℝ)) : ℝ))|
        ≤ |((k : ℝ) - (M : ℝ) / (N : ℝ) * (i : ℝ)) -
            ((k : ℝ) - (nearInt ((M : ℝ) / (N : ℝ) * (i : ℝ)) : ℝ))| :=
          abs_distMod_sub_le hMpos _ _
      _ = |(nearInt ((M : ℝ) / (N : ℝ) * (i : ℝ)) : ℝ) - (M : ℝ) / (N : ℝ) * (i : ℝ)| := by
          rw [hdiff]
      _ ≤ 1 / 2 := hbound
  have hlow : distMod (M : ℝ) ((k : ℝ) - (M : ℝ) / (N : ℝ) * (i : ℝ)) ≥
      distMod (M : ℝ) ((k : ℝ) - (nearInt ((M : ℝ) / (N : ℝ) * (i : ℝ)) : ℝ)) - 1 / 2 := by
    have := (abs_le.mp hlip).1
    linarith
  linarith [hge, hlow]

end

end Qatlib.Papers.HiddenSubgrp04.MainResults
