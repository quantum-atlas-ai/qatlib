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
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Disjoint
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
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Zify
import Qatlib.Papers.HiddenSubgrp04.MainResults.Defs
import Qatlib.Papers.HiddenSubgrp04.MainResults.AppendixASets

/-!
# Equal cardinality and disjointness of rounded cells

This module develops periodicity, symmetry, and the triangle inequality for `distMod`, together
with cyclic shifts of natural-number residues. It uses shifts to prove equal cardinalities of
cells and separation of their rounded centers to prove `lemma_A4_disjoint`.

The development follows [Lomont2004].

## Main statements

* `lemma_A4_card`: For positive M, every pair of cells has equal cardinality.
* `distMod_center_sep_ordered`: For positive N and M ≥ 2N, two ordered distinct valid rounded
  centers have modular distance at least M/N − 1.
* `lemma_A4_disjoint`: For positive N and M ≥ 2N, cells with distinct indices below N are
  disjoint.

## References

* [Lomont, 2004][Lomont2004]
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.HiddenSubgrp04.MainResults

noncomputable section

/-- Nearest-integer rounding commutes with addition of an integer. -/
theorem nearInt_add_intCast (x : ℝ) (z : ℤ) : nearInt (x + (z : ℝ)) = nearInt x + z := by
  unfold nearInt
  rw [show x + (z : ℝ) + 1 / 2 = (x + 1 / 2) + (z : ℝ) by ring, Int.floor_add_intCast]

/-- For nonzero modulus M, adding any integer multiple of M preserves `distMod M`. -/
theorem distMod_periodic {M : ℝ} (hM : M ≠ 0) (x : ℝ) (z : ℤ) :
    distMod M (x + M * (z : ℝ)) = distMod M x := by
  unfold distMod
  have hdiv : (x + M * (z : ℝ)) / M = x / M + (z : ℝ) := by field_simp
  rw [hdiv, nearInt_add_intCast, Int.cast_add]
  ring_nf

/-- For positive M, the modular distance of `x` is at most its distance from any integer
multiple of M. -/
theorem distMod_le_any {M : ℝ} (hM : 0 < M) (x : ℝ) (z : ℤ) :
    distMod M x ≤ |x - M * (z : ℝ)| := by
  unfold distMod
  have hscale : ∀ w : ℝ, |x - M * w| = M * |x / M - w| := by
    intro w
    rw [show x - M * w = M * (x / M - w) by field_simp]
    rw [abs_mul, abs_of_pos hM]
  rw [hscale, hscale]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hM)
  have h := abs_nearInt_sub_le_any (x / M) z
  rw [abs_sub_comm ((nearInt (x / M) : ℝ)) (x / M),
    abs_sub_comm (z : ℝ) (x / M)] at h
  exact h

/-- For positive modulus M, negating the argument preserves modular distance. -/
theorem distMod_neg {M : ℝ} (hM : 0 < M) (x : ℝ) : distMod M (-x) = distMod M x := by
  apply le_antisymm
  · calc distMod M (-x)
        ≤ |(-x) - M * ((-(nearInt (x / M)) : ℤ) : ℝ)| :=
          distMod_le_any hM (-x) (-(nearInt (x / M)))
      _ = distMod M x := by
          unfold distMod
          rw [show -x - M * ((-(nearInt (x / M)) : ℤ) : ℝ)
                = -(x - M * (nearInt (x / M) : ℝ)) by push_cast; ring]
          rw [abs_neg]
  · calc distMod M x
        ≤ |x - M * ((-(nearInt ((-x) / M)) : ℤ) : ℝ)| :=
          distMod_le_any hM x (-(nearInt ((-x) / M)))
      _ = distMod M (-x) := by
          unfold distMod
          rw [show x - M * ((-(nearInt ((-x) / M)) : ℤ) : ℝ)
                = -((-x) - M * (nearInt ((-x) / M) : ℝ)) by push_cast; ring]
          rw [abs_neg]

/-- For positive M, the modular distance of a sum is at most the sum of the modular distances. -/
theorem distMod_add_le {M : ℝ} (hM : 0 < M) (x y : ℝ) :
    distMod M (x + y) ≤ distMod M x + distMod M y := by
  have hkey : distMod M (x + y) ≤
      |(x + y) - M * (((nearInt (x / M) + nearInt (y / M) : ℤ)) : ℝ)| :=
    distMod_le_any hM (x + y) (nearInt (x / M) + nearInt (y / M))
  calc distMod M (x + y)
      ≤ |(x + y) - M * (((nearInt (x / M) + nearInt (y / M) : ℤ)) : ℝ)| := hkey
    _ = |(x - M * (nearInt (x / M) : ℝ)) + (y - M * (nearInt (y / M) : ℝ))| := by
        congr 1
        rw [Int.cast_add]
        ring
    _ ≤ |x - M * (nearInt (x / M) : ℝ)| + |y - M * (nearInt (y / M) : ℝ)| :=
        abs_add_le _ _
    _ = distMod M x + distMod M y := rfl

/-- The natural representative of the integer b + d reduced modulo M. -/
def shiftMod (M : ℕ) (d : ℤ) (b : ℕ) : ℕ := (((b : ℤ) + d) % (M : ℤ)).toNat

/-- For positive M, the shifted residue `shiftMod M d b` is less than M. -/
theorem shiftMod_lt (M : ℕ) (d : ℤ) (b : ℕ) (hM : 0 < M) : shiftMod M d b < M := by
  unfold shiftMod
  have hMz : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
  have hnonneg : 0 ≤ ((b : ℤ) + d) % (M : ℤ) := Int.emod_nonneg _ (ne_of_gt hMz)
  have hlt : ((b : ℤ) + d) % (M : ℤ) < (M : ℤ) := Int.emod_lt_of_pos _ hMz
  have hcast : (((((b : ℤ) + d) % (M : ℤ)).toNat : ℕ) : ℤ) < (M : ℤ) := by
    rw [Int.toNat_of_nonneg hnonneg]; exact hlt
  exact_mod_cast hcast

/-- Shifting a residue by the difference of two integer centers preserves its modular distance
relative to the corresponding center, for positive M. -/
theorem distMod_shiftMod (M : ℕ) (hM : 0 < M) (d : ℤ) (b : ℕ) (c1 c2 : ℤ)
    (hd : d = c2 - c1) :
    distMod (M : ℝ) (((shiftMod M d b : ℕ) : ℝ) - (c2 : ℝ))
      = distMod (M : ℝ) ((b : ℝ) - (c1 : ℝ)) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  have hMz : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
  unfold shiftMod
  set x : ℤ := (b : ℤ) + d with hx
  have hnonneg : 0 ≤ x % (M : ℤ) := Int.emod_nonneg _ (ne_of_gt hMz)
  have hcast : ((((x % (M : ℤ)).toNat : ℕ) : ℝ)) = (((x % (M : ℤ)) : ℤ) : ℝ) := by
    have hz : ((x % (M : ℤ)).toNat : ℤ) = x % (M : ℤ) := Int.toNat_of_nonneg hnonneg
    exact_mod_cast hz
  rw [hcast]
  have hq : (x % (M : ℤ) : ℤ) = x - (M : ℤ) * (x / (M : ℤ)) := by
    have h := Int.emod_add_mul_ediv x (M : ℤ)
    linarith
  rw [hq]
  have hre : (((x - (M : ℤ) * (x / (M : ℤ)) : ℤ)) : ℝ) - (c2 : ℝ)
      = ((x : ℝ) - (c2 : ℝ)) + (M : ℝ) * (-(x / (M : ℤ)) : ℤ) := by
    push_cast
    ring
  rw [hre]
  rw [distMod_periodic hMne]
  have hc : (x : ℝ) - (c2 : ℝ) = (b : ℝ) - (c1 : ℝ) := by
    rw [hx, hd]
    push_cast
    ring
  rw [hc]

/-- For positive M, equality of two residues shifted by the same integer implies equality of the
original representatives below M. -/
theorem shiftMod_injective (M : ℕ) (hM0 : 0 < M) (d : ℤ) (b1 b2 : ℕ)
    (h1 : b1 < M) (h2 : b2 < M) (heq : shiftMod M d b1 = shiftMod M d b2) :
    b1 = b2 := by
  have hMz : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM0
  have hz : ((b1 : ℤ) + d) % (M : ℤ) = ((b2 : ℤ) + d) % (M : ℤ) := by
    unfold shiftMod at heq
    have h1n : 0 ≤ ((b1 : ℤ) + d) % (M : ℤ) := Int.emod_nonneg _ (ne_of_gt hMz)
    have h2n : 0 ≤ ((b2 : ℤ) + d) % (M : ℤ) := Int.emod_nonneg _ (ne_of_gt hMz)
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) heq
    push_cast at hcast
    rw [Int.toNat_of_nonneg h1n, Int.toNat_of_nonneg h2n] at hcast
    exact hcast
  have hdvd : (M : ℤ) ∣ ((b2 : ℤ) + d) - ((b1 : ℤ) + d) :=
    Int.modEq_iff_dvd.mp hz
  obtain ⟨k, hk⟩ := hdvd
  have hk' : (b2 : ℤ) - (b1 : ℤ) = (M : ℤ) * k := by linarith [hk]
  have hcastR : (b2 : ℝ) - (b1 : ℝ) = (M : ℝ) * (k : ℝ) := by
    have h : (((b2 : ℤ) - (b1 : ℤ) : ℤ) : ℝ) = ((((M : ℤ) * k : ℤ)) : ℝ) := by
      exact_mod_cast hk'
    push_cast at h
    exact h
  have hb1r : (0 : ℝ) ≤ (b1 : ℝ) := by positivity
  have hb2r : (b2 : ℝ) < (M : ℝ) := by exact_mod_cast h2
  have hMposR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
  have hk0 : k = 0 := by
    by_contra hk0
    rcases lt_or_gt_of_ne hk0 with hneg | hpos
    · have hle : (k : ℝ) ≤ -1 := by
        have hki : k ≤ -1 := by omega
        exact_mod_cast hki
      nlinarith [hcastR, hb1r, hb2r, hMposR]
    · have hge : (1 : ℝ) ≤ (k : ℝ) := by
        have hki : 1 ≤ k := by omega
        exact_mod_cast hki
      nlinarith [hcastR, hb1r, hb2r, hMposR]
  have hbz : (b2 : ℤ) = (b1 : ℤ) := by
    rw [hk0] at hk'
    linarith
  omega

/-- A natural number belongs to a cell exactly when it is below M and satisfies the strict
modular-distance bound from its rounded center. -/
theorem mem_cell_iff (M N : ℕ) (i b : ℕ) :
    b ∈ cell M N i ↔ b < M ∧
      distMod (M : ℝ) ((b : ℝ) - (nearInt ((M : ℝ) / (N : ℝ) * (i : ℝ)) : ℝ))
        < (M : ℝ) / (2 * (N : ℝ)) - 1 / 2 := by
  simp only [cell, Finset.mem_filter, Finset.mem_range]

/-- For positive M, every pair of cells has equal cardinality ([Lemma A.4][Lomont2004]). -/
theorem lemma_A4_card (M N : ℕ) (hM0 : 0 < M) (i1 i2 : ℕ) :
    (cell M N i1).card = (cell M N i2).card := by
  set c1 : ℤ := nearInt ((M : ℝ) / (N : ℝ) * (i1 : ℝ)) with hc1
  set c2 : ℤ := nearInt ((M : ℝ) / (N : ℝ) * (i2 : ℝ)) with hc2
  apply le_antisymm
  · refine Finset.card_le_card_of_injOn (shiftMod M (c2 - c1)) ?_ ?_
    · intro b hb
      simp only [Finset.mem_coe] at hb ⊢
      rw [mem_cell_iff] at hb ⊢
      refine ⟨shiftMod_lt M (c2 - c1) b hM0, ?_⟩
      have hs := distMod_shiftMod M hM0 (c2 - c1) b c1 c2 rfl
      rw [hs]
      simpa only [hc1] using hb.2
    · intro b1 hb1 b2 hb2 heq
      simp only [Finset.mem_coe] at hb1 hb2
      rw [mem_cell_iff] at hb1 hb2
      exact shiftMod_injective M hM0 (c2 - c1) b1 b2 hb1.1 hb2.1 heq
  · refine Finset.card_le_card_of_injOn (shiftMod M (c1 - c2)) ?_ ?_
    · intro b hb
      simp only [Finset.mem_coe] at hb ⊢
      rw [mem_cell_iff] at hb ⊢
      refine ⟨shiftMod_lt M (c1 - c2) b hM0, ?_⟩
      have hs := distMod_shiftMod M hM0 (c1 - c2) b c2 c1 rfl
      rw [hs]
      simpa only [hc2] using hb.2
    · intro b1 hb1 b2 hb2 heq
      simp only [Finset.mem_coe] at hb1 hb2
      rw [mem_cell_iff] at hb1 hb2
      exact shiftMod_injective M hM0 (c1 - c2) b1 b2 hb1.1 hb2.1 heq

/-- If a > 0, a < M, and a ≤ d ≤ M − a, then the distance from d to every integer multiple of
positive M is at least a. -/
theorem distMod_int_sep {M : ℝ} (hM : 0 < M) (a : ℝ) (ha0 : 0 < a) (_haM : a < M)
    (d : ℝ) (hd : a ≤ d) (hdM : d ≤ M - a) (z : ℤ) :
    a ≤ |d - M * (z : ℝ)| := by
  by_cases hz : z ≤ 0
  · have hzr : (z : ℝ) ≤ 0 := by exact_mod_cast hz
    have hnonneg : 0 ≤ d - M * (z : ℝ) := by nlinarith
    rw [abs_of_nonneg hnonneg]
    nlinarith
  · have hzi : 1 ≤ z := by omega
    have hzr : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hzi
    have hneg : d - M * (z : ℝ) < 0 := by nlinarith
    rw [abs_of_neg hneg]
    nlinarith

/-- For positive N and M ≥ 2N, two ordered distinct valid rounded centers have modular distance
at least M/N − 1. -/
theorem distMod_center_sep_ordered (M N : ℕ) (hN : 0 < N) (hM : 2 * N ≤ M)
    (i1 i2 : ℕ) (h1 : i1 < N) (h2 : i2 < N) (hlt : i1 < i2) :
    (M : ℝ) / (N : ℝ) - 1 ≤
      distMod (M : ℝ) (((nearInt ((M : ℝ) / (N : ℝ) * (i2 : ℝ))) : ℝ)
        - ((nearInt ((M : ℝ) / (N : ℝ) * (i1 : ℝ))) : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  set x1 : ℝ := (M : ℝ) / (N : ℝ) * (i1 : ℝ) with hx1
  set x2 : ℝ := (M : ℝ) / (N : ℝ) * (i2 : ℝ) with hx2
  set c1 : ℝ := (nearInt x1 : ℝ) with hc1
  set c2 : ℝ := (nearInt x2 : ℝ) with hc2
  have hb1 := abs_nearInt_sub_le x1
  have hb2 := abs_nearInt_sub_le x2
  rw [← hc1] at hb1
  rw [← hc2] at hb2
  have hc1lo : x1 - 1 / 2 ≤ c1 := by
    have := (abs_sub_le_iff.mp hb1).2; linarith
  have hc1hi : c1 ≤ x1 + 1 / 2 := by
    have := (abs_sub_le_iff.mp hb1).1; linarith
  have hc2lo : x2 - 1 / 2 ≤ c2 := by
    have := (abs_sub_le_iff.mp hb2).2; linarith
  have hc2hi : c2 ≤ x2 + 1 / 2 := by
    have := (abs_sub_le_iff.mp hb2).1; linarith
  have hcoef : (0 : ℝ) ≤ (M : ℝ) / (N : ℝ) := by positivity
  have hx : x2 - x1 = (M : ℝ) / (N : ℝ) * ((i2 : ℝ) - (i1 : ℝ)) := by
    rw [hx1, hx2]; ring
  have hge1 : (1 : ℝ) ≤ (i2 : ℝ) - (i1 : ℝ) := by
    have : (i1 : ℝ) + 1 ≤ (i2 : ℝ) := by
      have h : i1 + 1 ≤ i2 := hlt
      exact_mod_cast h
    linarith
  have hdiff_ge : (M : ℝ) / (N : ℝ) - 1 ≤ c2 - c1 := by
    have hmul : (M : ℝ) / (N : ℝ) ≤ (M : ℝ) / (N : ℝ) * ((i2 : ℝ) - (i1 : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hge1 hcoef
      simpa using this
    linarith [hc1hi, hc2lo, hx, hmul]
  have hle1 : (i2 : ℝ) - (i1 : ℝ) ≤ (N : ℝ) - 1 := by
    have hi2 : (i2 : ℝ) + 1 ≤ (N : ℝ) := by
      have h : i2 + 1 ≤ N := h2
      exact_mod_cast h
    have hi1 : (0 : ℝ) ≤ (i1 : ℝ) := by positivity
    linarith
  have hdiff_le : c2 - c1 ≤ (M : ℝ) - ((M : ℝ) / (N : ℝ) - 1) := by
    have hmul : (M : ℝ) / (N : ℝ) * ((i2 : ℝ) - (i1 : ℝ))
        ≤ (M : ℝ) / (N : ℝ) * ((N : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hle1 hcoef
    have hMN : (M : ℝ) / (N : ℝ) * ((N : ℝ) - 1) = (M : ℝ) - (M : ℝ) / (N : ℝ) := by
      field_simp
    linarith [hc1lo, hc2hi, hx, hmul, hMN]
  have ha0 : (0 : ℝ) < (M : ℝ) / (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (M : ℝ) / (N : ℝ) := by
      rw [le_div_iff₀ hNpos]
      have h : (2 : ℝ) * (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith
    linarith
  have haM : (M : ℝ) / (N : ℝ) - 1 < (M : ℝ) := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hle : (M : ℝ) / (N : ℝ) ≤ (M : ℝ) := by
      rw [div_le_iff₀ hNpos]
      nlinarith [hMpos, hN1]
    linarith
  have key := distMod_int_sep hMpos ((M : ℝ) / (N : ℝ) - 1) ha0 haM
    (c2 - c1) hdiff_ge hdiff_le (nearInt ((c2 - c1) / (M : ℝ)))
  have hgoal : (((nearInt ((M : ℝ) / (N : ℝ) * (i2 : ℝ))) : ℝ)
      - ((nearInt ((M : ℝ) / (N : ℝ) * (i1 : ℝ))) : ℝ)) = c2 - c1 := by
    simp only [← hx1, ← hx2, hc1, hc2]
  rw [hgoal]
  exact key

/-- For positive N and M ≥ 2N, cells with distinct indices below N are disjoint ([Lemma
A.4][Lomont2004]). -/
theorem lemma_A4_disjoint (M N : ℕ) (hN : 0 < N) (hM : 2 * N ≤ M)
    (i1 i2 : ℕ) (h1 : i1 < N) (h2 : i2 < N) (hne : i1 ≠ i2) :
    Disjoint (cell M N i1) (cell M N i2) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  rw [Finset.disjoint_left]
  intro b hb1 hb2
  rw [mem_cell_iff] at hb1 hb2
  set c1 : ℝ := (nearInt ((M : ℝ) / (N : ℝ) * (i1 : ℝ)) : ℝ) with hc1
  set c2 : ℝ := (nearInt ((M : ℝ) / (N : ℝ) * (i2 : ℝ)) : ℝ) with hc2
  set w : ℝ := (M : ℝ) / (2 * (N : ℝ)) - 1 / 2 with hw
  have hlt1 : distMod (M : ℝ) ((b : ℝ) - c1) < w := by
    simpa only [hc1, hw] using hb1.2
  have hlt2 : distMod (M : ℝ) ((b : ℝ) - c2) < w := by
    simpa only [hc2, hw] using hb2.2
  have htri : distMod (M : ℝ) (c2 - c1)
      ≤ distMod (M : ℝ) (b - c1) + distMod (M : ℝ) (b - c2) := by
    have hsplit : c2 - c1 = (c2 - b) + (b - c1) := by ring
    rw [hsplit]
    calc distMod (M : ℝ) ((c2 - b) + (b - c1))
        ≤ distMod (M : ℝ) (c2 - b) + distMod (M : ℝ) (b - c1) :=
          distMod_add_le hMpos _ _
      _ = distMod (M : ℝ) (b - c2) + distMod (M : ℝ) (b - c1) := by
          rw [show c2 - b = -(b - c2) by ring, distMod_neg hMpos]
      _ = distMod (M : ℝ) (b - c1) + distMod (M : ℝ) (b - c2) := by ring
  have hw2 : (2 : ℝ) * w = (M : ℝ) / (N : ℝ) - 1 := by
    rw [hw]
    field_simp
  have hsum : distMod (M : ℝ) (c2 - c1) < (M : ℝ) / (N : ℝ) - 1 := by
    have : distMod (M : ℝ) (c2 - c1) < 2 * w := by nlinarith [htri, hlt1, hlt2]
    linarith [hw2]
  have hsep : (M : ℝ) / (N : ℝ) - 1 ≤ distMod (M : ℝ) (c2 - c1) := by
    rcases lt_or_gt_of_ne hne with hcase | hcase
    · have := distMod_center_sep_ordered M N hN hM i1 i2 h1 h2 hcase
      simpa only [hc1, hc2] using this
    · have := distMod_center_sep_ordered M N hN hM i2 i1 h2 h1 hcase
      rw [show ((nearInt ((M : ℝ) / (N : ℝ) * (i1 : ℝ))) : ℝ)
            - ((nearInt ((M : ℝ) / (N : ℝ) * (i2 : ℝ))) : ℝ)
            = -(((nearInt ((M : ℝ) / (N : ℝ) * (i2 : ℝ))) : ℝ)
                - ((nearInt ((M : ℝ) / (N : ℝ) * (i1 : ℝ))) : ℝ)) by ring,
        distMod_neg hMpos] at this
      simpa only [hc1, hc2] using this
  linarith

end

end Qatlib.Papers.HiddenSubgrp04.MainResults
