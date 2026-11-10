/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Qatlib.Foundations.ProbabilityCore.Conditioning

open scoped BigOperators

variable {ι : Type*}
variable {θ : Type*}

def MultiplicativeClose (p q : θ → ℝ) (ε : ℝ) : Prop :=
  ∀ z, |p z - q z| ≤ ε * q z

theorem multiplicative_bounds {p q : θ → ℝ}
    (h : MultiplicativeClose p q (1/10)) (z : θ) :
    (9 / 10 : ℝ) * q z ≤ p z ∧ p z ≤ (11 / 10 : ℝ) * q z := by
  have hz := h z
  have h1 := (abs_le.mp hz).1
  have h2 := (abs_le.mp hz).2
  constructor <;> linarith

noncomputable def postSelect (p : Bool × ι → ℝ) (r : ι) (b : Bool) : ℝ :=
  p (b, r) / (p (false, r) + p (true, r))

theorem postSelect_ratio_one {p q : Bool × ι → ℝ} {r : ι}
    (h : MultiplicativeClose p q (1/10))
    (hq0 : 0 ≤ q (false, r)) (hq1 : 0 ≤ q (true, r))
    (hqS : 0 < q (false, r) + q (true, r)) (b : Bool) :
    (9 / 11 : ℝ) * postSelect q r b ≤ postSelect p r b ∧
      postSelect p r b ≤ (11 / 9 : ℝ) * postSelect q r b := by
  obtain ⟨hp0l, hp0u⟩ := multiplicative_bounds h (false, r)
  obtain ⟨hp1l, hp1u⟩ := multiplicative_bounds h (true, r)
  have hSl : (9 / 10 : ℝ) * (q (false, r) + q (true, r))
      ≤ p (false, r) + p (true, r) := by linarith
  have hSu : p (false, r) + p (true, r)
      ≤ (11 / 10 : ℝ) * (q (false, r) + q (true, r)) := by linarith
  have hTpos : 0 < p (false, r) + p (true, r) := lt_of_lt_of_le (by linarith) hSl
  have hqSpos : 0 < (9 / 10 : ℝ) * (q (false, r) + q (true, r)) := by linarith
  have hb0 : b = false ∨ b = true := by cases b <;> simp
  rcases hb0 with rfl | rfl
  · have hqb : 0 ≤ q (false, r) := hq0
    have hpbl : (9 / 10 : ℝ) * q (false, r) ≤ p (false, r) := hp0l
    have hpbu : p (false, r) ≤ (11 / 10 : ℝ) * q (false, r) := hp0u
    have hqden : (0 : ℝ) < q (false, r) + q (true, r) := hqS
    constructor
    · have h1 : (9 / 11 : ℝ) * (q (false, r) / (q (false, r) + q (true, r)))
          = ((9 / 10 : ℝ) * q (false, r))
              / ((11 / 10 : ℝ) * (q (false, r) + q (true, r))) := by
        field_simp [ne_of_gt hqS]
      rw [postSelect, postSelect, h1]
      calc ((9 / 10 : ℝ) * q (false, r))
            / ((11 / 10 : ℝ) * (q (false, r) + q (true, r)))
          ≤ ((9 / 10 : ℝ) * q (false, r)) / (p (false, r) + p (true, r)) :=
            div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hq0) hTpos hSu
        _ ≤ p (false, r) / (p (false, r) + p (true, r)) :=
            div_le_div_of_nonneg_right hpbl hTpos.le
    · have h2 : ((11 / 10 : ℝ) * q (false, r))
            / ((9 / 10 : ℝ) * (q (false, r) + q (true, r)))
          = (11 / 9 : ℝ) * (q (false, r) / (q (false, r) + q (true, r))) := by
        field_simp [ne_of_gt hqS, ne_of_gt hqSpos]
      rw [postSelect, postSelect, ← h2]
      calc p (false, r) / (p (false, r) + p (true, r))
          ≤ ((11 / 10 : ℝ) * q (false, r)) / (p (false, r) + p (true, r)) :=
            div_le_div_of_nonneg_right hpbu hTpos.le
        _ ≤ ((11 / 10 : ℝ) * q (false, r))
              / ((9 / 10 : ℝ) * (q (false, r) + q (true, r))) :=
            div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hq0) hqSpos hSl
  · have hqb : 0 ≤ q (true, r) := hq1
    have hpbl : (9 / 10 : ℝ) * q (true, r) ≤ p (true, r) := hp1l
    have hpbu : p (true, r) ≤ (11 / 10 : ℝ) * q (true, r) := hp1u
    constructor
    · have h1 : (9 / 11 : ℝ) * (q (true, r) / (q (false, r) + q (true, r)))
          = ((9 / 10 : ℝ) * q (true, r))
              / ((11 / 10 : ℝ) * (q (false, r) + q (true, r))) := by
        field_simp [ne_of_gt hqS]
      rw [postSelect, postSelect, h1]
      calc ((9 / 10 : ℝ) * q (true, r))
            / ((11 / 10 : ℝ) * (q (false, r) + q (true, r)))
          ≤ ((9 / 10 : ℝ) * q (true, r)) / (p (false, r) + p (true, r)) :=
            div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hq1) hTpos hSu
        _ ≤ p (true, r) / (p (false, r) + p (true, r)) :=
            div_le_div_of_nonneg_right hpbl hTpos.le
    · have h2 : ((11 / 10 : ℝ) * q (true, r))
            / ((9 / 10 : ℝ) * (q (false, r) + q (true, r)))
          = (11 / 9 : ℝ) * (q (true, r) / (q (false, r) + q (true, r))) := by
        field_simp [ne_of_gt hqS, ne_of_gt hqSpos]
      rw [postSelect, postSelect, ← h2]
      calc p (true, r) / (p (false, r) + p (true, r))
          ≤ ((11 / 10 : ℝ) * q (true, r)) / (p (false, r) + p (true, r)) :=
            div_le_div_of_nonneg_right hpbu hTpos.le
        _ ≤ ((11 / 10 : ℝ) * q (true, r))
              / ((9 / 10 : ℝ) * (q (false, r) + q (true, r))) :=
            div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hq1) hqSpos hSl

theorem postSelect_ratio {p q : Bool × ι → ℝ} {r : ι}
    (h : MultiplicativeClose p q (1/10))
    (hq0 : 0 ≤ q (false, r)) (hq1 : 0 ≤ q (true, r))
    (hqS : 0 < q (false, r) + q (true, r)) (b : Bool) :
    (9 / 11 : ℝ) * postSelect q r b ≤ postSelect p r b ∧
      postSelect p r b ≤ (11 / 9 : ℝ) * postSelect q r b :=
  postSelect_ratio_one h hq0 hq1 hqS b

theorem postSelect_nonneg {p q : Bool × ι → ℝ} {r : ι}
    (h : MultiplicativeClose p q (1/10))
    (_hq0 : 0 ≤ q (false, r)) (hq1 : 0 ≤ q (true, r))
    (hqS : 0 < q (false, r) + q (true, r)) :
    0 ≤ postSelect p r true := by
  obtain ⟨hp0l, _⟩ := multiplicative_bounds h (false, r)
  obtain ⟨hp1l, _⟩ := multiplicative_bounds h (true, r)
  have hSl : (9 / 10 : ℝ) * (q (false, r) + q (true, r))
      ≤ p (false, r) + p (true, r) := by linarith
  have hTpos : 0 < p (false, r) + p (true, r) := lt_of_lt_of_le (by linarith) hSl
  have hp1nn : 0 ≤ p (true, r) := le_trans (mul_nonneg (by norm_num) hq1) hp1l
  exact div_nonneg hp1nn hTpos.le

theorem postSelect_thresholds {p q : Bool × ι → ℝ} {r : ι}
    (h : MultiplicativeClose p q (1/10))
    (hq0 : 0 ≤ q (false, r)) (hq1 : 0 ≤ q (true, r))
    (hqS : 0 < q (false, r) + q (true, r)) :
    (2 / 3 ≤ postSelect q r true → (0.54 : ℝ) ≤ postSelect p r true) ∧
      (postSelect q r true ≤ 1 / 3 → postSelect p r true ≤ (0.41 : ℝ)) := by
  obtain ⟨hlow, hup⟩ := postSelect_ratio h hq0 hq1 hqS true
  constructor
  · intro hyes
    nlinarith [hlow, hyes]
  · intro hno
    nlinarith [hup, hno]

theorem postSelect_yes_lower {p q : Bool × ι → ℝ} {r : ι}
    (h : MultiplicativeClose p q (1/10))
    (hq0 : 0 ≤ q (false, r)) (hq1 : 0 ≤ q (true, r))
    (hqS : 0 < q (false, r) + q (true, r))
    (hyes : 2 / 3 ≤ postSelect q r true) :
    (0.54 : ℝ) ≤ postSelect p r true := by
  obtain ⟨hlow, _⟩ := postSelect_ratio h hq0 hq1 hqS true
  nlinarith [hlow, hyes]

theorem postSelect_no_upper {p q : Bool × ι → ℝ} {r : ι}
    (h : MultiplicativeClose p q (1/10))
    (hq0 : 0 ≤ q (false, r)) (hq1 : 0 ≤ q (true, r))
    (hqS : 0 < q (false, r) + q (true, r))
    (hno : postSelect q r true ≤ 1 / 3) :
    postSelect p r true ≤ (0.41 : ℝ) := by
  obtain ⟨_, hup⟩ := postSelect_ratio h hq0 hq1 hqS true
  nlinarith [hup, hno]

end Qatlib.Foundations.ProbabilityCore.Conditioning
