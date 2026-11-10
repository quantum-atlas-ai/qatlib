/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Defs
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
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Foundations.TimeEvolution.TelegraphLimit

def discr (δ a : ℝ) : ℝ := Real.sqrt (1-4*δ*a)

def slow (δ a : ℝ) : ℝ := 2*a/(1+discr δ a)

def fast (δ a : ℝ) : ℝ := (1+discr δ a)/(2*δ)

def coeff (δ a : ℝ) : ℝ := (1-discr δ a)/(2*discr δ a)

theorem discr_bounds {δ a : ℝ} (hδ : 0<δ) (ha : 0 ≤ a) (hm : 4*δ*a ≤ 3/4) :
    1/2 ≤ discr δ a ∧ discr δ a ≤ 1 ∧ (discr δ a)^2=1-4*δ*a := by
  have h0 : 0 ≤ 1-4*δ*a := by linarith
  have hs := Real.sq_sqrt h0
  have hn := Real.sqrt_nonneg (1-4*δ*a)
  have hp : 0 ≤ δ*a := mul_nonneg hδ.le ha
  dsimp [discr]
  constructor
  · nlinarith
  constructor
  · nlinarith
  · exact hs

theorem slow_gap {δ a : ℝ} (hδ : 0<δ) (ha : 0 ≤ a) (hm : 4*δ*a ≤ 3/4) :
    slow δ a-a=4*δ*a^2/(1+discr δ a)^2 := by
  obtain ⟨hd,_,hs⟩ := discr_bounds hδ ha hm
  have hp : 1+discr δ a≠0 := by linarith
  dsimp [slow]
  field_simp
  nlinarith [hs]

theorem coeff_eq {δ a : ℝ} (hδ : 0<δ) (ha : 0 ≤ a) (hm : 4*δ*a ≤ 3/4) :
    coeff δ a=2*δ*a/(discr δ a*(1+discr δ a)) := by
  obtain ⟨hd,_,hs⟩ := discr_bounds hδ ha hm
  have hz : discr δ a≠0 := by linarith
  have hp : 1+discr δ a≠0 := by linarith
  dsimp [coeff]
  field_simp
  nlinarith [hs]

theorem rate_bounds {δ a : ℝ} (hδ : 0<δ) (ha : 0 ≤ a) (hm : 4*δ*a ≤ 3/4) :
    a  ≤  slow δ a ∧ slow δ a  ≤  fast δ a ∧
    0 ≤ coeff δ a ∧ coeff δ a ≤ 4*δ*a ∧ slow δ a-a ≤ 4*δ*a^2 := by
  obtain ⟨hd,hd1,hs⟩ := discr_bounds hδ ha hm
  have hp : 0<1+discr δ a := by linarith
  have hz : 0<discr δ a := by linarith
  have hg := slow_gap hδ ha hm
  have hc := coeff_eq hδ ha hm
  have hgap : 0 ≤ slow δ a-a := by rw [hg]; positivity
  have hfg : slow δ a  ≤  fast δ a := by
    dsimp [slow,fast]
    rw [div_le_div_iff₀ hp (by positivity : 0<2*δ)]
    nlinarith [sq_nonneg (discr δ a)]
  refine ⟨by linarith,hfg,?_,?_,?_⟩
  · rw [hc]; positivity
  · rw [hc]
    apply (div_le_iff₀ (mul_pos hz hp)).mpr
    have hh : 1/2 ≤ discr δ a*(1+discr δ a) := by nlinarith
    nlinarith [mul_nonneg (by positivity : 0 ≤ δ*a) (show 0 ≤ discr δ a*(1+discr δ a)-1/2 by linarith)]
  · rw [hg]
    apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
    have hh : 1 ≤ (1+discr δ a)^2 := by nlinarith
    nlinarith [mul_nonneg (by positivity : 0 ≤ 4*δ*a^2) (show 0 ≤ (1+discr δ a)^2-1 by linarith)]

theorem characteristic {δ a : ℝ} (hδ : 0<δ) (ha : 0 ≤ a) (hm : 4*δ*a ≤ 3/4) :
    δ*(slow δ a)^2-slow δ a+a=0 ∧ δ*(fast δ a)^2-fast δ a+a=0 := by
  obtain ⟨hd,_,hs⟩ := discr_bounds hδ ha hm
  have hp : 1+discr δ a≠0 := by linarith
  have hz : δ≠0 := ne_of_gt hδ
  constructor
  · dsimp [slow]
    field_simp
    nlinarith [mul_nonneg ha (show 0 ≤ δ from hδ.le)]
  · dsimp [fast]
    field_simp
    nlinarith [hs]

theorem zero_initial_flux {δ a : ℝ} (hδ : 0<δ) (ha : 0 ≤ a) (hm : 4*δ*a ≤ 3/4) :
    (1+coeff δ a)*slow δ a=coeff δ a*fast δ a := by
  obtain ⟨hd,_,hs⟩ := discr_bounds hδ ha hm
  have hp : 1+discr δ a≠0 := by linarith
  have hz : discr δ a≠0 := by linarith
  have hδz := ne_of_gt hδ
  dsimp [coeff,slow,fast]
  field_simp
  nlinarith [hs]
end Qatlib.Foundations.TimeEvolution.TelegraphLimit
