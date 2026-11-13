/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Qatlib Contributors

Adapted from https://github.com/TauCetiProject/TauCeti@3780371c
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.ProjIcc

/-!
# Unit-interval partitions and clamped steps

Defines `unitInterval.Partition` as a monotone finite vertex family with prescribed endpoints.
Further lemmas describe clamped repeated steps, their continuity in the step size, and eventual
arrival at the right endpoint for locally positive step sizes.

These subdivision tools support the path and contour arguments associated with [WangEtAl2026].

## Main statements

* `Partition`: A monotone sequence of `n + 1` unit-interval vertices starting at zero and ending
  at one.
* `t_castSucc_le_succ`: Consecutive vertices of a unit-interval partition are nondecreasing.
* `exists_eventually_addNSMul_eq_right`: A step size continuous and positive at a point makes
  all sufficiently large clamped sums equal the right endpoint throughout some neighborhood.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

namespace unitInterval
open scoped _root_.unitInterval

/-- A monotone sequence of `n + 1` unit-interval vertices starting at zero and ending at one. -/
structure Partition (n : ℕ) where

  t : Fin (n + 1) → I

  mono : Monotone t

  t_zero : t 0 = 0

  t_last : t (Fin.last n) = 1

namespace Partition

attribute [simp] t_zero t_last

instance : IsEmpty (Partition 0) :=
  ⟨fun p ↦ zero_ne_one (p.t_zero.symm.trans p.t_last)⟩

/-- Consecutive vertices of a unit-interval partition are nondecreasing. -/
theorem t_castSucc_le_succ {n : ℕ} (part : Partition n) (i : Fin n) :
    part.t i.castSucc ≤ part.t i.succ :=
  part.mono i.castSucc_lt_succ.le

end Partition

end unitInterval

open Filter Set Topology

namespace Set.Icc
open _root_.Set.Icc

/-- For a nonnegative step, the clamped `n`-step sum has underlying value `min b (a + n • δ)`. -/
@[simp]
theorem coe_addNSMul {α : Type*} [AddCommGroup α] [LinearOrder α]
    [IsOrderedAddMonoid α] {a b δ : α} (h : a ≤ b) (hδ : 0 ≤ δ) (n : ℕ) :
    (addNSMul h δ n : α) = min b (a + n • δ) := by
  rw [addNSMul, coe_projIcc, max_eq_right]
  exact le_min h (le_add_of_nonneg_right (nsmul_nonneg hδ n))

/-- The clamped `n`-step sum depends continuously on the step size. -/
@[fun_prop]
theorem continuous_addNSMul {α : Type*} [AddCommGroup α] [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [ContinuousAdd α]
    {a b : α} (h : a ≤ b) (n : ℕ) :
    Continuous fun δ : α ↦ addNSMul h δ n := by
  unfold addNSMul
  exact continuous_projIcc.comp (continuous_const.add (continuous_id.nsmul n))

/-- A step size continuous and positive at a point makes all sufficiently large clamped sums
equal the right endpoint throughout some neighborhood. -/
theorem exists_eventually_addNSMul_eq_right {α X : Type*} [AddCommGroup α] [LinearOrder α]
    [IsOrderedAddMonoid α] [Archimedean α] [TopologicalSpace α] [OrderTopology α]
    [TopologicalSpace X] {a b : α} (h : a ≤ b) {δ : X → α} {x : X}
    (hδ : ContinuousAt δ x) (hpos : 0 < δ x) :
    ∃ N : ℕ, ∀ᶠ y in 𝓝 x, ∀ n ≥ N, addNSMul h (δ y) n = b := by
  have hlower : ∃ c > (0 : α), ∀ᶠ y in 𝓝 x, c ≤ δ y := by
    by_cases hbetween : ∃ c : α, 0 < c ∧ c < δ x
    · obtain ⟨c, hc, hcx⟩ := hbetween
      exact ⟨c, hc, (hδ.eventually (Ioi_mem_nhds hcx)).mono fun _ hy ↦ hy.le⟩
    · refine ⟨δ x, hpos, ?_⟩
      filter_upwards [hδ.eventually (Ioi_mem_nhds hpos)] with y hy
      exact le_of_not_gt fun hlt ↦ hbetween ⟨δ y, hy, hlt⟩
  obtain ⟨c, hc, hnear⟩ := hlower
  obtain ⟨N, hN⟩ := Archimedean.arch (b - a) hc
  refine ⟨N, ?_⟩
  filter_upwards [hnear] with y hy n hn
  have hbound : b - a ≤ n • δ y :=
    hN.trans ((nsmul_le_nsmul_left hc.le hn).trans (nsmul_le_nsmul_right hy n))
  rw [coe_addNSMul h (hc.le.trans hy), min_eq_left]
  exact sub_le_iff_le_add'.mp hbound

end Set.Icc

end
end Qatlib.Foundations.CbmdAnalysis.Residue
