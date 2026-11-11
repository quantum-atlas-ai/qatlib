/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.QLowerBound00.MainResults.AdversaryCore

/-!
# Coherent input labels in the adversary method

This module tracks input-dependent amplitudes through `phaseQuery` and `rhoEntry`, and proves
invariance of overlaps under a common workspace unitary. The normalized distance identity
`dist_sq_eq` and the complementary mass bound `error_mass_le` support the interpretation of
adversary progress. See [Ambainis2002] for the paper's setting.

## Main statements

* `phaseQuery_jointState`: A phase query commutes with multiplication by an amplitude depending
  only on the input label.
* `error_mass_le`: For a normalized vector, mass at least `1-ε` on `P` implies mass at most `ε`
  on its complement.

## References

* [Ambainis, 2002][Ambainis2002]
-/

set_option warningAsError false

namespace Qatlib.Papers.QLowerBound00.CoherentLabel

open scoped BigOperators
open Finset

open Qatlib.Papers.QLowerBound00.MainResults.AdversaryCore

variable {ι : Type*}

/-- A phase query commutes with multiplication by an amplitude depending only on the input
label. See [Ambainis2002]. -/
theorem phaseQuery_jointState {n : ℕ} (i : Fin n)
    (α : Input n → ℂ) (ψ : ι → Input n → ℂ) :
    phaseQuery i (fun iw z => α z * ψ iw z) =
      fun iw z => α z * phaseQuery i ψ iw z := by
  funext iw z
  unfold phaseQuery
  by_cases h : z i
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]

/-- Weighting each input column by `α` multiplies `rhoEntry` at `x, y` by `star (α x) * α y`.
See [Ambainis2002]. -/
theorem rhoEntry_jointState {ι : Type*} [Fintype ι] {n : ℕ}
    (α : Input n → ℂ) (ψ : ι → Input n → ℂ) (x y : Input n) :
    rhoEntry (fun iw z => α z * ψ iw z) x y =
      star (α x) * α y * rhoEntry ψ x y := by
  unfold rhoEntry
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun iw _ => ?_)
  rw [star_mul]
  ring

/-- Applying the same matrix with orthonormal columns to every workspace column preserves each
`rhoEntry`. See [Ambainis2002]. -/
theorem rhoEntry_workspace_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}
    (U : ι → ι → ℂ)
    (hU : ∀ a b : ι, (∑ c, star (U c a) * U c b) = if a = b then 1 else 0)
    (ψ : ι → α → ℂ) (x y : α) :
    rhoEntry (fun iw z => ∑ j, U iw j * ψ j z) x y = rhoEntry ψ x y := by
  classical
  unfold rhoEntry
  change (∑ iw, star (∑ j, U iw j * ψ j x) * (∑ k, U iw k * ψ k y)) =
    ∑ j, star (ψ j x) * ψ j y
  have hstar : ∀ iw, star (∑ j, U iw j * ψ j x) =
      ∑ j, star (U iw j) * star (ψ j x) := by
    intro iw
    rw [star_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [star_mul, mul_comm])
  have hexp : ∀ iw, (∑ j, star (U iw j) * star (ψ j x)) *
      (∑ k, U iw k * ψ k y) =
      ∑ j, ∑ k, star (U iw j) * star (ψ j x) * (U iw k * ψ k y) := by
    intro iw
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
  simp only [hstar, hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  have hinner : ∀ k, (∑ iw, star (U iw j) * star (ψ j x) * (U iw k * ψ k y)) =
      (if j = k then 1 else 0) * (star (ψ j x) * ψ k y) := by
    intro k
    have hfac : ∀ iw, star (U iw j) * star (ψ j x) * (U iw k * ψ k y) =
        (star (U iw j) * U iw k) * (star (ψ j x) * ψ k y) := by
      intro iw; ring
    rw [Finset.sum_congr rfl (fun iw _ => hfac iw), ← Finset.sum_mul, hU j k]
  rw [Finset.sum_congr rfl (fun k _ => hinner k)]
  have hite : ∀ k, (if j = k then (1 : ℂ) else 0) * (star (ψ j x) * ψ k y) =
      if j = k then star (ψ j x) * ψ k y else 0 := by
    intro k; by_cases h : j = k <;> simp [h]
  rw [Finset.sum_congr rfl (fun k _ => hite k)]
  have hsingle : (∑ k, (if j = k then star (ψ j x) * ψ k y else 0)) =
      star (ψ j x) * ψ j y := by
    have h1 := Finset.sum_eq_single (s := (univ : Finset ι))
      (f := fun k => if j = k then star (ψ j x) * ψ k y else 0) j
      (fun b _ hb => by
        show (if j = b then star (ψ j x) * ψ b y else 0) = 0
        rw [if_neg (fun h => hb h.symm)])
      (fun h => absurd (Finset.mem_univ j) h)
    rw [h1]; simp
  exact hsingle

/-- For two vectors of squared norm one, their squared distance is `2 - 2` times the real part
of their inner product. See [Ambainis2002]. -/
theorem dist_sq_eq {ι : Type*} [Fintype ι] (u v : ι → ℂ)
    (hu : ∑ iw, ‖u iw‖ ^ 2 = 1) (hv : ∑ iw, ‖v iw‖ ^ 2 = 1) :
    ∑ iw, ‖u iw - v iw‖ ^ 2 =
      2 - 2 * (∑ iw, (star (u iw) * v iw).re) := by
  have hterm : ∀ iw, ‖u iw - v iw‖ ^ 2 =
      ‖u iw‖ ^ 2 + ‖v iw‖ ^ 2 - 2 * (star (u iw) * v iw).re := by
    intro iw
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  calc ∑ iw, ‖u iw - v iw‖ ^ 2
      = ∑ iw, (‖u iw‖ ^ 2 + ‖v iw‖ ^ 2 - 2 * (star (u iw) * v iw).re) :=
          Finset.sum_congr rfl (fun iw _ => hterm iw)
    _ = (∑ iw, ‖u iw‖ ^ 2) + (∑ iw, ‖v iw‖ ^ 2) -
          2 * (∑ iw, (star (u iw) * v iw).re) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 2 - 2 * (∑ iw, (star (u iw) * v iw).re) := by rw [hu, hv]; ring

/-- For a normalized vector, mass at least `1-ε` on `P` implies mass at most `ε` on its
complement. See [Ambainis2002]. -/
theorem error_mass_le {ι : Type*} [Fintype ι] (w : ι → ℂ) (P : ι → Prop) [DecidablePred P] (ε : ℝ)
    (hn : ∑ iw, ‖w iw‖ ^ 2 = 1)
    (hok : 1 - ε ≤ ∑ iw ∈ (Finset.univ.filter P), ‖w iw‖ ^ 2) :
    ∑ iw ∈ (Finset.univ.filter (fun iw => ¬ P iw)), ‖w iw‖ ^ 2 ≤ ε := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset ι) P
    (fun iw => ‖w iw‖ ^ 2)
  rw [hn] at hsplit
  linarith

end Qatlib.Papers.QLowerBound00.CoherentLabel
