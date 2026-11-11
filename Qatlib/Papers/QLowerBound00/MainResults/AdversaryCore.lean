/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
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
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
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
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Disjoint
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
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Progress estimates for quantum adversary lower bounds

This module defines Boolean inputs, phase queries, Gram entries `rhoEntry`, and the
relation-weighted progress `progress`. Initial-state normalization, output-distinguishability
bounds, and telescoping estimates provide the ingredients for adversary lower bounds.

The query estimates `progress_step_le` and `progress_step_le_lmax` bound a single progress
change using uniform mismatch degrees or a bound on their local products. See [Ambainis2002] for
the paper's setting.

## Main statements

* `Input`: The type of length-`n` Boolean inputs.
* `progress_step_le_lmax`: Under the stated local mismatch-degree product bound and total-mass
  bound, the sum of Gram-entry changes from one phase query is at most `sqrt lmax`.

## References

* [Ambainis, 2002][Ambainis2002]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QLowerBound00.MainResults.AdversaryCore

/-- The type of length-`n` Boolean inputs. -/
abbrev Input (n : ℕ) := Fin n → Bool

/-- The type of ordered pairs of length-`n` Boolean inputs. -/
abbrev InputPair (n : ℕ) := Input n × Input n

/-- For error probabilities bounded by `ε ∈ [0, 1/2]`, the sum of the two binary overlap terms
is at most `2 * sqrt (ε*(1-ε))`. -/
theorem hellinger_pair_le {ε ε₁ ε₂ : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (h10 : 0 ≤ ε₁) (h20 : 0 ≤ ε₂)
    (h1 : ε₁ ≤ ε) (h2 : ε₂ ≤ ε) :
    Real.sqrt ((1 - ε₁) * ε₂) + Real.sqrt (ε₁ * (1 - ε₂)) ≤
      2 * Real.sqrt (ε * (1 - ε)) := by
  have hε1 : ε ≤ 1 := by linarith
  have h1' : ε₁ ≤ 1 := h1.trans hε1
  have h2' : ε₂ ≤ 1 := h2.trans hε1
  have hne1 : 0 ≤ 1 - ε₁ := by linarith
  have hne2 : 0 ≤ 1 - ε₂ := by linarith
  have hneε : 0 ≤ 1 - ε := by linarith
  have hs1 : Real.sqrt ε₁ ≤ 1 := by
    simpa using Real.sqrt_le_sqrt h1'
  have hs2 : Real.sqrt ε₂ ≤ 1 := by
    simpa using Real.sqrt_le_sqrt h2'
  have hsε1 : Real.sqrt ε ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hε1
  set a : ℝ := Real.arcsin (Real.sqrt ε₁) with ha
  set b : ℝ := Real.arcsin (Real.sqrt ε₂) with hb
  set g : ℝ := Real.arcsin (Real.sqrt ε) with hg
  have ha0 : 0 ≤ a := by
    rw [ha]; exact Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _)
  have hb0 : 0 ≤ b := by
    rw [hb]; exact Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _)
  have hle_ag : a ≤ g := by
    rw [ha, hg]; exact Real.arcsin_le_arcsin (Real.sqrt_le_sqrt h1)
  have hle_bg : b ≤ g := by
    rw [hb, hg]; exact Real.arcsin_le_arcsin (Real.sqrt_le_sqrt h2)
  have hsum : a + b ≤ 2 * g := by linarith
  have hg_le : g ≤ Real.pi / 4 := by
    have hmain : Real.arcsin (Real.sqrt (1 / 2)) = Real.pi / 4 := by
      refine Real.arcsin_eq_of_sin_eq ?_ ?_
      · have h4 : Real.sqrt 4 = 2 := by
          rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]
          norm_num
        have hhalf : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
          rw [show (1 / 2 : ℝ) = 2 / 4 by norm_num, Real.sqrt_div (by norm_num)]
          rw [h4]
        rw [hhalf, Real.sin_pi_div_four]
      · constructor <;> [linarith [Real.pi_pos]; linarith [Real.pi_pos]]
    calc g = Real.arcsin (Real.sqrt ε) := by rw [hg]
      _ ≤ Real.arcsin (Real.sqrt (1 / 2)) := Real.arcsin_le_arcsin (Real.sqrt_le_sqrt hε)
      _ = Real.pi / 4 := hmain
  have h2g : 2 * g ≤ Real.pi / 2 := by linarith
  have hsin_le : Real.sin (a + b) ≤ Real.sin (2 * g) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h2g hsum
  have hsin_a : Real.sin a = Real.sqrt ε₁ := by
    rw [ha, Real.sin_arcsin (by have := Real.sqrt_nonneg ε₁; linarith) hs1]
  have hsin_b : Real.sin b = Real.sqrt ε₂ := by
    rw [hb, Real.sin_arcsin (by have := Real.sqrt_nonneg ε₂; linarith) hs2]
  have hsin_g : Real.sin g = Real.sqrt ε := by
    rw [hg, Real.sin_arcsin (by have := Real.sqrt_nonneg ε; linarith) hsε1]
  have hcos_a : Real.cos a = Real.sqrt (1 - ε₁) := by
    rw [ha, Real.cos_arcsin, Real.sq_sqrt h10]
  have hcos_b : Real.cos b = Real.sqrt (1 - ε₂) := by
    rw [hb, Real.cos_arcsin, Real.sq_sqrt h20]
  have hcos_g : Real.cos g = Real.sqrt (1 - ε) := by
    rw [hg, Real.cos_arcsin, Real.sq_sqrt hε0]
  have hkey : Real.sqrt ((1 - ε₁) * ε₂) + Real.sqrt (ε₁ * (1 - ε₂)) =
      Real.sin (a + b) := by
    rw [Real.sqrt_mul hne1 ε₂, Real.sqrt_mul h10 (1 - ε₂)]
    rw [← hcos_a, ← hsin_b, ← hsin_a, ← hcos_b, Real.sin_add]
    ring
  rw [hkey]
  calc Real.sin (a + b) ≤ Real.sin (2 * g) := hsin_le
    _ = 2 * Real.sqrt (ε * (1 - ε)) := by
      have hmul : Real.sqrt ε * Real.sqrt (1 - ε) = Real.sqrt (ε * (1 - ε)) :=
        (Real.sqrt_mul hε0 (1 - ε)).symm
      rw [Real.sin_two_mul, hsin_g, hcos_g, mul_assoc, hmul]

/-- For normalized vectors separated by the stated output-error bounds, the weighted
inner-product norm is at most `2 * sqrt (ε*(1-ε)) * ‖αx‖ * ‖αy‖`. -/
theorem lemma1_density_entry
    {ZW : Type*} [Fintype ZW] [DecidableEq ZW] {β : Type*} [DecidableEq β]
    (ans : ZW → β) (fx : β) (a b : ZW → ℂ) (αx αy : ℂ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (ha : (∑ z, ‖a z‖ ^ 2) = 1) (hb : (∑ z, ‖b z‖ ^ 2) = 1)
    (h1 : (∑ z ∈ univ.filter (fun z => ans z ≠ fx), ‖a z‖ ^ 2) ≤ ε)
    (h2 : (∑ z ∈ univ.filter (fun z => ans z = fx), ‖b z‖ ^ 2) ≤ ε) :
    ‖αx * αy * (∑ z, star (a z) * b z)‖ ≤
      2 * Real.sqrt (ε * (1 - ε)) * ‖αx‖ * ‖αy‖ := by

  set sE : Finset ZW := univ.filter (fun z => ans z = fx) with hsE
  set sN : Finset ZW := univ.filter (fun z => ¬ (ans z = fx)) with hsN
  have hfilter : sN = univ.filter (fun z => ans z ≠ fx) := rfl

  set ε₁ : ℝ := ∑ z ∈ sN, ‖a z‖ ^ 2 with hε₁def
  set ε₂ : ℝ := ∑ z ∈ sE, ‖b z‖ ^ 2 with hε₂def
  have hε1eq : ε₁ = ∑ z ∈ univ.filter (fun z => ans z ≠ fx), ‖a z‖ ^ 2 := by
    rw [hε₁def, hfilter]
  have hε2eq : ε₂ = ∑ z ∈ univ.filter (fun z => ans z = fx), ‖b z‖ ^ 2 := by
    rw [hε₂def, hsE]
  have hε1nonneg : 0 ≤ ε₁ := by
    rw [hε₁def]; exact Finset.sum_nonneg (fun z _ => by positivity)
  have hε2nonneg : 0 ≤ ε₂ := by
    rw [hε₂def]; exact Finset.sum_nonneg (fun z _ => by positivity)
  have hε1le : ε₁ ≤ ε := by rw [hε1eq]; exact h1
  have hε2le : ε₂ ≤ ε := by rw [hε2eq]; exact h2
  have hne1 : 0 ≤ 1 - ε₁ := by
    have : ε₁ ≤ 1 / 2 := hε1le.trans hε
    linarith
  have hne2 : 0 ≤ 1 - ε₂ := by
    have : ε₂ ≤ 1 / 2 := hε2le.trans hε
    linarith

  have hsplit_a : (∑ z ∈ sE, ‖a z‖ ^ 2) + (∑ z ∈ sN, ‖a z‖ ^ 2) = 1 := by
    have := Finset.sum_filter_add_sum_filter_not (s := (univ : Finset ZW))
      (p := fun z => ans z = fx) (f := fun z => ‖a z‖ ^ 2)
    rw [hsE, hsN]
    exact this.trans ha
  have hsplit_b : (∑ z ∈ sE, ‖b z‖ ^ 2) + (∑ z ∈ sN, ‖b z‖ ^ 2) = 1 := by
    have := Finset.sum_filter_add_sum_filter_not (s := (univ : Finset ZW))
      (p := fun z => ans z = fx) (f := fun z => ‖b z‖ ^ 2)
    rw [hsE, hsN]
    exact this.trans hb
  have hEa : (∑ z ∈ sE, ‖a z‖ ^ 2) = 1 - ε₁ := by
    rw [hε₁def]; linarith
  have hNb : (∑ z ∈ sN, ‖b z‖ ^ 2) = 1 - ε₂ := by
    rw [hε₂def]; linarith

  have hnorm : ‖∑ z, star (a z) * b z‖ ≤ ∑ z, ‖a z‖ * ‖b z‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl (fun z _ => by rw [norm_mul, norm_star])
  have hsplit_norm : (∑ z, ‖a z‖ * ‖b z‖) =
      (∑ z ∈ sE, ‖a z‖ * ‖b z‖) + (∑ z ∈ sN, ‖a z‖ * ‖b z‖) := by
    have := Finset.sum_filter_add_sum_filter_not (s := (univ : Finset ZW))
      (p := fun z => ans z = fx) (f := fun z => ‖a z‖ * ‖b z‖)
    rw [hsE, hsN]
    exact this.symm

  have hCS_E : (∑ z ∈ sE, ‖a z‖ * ‖b z‖) ≤
      Real.sqrt (∑ z ∈ sE, ‖a z‖ ^ 2) * Real.sqrt (∑ z ∈ sE, ‖b z‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hCS_N : (∑ z ∈ sN, ‖a z‖ * ‖b z‖) ≤
      Real.sqrt (∑ z ∈ sN, ‖a z‖ ^ 2) * Real.sqrt (∑ z ∈ sN, ‖b z‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hEeq : Real.sqrt (∑ z ∈ sE, ‖a z‖ ^ 2) * Real.sqrt (∑ z ∈ sE, ‖b z‖ ^ 2)
      = Real.sqrt ((1 - ε₁) * ε₂) := by
    rw [hEa, hε₂def]
    exact (Real.sqrt_mul hne1 ε₂).symm
  have hNeq : Real.sqrt (∑ z ∈ sN, ‖a z‖ ^ 2) * Real.sqrt (∑ z ∈ sN, ‖b z‖ ^ 2)
      = Real.sqrt (ε₁ * (1 - ε₂)) := by
    rw [hε₁def, hNb]
    exact (Real.sqrt_mul hε1nonneg (1 - ε₂)).symm
  have hmain : ‖∑ z, star (a z) * b z‖ ≤
      Real.sqrt ((1 - ε₁) * ε₂) + Real.sqrt (ε₁ * (1 - ε₂)) := by
    calc ‖∑ z, star (a z) * b z‖ ≤ ∑ z, ‖a z‖ * ‖b z‖ := hnorm
      _ = (∑ z ∈ sE, ‖a z‖ * ‖b z‖) + (∑ z ∈ sN, ‖a z‖ * ‖b z‖) := hsplit_norm
      _ ≤ Real.sqrt (∑ z ∈ sE, ‖a z‖ ^ 2) * Real.sqrt (∑ z ∈ sE, ‖b z‖ ^ 2)
            + Real.sqrt (∑ z ∈ sN, ‖a z‖ ^ 2) * Real.sqrt (∑ z ∈ sN, ‖b z‖ ^ 2) :=
          add_le_add hCS_E hCS_N
      _ = Real.sqrt ((1 - ε₁) * ε₂) + Real.sqrt (ε₁ * (1 - ε₂)) := by rw [hEeq, hNeq]
  have hhell := hellinger_pair_le hε0 hε hε1nonneg hε2nonneg hε1le hε2le
  have hcore : ‖∑ z, star (a z) * b z‖ ≤ 2 * Real.sqrt (ε * (1 - ε)) := hmain.trans hhell
  calc ‖αx * αy * (∑ z, star (a z) * b z)‖
      = ‖αx‖ * ‖αy‖ * ‖∑ z, star (a z) * b z‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖αx‖ * ‖αy‖ * (2 * Real.sqrt (ε * (1 - ε))) := by
        have : 0 ≤ ‖αx‖ * ‖αy‖ := by positivity
        exact mul_le_mul_of_nonneg_left hcore this
    _ = 2 * Real.sqrt (ε * (1 - ε)) * ‖αx‖ * ‖αy‖ := by ring

/-- The inner product of the workspace columns of `ψ` indexed by `x` and `y`. -/
def rhoEntry {ι : Type*} [Fintype ι] {α : Type*} (ψ : ι → α → ℂ)
    (x y : α) : ℂ :=
  ∑ iw, star (ψ iw x) * ψ iw y

/-- The phase query that negates amplitudes when input bit `i` is true. -/
def phaseQuery {ι : Type*} {n : ℕ} (i : Fin n) (ψ : ι → Input n → ℂ) :
    ι → Input n → ℂ :=
  fun iw x => if x i then - ψ iw x else ψ iw x

/-- The sum of the norms of `ρ x y` over pairs in the relation `R`. -/
def progress {α : Type*} (R : Finset (α × α))
    (ρ : α → α → ℂ) : ℝ :=
  ∑ p ∈ R, ‖ρ p.1 p.2‖

/-- The decrease in relation progress is at most the sum of the norms of the entrywise
differences. -/
theorem progress_sub_le {α : Type*} (R : Finset (α × α))
    (ρ σ : α → α → ℂ) :
    progress R ρ - progress R σ ≤
      ∑ p ∈ R, ‖ρ p.1 p.2 - σ p.1 p.2‖ := by
  unfold progress
  have h : (∑ p ∈ R, ‖ρ p.1 p.2‖) ≤
      ∑ p ∈ R, (‖σ p.1 p.2‖ + ‖ρ p.1 p.2 - σ p.1 p.2‖) := by
    refine Finset.sum_le_sum (fun p _ => ?_)
    have := norm_add_le (σ p.1 p.2) (ρ p.1 p.2 - σ p.1 p.2)
    rwa [add_sub_cancel] at this
  rw [Finset.sum_add_distrib] at h
  linarith

/-- If each of `T` successive decreases is at most `B`, the total decrease is at most `T*B`. -/
theorem telescope_lower {S : ℕ → ℝ} {T : ℕ} {B : ℝ}
    (h : ∀ k < T, S k - S (k + 1) ≤ B) : S 0 - S T ≤ (T : ℝ) * B := by
  induction T with
  | zero => simp
  | succ T ih =>
    have h1 : ∀ k < T, S k - S (k + 1) ≤ B := fun k hk => h k (Nat.lt_succ_of_lt hk)
    have ih' := ih h1
    have hlast := h T (Nat.lt_succ_self T)
    have hcast : ((T + 1 : ℕ) : ℝ) = (T : ℝ) + 1 := by push_cast; ring
    have he : S 0 - S (T + 1) = (S 0 - S T) + (S T - S (T + 1)) := by ring
    rw [he, hcast]
    nlinarith

/-- The real initial amplitude, equal to `1 / sqrt (2*|X|)` on `X`, `1 / sqrt (2*|Y|)` on `Y`
outside `X`, and zero elsewhere. -/
noncomputable def initialAmplitude {α : Type*} [DecidableEq α] (X Y : Finset α)
    (x : α) : ℝ :=
  if x ∈ X then (Real.sqrt (2 * (X.card : ℝ)))⁻¹
  else if x ∈ Y then (Real.sqrt (2 * (Y.card : ℝ)))⁻¹ else 0

/-- The complex-valued initial amplitude obtained from `initialAmplitude`. -/
noncomputable def initialState {α : Type*} [DecidableEq α] (X Y : Finset α)
    (x : α) : ℂ :=
  (initialAmplitude X Y x : ℂ)

/-- For disjoint nonempty `X, Y` and `R ⊆ X × Y`, the initial progress is `|R| / (2 * sqrt |X| *
sqrt |Y|)`. -/
theorem progress_initial {α : Type*} [DecidableEq α] (X Y : Finset α) (R : Finset (α × α))
    (hdisj : Disjoint X Y) (hRsub : ∀ p ∈ R, p.1 ∈ X ∧ p.2 ∈ Y)
    (hX : 0 < X.card) (hY : 0 < Y.card) :
    progress R (fun x y => initialState X Y x * initialState X Y y) =
      (R.card : ℝ) * (2 * Real.sqrt (X.card : ℝ) * Real.sqrt (Y.card : ℝ))⁻¹ := by
  unfold progress
  have hsqrtX : 0 < Real.sqrt (X.card : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hX)
  have hsqrtY : 0 < Real.sqrt (Y.card : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hY)
  have hs2X : Real.sqrt (2 * (X.card : ℝ)) = Real.sqrt 2 * Real.sqrt (X.card : ℝ) :=
    Real.sqrt_mul (by norm_num) _
  have hs2Y : Real.sqrt (2 * (Y.card : ℝ)) = Real.sqrt 2 * Real.sqrt (Y.card : ℝ) :=
    Real.sqrt_mul (by norm_num) _
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    simpa [sq] using this
  have hprod : Real.sqrt (2 * (X.card : ℝ)) * Real.sqrt (2 * (Y.card : ℝ)) =
      2 * Real.sqrt (X.card : ℝ) * Real.sqrt (Y.card : ℝ) := by
    rw [hs2X, hs2Y]
    calc Real.sqrt 2 * Real.sqrt (X.card : ℝ) * (Real.sqrt 2 * Real.sqrt (Y.card : ℝ))
        = (Real.sqrt 2 * Real.sqrt 2) * (Real.sqrt (X.card : ℝ) * Real.sqrt (Y.card : ℝ)) := by
          ring
      _ = 2 * (Real.sqrt (X.card : ℝ) * Real.sqrt (Y.card : ℝ)) := by rw [hs2]
      _ = 2 * Real.sqrt (X.card : ℝ) * Real.sqrt (Y.card : ℝ) := by ring
  have hconst : ∀ p ∈ R,
      ‖initialState X Y p.1 * initialState X Y p.2‖ =
        (2 * Real.sqrt (X.card : ℝ) * Real.sqrt (Y.card : ℝ))⁻¹ := by
    intro p hp
    obtain ⟨hxX, hyY⟩ := hRsub p hp
    have hxY : p.1 ∉ Y := fun h => (Finset.disjoint_left.mp hdisj) hxX h
    have hay : initialAmplitude X Y p.2 = (Real.sqrt (2 * (Y.card : ℝ)))⁻¹ := by
      rw [initialAmplitude, if_neg (fun h => (Finset.disjoint_left.mp hdisj) h hyY), if_pos hyY]
    have hax : initialAmplitude X Y p.1 = (Real.sqrt (2 * (X.card : ℝ)))⁻¹ := by
      rw [initialAmplitude, if_pos hxX]
    have hspX : 0 < Real.sqrt (2 * (X.card : ℝ)) := Real.sqrt_pos.mpr (by positivity)
    have hspY : 0 < Real.sqrt (2 * (Y.card : ℝ)) := Real.sqrt_pos.mpr (by positivity)
    rw [initialState, initialState, hax, hay, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hspX),
      abs_of_pos (inv_pos.mpr hspY), ← mul_inv, hprod]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]

/-- Lower bounds `m, m'` on the two relation degrees imply `sqrt (m*m'*|X|*|Y|) ≤ |R|`. -/
theorem card_relation_ge {α : Type*} [DecidableEq α] (X Y : Finset α)
    (R : Finset (α × α))
    (m m' : ℕ)
    (hRsub : ∀ p ∈ R, p.1 ∈ X ∧ p.2 ∈ Y)
    (hm : ∀ x ∈ X, m ≤ (R.filter (fun p => p.1 = x)).card)
    (hm' : ∀ y ∈ Y, m' ≤ (R.filter (fun p => p.2 = y)).card) :
    Real.sqrt ((m : ℝ) * (m' : ℝ) * (X.card : ℝ) * (Y.card : ℝ)) ≤ (R.card : ℝ) := by
  have hfibX : R.card = ∑ x ∈ X, (R.filter (fun p => p.1 = x)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (t := X) (fun p hp => (hRsub p hp).1)]
  have hfibY : R.card = ∑ y ∈ Y, (R.filter (fun p => p.2 = y)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (t := Y) (fun p hp => (hRsub p hp).2)]
  have hXle : (m : ℝ) * (X.card : ℝ) ≤ (R.card : ℝ) := by
    have hsum : (∑ x ∈ X, ((R.filter (fun p => p.1 = x)).card : ℝ)) ≤ (R.card : ℝ) := by
      rw [hfibX]; push_cast; rfl
    calc (m : ℝ) * (X.card : ℝ) = ∑ _x ∈ X, (m : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ X, ((R.filter (fun p => p.1 = x)).card : ℝ) := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          exact_mod_cast hm x hx
      _ ≤ (R.card : ℝ) := hsum
  have hYle : (m' : ℝ) * (Y.card : ℝ) ≤ (R.card : ℝ) := by
    have hsum : (∑ y ∈ Y, ((R.filter (fun p => p.2 = y)).card : ℝ)) ≤ (R.card : ℝ) := by
      rw [hfibY]; push_cast; rfl
    calc (m' : ℝ) * (Y.card : ℝ) = ∑ _y ∈ Y, (m' : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ y ∈ Y, ((R.filter (fun p => p.2 = y)).card : ℝ) := by
          refine Finset.sum_le_sum (fun y hy => ?_)
          exact_mod_cast hm' y hy
      _ ≤ (R.card : ℝ) := hsum
  have hprod : (m : ℝ) * (m' : ℝ) * (X.card : ℝ) * (Y.card : ℝ) ≤
      (R.card : ℝ) * (R.card : ℝ) := by
    have h := mul_le_mul hXle hYle (by positivity) (by positivity)
    calc (m : ℝ) * (m' : ℝ) * (X.card : ℝ) * (Y.card : ℝ)
        = ((m : ℝ) * (X.card : ℝ)) * ((m' : ℝ) * (Y.card : ℝ)) := by ring
      _ ≤ (R.card : ℝ) * (R.card : ℝ) := h
  have hs := Real.sqrt_le_sqrt hprod
  rwa [Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ (R.card : ℝ))] at hs

/-- A uniform pairwise final-overlap bound gives the same factor `2 * sqrt (ε*(1-ε))` as a bound
on final progress relative to initial progress. -/
theorem final_progress_le {α : Type*} (R : Finset (α × α)) (ε : ℝ)
    (aT a0 : α → α → ℂ)
    (hpair : ∀ p ∈ R,
      ‖aT p.1 p.2‖ ≤ 2 * Real.sqrt (ε * (1 - ε)) * ‖a0 p.1 p.2‖) :
    progress R aT ≤ 2 * Real.sqrt (ε * (1 - ε)) * progress R a0 := by
  unfold progress
  calc (∑ p ∈ R, ‖aT p.1 p.2‖) ≤
      ∑ p ∈ R, (2 * Real.sqrt (ε * (1 - ε)) * ‖a0 p.1 p.2‖) := Finset.sum_le_sum hpair
    _ = 2 * Real.sqrt (ε * (1 - ε)) * ∑ p ∈ R, ‖a0 p.1 p.2‖ := by
        rw [Finset.mul_sum]

/-- The stated one-step, initial, and final progress bounds imply `(1 - 2*sqrt (ε*(1-ε))) * S0 ≤
T*B`. -/
theorem adversary_lower_bound {S : ℕ → ℝ} {T : ℕ} {B S0 ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hstep : ∀ k < T, S k - S (k + 1) ≤ B)
    (h0 : S0 ≤ S 0)
    (hT : S T ≤ 2 * Real.sqrt (ε * (1 - ε)) * S 0) :
    (1 - 2 * Real.sqrt (ε * (1 - ε))) * S0 ≤ (T : ℝ) * B := by
  have htel := telescope_lower hstep
  have hc0 : 0 ≤ 2 * Real.sqrt (ε * (1 - ε)) := by positivity
  have hc1 : 2 * Real.sqrt (ε * (1 - ε)) ≤ 1 := by
    have h4 : ε * (1 - ε) ≤ 1 / 4 := by nlinarith
    have hs := Real.sqrt_le_sqrt h4
    have hhalf : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    nlinarith [hs, hhalf]
  nlinarith [htel, h0, hT, hc0, hc1]

/-- Factoring each input column by a real input amplitude factors its Gram entry by the product
of the two amplitudes. -/
theorem rhoEntry_eq_of_factor {ι : Type*} [Fintype ι] [DecidableEq ι] {αT : Type*}
    {ψ : ι → αT → ℂ} {a : ι → αT → ℂ} {α : αT → ℝ}
    (h : ∀ iw x, ψ iw x = (α x : ℂ) * a iw x) (x y : αT) :
    rhoEntry ψ x y = (α x : ℂ) * (α y : ℂ) * ∑ iw, star (a iw x) * a iw y := by
  unfold rhoEntry
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun iw _ => ?_)
  have hs : star ((α x : ℝ) : ℂ) = ((α x : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [h iw x, h iw y, star_mul, hs]
  ring

/-- For normalized vectors with the stated opposite Boolean output-error bounds, the weighted
overlap is at most `2 * sqrt (ε*(1-ε))` times the two amplitude norms. -/
theorem lemma1_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ans : ι → Bool) (fx : Bool) (a b : ι → ℂ) (αx αy : ℝ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (ha : (∑ iw, ‖a iw‖ ^ 2) = 1) (hb : (∑ iw, ‖b iw‖ ^ 2) = 1)
    (h1 : (∑ iw ∈ univ.filter (fun iw => ans iw ≠ fx), ‖a iw‖ ^ 2) ≤ ε)
    (h2 : (∑ iw ∈ univ.filter (fun iw => ans iw = fx), ‖b iw‖ ^ 2) ≤ ε) :
    ‖(αx : ℂ) * (αy : ℂ) * (∑ iw, star (a iw) * b iw)‖ ≤
      2 * Real.sqrt (ε * (1 - ε)) * ‖(αx : ℂ)‖ * ‖(αy : ℂ)‖ :=
  lemma1_density_entry (ZW := ι) ans fx a b (αx : ℂ) (αy : ℂ) ε hε0 hε ha hb h1 h2

/-- The total squared workspace amplitude in the input column indexed by `x`. -/
def mass {ι : Type*} [Fintype ι] {α : Type*} (ψ : ι → α → ℂ) (x : α) : ℝ :=
  ∑ iw, ‖ψ iw x‖ ^ 2

/-- A phase query preserves a Gram entry when the queried bits agree and negates it when they
differ. -/
theorem rhoEntry_phaseQuery {ι : Type*} [Fintype ι] {n : ℕ}
    (i : Fin n) (ψ : ι → Input n → ℂ) (x y : Input n) :
    rhoEntry (phaseQuery i ψ) x y =
      if x i = y i then rhoEntry ψ x y else -rhoEntry ψ x y := by
  unfold rhoEntry phaseQuery
  by_cases hxy : x i = y i
  · rw [if_pos hxy]
    refine Finset.sum_congr rfl (fun iw _ => ?_)
    by_cases hx : x i <;> by_cases hy : y i <;> simp_all
  · rw [if_neg hxy, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun iw _ => ?_)
    by_cases hx : x i <;> by_cases hy : y i <;> simp_all

/-- The norm of a Gram entry is at most the product of the square roots of the two column
masses. -/
theorem rhoEntry_norm_le {ι : Type*} [Fintype ι] {α : Type*}
    (ψ : ι → α → ℂ) (x y : α) :
    ‖rhoEntry ψ x y‖ ≤
      Real.sqrt (∑ iw, ‖ψ iw x‖ ^ 2) * Real.sqrt (∑ iw, ‖ψ iw y‖ ^ 2) := by
  unfold rhoEntry
  calc ‖∑ iw, star (ψ iw x) * ψ iw y‖
      ≤ ∑ iw, ‖star (ψ iw x) * ψ iw y‖ := norm_sum_le _ _
    _ = ∑ iw, ‖ψ iw x‖ * ‖ψ iw y‖ := by simp [norm_mul]
    _ ≤ Real.sqrt (∑ iw, ‖ψ iw x‖ ^ 2) * Real.sqrt (∑ iw, ‖ψ iw y‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- For nonnegative `A, B, α, β` with `α*β = 1`, the weighted arithmetic-geometric mean bound is
`2*sqrt A*sqrt B ≤ α*A + β*B`. -/
theorem amgm_two {A B α β : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α * β = 1) :
    2 * (Real.sqrt A * Real.sqrt B) ≤ α * A + β * B := by
  have hαA : (Real.sqrt α * Real.sqrt A) ^ 2 = α * A := by
    rw [mul_pow, Real.sq_sqrt hα, Real.sq_sqrt hA]
  have hβB : (Real.sqrt β * Real.sqrt B) ^ 2 = β * B := by
    rw [mul_pow, Real.sq_sqrt hβ, Real.sq_sqrt hB]
  have hsαβ : Real.sqrt α * Real.sqrt β = 1 := by
    rw [← Real.sqrt_mul hα β, hαβ, Real.sqrt_one]
  have hexpand : (Real.sqrt α * Real.sqrt A - Real.sqrt β * Real.sqrt B) ^ 2 =
      α * A + β * B - 2 * (Real.sqrt A * Real.sqrt B) := by
    have hcross : 2 * (Real.sqrt α * Real.sqrt A) * (Real.sqrt β * Real.sqrt B)
        = 2 * (Real.sqrt A * Real.sqrt B) := by
      calc 2 * (Real.sqrt α * Real.sqrt A) * (Real.sqrt β * Real.sqrt B)
          = 2 * ((Real.sqrt α * Real.sqrt β) * (Real.sqrt A * Real.sqrt B)) := by ring
        _ = 2 * (Real.sqrt A * Real.sqrt B) := by rw [hsαβ]; ring
    nlinarith [hαA, hβB, hcross]
  nlinarith [sq_nonneg (Real.sqrt α * Real.sqrt A - Real.sqrt β * Real.sqrt B), hexpand]

/-- For `a > 0` and `b ≥ 0`, the identity `sqrt (b/a) * a = sqrt (a*b)` holds. -/
theorem sqrt_div_mul {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    Real.sqrt (b / a) * a = Real.sqrt (a * b) := by
  have h : Real.sqrt ((b / a) * a ^ 2) = Real.sqrt (b / a) * Real.sqrt (a ^ 2) :=
    Real.sqrt_mul (x := b / a) (by positivity) (a ^ 2)
  rw [Real.sqrt_sq (le_of_lt ha)] at h
  rw [← h]
  congr 1
  field_simp

/-- Under the stated relation-degree bounds and total-mass bound, the sum of Gram-entry changes
from one phase query is at most `sqrt (l*l')`. -/
theorem progress_step_le {ι : Type*} [Fintype ι] {n : ℕ}
    (X Y : Finset (Input n)) (R : Finset (InputPair n)) (l l' : ℕ)
    (hl : 0 < l) (hl' : 0 < l') (i : Fin n) (ψ : ι → Input n → ℂ)
    (hRsub : ∀ p ∈ R, p.1 ∈ X ∧ p.2 ∈ Y)
    (hxcard : ∀ x ∈ X, (R.filter (fun p => p.1 = x ∧ p.2 i ≠ x i)).card ≤ l)
    (hycard : ∀ y ∈ Y, (R.filter (fun p => p.2 = y ∧ p.1 i ≠ y i)).card ≤ l')
    (hmass : (∑ iw, ∑ x ∈ X, ‖ψ iw x‖ ^ 2) + (∑ iw, ∑ y ∈ Y, ‖ψ iw y‖ ^ 2) ≤ 1) :
    ∑ p ∈ R, ‖rhoEntry (phaseQuery i ψ) p.1 p.2 - rhoEntry ψ p.1 p.2‖ ≤
      Real.sqrt ((l : ℝ) * (l' : ℝ)) := by
  classical
  set A : Input n → ℝ := fun x => ∑ iw, ‖ψ iw x‖ ^ 2 with hA
  have hAnonneg : ∀ x, 0 ≤ A x := fun x => Finset.sum_nonneg (fun iw _ => by positivity)
  set α : ℝ := Real.sqrt ((l' : ℝ) / (l : ℝ)) with hα
  set β : ℝ := Real.sqrt ((l : ℝ) / (l' : ℝ)) with hβ
  have hαnn : 0 ≤ α := Real.sqrt_nonneg _
  have hβnn : 0 ≤ β := Real.sqrt_nonneg _
  have hαβ1 : Real.sqrt ((l' : ℝ) / (l : ℝ)) * Real.sqrt ((l : ℝ) / (l' : ℝ)) = 1 := by
    have hmul : Real.sqrt (((l' : ℝ) / (l : ℝ)) * ((l : ℝ) / (l' : ℝ)))
        = Real.sqrt ((l' : ℝ) / (l : ℝ)) * Real.sqrt ((l : ℝ) / (l' : ℝ)) :=
      Real.sqrt_mul (x := (l' : ℝ) / (l : ℝ)) (by positivity) ((l : ℝ) / (l' : ℝ))
    rw [← hmul]
    rw [show ((l' : ℝ) / (l : ℝ)) * ((l : ℝ) / (l' : ℝ)) = 1 by field_simp]
    exact Real.sqrt_one
  have hαβ : α * β = 1 := by
    rw [hα, hβ]; exact hαβ1

  have hterm : ∀ p ∈ R, ‖rhoEntry (phaseQuery i ψ) p.1 p.2 - rhoEntry ψ p.1 p.2‖ =
      if p.1 i = p.2 i then 0 else 2 * ‖rhoEntry ψ p.1 p.2‖ := by
    intro p hp
    rw [rhoEntry_phaseQuery]
    by_cases h : p.1 i = p.2 i
    · rw [if_pos h, if_pos h]; simp
    · rw [if_neg h, if_neg h]
      rw [show -rhoEntry ψ p.1 p.2 - rhoEntry ψ p.1 p.2 = -(2 * rhoEntry ψ p.1 p.2) by ring,
        norm_neg, norm_mul, Complex.norm_ofNat]
  rw [Finset.sum_congr rfl hterm]

  have hfilt : (∑ p ∈ R, (if p.1 i = p.2 i then 0 else 2 * ‖rhoEntry ψ p.1 p.2‖))
      = ∑ p ∈ R.filter (fun p => p.1 i ≠ p.2 i), 2 * ‖rhoEntry ψ p.1 p.2‖ := by
    rw [Finset.sum_filter (s := R) (p := fun p => p.1 i ≠ p.2 i)
      (f := fun p => 2 * ‖rhoEntry ψ p.1 p.2‖)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : p.1 i = p.2 i <;> simp [h]
  rw [hfilt]

  have hpoint : ∀ p ∈ R.filter (fun p => p.1 i ≠ p.2 i),
      2 * ‖rhoEntry ψ p.1 p.2‖ ≤ α * A p.1 + β * A p.2 := by
    intro p hp
    have hρ := rhoEntry_norm_le ψ p.1 p.2
    have h1 : 2 * ‖rhoEntry ψ p.1 p.2‖ ≤
        2 * (Real.sqrt (A p.1) * Real.sqrt (A p.2)) := by linarith [hρ]
    have h2 := amgm_two (A := A p.1) (B := A p.2) (hAnonneg p.1) (hAnonneg p.2)
      hαnn hβnn hαβ
    linarith [h1, h2]
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [Finset.sum_add_distrib]

  have hfilteqX : ∀ x, (R.filter (fun p => p.1 i ≠ p.2 i)).filter (fun p => p.1 = x)
      = R.filter (fun p => p.1 = x ∧ p.2 i ≠ x i) := by
    intro x
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro p hp
    constructor
    · rintro ⟨hne, hpx⟩
      exact ⟨hpx, fun h2 => hne (by rw [hpx, h2])⟩
    · rintro ⟨hpx, hne⟩
      exact ⟨fun h2 => hne (by rw [← hpx]; exact h2.symm), hpx⟩
  have hfilteqY : ∀ y, (R.filter (fun p => p.1 i ≠ p.2 i)).filter (fun p => p.2 = y)
      = R.filter (fun p => p.2 = y ∧ p.1 i ≠ y i) := by
    intro y
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro p hp
    constructor
    · rintro ⟨hne, hpy⟩
      exact ⟨hpy, fun h2 => hne (by rw [h2, hpy])⟩
    · rintro ⟨hpy, hne⟩
      exact ⟨fun h2 => hne (by rw [h2, ← hpy]), hpy⟩
  have hcardX : ∀ x ∈ X, ((R.filter (fun p => p.1 i ≠ p.2 i)).filter
      (fun p => p.1 = x)).card ≤ l := by
    intro x hx
    rw [hfilteqX x]
    exact hxcard x hx
  have hcardY : ∀ y ∈ Y, ((R.filter (fun p => p.1 i ≠ p.2 i)).filter
      (fun p => p.2 = y)).card ≤ l' := by
    intro y hy
    rw [hfilteqY y]
    exact hycard y hy

  have hopenX : ∑ p ∈ R.filter (fun p => p.1 i ≠ p.2 i), A p.1
      = ∑ x ∈ X, A x * (((R.filter (fun p => p.1 i ≠ p.2 i)).filter
          (fun p => p.1 = x)).card : ℝ) := by
    have h := Finset.sum_fiberwise_of_maps_to'
      (s := R.filter (fun p => p.1 i ≠ p.2 i)) (t := X) (g := fun p => p.1) (f := A)
      (h := fun p hp => (hRsub p (Finset.mem_filter.mp hp).1).1)
    calc ∑ p ∈ R.filter (fun p => p.1 i ≠ p.2 i), A p.1
        = ∑ x ∈ X, ∑ p ∈ (R.filter (fun p => p.1 i ≠ p.2 i)).filter
            (fun p => p.1 = x), A x := h.symm
      _ = ∑ x ∈ X, A x * (((R.filter (fun p => p.1 i ≠ p.2 i)).filter
            (fun p => p.1 = x)).card : ℝ) := by
          refine Finset.sum_congr rfl (fun x hx => ?_)
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hopenY : ∑ p ∈ R.filter (fun p => p.1 i ≠ p.2 i), A p.2
      = ∑ y ∈ Y, A y * (((R.filter (fun p => p.1 i ≠ p.2 i)).filter
          (fun p => p.2 = y)).card : ℝ) := by
    have h := Finset.sum_fiberwise_of_maps_to'
      (s := R.filter (fun p => p.1 i ≠ p.2 i)) (t := Y) (g := fun p => p.2) (f := A)
      (h := fun p hp => (hRsub p (Finset.mem_filter.mp hp).1).2)
    calc ∑ p ∈ R.filter (fun p => p.1 i ≠ p.2 i), A p.2
        = ∑ y ∈ Y, ∑ p ∈ (R.filter (fun p => p.1 i ≠ p.2 i)).filter
            (fun p => p.2 = y), A y := h.symm
      _ = ∑ y ∈ Y, A y * (((R.filter (fun p => p.1 i ≠ p.2 i)).filter
            (fun p => p.2 = y)).card : ℝ) := by
          refine Finset.sum_congr rfl (fun y hy => ?_)
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

  have hXbound : ∑ p ∈ R.filter (fun p => p.1 i ≠ p.2 i), α * A p.1
      ≤ α * ((l : ℝ) * ∑ x ∈ X, A x) := by
    have h1 : ∑ p ∈ R.filter (fun p => p.1 i ≠ p.2 i), α * A p.1
        = α * ∑ p ∈ R.filter (fun p => p.1 i ≠ p.2 i), A p.1 := by
      rw [Finset.mul_sum]
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ hαnn
    rw [hopenX]
    calc ∑ x ∈ X, A x * (((R.filter (fun p => p.1 i ≠ p.2 i)).filter
            (fun p => p.1 = x)).card : ℝ)
        ≤ ∑ x ∈ X, A x * (l : ℝ) := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (hAnonneg x)
          exact_mod_cast hcardX x hx
      _ = (l : ℝ) * ∑ x ∈ X, A x := by rw [← Finset.sum_mul, mul_comm]
  have hYbound : ∑ p ∈ R.filter (fun p => p.1 i ≠ p.2 i), β * A p.2
      ≤ β * ((l' : ℝ) * ∑ y ∈ Y, A y) := by
    have h1 : ∑ p ∈ R.filter (fun p => p.1 i ≠ p.2 i), β * A p.2
        = β * ∑ p ∈ R.filter (fun p => p.1 i ≠ p.2 i), A p.2 := by
      rw [Finset.mul_sum]
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ hβnn
    rw [hopenY]
    calc ∑ y ∈ Y, A y * (((R.filter (fun p => p.1 i ≠ p.2 i)).filter
            (fun p => p.2 = y)).card : ℝ)
        ≤ ∑ y ∈ Y, A y * (l' : ℝ) := by
          refine Finset.sum_le_sum (fun y hy => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (hAnonneg y)
          exact_mod_cast hcardY y hy
      _ = (l' : ℝ) * ∑ y ∈ Y, A y := by rw [← Finset.sum_mul, mul_comm]

  refine (add_le_add hXbound hYbound).trans ?_
  have hαl : α * (l : ℝ) = Real.sqrt ((l : ℝ) * (l' : ℝ)) := by
    rw [hα]; exact sqrt_div_mul (by exact_mod_cast hl) (by positivity)
  have hβl : β * (l' : ℝ) = Real.sqrt ((l : ℝ) * (l' : ℝ)) := by
    rw [hβ, sqrt_div_mul (by exact_mod_cast hl') (by positivity), mul_comm]
  have hcombine : α * ((l : ℝ) * ∑ x ∈ X, A x) + β * ((l' : ℝ) * ∑ y ∈ Y, A y)
      = Real.sqrt ((l : ℝ) * (l' : ℝ)) * ((∑ x ∈ X, A x) + (∑ y ∈ Y, A y)) := by
    have e1 : α * ((l : ℝ) * ∑ x ∈ X, A x) =
        Real.sqrt ((l : ℝ) * (l' : ℝ)) * ∑ x ∈ X, A x := by
      rw [← mul_assoc, hαl]
    have e2 : β * ((l' : ℝ) * ∑ y ∈ Y, A y) =
        Real.sqrt ((l : ℝ) * (l' : ℝ)) * ∑ y ∈ Y, A y := by
      rw [← mul_assoc, hβl]
    rw [e1, e2]; ring
  rw [hcombine]
  have hmassA : (∑ x ∈ X, A x) + (∑ y ∈ Y, A y) ≤ 1 := by
    have hAX : ∑ x ∈ X, A x = ∑ iw, ∑ x ∈ X, ‖ψ iw x‖ ^ 2 := by
      rw [hA]; exact Finset.sum_comm
    have hAY : ∑ y ∈ Y, A y = ∑ iw, ∑ y ∈ Y, ‖ψ iw y‖ ^ 2 := by
      rw [hA]; exact Finset.sum_comm
    rw [hAX, hAY]; exact hmass
  calc Real.sqrt ((l : ℝ) * (l' : ℝ)) * ((∑ x ∈ X, A x) + (∑ y ∈ Y, A y))
      ≤ Real.sqrt ((l : ℝ) * (l' : ℝ)) * 1 := by
        refine mul_le_mul_of_nonneg_left hmassA (Real.sqrt_nonneg _)
    _ = Real.sqrt ((l : ℝ) * (l' : ℝ)) := by ring

/-- For positive natural `a, b` with `a*b ≤ L`, the quantity `sqrt (b/a)` is at most `sqrt L /
a`. -/
theorem sqrt_div_le {a b L : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a * b ≤ L) :
    Real.sqrt ((b : ℝ) / (a : ℝ)) ≤ Real.sqrt (L : ℝ) / (a : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hsq : Real.sqrt ((b : ℝ) / (a : ℝ)) * (a : ℝ) = Real.sqrt ((a : ℝ) * (b : ℝ)) :=
    sqrt_div_mul haR (by positivity)
  rw [le_div_iff₀ haR, hsq]
  apply Real.sqrt_le_sqrt
  exact_mod_cast h

/-- Under the stated local mismatch-degree product bound and total-mass bound, the sum of
Gram-entry changes from one phase query is at most `sqrt lmax`. -/
theorem progress_step_le_lmax {ι : Type*} [Fintype ι] {n : ℕ}
    (X Y : Finset (Input n)) (R : Finset (InputPair n)) (lmax : ℕ)
    (i : Fin n) (ψ : ι → Input n → ℂ) (lx ly : Input n → ℕ)
    (hRsub : ∀ p ∈ R, p.1 ∈ X ∧ p.2 ∈ Y)
    (hxcard : ∀ x ∈ X, (R.filter (fun p => p.1 = x ∧ p.2 i ≠ x i)).card = lx x)
    (hycard : ∀ y ∈ Y, (R.filter (fun p => p.2 = y ∧ p.1 i ≠ y i)).card = ly y)
    (hlmax : ∀ p ∈ R, p.1 i ≠ p.2 i → lx p.1 * ly p.2 ≤ lmax)
    (hmass : (∑ iw, ∑ x ∈ X, ‖ψ iw x‖ ^ 2) + (∑ iw, ∑ y ∈ Y, ‖ψ iw y‖ ^ 2) ≤ 1) :
    ∑ p ∈ R, ‖rhoEntry (phaseQuery i ψ) p.1 p.2 - rhoEntry ψ p.1 p.2‖ ≤
      Real.sqrt (lmax : ℝ) := by
  classical
  set A : Input n → ℝ := fun x => ∑ iw, ‖ψ iw x‖ ^ 2 with hA
  have hAnonneg : ∀ x, 0 ≤ A x := fun x => Finset.sum_nonneg (fun iw _ => by positivity)
  set R' : Finset (InputPair n) := R.filter (fun p => p.1 i ≠ p.2 i) with hR'def
  have hterm : ∀ p ∈ R, ‖rhoEntry (phaseQuery i ψ) p.1 p.2 - rhoEntry ψ p.1 p.2‖ =
      if p.1 i = p.2 i then 0 else 2 * ‖rhoEntry ψ p.1 p.2‖ := by
    intro p hp
    rw [rhoEntry_phaseQuery]
    by_cases h : p.1 i = p.2 i
    · rw [if_pos h, if_pos h]; simp
    · rw [if_neg h, if_neg h]
      rw [show -rhoEntry ψ p.1 p.2 - rhoEntry ψ p.1 p.2 = -(2 * rhoEntry ψ p.1 p.2) by ring,
        norm_neg, norm_mul, Complex.norm_ofNat]
  rw [Finset.sum_congr rfl hterm]
  have hfilt : (∑ p ∈ R, (if p.1 i = p.2 i then 0 else 2 * ‖rhoEntry ψ p.1 p.2‖))
      = ∑ p ∈ R', 2 * ‖rhoEntry ψ p.1 p.2‖ := by
    rw [hR'def, Finset.sum_filter (s := R) (p := fun p => p.1 i ≠ p.2 i)
      (f := fun p => 2 * ‖rhoEntry ψ p.1 p.2‖)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : p.1 i = p.2 i <;> simp [h]
  rw [hfilt]

  have hlxpos : ∀ p ∈ R', 0 < lx p.1 := by
    intro p hp
    have hpR : p ∈ R := (Finset.mem_filter.mp hp).1
    have hdiff : p.1 i ≠ p.2 i := (Finset.mem_filter.mp hp).2
    have hc : (R.filter (fun q => q.1 = p.1 ∧ q.2 i ≠ p.1 i)).card = lx p.1 :=
      hxcard p.1 (hRsub p hpR).1
    have hpos : 0 < (R.filter (fun q => q.1 = p.1 ∧ q.2 i ≠ p.1 i)).card :=
      Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hpR, rfl, Ne.symm hdiff⟩⟩
    rwa [hc] at hpos
  have hlypos : ∀ p ∈ R', 0 < ly p.2 := by
    intro p hp
    have hpR : p ∈ R := (Finset.mem_filter.mp hp).1
    have hdiff : p.1 i ≠ p.2 i := (Finset.mem_filter.mp hp).2
    have hc : (R.filter (fun q => q.2 = p.2 ∧ q.1 i ≠ p.2 i)).card = ly p.2 :=
      hycard p.2 (hRsub p hpR).2
    have hpos : 0 < (R.filter (fun q => q.2 = p.2 ∧ q.1 i ≠ p.2 i)).card :=
      Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hpR, rfl, hdiff⟩⟩
    rwa [hc] at hpos
  have hpoint : ∀ p ∈ R', 2 * ‖rhoEntry ψ p.1 p.2‖ ≤
      Real.sqrt ((ly p.2 : ℝ) / (lx p.1 : ℝ)) * A p.1 +
        Real.sqrt ((lx p.1 : ℝ) / (ly p.2 : ℝ)) * A p.2 := by
    intro p hp
    have hpR : p ∈ R := (Finset.mem_filter.mp hp).1
    have hαnn : 0 ≤ Real.sqrt ((ly p.2 : ℝ) / (lx p.1 : ℝ)) := Real.sqrt_nonneg _
    have hβnn : 0 ≤ Real.sqrt ((lx p.1 : ℝ) / (ly p.2 : ℝ)) := Real.sqrt_nonneg _
    have hαβ : Real.sqrt ((ly p.2 : ℝ) / (lx p.1 : ℝ)) *
        Real.sqrt ((lx p.1 : ℝ) / (ly p.2 : ℝ)) = 1 := by
      have hmul : Real.sqrt (((ly p.2 : ℝ) / (lx p.1 : ℝ)) *
            ((lx p.1 : ℝ) / (ly p.2 : ℝ))) =
          Real.sqrt ((ly p.2 : ℝ) / (lx p.1 : ℝ)) *
            Real.sqrt ((lx p.1 : ℝ) / (ly p.2 : ℝ)) :=
        Real.sqrt_mul (x := (ly p.2 : ℝ) / (lx p.1 : ℝ)) (by positivity) ((lx p.1 : ℝ) / (ly p.2 : ℝ))
      rw [← hmul]
      rw [show ((ly p.2 : ℝ) / (lx p.1 : ℝ)) * ((lx p.1 : ℝ) / (ly p.2 : ℝ)) = 1 by
        have h1 : (lx p.1 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hlxpos p hp))
        have h2 : (ly p.2 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hlypos p hp))
        field_simp]
      exact Real.sqrt_one
    have hρ := rhoEntry_norm_le ψ p.1 p.2
    have h1 : 2 * ‖rhoEntry ψ p.1 p.2‖ ≤
        2 * (Real.sqrt (A p.1) * Real.sqrt (A p.2)) := by linarith [hρ]
    have h2 := amgm_two (A := A p.1) (B := A p.2) (hAnonneg p.1) (hAnonneg p.2)
      hαnn hβnn hαβ
    linarith [h1, h2]
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [Finset.sum_add_distrib]

  have hfilteqX : ∀ x, R'.filter (fun p => p.1 = x)
      = R.filter (fun p => p.1 = x ∧ p.2 i ≠ x i) := by
    intro x
    rw [hR'def, Finset.filter_filter]
    apply Finset.filter_congr
    intro p hp
    constructor
    · rintro ⟨hne, hpx⟩
      exact ⟨hpx, fun h2 => hne (by rw [hpx, h2])⟩
    · rintro ⟨hpx, hne⟩
      exact ⟨fun h2 => hne (by rw [← hpx]; exact h2.symm), hpx⟩
  have hfilteqY : ∀ y, R'.filter (fun p => p.2 = y)
      = R.filter (fun p => p.2 = y ∧ p.1 i ≠ y i) := by
    intro y
    rw [hR'def, Finset.filter_filter]
    apply Finset.filter_congr
    intro p hp
    constructor
    · rintro ⟨hne, hpy⟩
      exact ⟨hpy, fun h2 => hne (by rw [h2, hpy])⟩
    · rintro ⟨hpy, hne⟩
      exact ⟨fun h2 => hne (by rw [h2, ← hpy]), hpy⟩
  have hcardX : ∀ x ∈ X, (R'.filter (fun p => p.1 = x)).card = lx x := by
    intro x hx; rw [hfilteqX x]; exact hxcard x hx
  have hcardY : ∀ y ∈ Y, (R'.filter (fun p => p.2 = y)).card = ly y := by
    intro y hy; rw [hfilteqY y]; exact hycard y hy

  have hfiberX : ∑ p ∈ R', Real.sqrt ((ly p.2 : ℝ) / (lx p.1 : ℝ)) * A p.1
      = ∑ x ∈ X, A x * ∑ p ∈ R'.filter (fun p => p.1 = x),
          Real.sqrt ((ly p.2 : ℝ) / (lx x : ℝ)) := by
    have h := Finset.sum_fiberwise_of_maps_to
      (s := R') (t := X) (g := fun p => p.1)
      (h := fun p hp => (hRsub p (Finset.mem_filter.mp hp).1).1)
      (f := fun p => Real.sqrt ((ly p.2 : ℝ) / (lx p.1 : ℝ)) * A p.1)
    rw [← h]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hpx : p.1 = x := (Finset.mem_filter.mp hp).2
    rw [hpx]; ring
  have hfiberY : ∑ p ∈ R', Real.sqrt ((lx p.1 : ℝ) / (ly p.2 : ℝ)) * A p.2
      = ∑ y ∈ Y, A y * ∑ p ∈ R'.filter (fun p => p.2 = y),
          Real.sqrt ((lx p.1 : ℝ) / (ly y : ℝ)) := by
    have h := Finset.sum_fiberwise_of_maps_to
      (s := R') (t := Y) (g := fun p => p.2)
      (h := fun p hp => (hRsub p (Finset.mem_filter.mp hp).1).2)
      (f := fun p => Real.sqrt ((lx p.1 : ℝ) / (ly p.2 : ℝ)) * A p.2)
    rw [← h]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hpy : p.2 = y := (Finset.mem_filter.mp hp).2
    rw [hpy]; ring
  have hinnerX : ∀ x ∈ X, ∑ p ∈ R'.filter (fun p => p.1 = x),
      Real.sqrt ((ly p.2 : ℝ) / (lx x : ℝ)) ≤ Real.sqrt (lmax : ℝ) := by
    intro x hx
    have hcard : (R'.filter (fun p => p.1 = x)).card = lx x := hcardX x hx
    rcases Nat.eq_zero_or_pos (lx x) with h0 | hpos
    · have hz : (R'.filter (fun p => p.1 = x)).card = 0 := by rw [hcard, h0]
      rw [Finset.card_eq_zero.mp hz]; simp
    · calc ∑ p ∈ R'.filter (fun p => p.1 = x), Real.sqrt ((ly p.2 : ℝ) / (lx x : ℝ))
          ≤ ∑ p ∈ R'.filter (fun p => p.1 = x), Real.sqrt (lmax : ℝ) / (lx x : ℝ) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hpR : p ∈ R' := (Finset.mem_filter.mp hp).1
            have hpRsubR : p ∈ R := (Finset.mem_filter.mp hpR).1
            have hdiff : p.1 i ≠ p.2 i := (Finset.mem_filter.mp hpR).2
            have hlyp : 0 < ly p.2 := hlypos p hpR
            have hprod : lx x * ly p.2 ≤ lmax := by
              have := hlmax p hpRsubR hdiff
              rwa [(Finset.mem_filter.mp hp).2] at this
            exact sqrt_div_le hpos hlyp hprod
        _ = ((R'.filter (fun p => p.1 = x)).card : ℝ) *
              (Real.sqrt (lmax : ℝ) / (lx x : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = (lx x : ℝ) * (Real.sqrt (lmax : ℝ) / (lx x : ℝ)) := by rw [hcard]
        _ = Real.sqrt (lmax : ℝ) := by
              rw [mul_div_cancel₀ _ (by exact_mod_cast (ne_of_gt hpos))]
  have hinnerY : ∀ y ∈ Y, ∑ p ∈ R'.filter (fun p => p.2 = y),
      Real.sqrt ((lx p.1 : ℝ) / (ly y : ℝ)) ≤ Real.sqrt (lmax : ℝ) := by
    intro y hy
    have hcard : (R'.filter (fun p => p.2 = y)).card = ly y := hcardY y hy
    rcases Nat.eq_zero_or_pos (ly y) with h0 | hpos
    · have hz : (R'.filter (fun p => p.2 = y)).card = 0 := by rw [hcard, h0]
      rw [Finset.card_eq_zero.mp hz]; simp
    · calc ∑ p ∈ R'.filter (fun p => p.2 = y), Real.sqrt ((lx p.1 : ℝ) / (ly y : ℝ))
          ≤ ∑ p ∈ R'.filter (fun p => p.2 = y), Real.sqrt (lmax : ℝ) / (ly y : ℝ) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hpR : p ∈ R' := (Finset.mem_filter.mp hp).1
            have hpRsubR : p ∈ R := (Finset.mem_filter.mp hpR).1
            have hdiff : p.1 i ≠ p.2 i := (Finset.mem_filter.mp hpR).2
            have hlxp : 0 < lx p.1 := hlxpos p hpR
            have hprod : ly y * lx p.1 ≤ lmax := by
              have := hlmax p hpRsubR hdiff
              rw [(Finset.mem_filter.mp hp).2] at this
              rwa [mul_comm]
            exact sqrt_div_le hpos hlxp hprod
        _ = ((R'.filter (fun p => p.2 = y)).card : ℝ) *
              (Real.sqrt (lmax : ℝ) / (ly y : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = (ly y : ℝ) * (Real.sqrt (lmax : ℝ) / (ly y : ℝ)) := by rw [hcard]
        _ = Real.sqrt (lmax : ℝ) := by
              rw [mul_div_cancel₀ _ (by exact_mod_cast (ne_of_gt hpos))]
  have hXbound : ∑ p ∈ R', Real.sqrt ((ly p.2 : ℝ) / (lx p.1 : ℝ)) * A p.1
      ≤ Real.sqrt (lmax : ℝ) * ∑ x ∈ X, A x := by
    rw [hfiberX]
    calc ∑ x ∈ X, A x * ∑ p ∈ R'.filter (fun p => p.1 = x),
            Real.sqrt ((ly p.2 : ℝ) / (lx x : ℝ))
        ≤ ∑ x ∈ X, A x * Real.sqrt (lmax : ℝ) := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          exact mul_le_mul_of_nonneg_left (hinnerX x hx) (hAnonneg x)
      _ = Real.sqrt (lmax : ℝ) * ∑ x ∈ X, A x := by rw [← Finset.sum_mul, mul_comm]
  have hYbound : ∑ p ∈ R', Real.sqrt ((lx p.1 : ℝ) / (ly p.2 : ℝ)) * A p.2
      ≤ Real.sqrt (lmax : ℝ) * ∑ y ∈ Y, A y := by
    rw [hfiberY]
    calc ∑ y ∈ Y, A y * ∑ p ∈ R'.filter (fun p => p.2 = y),
            Real.sqrt ((lx p.1 : ℝ) / (ly y : ℝ))
        ≤ ∑ y ∈ Y, A y * Real.sqrt (lmax : ℝ) := by
          refine Finset.sum_le_sum (fun y hy => ?_)
          exact mul_le_mul_of_nonneg_left (hinnerY y hy) (hAnonneg y)
      _ = Real.sqrt (lmax : ℝ) * ∑ y ∈ Y, A y := by rw [← Finset.sum_mul, mul_comm]
  refine (add_le_add hXbound hYbound).trans ?_
  have hmassA : (∑ x ∈ X, A x) + (∑ y ∈ Y, A y) ≤ 1 := by
    have hAX : ∑ x ∈ X, A x = ∑ iw, ∑ x ∈ X, ‖ψ iw x‖ ^ 2 := by
      rw [hA]; exact Finset.sum_comm
    have hAY : ∑ y ∈ Y, A y = ∑ iw, ∑ y ∈ Y, ‖ψ iw y‖ ^ 2 := by
      rw [hA]; exact Finset.sum_comm
    rw [hAX, hAY]; exact hmass
  calc Real.sqrt (lmax : ℝ) * ∑ x ∈ X, A x + Real.sqrt (lmax : ℝ) * ∑ y ∈ Y, A y
      = Real.sqrt (lmax : ℝ) * ((∑ x ∈ X, A x) + (∑ y ∈ Y, A y)) := by ring
    _ ≤ Real.sqrt (lmax : ℝ) * 1 := by
        refine mul_le_mul_of_nonneg_left hmassA (Real.sqrt_nonneg _)
    _ = Real.sqrt (lmax : ℝ) := by ring

end Qatlib.Papers.QLowerBound00.MainResults.AdversaryCore
