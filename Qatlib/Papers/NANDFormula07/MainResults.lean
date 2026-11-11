/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Pi.Defs
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
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Relation
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Spectral Ingredients for NAND Formula Evaluation

This module develops weighted tree and spectral estimates for the NAND formula framework of
[ChildsEtAl2007]. `NandTreeData` records the parent map, tail vertices, weights, Boolean labels,
and size and spectral parameters; `NandTreeData.ham` gives the corresponding real weighted
adjacency action.

The results provide subtree geometry, zero energy amplitude and normalization lemmas, tail
extension estimates, local eigenvector ratio bounds, Perron factorization identities, and
elementary cost comparisons. These are component statements with their hypotheses stated
explicitly.

## Main statements

* `lemma3_zero_amplitude_of_eval_true` forces zero amplitude at an internal true vertex under
  the NAND and weight conditions.
* `lemma4_normalize_of_unnormalized` normalizes a subtree vector and retains a lower bound on
  its root amplitude.
* `theorem2_tail_extension` extends a subtree vector to a global zero energy vector with a tail
  overlap bound.
* `gammaV_ge_inv_GammaPrime`, `lemma6_eval_false_branch`, and `lemma6_eval_true_step` supply
  local spectral estimates.
* `perron_factorization_norm_one` supplies oppositely directed edge factors with unit squared
  row sums from a positive eigenvector of eigenvalue one.

## References

* [Childs et al., 2007][ChildsEtAl2007]
-/

set_option warningAsError false

namespace Qatlib.Papers.NANDFormula07.MainResults

open scoped BigOperators

set_option autoImplicit false

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Data for a finite weighted NAND tree with two distinguished tail vertices, Boolean labels,
sizes, heights, and spectral parameters. The fields impose the tail parent relations, strict
height descent, positive sizes, symmetric weights, and the stated parameter monotonicity
bounds. -/
structure NandTreeData (V : Type) [Fintype V] [DecidableEq V] where
  root : V
  root' : V
  root'' : V
  parent : V → Option V
  eval : V → Bool
  sz : V → ℕ
  weight : V → V → ℝ
  height : V → ℕ
  sigmaMinus : V → ℝ
  sigmaPlus : V → ℝ

  parent_root : parent root = some root'

  parent_root' : parent root' = some root''

  parent_root'' : parent root'' = none

  height_lt : ∀ {p c : V}, parent c = some p → height c < height p

  sz_pos : ∀ v, 0 < sz v

  weight_symm : ∀ u v, weight u v = weight v u

  sigmaMinus_mono : ∀ {v c : V}, parent c = some v → sigmaMinus c ≤ sigmaMinus v

  sigmaPlus_mono : ∀ {v c : V}, parent c = some v → sigmaPlus c ≤ sigmaPlus v

  sigmaMinus_le_root : ∀ v, sigmaMinus v ≤ sigmaMinus root

  sigmaPlus_le_root : ∀ v, sigmaPlus v ≤ sigmaPlus root

namespace NandTreeData

variable (D : NandTreeData V)

/-- A vertex is a leaf when no vertex has it as its parent. -/
def IsLeaf (v : V) : Prop := ∀ c, D.parent c ≠ some v

/-- A vertex is internal when it has at least one child under the parent map. -/
def IsInternal (v : V) : Prop := ∃ c, D.parent c = some v

/-- Membership in the subtree rooted at `p`, defined by the reflexive transitive closure of the
parent to child relation. -/
def InSubtree (p v : V) : Prop :=
  Relation.ReflTransGen (fun a b : V => D.parent b = some a) p v

/-- The real weighted adjacency action at `v`, formed by adding its parent contribution, when
present, to the weighted contributions of all its children. -/
noncomputable def ham (a : V → ℝ) (v : V) : ℝ :=
  (match D.parent v with
    | some p => D.weight p v * a p
    | none => 0) +
  ∑ x : V, if D.parent x = some v then D.weight v x * a x else 0

/-- Every vertex belongs to its own subtree. -/
theorem inSubtree_refl (p : V) : D.InSubtree p p := Relation.ReflTransGen.refl

/-- A child of `p` belongs to the subtree rooted at `p`. -/
theorem inSubtree_child {p c : V} (h : D.parent c = some p) : D.InSubtree p c :=
  Relation.ReflTransGen.single h

/-- Subtree membership is transitive: a descendant of a descendant of `p` is a descendant of
`p`. -/
theorem inSubtree_trans {p v u : V} (hpv : D.InSubtree p v) (hvu : D.InSubtree v u) :
    D.InSubtree p u := Relation.ReflTransGen.trans hpv hvu

/-- The weighted adjacency action commutes with multiplication of the amplitude vector by a real
scalar. -/
theorem ham_smul (c : ℝ) (a : V → ℝ) (v : V) :
    D.ham (c • a) v = c * D.ham a v := by
  simp only [NandTreeData.ham, Pi.smul_apply, smul_eq_mul]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · cases h : D.parent v with
    | none => simp
    | some p => simp only [h]; ring
  · apply Finset.sum_congr rfl
    intro x _
    by_cases hx : D.parent x = some v
    · simp only [hx, if_true]; ring
    · simp only [hx, if_false]; ring

/-- At a leaf, the weighted adjacency action consists only of the parent contribution, or is
zero when the leaf has no parent. -/
theorem ham_leaf_eq (a : V → ℝ) {v : V} (hleaf : D.IsLeaf v) :
    D.ham a v =
      (match D.parent v with
        | some p => D.weight p v * a p
        | none => 0) := by
  unfold NandTreeData.ham
  have hsum : (∑ x : V, if D.parent x = some v then D.weight v x * a x else 0) = 0 := by
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [if_neg (hleaf x)]
  rw [hsum, add_zero]

end NandTreeData

/-- Under the stated NAND label and edge weight conditions, an internal vertex labeled `true`
has zero amplitude whenever `ham a` vanishes throughout its subtree. This is the zero
amplitude conclusion associated with Lemma 3 of [ChildsEtAl2007]. -/
theorem lemma3_zero_amplitude_of_eval_true (D : NandTreeData V) {a : V → ℝ} {p : V}
    (hNandTrue : ∀ v, D.IsInternal v → D.eval v = true →
      ∃ c, D.parent c = some v ∧ D.eval c = false)
    (hNandFalse : ∀ {v c : V}, D.parent c = some v → D.eval v = false → D.eval c = true)
    (hWeight_pos : ∀ {v c : V}, D.parent c = some v → D.eval c = false → 0 < D.weight v c)
    (hWeight_leaf_true : ∀ {v c : V}, D.parent c = some v → D.IsLeaf c → D.eval c = true →
      D.weight v c = 0)
    (hp_int : D.IsInternal p) (hp_eval : D.eval p = true)
    (ha : ∀ v, D.InSubtree p v → D.ham a v = 0) : a p = 0 := by

  have key : ∀ n v, D.height v = n → D.IsInternal v → D.eval v = true →
      (∀ u, D.InSubtree v u → D.ham a u = 0) → a v = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv hint hev hlocal

      obtain ⟨c, hpc, hcfalse⟩ := hNandTrue v hint hev
      by_cases hcleaf : D.IsLeaf c
      · have hc_ham : D.ham a c = 0 := hlocal c (D.inSubtree_child hpc)
        have hsum : (∑ x : V, if D.parent x = some c then D.weight c x * a x else 0) = 0 := by
          refine Finset.sum_eq_zero (fun x _ => ?_)
          rw [if_neg (hcleaf x)]
        have hprod : D.weight v c * a v = 0 := by
          simpa [NandTreeData.ham, hpc, hsum] using hc_ham
        exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (hWeight_pos hpc hcfalse))
      · have hsum : (∑ x : V, if D.parent x = some c then D.weight c x * a x else 0) = 0 := by
          refine Finset.sum_eq_zero (fun x _ => ?_)
          by_cases hx : D.parent x = some c
          · rw [if_pos hx]
            have hxeval : D.eval x = true := hNandFalse hx hcfalse
            by_cases hxleaf : D.IsLeaf x
            · rw [hWeight_leaf_true hx hxleaf hxeval, zero_mul]
            · have hxint : D.IsInternal x := by
                by_contra h
                exact hxleaf (fun y hy => h ⟨y, hy⟩)
              have hxh : D.height x < D.height c := D.height_lt hx
              have hxc : D.height c < n := by
                rw [← hv]
                exact D.height_lt hpc
              have hxle : D.height x < n := lt_trans hxh hxc
              have hxa : a x = 0 := by
                refine ih (D.height x) hxle x rfl hxint hxeval ?_
                intro u hu
                exact hlocal u (D.inSubtree_trans
                  (D.inSubtree_trans (D.inSubtree_child hpc) (D.inSubtree_child hx)) hu)
              rw [hxa, mul_zero]
          · rw [if_neg hx]
        have hc_ham : D.ham a c = 0 := hlocal c (D.inSubtree_child hpc)
        have hprod : D.weight v c * a v = 0 := by
          simpa [NandTreeData.ham, hpc, hsum] using hc_ham
        exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (hWeight_pos hpc hcfalse))
  exact key (D.height p) p rfl hp_int hp_eval ha

/-- For positive `σ`, `s`, and `y` with `y <= sqrt s * σ`, the reciprocal of `sqrt σ * s^(1 /
4)` is at most `1 / sqrt y`. This is a scalar normalization estimate associated with Lemma 4
of [ChildsEtAl2007]. -/
theorem lemma4_normalization_bound {σ s y : ℝ} (hσ : 0 < σ) (hs : 0 < s)
    (hy : 0 < y) (hle : y ≤ Real.sqrt s * σ) :
    1 / (Real.sqrt σ * s ^ (1 / 4 : ℝ)) ≤ 1 / Real.sqrt y := by
  have hs14_pos : 0 < s ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hs _

  have hsq : (Real.sqrt σ * s ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt s * σ := by
    rw [mul_pow, Real.sq_sqrt hσ.le]
    have hs14sq : (s ^ (1 / 4 : ℝ)) ^ 2 = s ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hs.le]
      norm_num
    rw [hs14sq, ← Real.sqrt_eq_rpow]
    ring
  have hden_pos : 0 < Real.sqrt σ * s ^ (1 / 4 : ℝ) := by positivity
  have hroot : Real.sqrt y ≤ Real.sqrt σ * s ^ (1 / 4 : ℝ) := by
    have haux : Real.sqrt y ≤ Real.sqrt ((Real.sqrt σ * s ^ (1 / 4 : ℝ)) ^ 2) := by
      rw [hsq]
      exact Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq hden_pos.le] at haux
  have hspos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  exact one_div_le_one_div_of_le hspos hroot

/-- Normalizes a vector supported in the subtree of `p` whose weighted adjacency action vanishes
there and whose amplitude at `p` is one, as a component associated with Lemma 4 and Theorem
2 of [ChildsEtAl2007]. Under the positive norm and parameter bounds, the normalized vector
retains these support and zero energy properties and has amplitude at least `1 / (sqrt
(D.sigmaMinus p) * (D.sz p)^(1 / 4))` at `p`. -/
theorem lemma4_normalize_of_unnormalized (D : NandTreeData V) {p : V} {a : V → ℝ}
    (hnorm_pos : 0 < ∑ v : V, (a v) ^ 2)
    (hzero : ∀ v, D.InSubtree p v → D.ham a v = 0)
    (hsupp : ∀ v, ¬ D.InSubtree p v → a v = 0)
    (hap : a p = 1)
    (hbound : ∑ v : V, (a v) ^ 2 ≤ Real.sqrt (D.sz p : ℝ) * D.sigmaMinus p)
    (hσ : 0 < D.sigmaMinus p) (hs : 0 < (D.sz p : ℝ)) :
    ∃ a' : V → ℝ,
      (∀ v, D.InSubtree p v → D.ham a' v = 0) ∧
      (∀ v, ¬ D.InSubtree p v → a' v = 0) ∧
      Real.sqrt (∑ v : V, (a' v) ^ 2) = 1 ∧
      1 / (Real.sqrt (D.sigmaMinus p) * (D.sz p : ℝ) ^ (1 / 4 : ℝ)) ≤ a' p := by
  set n := ∑ v : V, (a v) ^ 2 with hn_def
  have hn_pos : 0 < n := hnorm_pos
  have hcpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hcne : Real.sqrt n ≠ 0 := ne_of_gt hcpos
  refine ⟨(1 / Real.sqrt n) • a, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [NandTreeData.ham_smul, hzero v hv, mul_zero]
  · intro v hv
    simp only [Pi.smul_apply, smul_eq_mul, hsupp v hv, mul_zero]
  · have hterm : ∀ v : V, (((1 / Real.sqrt n) • a) v) ^ 2 = (a v) ^ 2 / n := by
      intro v
      simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_pow]
      rw [show (Real.sqrt n)⁻¹ ^ 2 = n⁻¹ by
        rw [inv_pow, Real.sq_sqrt hn_pos.le]]
      ring
    have hsum : (∑ v : V, (((1 / Real.sqrt n) • a) v) ^ 2) = 1 := by
      simp_rw [hterm]
      rw [← Finset.sum_div, ← hn_def]
      exact div_self (ne_of_gt hn_pos)
    rw [hsum, Real.sqrt_one]
  · have ha'p : (((1 / Real.sqrt n) • a) p) = 1 / Real.sqrt n := by
      simp only [Pi.smul_apply, smul_eq_mul, hap, mul_one]
    rw [ha'p]
    exact lemma4_normalization_bound hσ hs hn_pos hbound

/-- If `x > 0` and `0 <= y <= x^2`, then `x / sqrt (y + x^2)` is at least `1 / sqrt 2`. This is
the scalar overlap estimate associated with Theorem 2 of [ChildsEtAl2007]. -/
theorem overlap_ratio_ge_inv_sqrt_two {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hxy : y ≤ x ^ 2) :
    1 / Real.sqrt 2 ≤ x / Real.sqrt (y + x ^ 2) := by
  have hle : y + x ^ 2 ≤ 2 * x ^ 2 := by nlinarith
  have hsqrt_le : Real.sqrt (y + x ^ 2) ≤ Real.sqrt (2 * x ^ 2) := Real.sqrt_le_sqrt hle
  have hs2 : Real.sqrt (2 * x ^ 2) = Real.sqrt 2 * x := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [Real.sqrt_sq hx.le]
  have hspos : 0 < Real.sqrt (y + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  calc 1 / Real.sqrt 2 = x / (Real.sqrt 2 * x) := by
        field_simp
    _ = x / Real.sqrt (2 * x ^ 2) := by rw [hs2]
    _ ≤ x / Real.sqrt (y + x ^ 2) := by
        apply div_le_div_of_nonneg_left hx.le hspos hsqrt_le

/-- The spectral parameter `Gamma σr = 1 / (2 * σr)`. -/
noncomputable def Gamma (σr : ℝ) : ℝ := 1 / (2 * σr)

/-- The spectral parameter `GammaPrime σr = 8 * σr`. -/
noncomputable def GammaPrime (σr : ℝ) : ℝ := 8 * σr

/-- The local spectral expression `Gamma σr - (Gamma σr)^2 * σv - E^2 * (1 + GammaPrime σr) *
σpv`. -/
noncomputable def gammaV (σr σv σpv E : ℝ) : ℝ :=
  Gamma σr - Gamma σr ^ 2 * σv - E ^ 2 * (1 + GammaPrime σr) * σpv

/-- For nonnegative local parameters and positive `σr`, the local expression `gammaV` is at most
`Gamma σr`. This is a scalar estimate associated with Lemma 6 and Theorem 5 of
[ChildsEtAl2007]. -/
theorem gammaV_le_Gamma {σr σv σpv E : ℝ}
    (hσv : 0 ≤ σv) (hσpv : 0 ≤ σpv) (hσr : 0 < σr) :
    gammaV σr σv σpv E ≤ Gamma σr := by
  have hΓ'nonneg : 0 ≤ 1 + GammaPrime σr := by
    have : 0 < 8 * σr := by linarith
    unfold GammaPrime
    linarith
  have h1 : 0 ≤ Gamma σr ^ 2 * σv := mul_nonneg (sq_nonneg _) hσv
  have h2 : 0 ≤ E ^ 2 * (1 + GammaPrime σr) * σpv :=
    mul_nonneg (mul_nonneg (sq_nonneg E) hΓ'nonneg) hσpv
  unfold gammaV
  linarith

/-- Under the stated lower and upper bounds on the spectral parameters and `0 < E <= 1 / (9 * σr
* sqrt σpr)`, the local expression `gammaV` is at least `1 / GammaPrime σr`. This is a
scalar spectral estimate associated with Theorems 2 and 5 of [ChildsEtAl2007]. -/
theorem gammaV_ge_inv_GammaPrime {σr σv σpv σpr E : ℝ}
    (hσr1 : 1 ≤ σr) (hσv1 : 1 ≤ σv) (hσvr : σv ≤ σr)
    (hσpv1 : 1 ≤ σpv) (hσpvr : σpv ≤ σpr)
    (hE0 : 0 < E) (hE : E ≤ 1 / (9 * σr * Real.sqrt σpr)) :
    1 / GammaPrime σr ≤ gammaV σr σv σpv E := by
  have hσr0 : 0 < σr := by linarith
  have hσpr1 : 1 ≤ σpr := le_trans hσpv1 hσpvr
  have hσpr0 : 0 < σpr := by linarith
  have hsqrtpos : 0 < Real.sqrt σpr := Real.sqrt_pos.mpr hσpr0
  have hE2prod : E ^ 2 * (81 * σr ^ 2 * σpr) ≤ 1 := by
    have hs : E ^ 2 ≤ (1 / (9 * σr * Real.sqrt σpr)) ^ 2 := pow_le_pow_left₀ hE0.le hE 2
    have hd : 0 < (9 * σr * Real.sqrt σpr) ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hs hd.le
    have hcalc : (1 / (9 * σr * Real.sqrt σpr)) ^ 2 * (9 * σr * Real.sqrt σpr) ^ 2 = 1 := by
      rw [div_pow, one_pow]
      field_simp
    have hsq : (9 * σr * Real.sqrt σpr) ^ 2 = 81 * σr ^ 2 * σpr := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hσpr0.le]
      ring
    rw [hcalc, hsq] at hmul
    exact hmul
  have hE2pv : E ^ 2 * σpv * (81 * σr ^ 2) ≤ 1 := by
    have hE2nn : 0 ≤ E ^ 2 := sq_nonneg E
    have hσr2nn : 0 ≤ 81 * σr ^ 2 := by positivity
    have hmono : E ^ 2 * (81 * σr ^ 2) * σpv ≤ E ^ 2 * (81 * σr ^ 2) * σpr :=
      mul_le_mul_of_nonneg_left hσpvr (mul_nonneg hE2nn hσr2nn)
    nlinarith [hE2prod, hmono]
  unfold gammaV Gamma GammaPrime
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 8 * σr)]
  field_simp
  nlinarith [hE2pv, hσvr, hσpv1, hσpvr, hσr1]

/-- For a positive energy eigenvector with nonzero amplitude at a leaf and positive parent edge
weight, the parent to leaf amplitude ratio is positive and equals the energy divided by that
weight. This is the leaf component associated with Lemma 6 of [ChildsEtAl2007]. -/
theorem lemma6_leaf_ratio (D : NandTreeData V) {a : V → ℝ} {E : ℝ} {v p : V}
    (hpv : D.parent v = some p) (hleaf : D.IsLeaf v)
    (heig : ∀ w, D.ham a w = E * a w) (hE : 0 < E)
    (hw : 0 < D.weight p v) (hav : a v ≠ 0) :
    0 < a p / a v ∧ a p / a v = E / D.weight p v := by
  have hsum : (∑ x : V, if D.parent x = some v then D.weight v x * a x else 0) = 0 := by
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [if_neg (hleaf x)]
  have hham : D.ham a v = D.weight p v * a p := by
    simp only [NandTreeData.ham, hpv, hsum, add_zero]
  have heq : D.weight p v * a p = E * a v := by
    rw [← hham]; exact heig v
  have hratio : a p / a v = E / D.weight p v := by
    rw [eq_div_iff (ne_of_gt hw)]
    have : a p * D.weight p v = E * a v := by rw [mul_comm]; exact heq
    field_simp
    linarith
  exact ⟨by rw [hratio]; positivity, hratio⟩

/-- The bounds `1 / (8 * σ^2 * N + σ * sqrt N) <= E^2` and `E^2 <= 1 / (81 * σ^2 * N)` are
incompatible when `σ >= 1`, `N >= 1`, and `E > 0`. This is a scalar contradiction associated
with Theorem 5 of [ChildsEtAl2007]. -/
theorem tail_energy_contradiction {σ N E : ℝ} (hσ : 1 ≤ σ) (hN : 1 ≤ N)
    (hE : 0 < E)
    (hlow : 1 / (8 * σ ^ 2 * N + σ * Real.sqrt N) ≤ E ^ 2)
    (hup : E ^ 2 ≤ 1 / (81 * σ ^ 2 * N)) : False := by
  have hσ0 : 0 < σ := by linarith
  have hN0 : 0 < N := by linarith
  have hsqrtN_le_N : Real.sqrt N ≤ N := by
    calc Real.sqrt N ≤ Real.sqrt (N ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = N := Real.sqrt_sq hN0.le
  have hden1 : 0 < 81 * σ ^ 2 * N := by positivity
  have hden2 : 0 < 8 * σ ^ 2 * N + σ * Real.sqrt N := by positivity
  have hstrict : 8 * σ ^ 2 * N + σ * Real.sqrt N < 81 * σ ^ 2 * N := by
    have hlt : σ * Real.sqrt N < 73 * σ ^ 2 * N := by
      have h1 : σ * Real.sqrt N ≤ σ * N := mul_le_mul_of_nonneg_left hsqrtN_le_N hσ0.le
      have h2 : σ * N < 73 * σ ^ 2 * N := by nlinarith [hσ, hN, hσ0]
      linarith
    nlinarith
  have hcmp : 1 / (81 * σ ^ 2 * N) < 1 / (8 * σ ^ 2 * N + σ * Real.sqrt N) :=
    one_div_lt_one_div_of_lt hden2 hstrict
  linarith

/-- Converts the given bound with exponent `1 / 2 + C / sqrt (log N)` into a bound with exponent
`1 / 2 + ε` for every `N >= max N₀ 2`, assuming the exponent correction is at most `ε` from
`N₀` onward. This is a conditional cost comparison associated with Theorems 1 and 9 of
[ChildsEtAl2007]. -/
theorem cost_half_add_eps (cost : ℕ → ℝ) {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ N : ℕ, 2 ≤ N →
      cost N ≤ c * (N : ℝ) ^ ((1 : ℝ) / 2 + C / Real.sqrt (Real.log (N : ℝ))))
    (ε : ℝ) (hε : 0 < ε) (N₀ : ℕ)
    (hNε : ∀ N : ℕ, N₀ ≤ N → C / Real.sqrt (Real.log (N : ℝ)) ≤ ε) :
    ∀ N : ℕ, max N₀ 2 ≤ N →
      cost N ≤ c * (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  intro N hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hcost := hbound N hN2
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    linarith
  have hexp : (1 : ℝ) / 2 + C / Real.sqrt (Real.log (N : ℝ)) ≤ (1 : ℝ) / 2 + ε := by
    have := hNε N hN0
    linarith
  have hpow : (N : ℝ) ^ ((1 : ℝ) / 2 + C / Real.sqrt (Real.log (N : ℝ)))
      ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hexp
  calc cost N ≤ c * (N : ℝ) ^ ((1 : ℝ) / 2 + C / Real.sqrt (Real.log (N : ℝ))) := hcost
    _ ≤ c * (N : ℝ) ^ ((1 : ℝ) / 2 + ε) :=
        mul_le_mul_of_nonneg_left hpow hc.le

/-- For `N > 1` and `C > 0`, the square root of `N` is at most `N^(1 / 2 + C / sqrt (log N))`.
This is a scalar comparison associated with the cost scales in Theorems 1 and 9 of
[ChildsEtAl2007]. -/
theorem sqrt_le_rpow_add {N : ℝ} (hN : 1 < N) {C : ℝ} (hC : 0 < C) :
    Real.sqrt N ≤ N ^ ((1 : ℝ) / 2 + C / Real.sqrt (Real.log N)) := by
  rw [Real.sqrt_eq_rpow]
  apply Real.rpow_le_rpow_of_exponent_le hN.le
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hs : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hlog
  have hnonneg : 0 ≤ C / Real.sqrt (Real.log N) := (div_pos hC hs).le
  linarith

namespace NandTreeData

/-- The height of a descendant is at most the height of its subtree root. -/
theorem inSubtree_height_le (D : NandTreeData V) {p v : V} (h : D.InSubtree p v) :
    D.height v ≤ D.height p := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans (Nat.le_of_lt (D.height_lt hbc)) ih

/-- A vertex in the subtree of `p` is either `p` itself or has a parent that also lies in that
subtree. -/
theorem inSubtree_tail (D : NandTreeData V) {p v : V} (h : D.InSubtree p v) :
    v = p ∨ ∃ q, D.InSubtree p q ∧ D.parent v = some q := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨q, hpq, hqv⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨q, hpq, hqv⟩

/-- The parent of a descendant other than the subtree root remains in the same subtree. -/
theorem inSubtree_parent (D : NandTreeData V) {p v c : V} (h : D.InSubtree p c)
    (hc : D.parent c = some v) (hne : c ≠ p) : D.InSubtree p v := by
  rcases D.inSubtree_tail h with rfl | ⟨q, hpq, hqc⟩
  · exact absurd rfl hne
  · have : some v = some q := by rw [← hc, hqc]
    have hvq : v = q := Option.some.inj this
    subst hvq
    exact hpq

/-- If two vertices have a common descendant, then one belongs to the subtree rooted at the
other. -/
theorem inSubtree_comparable (D : NandTreeData V) {a b u : V}
    (ha : D.InSubtree a u) (hb : D.InSubtree b u) :
    D.InSubtree a b ∨ D.InSubtree b a := by
  have key : ∀ u, D.InSubtree a u → ∀ b, D.InSubtree b u →
      D.InSubtree a b ∨ D.InSubtree b a := by
    intro u hau
    induction hau with
    | refl =>
        intro b hb
        exact Or.inr hb
    | tail ha1 hstep ih =>
        rename_i u1 c
        intro b hb
        rcases Relation.ReflTransGen.cases_tail hb with rfl | ⟨u2, hb2, hstep2⟩
        · exact Or.inl (D.inSubtree_trans ha1 (D.inSubtree_child hstep))
        · have hsame : some u2 = some u1 := by
            rw [← hstep2, hstep]
          have hu12 : u2 = u1 := Option.some.inj hsame
          subst hu12
          exact ih b hb2
  exact key u ha b hb

/-- A descendant distinct from the subtree root has strictly smaller height. -/
theorem inSubtree_height_lt_of_ne (D : NandTreeData V) {p v : V}
    (h : D.InSubtree p v) (hne : v ≠ p) : D.height v < D.height p := by
  have hle := D.inSubtree_height_le h
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    have key : ∀ w : V, D.InSubtree p w → D.height w = D.height p → w = p := by
      intro w hw
      induction hw with
      | refl => intro _; rfl
      | tail h1 hstep ih =>
          intro hweq
          exfalso
          have hlt' := D.height_lt hstep
          have hle' := D.inSubtree_height_le h1
          omega
    exact hne (key v h heq)

/-- Mutual subtree membership forces two vertices to be equal. -/
theorem inSubtree_antisymm (D : NandTreeData V) {a b : V} (hab : D.InSubtree a b)
    (hba : D.InSubtree b a) : a = b := by
  by_contra hne
  have h1 := D.inSubtree_height_lt_of_ne hab (Ne.symm hne)
  have h2 := D.inSubtree_height_lt_of_ne hba hne
  omega

/-- When `v` has parent `p`, expands its weighted adjacency action as the weighted amplitude at
`p` plus the sum of weighted child amplitudes. -/
theorem ham_eq_of_parent (D : NandTreeData V) {a : V → ℝ} {v p : V}
    (hp : D.parent v = some p) :
    D.ham a v = D.weight p v * a p +
      ∑ x : V, if D.parent x = some v then D.weight v x * a x else 0 := by
  unfold NandTreeData.ham
  rw [hp]

/-- At a vertex without a parent, the weighted adjacency action is the sum of its weighted child
amplitudes. -/
theorem ham_eq_of_parent_none (D : NandTreeData V) {a : V → ℝ} {v : V}
    (hp : D.parent v = none) :
    D.ham a v = ∑ x : V, if D.parent x = some v then D.weight v x * a x else 0 := by
  unfold NandTreeData.ham
  rw [hp]
  exact zero_add _

/-- The weighted adjacency action is additive in the amplitude vector. -/
theorem ham_add (D : NandTreeData V) (a b : V → ℝ) (v : V) :
    D.ham (a + b) v = D.ham a v + D.ham b v := by
  classical
  have hsum : (∑ x : V, if D.parent x = some v then D.weight v x * (a x + b x) else 0)
      = (∑ x : V, if D.parent x = some v then D.weight v x * a x else 0)
        + (∑ x : V, if D.parent x = some v then D.weight v x * b x else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : D.parent x = some v
    · rw [if_pos hx, if_pos hx, if_pos hx, mul_add]
    · rw [if_neg hx, if_neg hx, if_neg hx, add_zero]
  rcases hpar : D.parent v with _ | p
  · rw [D.ham_eq_of_parent_none hpar, D.ham_eq_of_parent_none hpar,
        D.ham_eq_of_parent_none hpar]
    simp only [Pi.add_apply]
    exact hsum
  · rw [D.ham_eq_of_parent hpar, D.ham_eq_of_parent hpar, D.ham_eq_of_parent hpar]
    simp only [Pi.add_apply]
    rw [hsum, mul_add]
    ring

/-- The weighted adjacency action of the zero amplitude vector vanishes at every vertex. -/
theorem ham_zero (D : NandTreeData V) (v : V) : D.ham (fun _ => 0) v = 0 := by
  have h := D.ham_smul 0 (fun _ => (1 : ℝ)) v
  simpa using! h

/-- The weighted adjacency action commutes with a finite sum of amplitude vectors. -/
theorem ham_sum (D : NandTreeData V) {ι : Type*} (s : Finset ι) (f : ι → V → ℝ)
    (v : V) :
    D.ham (fun u => ∑ i ∈ s, f i u) v = ∑ i ∈ s, D.ham (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using D.ham_zero v
  | insert a s ha ih =>
      have hsplit : (fun u => ∑ i ∈ insert a s, f i u)
          = (f a + fun u => ∑ i ∈ s, f i u) := by
        funext u
        rw [Finset.sum_insert ha, Pi.add_apply]
      rw [hsplit, D.ham_add, ih, Finset.sum_insert ha]

end NandTreeData

/-- Bounds `1 + ∑ i, s i * σ i / sqrt sp` by `sqrt sp * σp` when the nonnegative sizes sum to
positive `sp`, each `σ i <= σmax`, and `1 / sqrt sp + σmax <= σp`. This is a scalar norm
estimate associated with Lemma 4 of [ChildsEtAl2007]. -/
theorem lemma4_norm_bound {sp σp σmax : ℝ} {ι : Type*} [Fintype ι]
    (s σ : ι → ℝ) (hsp : 0 < sp) (hs : ∀ i, 0 ≤ s i)
    (hσmax : ∀ i, σ i ≤ σmax) (hsum : ∑ i, s i = sp)
    (hpath : 1 / Real.sqrt sp + σmax ≤ σp) :
    1 + ∑ i, s i * σ i / Real.sqrt sp ≤ Real.sqrt sp * σp := by
  have hspos : 0 < Real.sqrt sp := Real.sqrt_pos.mpr hsp
  have hstep1 : ∑ i, s i * σ i / Real.sqrt sp ≤ Real.sqrt sp * σmax := by
    have hle : ∑ i, s i * σ i / Real.sqrt sp ≤ ∑ i, s i * σmax / Real.sqrt sp := by
      apply Finset.sum_le_sum
      intro i _
      apply div_le_div_of_nonneg_right _ hspos.le
      exact mul_le_mul_of_nonneg_left (hσmax i) (hs i)
    have heq : ∑ i, s i * σmax / Real.sqrt sp = Real.sqrt sp * σmax := by
      have h1 : ∀ i, s i * σmax / Real.sqrt sp
          = s i * σmax * (Real.sqrt sp)⁻¹ := fun i => div_eq_mul_inv ..
      simp_rw [h1]
      rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
      have hspdiv : sp * (Real.sqrt sp)⁻¹ = Real.sqrt sp := by
        rw [← div_eq_mul_inv, div_eq_iff hspos.ne']
        exact (Real.mul_self_sqrt hsp.le).symm
      calc (sp * σmax) * (Real.sqrt sp)⁻¹
          = σmax * (sp * (Real.sqrt sp)⁻¹) := by ring
        _ = σmax * Real.sqrt sp := by rw [hspdiv]
        _ = Real.sqrt sp * σmax := by ring
    linarith
  have hstep2 : 1 + Real.sqrt sp * σmax ≤ Real.sqrt sp * σp := by
    have hmul := mul_le_mul_of_nonneg_left hpath hspos.le
    have hsimp : Real.sqrt sp * (1 / Real.sqrt sp + σmax) = 1 + Real.sqrt sp * σmax := by
      rw [mul_add]
      congr 1
      rw [mul_one_div, div_self hspos.ne']
    linarith
  linarith

/-- Under the stated tail adjacency, weight, and root amplitude conditions, extends a unit
squared norm vector supported in the root subtree and having zero energy there to a global
zero energy vector, as a component associated with Theorem 2 of [ChildsEtAl2007]. The
extension preserves the subtree amplitudes, has the specified values at the two tail
vertices, and has normalized absolute amplitude at least `1 / sqrt 2` at `root''`. -/
theorem theorem2_tail_extension (D : NandTreeData V) {a : V → ℝ}
    (hzero : ∀ v, D.InSubtree D.root v → D.ham a v = 0)
    (hsupp : ∀ v, ¬ D.InSubtree D.root v → a v = 0)
    (hnorm : ∑ v : V, (a v) ^ 2 = 1)
    (hnoextra : ∀ x, D.parent x = some D.root'' → x = D.root')
    (hwr : D.weight D.root D.root' = 1)
    (hwpos : 0 < D.weight D.root' D.root'')
    (hamp : 1 ≤ |a D.root| / D.weight D.root' D.root'') :
    ∃ b : V → ℝ,
      (∀ v, D.ham b v = 0) ∧
      (∀ v, D.InSubtree D.root v → b v = a v) ∧
      b D.root' = 0 ∧
      b D.root'' = -(a D.root) / D.weight D.root' D.root'' ∧
      1 / Real.sqrt 2 ≤ |b D.root''| / Real.sqrt (∑ v : V, (b v) ^ 2) := by
  classical
  have hroot'_not : ¬ D.InSubtree D.root D.root' := by
    intro h
    have hle := D.inSubtree_height_le h
    have hlt := D.height_lt D.parent_root
    omega
  have hroot''_not : ¬ D.InSubtree D.root D.root'' := by
    intro h
    have hle := D.inSubtree_height_le h
    have hlt1 := D.height_lt D.parent_root
    have hlt2 := D.height_lt D.parent_root'
    omega
  have hne' : D.root' ≠ D.root'' := by
    intro h
    have hlt := D.height_lt D.parent_root'
    rw [h] at hlt
    omega
  let b : V → ℝ := fun u =>
    if u = D.root'' then -(a D.root) / D.weight D.root' D.root''
    else if D.InSubtree D.root u then a u
    else 0
  have hb_def : ∀ u, b u =
      (if u = D.root'' then -(a D.root) / D.weight D.root' D.root''
       else if D.InSubtree D.root u then a u
       else 0) := fun u => rfl
  have hb_agree : ∀ v, D.InSubtree D.root v → b v = a v := by
    intro v hv
    have hv'' : v ≠ D.root'' := by
      intro hh
      exact hroot''_not (hh ▸ hv)
    rw [hb_def v, if_neg hv'', if_pos hv]
  have hb_root' : b D.root' = 0 := by
    rw [hb_def D.root', if_neg hne', if_neg hroot'_not]
  have hb_root'' : b D.root'' = -(a D.root) / D.weight D.root' D.root'' := by
    rw [hb_def D.root'', if_pos rfl]
  have hb_out : ∀ v, ¬ D.InSubtree D.root v → v ≠ D.root'' → b v = 0 := by
    intro v hv hv''
    rw [hb_def v, if_neg hv'', if_neg hv]

  have hham'' : D.ham b D.root'' = 0 := by
    rw [D.ham_eq_of_parent_none D.parent_root'']
    have hsum : (∑ x : V, if D.parent x = some D.root'' then
        D.weight D.root'' x * b x else 0) = 0 := by
      refine Finset.sum_eq_zero (fun x _ => ?_)
      by_cases hx : D.parent x = some D.root''
      · rw [if_pos hx, hnoextra x hx, hb_root', mul_zero]
      · rw [if_neg hx]
    rw [hsum]

  have hham' : D.ham b D.root' = 0 := by
    rw [D.ham_eq_of_parent D.parent_root']
    have hsum : (∑ x : V, if D.parent x = some D.root' then
        D.weight D.root' x * b x else 0) = D.weight D.root' D.root * a D.root := by
      have hsingle : (∑ x : V, if D.parent x = some D.root' then
          D.weight D.root' x * b x else 0)
          = (if D.parent D.root = some D.root' then
              D.weight D.root' D.root * b D.root else 0) := by
        refine Finset.sum_eq_single D.root ?_ ?_
        · intro u _ hune
          by_cases hx : D.parent u = some D.root'
          · rw [if_pos hx]
            have hnotin : ¬ D.InSubtree D.root u := by
              intro hsub
              rcases D.inSubtree_tail hsub with rfl | ⟨q, hq, hqu⟩
              · exact hune rfl
              · rw [hx] at hqu
                have hq' : q = D.root' := Option.some.inj hqu.symm
                subst hq'
                exact hroot'_not hq
            have hune'' : u ≠ D.root'' := by
              intro hh
              rw [hh] at hx
              rw [D.parent_root''] at hx
              cases hx
            rw [hb_out u hnotin hune'', mul_zero]
          · rw [if_neg hx]
        · intro h
          exact absurd (Finset.mem_univ D.root) h
      rw [hsingle, if_pos D.parent_root, hb_agree D.root (D.inSubtree_refl D.root)]
    rw [hsum]
    have hw1 : D.weight D.root'' D.root' = D.weight D.root' D.root'' := D.weight_symm _ _
    have hwroot : D.weight D.root' D.root = 1 := by rw [D.weight_symm]; exact hwr
    have hwne : D.weight D.root' D.root'' ≠ 0 := ne_of_gt hwpos
    have hprod : D.weight D.root' D.root'' * b D.root'' = -(a D.root) := by
      rw [hb_root'', div_eq_mul_inv, ← mul_assoc,
          mul_comm (D.weight D.root' D.root'') (-(a D.root)), mul_assoc,
          mul_inv_cancel₀ hwne, mul_one]
    rw [hw1, hprod, hwroot]
    ring

  have hham_root : D.ham b D.root = 0 := by
    have hz := hzero D.root (D.inSubtree_refl D.root)
    rw [D.ham_eq_of_parent D.parent_root] at hz
    rw [D.ham_eq_of_parent D.parent_root]
    have hsum : (∑ x : V, if D.parent x = some D.root then
        D.weight D.root x * b x else 0)
        = (∑ x : V, if D.parent x = some D.root then
            D.weight D.root x * a x else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : D.parent x = some D.root
      · rw [if_pos hx, if_pos hx, hb_agree x (D.inSubtree_child hx)]
      · rw [if_neg hx, if_neg hx]
    rw [hsum]
    rw [hsupp D.root' hroot'_not, mul_zero, zero_add] at hz
    rw [hb_root', mul_zero, zero_add]
    exact hz

  have hham_in : ∀ v, D.InSubtree D.root v → v ≠ D.root → D.ham b v = 0 := by
    intro v hsub hvr
    have hz := hzero v hsub
    rcases D.inSubtree_tail hsub with rfl | ⟨q, hq, hqv⟩
    · exact absurd rfl hvr
    · rw [D.ham_eq_of_parent hqv] at hz
      rw [D.ham_eq_of_parent hqv]
      have hbq : b q = a q := hb_agree q hq
      have hsum : (∑ x : V, if D.parent x = some v then
          D.weight v x * b x else 0)
          = (∑ x : V, if D.parent x = some v then
              D.weight v x * a x else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : D.parent x = some v
        · rw [if_pos hx, if_pos hx,
              hb_agree x (D.inSubtree_trans hsub (D.inSubtree_child hx))]
        · rw [if_neg hx, if_neg hx]
      rw [hbq, hsum]
      exact hz

  have hham_out : ∀ v, ¬ D.InSubtree D.root v → v ≠ D.root' → v ≠ D.root'' →
      D.ham b v = 0 := by
    intro v hsub hv' hv''
    have hb_parent : ∀ q, D.parent v = some q → b q = 0 := by
      intro q hqv
      have hq_notin : ¬ D.InSubtree D.root q := by
        intro hqin
        by_cases hvroot : v = D.root
        · exact hsub (hvroot ▸ D.inSubtree_refl D.root)
        · exact hsub (D.inSubtree_trans hqin (D.inSubtree_child hqv))
      have hq_ne'' : q ≠ D.root'' := by
        intro hh
        rw [hh] at hqv
        exact hv' (hnoextra v hqv)
      exact hb_out q hq_notin hq_ne''
    have hsum : (∑ x : V, if D.parent x = some v then
        D.weight v x * b x else 0) = 0 := by
      refine Finset.sum_eq_zero (fun x _ => ?_)
      by_cases hx : D.parent x = some v
      · rw [if_pos hx]
        have hx_notin : ¬ D.InSubtree D.root x := by
          intro hxin
          by_cases hxroot : x = D.root
          · subst hxroot
            rw [D.parent_root] at hx
            exact hv' (Option.some.inj hx.symm)
          · exact hsub (D.inSubtree_parent hxin hx hxroot)
        have hxne'' : x ≠ D.root'' := by
          intro hh
          rw [hh] at hx
          rw [D.parent_root''] at hx
          cases hx
        rw [hb_out x hx_notin hxne'', mul_zero]
      · rw [if_neg hx]
    cases hpar : D.parent v with
    | none => rw [D.ham_eq_of_parent_none hpar, hsum]
    | some q => rw [D.ham_eq_of_parent hpar, hb_parent q hpar, mul_zero, zero_add, hsum]

  have hnorm_b : ∑ v : V, (b v) ^ 2 = 1 + (b D.root'') ^ 2 := by
    have hsplit : ∑ v : V, (b v) ^ 2
        = (∑ v ∈ Finset.univ.filter (fun v => D.InSubtree D.root v), (b v) ^ 2)
          + (∑ v ∈ Finset.univ.filter (fun v => ¬ D.InSubtree D.root v),
              (b v) ^ 2) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun v => D.InSubtree D.root v) (fun v => (b v) ^ 2)]
    have hsupp_b : ∑ v ∈ Finset.univ.filter (fun v => ¬ D.InSubtree D.root v),
        (b v) ^ 2 = (b D.root'') ^ 2 := by
      refine Finset.sum_eq_single D.root'' ?_ ?_
      · intro u hu hune
        rw [Finset.mem_filter] at hu
        rw [hb_out u hu.2 hune]
        ring
      · intro h
        exfalso
        apply h
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hroot''_not⟩
    have hin : ∑ v ∈ Finset.univ.filter (fun v => D.InSubtree D.root v),
        (b v) ^ 2 = 1 := by
      have h1 : ∑ v ∈ Finset.univ.filter (fun v => D.InSubtree D.root v),
          (b v) ^ 2
          = ∑ v ∈ Finset.univ.filter (fun v => D.InSubtree D.root v),
              (a v) ^ 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.mem_filter] at hv
        rw [hb_agree v hv.2]
      have h2 : ∑ v ∈ Finset.univ.filter (fun v => D.InSubtree D.root v),
          (a v) ^ 2 = ∑ v : V, (a v) ^ 2 := by
        refine Finset.sum_subset ?_ ?_
        · intro x _
          exact Finset.mem_univ x
        · intro v _ hv
          rw [Finset.mem_filter] at hv
          rw [hsupp v (by simpa using hv)]
          ring
      rw [h1, h2, hnorm]
    rw [hsplit, hsupp_b, hin]
  refine ⟨b, ?_, hb_agree, hb_root', hb_root'', ?_⟩
  · intro v
    by_cases hv'' : v = D.root''
    · subst hv''
      exact hham''
    · by_cases hv' : v = D.root'
      · subst hv'
        exact hham'
      · by_cases hvr : v = D.root
        · subst hvr
          exact hham_root
        · by_cases hsub : D.InSubtree D.root v
          · exact hham_in v hsub hvr
          · exact hham_out v hsub hv' hv''
  · have habs : 1 ≤ |b D.root''| := by
      have hwne : D.weight D.root' D.root'' ≠ 0 := ne_of_gt hwpos
      rw [hb_root'', abs_div, abs_neg, abs_of_pos hwpos]
      exact hamp
    have hxpos : 0 < |b D.root''| := lt_of_lt_of_le zero_lt_one habs
    have hle : (1 : ℝ) ≤ |b D.root''| ^ 2 := by
      have h0 : (0 : ℝ) ≤ |b D.root''| := abs_nonneg _
      nlinarith [habs, h0]
    have hratio := overlap_ratio_ge_inv_sqrt_two (x := |b D.root''|) (y := (1 : ℝ))
      hxpos zero_le_one hle
    rw [hnorm_b, ← sq_abs]
    exact hratio

/-- For positive `sp` and `sv`, the square of the quarter power `(sv / sp)^(1 / 4)` equals `sqrt
(sv / sp)`. This is a scalar weight identity associated with Lemma 4 of [ChildsEtAl2007]. -/
theorem weight_sq_eq {sp sv : ℝ} (hsp : 0 < sp) (hsv : 0 < sv) :
    ((sv / sp) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (sv / sp) := by
  have hpos : 0 < sv / sp := div_pos hsv hsp
  rw [pow_two, ← Real.rpow_add hpos]
  have h : (1 / 4 : ℝ) + 1 / 4 = 1 / 2 := by norm_num
  rw [h, ← Real.sqrt_eq_rpow]

/-- For positive sizes, if `hpv = (sv / sp)^(1 / 4)` and `hvc` is at least `(sc / sv)^(1 / 4)`,
then `hpv^2 / hvc^2 <= sv / (sqrt sp * sqrt sc)`. This is a scalar weight estimate
associated with Lemma 4 of [ChildsEtAl2007]. -/
theorem weight_ratio_sq_le {sp sv sc hpv hvc : ℝ} (hsp : 0 < sp) (hsv : 0 < sv)
    (hsc : 0 < sc) (hhpv : hpv = (sv / sp) ^ (1 / 4 : ℝ))
    (hhvc : (sc / sv) ^ (1 / 4 : ℝ) ≤ hvc) (_hhvc_pos : 0 < hvc) :
    hpv ^ 2 / hvc ^ 2 ≤ sv / (Real.sqrt sp * Real.sqrt sc) := by
  have hspos : 0 < Real.sqrt sp := Real.sqrt_pos.mpr hsp
  have hsvpos : 0 < Real.sqrt sv := Real.sqrt_pos.mpr hsv
  have hscpos : 0 < Real.sqrt sc := Real.sqrt_pos.mpr hsc
  have hhpv_pos : 0 < hpv := by rw [hhpv]; positivity
  have hApos : 0 < hpv ^ 2 := pow_pos hhpv_pos 2
  have hpv_sq : hpv ^ 2 = Real.sqrt sv / Real.sqrt sp := by
    rw [hhpv, weight_sq_eq hsp hsv, ← Real.sqrt_div hsv.le]
  have hvc_sq : Real.sqrt sc / Real.sqrt sv ≤ hvc ^ 2 := by
    have h1 : ((sc / sv) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt sc / Real.sqrt sv := by
      rw [weight_sq_eq hsv hsc, ← Real.sqrt_div hsc.le]
    rw [← h1]
    exact pow_le_pow_left₀ (by positivity) hhvc 2
  calc hpv ^ 2 / hvc ^ 2
      ≤ hpv ^ 2 / (Real.sqrt sc / Real.sqrt sv) := by
        exact div_le_div_of_nonneg_left hApos.le (div_pos hscpos hsvpos) hvc_sq
    _ = sv / (Real.sqrt sp * Real.sqrt sc) := by
        rw [hpv_sq]
        have hsp_ne : Real.sqrt sp ≠ 0 := ne_of_gt hspos
        have hsv_ne : Real.sqrt sv ≠ 0 := ne_of_gt hsvpos
        have hsc_ne : Real.sqrt sc ≠ 0 := ne_of_gt hscpos
        field_simp
        rw [Real.sq_sqrt hsv.le]

namespace NandTreeData

/-- If a subtree contains a vertex distinct from its root, then its root has a child. -/
theorem inSubtree_exists_child (D : NandTreeData V) {p v : V} (h : D.InSubtree p v) :
    v ≠ p → ∃ c, D.parent c = some p := by
  induction h with
  | refl => intro hne; exact absurd rfl hne
  | tail h1 hstep ih =>
      rename_i u1 c
      intro _
      by_cases hu : u1 = p
      · subst hu
        exact ⟨c, hstep⟩
      · exact ih hu

/-- The only vertex in a leaf's subtree is the leaf itself. -/
theorem inSubtree_eq_self_of_isLeaf (D : NandTreeData V) {p v : V}
    (hleaf : D.IsLeaf p) (h : D.InSubtree p v) : v = p := by
  by_contra hne
  obtain ⟨c, hc⟩ := D.inSubtree_exists_child h hne
  exact hleaf c hc

/-- If a vertex lies outside a subtree and has a parent, then its parent also lies outside that
subtree. -/
theorem not_inSubtree_parent (D : NandTreeData V) {p v q : V}
    (h : ¬ D.InSubtree p v) (hq : D.parent v = some q) : ¬ D.InSubtree p q := by
  intro hpq
  exact h (D.inSubtree_trans hpq (D.inSubtree_child hq))

/-- A vertex's parent does not belong to the subtree rooted at that vertex. -/
theorem parent_not_inSubtree (D : NandTreeData V) {p q : V} (hpq : D.parent p = some q) :
    ¬ D.InSubtree p q := by
  intro h
  have h1 := D.inSubtree_height_le h
  have h2 := D.height_lt hpq
  omega

end NandTreeData

/-- For a leaf `p` with `1 / sqrt (D.sz p) <= D.sigmaMinus p`, constructs a vector supported in
its subtree with amplitude one at `p` and zero weighted adjacency action throughout that
subtree, as the leaf component associated with Lemma 4 of [ChildsEtAl2007]. Its squared norm
is at most `sqrt (D.sz p) * D.sigmaMinus p`. -/
theorem lemma4_leaf_exists (D : NandTreeData V) {p : V} (hleaf : D.IsLeaf p)
    (hσ : 1 / Real.sqrt (D.sz p : ℝ) ≤ D.sigmaMinus p) :
    ∃ a : V → ℝ,
      (∀ v, D.InSubtree p v → D.ham a v = 0) ∧
      (∀ v, ¬ D.InSubtree p v → a v = 0) ∧
      a p = 1 ∧
      (∑ v : V, (a v) ^ 2) ≤ Real.sqrt (D.sz p : ℝ) * D.sigmaMinus p := by
  classical
  refine ⟨fun u => if u = p then 1 else 0, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hv' : v = p := D.inSubtree_eq_self_of_isLeaf hleaf hv
    rw [hv']
    have hnochild : (∑ x : V, if D.parent x = some p then
        D.weight p x * (if x = p then 1 else 0) else 0) = 0 := by
      refine Finset.sum_eq_zero (fun x _ => ?_)
      by_cases hx : D.parent x = some p
      · exact absurd hx (hleaf x)
      · rw [if_neg hx]
    cases hpar : D.parent p with
    | none => rw [D.ham_eq_of_parent_none hpar, hnochild]
    | some q =>
        rw [D.ham_eq_of_parent hpar, hnochild]
        have hq_not : ¬ D.InSubtree p q := D.parent_not_inSubtree hpar
        have hq_ne : q ≠ p := by
          intro h
          rw [h] at hq_not
          exact hq_not (D.inSubtree_refl p)
        rw [if_neg hq_ne, mul_zero, add_zero]
  · intro v hv
    have hvne : v ≠ p := by
      intro hh
      apply hv
      rw [hh]
      exact D.inSubtree_refl p
    show (if v = p then (1 : ℝ) else 0) = 0
    rw [if_neg hvne]
  · show (if p = p then (1 : ℝ) else 0) = 1
    rw [if_pos rfl]
  · have hsum : (∑ v : V, (if v = p then (1 : ℝ) else 0) ^ 2) = 1 := by
      trans (if p = p then (1 : ℝ) else 0) ^ 2
      · exact Finset.sum_eq_single p
          (fun b _ hb => by rw [if_neg hb, zero_pow (by norm_num)])
          (fun h => absurd (Finset.mem_univ p) h)
      · rw [if_pos rfl]; norm_num
    rw [hsum]
    have hspos : 0 < Real.sqrt (D.sz p : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast D.sz_pos p)
    calc (1 : ℝ) = Real.sqrt (D.sz p : ℝ) * (1 / Real.sqrt (D.sz p : ℝ)) := by
          rw [mul_one_div]
          exact (div_self hspos.ne').symm
      _ ≤ Real.sqrt (D.sz p : ℝ) * D.sigmaMinus p :=
          mul_le_mul_of_nonneg_left hσ hspos.le

/-- Combines the stated squared weight ratio bound and amplitude bound to obtain `hpv^2 / (hvc^2
* ã^2) <= sv * σc / sqrt sp`, under the listed positivity assumptions. This is a scalar
child contribution estimate associated with Lemma 4 of [ChildsEtAl2007]. -/
theorem child_term_bound {hpv hvc ã sp sv sc σc : ℝ}
    (hã : 0 < ã) (hhvc : 0 < hvc) (hsp : 0 < Real.sqrt sp)
    (hsc : 0 < Real.sqrt sc) (hsv : 0 ≤ sv)
    (hb : hpv ^ 2 / hvc ^ 2 ≤ sv / (Real.sqrt sp * Real.sqrt sc))
    (hσ : 1 ≤ ã ^ 2 * σc * Real.sqrt sc) :
    hpv ^ 2 / (hvc ^ 2 * ã ^ 2) ≤ sv * σc / Real.sqrt sp := by
  have hã2 : 0 < ã ^ 2 := by positivity
  have hhvc2 : 0 < hvc ^ 2 := by positivity
  have h1 : 1 / ã ^ 2 ≤ σc * Real.sqrt sc := by
    rw [div_le_iff₀ hã2]
    nlinarith [hσ]
  have hsplit : hpv ^ 2 / (hvc ^ 2 * ã ^ 2) = (hpv ^ 2 / hvc ^ 2) * (1 / ã ^ 2) := by
    field_simp
  rw [hsplit]
  have hstep := mul_le_mul hb h1 (by positivity)
    (div_nonneg hsv (by positivity))
  calc (hpv ^ 2 / hvc ^ 2) * (1 / ã ^ 2)
      ≤ (sv / (Real.sqrt sp * Real.sqrt sc)) * (σc * Real.sqrt sc) := hstep
    _ = sv * σc / Real.sqrt sp := by
        field_simp

namespace NandTreeData

/-- Setting the parent amplitude to one and rescaling a vector supported in a chosen child's
subtree makes the weighted adjacency action vanish at the intermediate vertex. This
component associated with Lemma 4 of [ChildsEtAl2007] uses nonzero chosen child amplitude
and edge weight, with the scaling factor specified in the statement. -/
theorem construction_vertex_energy (D : NandTreeData V) {p v cv : V} {ã : V → ℝ}
    (hpv : D.parent v = some p) (hvcv : D.parent cv = some v)
    (hweight : D.weight v cv ≠ 0) (hãcv : ã cv ≠ 0)
    (hsupp : ∀ x, ¬ D.InSubtree cv x → ã x = 0) :
    D.ham (fun u => if u = p then 1
      else (-(D.weight p v) / (D.weight v cv * ã cv)) * ã u) v = 0 := by
  classical
  have hvp : v ≠ p := by
    intro h
    subst h
    exact absurd (D.height_lt hpv) (lt_irrefl _)
  have hcvp : cv ≠ p := by
    intro h
    subst h
    have h1 := D.height_lt hpv
    have h2 := D.height_lt hvcv
    omega
  have hcv_notin : ¬ D.InSubtree cv v := by
    intro h
    have h1 := D.inSubtree_height_le h
    have h2 := D.height_lt hvcv
    omega
  have hb_v : (if v = p then (1 : ℝ)
      else (-(D.weight p v) / (D.weight v cv * ã cv)) * ã v) = 0 := by
    rw [if_neg hvp, hsupp v hcv_notin, mul_zero]
  have hsum : (∑ x : V, if D.parent x = some v then
      D.weight v x * (if x = p then (1 : ℝ)
        else (-(D.weight p v) / (D.weight v cv * ã cv)) * ã x) else 0)
      = D.weight v cv * ((-(D.weight p v) / (D.weight v cv * ã cv)) * ã cv) := by
    rw [Finset.sum_eq_single cv]
    · rw [if_pos hvcv, if_neg hcvp]
    · intro x _ hxne
      by_cases hx : D.parent x = some v
      · rw [if_pos hx]
        have hx_notin : ¬ D.InSubtree cv x := by
          intro hsub
          rcases D.inSubtree_tail hsub with hxc | ⟨q, hq, hqx⟩
          · exact hxne hxc
          · have hqv : q = v := by
              rw [hx] at hqx
              exact Option.some.inj hqx.symm
            rw [hqv] at hq
            exact hcv_notin hq
        have hxp : x ≠ p := by
          intro h
          subst h
          have h1 := D.height_lt hx
          have h2 := D.height_lt hpv
          omega
        rw [if_neg hxp, hsupp x hx_notin, mul_zero, mul_zero]
      · rw [if_neg hx]
    · intro h
      exact absurd (Finset.mem_univ cv) h
  rw [D.ham_eq_of_parent hpv]
  have hbp : (if p = p then (1 : ℝ)
      else (-(D.weight p v) / (D.weight v cv * ã cv)) * ã p) = 1 := if_pos rfl
  rw [hbp, hsum]
  have hterm : D.weight v cv * ((-(D.weight p v) / (D.weight v cv * ã cv)) * ã cv)
      = -(D.weight p v) := by
    have hprod : D.weight v cv * ã cv ≠ 0 := mul_ne_zero hweight hãcv
    have hlam : (-(D.weight p v) / (D.weight v cv * ã cv)) * ã cv
        = -(D.weight p v) / D.weight v cv := by
      field_simp [hprod]
    rw [hlam]
    field_simp [hweight]
  rw [hterm]
  ring

end NandTreeData

/-- The nonnegative factor `sqrt (H v w * δ w / δ v)` associated with an ordered pair of
vertices. -/
noncomputable def perronFactor (H : V → V → ℝ) (δ : V → ℝ) (v w : V) : ℝ :=
  Real.sqrt (H v w * δ w / δ v)

/-- For symmetric nonnegative `H` and strictly positive `δ`, the product of the factors for `(v,
w)` and `(w, v)` equals `H v w`. This is the edge factorization component associated with
Claim 8 of [ChildsEtAl2007]. -/
theorem perronFactor_comp (H : V → V → ℝ) (δ : V → ℝ)
    (hsymm : ∀ v w, H v w = H w v)
    (hnonneg : ∀ v w, 0 ≤ H v w)
    (hδpos : ∀ v, 0 < δ v) :
    ∀ v w, perronFactor H δ v w * perronFactor H δ w v = H v w := by
  intro v w
  have hv : δ v ≠ 0 := ne_of_gt (hδpos v)
  have hw : δ w ≠ 0 := ne_of_gt (hδpos w)
  have ha : 0 ≤ H v w * δ w / δ v :=
    div_nonneg (mul_nonneg (hnonneg v w) (le_of_lt (hδpos w))) (le_of_lt (hδpos v))
  have hprod : (H v w * δ w / δ v) * (H w v * δ v / δ w) = H v w ^ 2 := by
    rw [hsymm w v]
    field_simp
  calc perronFactor H δ v w * perronFactor H δ w v
      = Real.sqrt ((H v w * δ w / δ v) * (H w v * δ v / δ w)) := by
        rw [perronFactor, perronFactor, Real.sqrt_mul ha]
    _ = Real.sqrt (H v w ^ 2) := by rw [hprod]
    _ = H v w := Real.sqrt_sq (hnonneg v w)

/-- If `δ` is a strictly positive eigenvector of a nonnegative `H` with eigenvalue `μ`, then
each row's sum of squared Perron factors equals `μ`. This is the row norm component
associated with Claim 8 of [ChildsEtAl2007]. -/
theorem perronFactor_row (H : V → V → ℝ) (δ : V → ℝ) (μ : ℝ)
    (hnonneg : ∀ v w, 0 ≤ H v w)
    (hδpos : ∀ v, 0 < δ v)
    (heig : ∀ v, ∑ w, H v w * δ w = μ * δ v) :
    ∀ v, ∑ w, (perronFactor H δ v w) ^ 2 = μ := by
  intro v
  have hv : δ v ≠ 0 := ne_of_gt (hδpos v)
  have hnn : ∀ w, 0 ≤ H v w * δ w / δ v := fun w =>
    div_nonneg (mul_nonneg (hnonneg v w) (le_of_lt (hδpos w))) (le_of_lt (hδpos v))
  have hterm : ∀ w, (perronFactor H δ v w) ^ 2 = H v w * δ w / δ v := by
    intro w
    rw [perronFactor, Real.sq_sqrt (hnn w)]
  simp_rw [hterm]
  rw [← Finset.sum_div, heig v]
  exact mul_div_cancel_right₀ μ hv

/-- For symmetric nonnegative `H` with a strictly positive eigenvector of eigenvalue one, the
oppositely directed Perron factors multiply to each matrix entry and every row's squared
factors sum to one. This is the normalized factorization associated with Claim 8 of
[ChildsEtAl2007]. -/
theorem perron_factorization_norm_one (H : V → V → ℝ) (δ : V → ℝ)
    (hsymm : ∀ v w, H v w = H w v)
    (hnonneg : ∀ v w, 0 ≤ H v w)
    (hδpos : ∀ v, 0 < δ v)
    (heig : ∀ v, ∑ w, H v w * δ w = δ v) :
    (∀ v w, perronFactor H δ v w * perronFactor H δ w v = H v w) ∧
    (∀ v, ∑ w, (perronFactor H δ v w) ^ 2 = 1) :=
  ⟨perronFactor_comp H δ hsymm hnonneg hδpos,
   perronFactor_row H δ 1 hnonneg hδpos (fun v => by simpa using heig v)⟩

/-- Every Perron factor is nonnegative, with no sign assumptions on its inputs. This is a
component associated with the factorization in Claim 8 of [ChildsEtAl2007]. -/
theorem perronFactor_nonneg (H : V → V → ℝ) (δ : V → ℝ) :
    ∀ v w, 0 ≤ perronFactor H δ v w :=
  fun v w => Real.sqrt_nonneg _

/-- For a positive energy eigenvector with nonzero amplitude at `v`, the stated nonpositive
child ratios and their bounds imply `0 < a p / a v <= y0 v * E`, as a local component
associated with Lemma 6 of [ChildsEtAl2007]. The coefficient `y0 v` is the specified
weighted child sum divided by the positive parent edge weight. -/
theorem lemma6_eval_false_branch (D : NandTreeData V) {a : V → ℝ} {E : ℝ}
    {v p : V} {y0 y1 : V → ℝ}
    (hpv : D.parent v = some p) (heig : ∀ w, D.ham a w = E * a w)
    (hE : 0 < E) (hpw : 0 < D.weight p v) (hav : a v ≠ 0)
    (hnonneg : ∀ c, D.parent c = some v → 0 ≤ D.weight v c)
    (hchild_ne : ∀ c, D.parent c = some v → a c / a v ≤ 0)
    (hchild_bd : ∀ c, D.parent c = some v → -(a c / a v) ≤ y1 c * E)
    (hy0 : y0 v = (1 + ∑ c : V, if D.parent c = some v then D.weight v c * y1 c else 0)
        / D.weight p v) :
    0 < a p / a v ∧ a p / a v ≤ y0 v * E := by
  classical
  have hkey : E * a v = D.weight p v * a p +
      ∑ c : V, if D.parent c = some v then D.weight v c * a c else 0 := by
    rw [← heig v, D.ham_eq_of_parent hpv]
  have hsumdiv : (∑ c : V, if D.parent c = some v then D.weight v c * a c else 0) / a v
      = ∑ c : V, if D.parent c = some v then D.weight v c * (a c / a v) else 0 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : D.parent c = some v
    · rw [if_pos h, if_pos h]
      field_simp
    · rw [if_neg h, if_neg h, zero_div]
  set S : ℝ := ∑ c : V, if D.parent c = some v then D.weight v c * (a c / a v) else 0
    with hS
  have hdiv : E = D.weight p v * (a p / a v) + S := by
    have h := congrArg (fun x => x / a v) hkey
    beta_reduce at h
    rw [add_div, hsumdiv] at h
    rw [mul_div_cancel_right₀ E hav, mul_div_assoc] at h
    exact h
  have hS_nonpos : S ≤ 0 := by
    rw [hS]
    apply Finset.sum_nonpos
    intro c _
    by_cases h : D.parent c = some v
    · rw [if_pos h]
      exact mul_nonpos_of_nonneg_of_nonpos (hnonneg c h) (hchild_ne c h)
    · rw [if_neg h]
  have hprod_pos : 0 < D.weight p v * (a p / a v) := by
    nlinarith [hdiv, hS_nonpos, hE]
  have hratio_pos : 0 < a p / a v := by
    by_contra hle
    have hle' : a p / a v ≤ 0 := by linarith
    have : D.weight p v * (a p / a v) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hpw.le hle'
    linarith
  have hS_low : -(∑ c : V,
      if D.parent c = some v then D.weight v c * y1 c * E else 0) ≤ S := by
    rw [hS, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro c _
    by_cases h : D.parent c = some v
    · rw [if_pos h, if_pos h]
      have hm := mul_le_mul_of_nonneg_left (hchild_bd c h) (hnonneg c h)
      nlinarith [hm]
    · rw [if_neg h, if_neg h]; norm_num
  have hupper : D.weight p v * (a p / a v) ≤
      (1 + ∑ c : V, if D.parent c = some v then D.weight v c * y1 c else 0) * E := by
    set T0 : ℝ := ∑ c : V, if D.parent c = some v then D.weight v c * y1 c else 0 with hT0
    have heq : (∑ c : V, if D.parent c = some v then D.weight v c * y1 c * E else 0)
        = T0 * E := by
      rw [hT0, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      split_ifs with h <;> ring
    have hS_low' : -T0 * E ≤ S := by
      have h := hS_low
      rw [heq] at h
      linarith
    have hEsub : D.weight p v * (a p / a v) = E - S := by linarith [hdiv]
    nlinarith [hEsub, hS_low']
  refine ⟨hratio_pos, ?_⟩
  rw [hy0, div_mul_eq_mul_div, le_div_iff₀ hpw]
  calc a p / a v * D.weight p v = D.weight p v * (a p / a v) := by ring
    _ ≤ _ := hupper

/-- If the local minus parameter increases by at least `1 / sqrt sc` and the local plus
parameter increases by at least `sv`, bounds the new `gammaV` by the old value minus the two
corresponding correction terms, for positive `σr`. This is a scalar induction estimate
associated with Lemma 6 of [ChildsEtAl2007]. -/
theorem gammaV_step {σr E σmd σpd σmv σpv sc sv : ℝ}
    (hσr : 0 < σr)
    (h1 : σmd + 1 / Real.sqrt sc ≤ σmv) (h2 : σpd + sv ≤ σpv) :
    gammaV σr σmv σpv E ≤
      gammaV σr σmd σpd E - Gamma σr ^ 2 * (1 / Real.sqrt sc)
        - E ^ 2 * (1 + GammaPrime σr) * sv := by
  unfold gammaV
  have hA : 0 ≤ Gamma σr ^ 2 := sq_nonneg _
  have hB : 0 ≤ E ^ 2 * (1 + GammaPrime σr) := by
    have h1' : 0 ≤ 1 + GammaPrime σr := by
      unfold GammaPrime
      linarith
    exact mul_nonneg (sq_nonneg E) h1'
  nlinarith [mul_le_mul_of_nonneg_left h1 hA,
             mul_le_mul_of_nonneg_left h2 hB]

/-- Combines the eigenvector equation and the stated lower bounds on false and true child
amplitude ratios to bound `-E * D.weight p v * (a p / a v)` from below, as a local component
associated with Lemma 6 of [ChildsEtAl2007]. The bound is the sum of `D.weight v c / y0 c`
over false children minus `E^2` times one plus the weighted `y1` sum over true children. -/
theorem lemma6_eval_true_step (D : NandTreeData V) {a : V → ℝ} {E : ℝ}
    {v p : V} {y0 y1 : V → ℝ}
    (hpv : D.parent v = some p) (heig : ∀ w, D.ham a w = E * a w)
    (hav : a v ≠ 0)
    (hy0pos : ∀ c, D.parent c = some v → D.eval c = false → 0 < y0 c)
    (hEpos : 0 < E)
    (hfalse : ∀ c, D.parent c = some v → D.eval c = false →
      1 / (y0 c * E) ≤ a c / a v)
    (htrue : ∀ c, D.parent c = some v → D.eval c = true →
      -(y1 c * E) ≤ a c / a v)
    (hnonneg : ∀ c, D.parent c = some v → 0 ≤ D.weight v c) :
    -E * D.weight p v * (a p / a v) ≥
      (∑ c : V, if D.parent c = some v ∧ D.eval c = false then
          D.weight v c / y0 c else 0)
        - E ^ 2 * (1 + ∑ c : V,
            if D.parent c = some v ∧ D.eval c = true then D.weight v c * y1 c else 0) := by
  classical
  have hkey : E * a v = D.weight p v * a p +
      ∑ c : V, if D.parent c = some v then D.weight v c * a c else 0 := by
    rw [← heig v, D.ham_eq_of_parent hpv]
  have hsumdiv : (∑ c : V, if D.parent c = some v then D.weight v c * a c else 0) / a v
      = ∑ c : V, if D.parent c = some v then D.weight v c * (a c / a v) else 0 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : D.parent c = some v
    · rw [if_pos h, if_pos h]; field_simp
    · rw [if_neg h, if_neg h, zero_div]
  set S : ℝ := ∑ c : V, if D.parent c = some v then D.weight v c * (a c / a v) else 0
    with hS
  have hdiv : E = D.weight p v * (a p / a v) + S := by
    have h := congrArg (fun x => x / a v) hkey
    beta_reduce at h
    rw [add_div, hsumdiv] at h
    rw [mul_div_cancel_right₀ E hav, mul_div_assoc] at h
    exact h
  have hpt : ∀ c : V, E * (if D.parent c = some v then
      D.weight v c * (a c / a v) else 0) ≥
      (if D.parent c = some v ∧ D.eval c = false then D.weight v c / y0 c else 0)
        - E ^ 2 * (if D.parent c = some v ∧ D.eval c = true then
            D.weight v c * y1 c else 0) := by
    intro c
    by_cases hc : D.parent c = some v
    · by_cases hev : D.eval c = false
      · rw [if_pos hc, if_pos ⟨hc, hev⟩, if_neg (by simp [hev])]
        have hy0c := hy0pos c hc hev
        have hbd := hfalse c hc hev
        have hmul : E * (1 / (y0 c * E)) ≤ E * (a c / a v) :=
          mul_le_mul_of_nonneg_left hbd (le_of_lt hEpos)
        have hEy : E * (1 / (y0 c * E)) = 1 / y0 c := by
          field_simp
        have hmul' := mul_le_mul_of_nonneg_left hmul (hnonneg c hc)
        have hleft : D.weight v c * (E * (1 / (y0 c * E))) = D.weight v c / y0 c := by
          rw [hEy]; ring
        nlinarith [hmul', hleft]
      · have hevtrue : D.eval c = true := by
          cases h : D.eval c <;> simp_all
        rw [if_pos hc, if_neg (by intro hh; exact hev hh.2), if_pos ⟨hc, hevtrue⟩]
        have hbd := htrue c hc hevtrue
        have hmul : E * (-(y1 c * E)) ≤ E * (a c / a v) :=
          mul_le_mul_of_nonneg_left hbd (le_of_lt hEpos)
        have hmul' := mul_le_mul_of_nonneg_left hmul (hnonneg c hc)
        nlinarith [hmul']
    · rw [if_neg hc, if_neg (by intro hh; exact hc hh.1),
            if_neg (by intro hh; exact hc hh.1)]
      simp
  have hES : E * S ≥
      (∑ c : V, if D.parent c = some v ∧ D.eval c = false then
          D.weight v c / y0 c else 0)
        - E ^ 2 * (∑ c : V,
            if D.parent c = some v ∧ D.eval c = true then D.weight v c * y1 c else 0) := by
    rw [hS, Finset.mul_sum]
    calc ∑ c : V, E * (if D.parent c = some v then D.weight v c * (a c / a v) else 0)
        ≥ ∑ c : V, ((if D.parent c = some v ∧ D.eval c = false then
              D.weight v c / y0 c else 0)
            - E ^ 2 * (if D.parent c = some v ∧ D.eval c = true then
                D.weight v c * y1 c else 0)) := Finset.sum_le_sum (fun c _ => hpt c)
      _ = (∑ c : V, if D.parent c = some v ∧ D.eval c = false then
              D.weight v c / y0 c else 0)
            - E ^ 2 * (∑ c : V,
                if D.parent c = some v ∧ D.eval c = true then
                  D.weight v c * y1 c else 0) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
  have hmain : -E * D.weight p v * (a p / a v) = E * S - E ^ 2 := by
    have hwp : D.weight p v * (a p / a v) = E - S := by linarith [hdiv]
    nlinarith [hwp]
  rw [hmain]
  nlinarith [hES]

/-- For quarter power weights determined by positive child sizes, the stated bounds on `y` and
the total child size imply `1 + ∑ i, h i * y i <= (1 + Γ') * sqrt sv`, assuming `sv >= 1`
and `Γ' >= 0`. This is a scalar coefficient estimate associated with Lemma 6 of
[ChildsEtAl2007]. -/
theorem coefficient_bound {sv Γ' : ℝ} {ι : Type*} [Fintype ι]
    (s y h : ι → ℝ) (hsv1 : 1 ≤ sv) (hΓ' : 0 ≤ Γ')
    (hspos : ∀ i, 0 < s i)
    (hh : ∀ i, h i = (s i / sv) ^ (1 / 4 : ℝ))
    (hy : ∀ i, y i ≤ h i * Real.sqrt (s i) * Γ')
    (hsum : ∑ i, s i ≤ sv) :
    1 + ∑ i, h i * y i ≤ (1 + Γ') * Real.sqrt sv := by
  have hsv0 : 0 < sv := by linarith
  have hsvp : 0 < Real.sqrt sv := Real.sqrt_pos.mpr hsv0
  have hterm : ∀ i, h i * y i ≤ Γ' * s i / Real.sqrt sv := by
    intro i
    have hsq : (h i) ^ 2 = Real.sqrt (s i) / Real.sqrt sv := by
      rw [hh i, pow_two, ← Real.rpow_add (div_pos (hspos i) hsv0)]
      norm_num
      rw [← Real.sqrt_eq_rpow, Real.sqrt_div (hspos i).le]
    have hhi_nonneg : 0 ≤ h i := by
      rw [hh i]
      exact Real.rpow_nonneg (div_pos (hspos i) hsv0).le _
    calc h i * y i ≤ h i * (h i * Real.sqrt (s i) * Γ') :=
          mul_le_mul_of_nonneg_left (hy i) hhi_nonneg
      _ = (h i) ^ 2 * Real.sqrt (s i) * Γ' := by ring
      _ = (Real.sqrt (s i) / Real.sqrt sv) * Real.sqrt (s i) * Γ' := by rw [hsq]
      _ = Γ' * s i / Real.sqrt sv := by
          rw [div_mul_eq_mul_div (Real.sqrt (s i)) (Real.sqrt sv) (Real.sqrt (s i)),
              Real.mul_self_sqrt (hspos i).le, div_mul_eq_mul_div, mul_comm (s i) Γ']
  have hsum_le : ∑ i, h i * y i ≤ Γ' * sv / Real.sqrt sv := by
    calc ∑ i, h i * y i ≤ ∑ i, Γ' * s i / Real.sqrt sv :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = Γ' * (∑ i, s i) / Real.sqrt sv := by
          rw [Finset.mul_sum, Finset.sum_div]
      _ ≤ Γ' * sv / Real.sqrt sv := by
          apply div_le_div_of_nonneg_right _ hsvp.le
          exact mul_le_mul_of_nonneg_left hsum hΓ'
  have hsvdiv : Γ' * sv / Real.sqrt sv = Γ' * Real.sqrt sv := by
    rw [div_eq_iff hsvp.ne', mul_assoc, Real.mul_self_sqrt hsv0.le]
  have hsp1 : 1 ≤ Real.sqrt sv := by
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt sv := Real.sqrt_le_sqrt hsv1
  have hlow : 1 + Γ' * Real.sqrt sv ≤ (1 + Γ') * Real.sqrt sv := by
    have hnonneg : 0 ≤ Γ' * (Real.sqrt sv - 1) := mul_nonneg hΓ' (by linarith)
    nlinarith [hnonneg]
  linarith [hsum_le, hsvdiv, hlow]

/-- Under the stated positivity conditions, a lower bound `-E * h * (αp / αv) >= γ / sqrt sv`
forces the reciprocal ratio to be negative and at least `-(h * sqrt sv / γ) * E`. This is a
scalar ratio estimate associated with Lemma 6 of [ChildsEtAl2007]. -/
theorem lemma6_eval_true_final {E h γ sv αp αv : ℝ}
    (hE : 0 < E) (hh : 0 < h) (hγ : 0 < γ) (hsv : 0 < sv)
    (hmain : -E * h * (αp / αv) ≥ γ / Real.sqrt sv) (hav : αv ≠ 0) :
    0 > αv / αp ∧ αv / αp ≥ -(h * Real.sqrt sv / γ) * E := by
  have hsvp : 0 < Real.sqrt sv := Real.sqrt_pos.mpr hsv
  have hc0 : 0 < γ / Real.sqrt sv := div_pos hγ hsvp
  set r : ℝ := αp / αv with hr
  have hEH : 0 < E * h := mul_pos hE hh
  have hmain' : -E * h * r ≥ γ / Real.sqrt sv := hmain
  have hrneg : r < 0 := by
    by_contra hnn
    have hnn' : 0 ≤ r := by linarith
    have hle : 0 ≤ E * h * r := mul_nonneg hEH.le hnn'
    have hneg : -E * h * r ≤ 0 := by nlinarith
    linarith [hmain', hc0, hneg]
  have havr : αv / αp = 1 / r := by
    rw [hr]; field_simp
  have hαv : αv / αp < 0 := by
    rw [havr]; exact div_neg_of_pos_of_neg one_pos hrneg
  refine ⟨hαv, ?_⟩
  rw [havr]
  set c : ℝ := γ / (Real.sqrt sv * E * h) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hbound : r ≤ -c := by
    have h1 : E * h * r ≤ -(γ / Real.sqrt sv) := by linarith [hmain']
    have h2 : r ≤ -(γ / Real.sqrt sv) / (E * h) := by
      rw [le_div_iff₀ hEH]
      linarith [h1]
    have heq : -(γ / Real.sqrt sv) / (E * h) = -c := by
      rw [hcdef]; field_simp
    rwa [heq] at h2
  set u : ℝ := -r with hudef
  have hu : 0 < u := by rw [hudef]; linarith
  have huc : c ≤ u := by rw [hudef]; linarith
  have h1r : 1 / r = -(1 / u) := by
    have hru : r = -u := by rw [hudef]; ring
    rw [hru]
    have hun : u ≠ 0 := ne_of_gt hu
    field_simp
  have hle : 1 / u ≤ 1 / c := one_div_le_one_div_of_le hcpos huc
  have hfin : 1 / r ≥ -1 / c := by
    rw [h1r, neg_div]
    exact neg_le_neg hle
  have heqc : -1 / c = -(h * Real.sqrt sv / γ) * E := by
    rw [hcdef]
    field_simp
  rwa [heqc] at hfin

end Qatlib.Papers.NANDFormula07.MainResults
