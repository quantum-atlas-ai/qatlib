/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Qatlib.Foundations.MixedFidelity.TraceNormRankBound

/-!
# Level-set matrices and fidelity bounds

This module constructs the level-set matrices `rho` and their explicit positive square roots
`sqrtRho` for the hidden nonlinear structures of [ChildsSchulmanVazirani2007]. It expresses
matrix traces in terms of level-set overlap counts and proves the codomain-size rank bound for
the square root.

The squared trace-norm fidelity is bounded using either the overlap second moment or the support
projector `suppProj`. Counting hypotheses on large overlaps then yield `lemma8` and `lemma9`;
the module also proves invariance under invertible relabeling of function values.

## Main statements

* `trace_rho_mul_re`: expresses a matrix overlap as a normalized sum of squared level-set
  intersections.
* `lemma8`: derives a squared-fidelity bound from a bound on large overlap pairs.
* `lemma9`: derives a squared-fidelity bound from a bound on rows containing a large overlap.
* `rho_comp_equiv`: proves invariance under codomain equivalences.

## References

* [Childs et al., 2007][ChildsSchulmanVazirani2007]
-/

namespace Qatlib.Papers.HiddenNonlin07.MainResults.LevelSetFidelity

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

set_option autoImplicit false

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The finite level set of `f` with value `y`. -/
def lset (f : X → Y) (y : Y) : Finset X := Finset.univ.filter (fun x => f x = y)

/-- The cardinality of the intersection of the level sets `lset f y` and `lset f' y'`. -/
def ovl (f f' : X → Y) (y y' : Y) : ℕ := (lset f y ∩ lset f' y').card

/-- Membership in `lset f y` is equivalent to the equation `f x = y`. -/
@[simp] theorem mem_lset {f : X → Y} {y : Y} {x : X} : x ∈ lset f y ↔ f x = y := by
  simp [lset]

/-- The level set containing a given input has positive cardinality. -/
theorem card_lset_pos (f : X → Y) (x : X) : 0 < (lset f (f x)).card :=
  Finset.card_pos.mpr ⟨x, by simp⟩

/-- The overlap of two level sets counts the inputs whose pair of function values equals `(y,
y')`. -/
theorem ovl_eq_card_filter (f f' : X → Y) (y y' : Y) :
    ovl f f' y y'
      = (Finset.univ.filter (fun x => (f x, f' x) = (y, y'))).card := by
  unfold ovl lset
  congr 1
  ext x
  simp [Finset.mem_inter, Finset.mem_filter, Prod.ext_iff]

/-- The level-set matrix with entry `1 / |X|` when the two function values agree and zero
otherwise. -/
noncomputable def rho (f : X → Y) : Matrix X X ℂ :=
  fun x x' => if f x = f x' then ((Fintype.card X : ℂ))⁻¹ else 0

/-- The complex-valued indicator of the level set `lset f y`. -/
def indL (f : X → Y) (y : Y) : X → ℂ := fun x => if f x = y then 1 else 0

/-- The inverse square root of the product of the domain cardinality and the cardinality of
`lset f y`. -/
noncomputable def wt (f : X → Y) (y : Y) : ℝ :=
  (Real.sqrt ((Fintype.card X : ℝ) * ((lset f y).card : ℝ)))⁻¹

/-- The blockwise square-root matrix of `rho f`, with entry `wt f (f x)` when the two function
values agree and zero otherwise. -/
noncomputable def sqrtRho (f : X → Y) : Matrix X X ℂ :=
  fun x x' => if f x = f x' then (wt f (f x) : ℂ) else 0

/-- The matrix `sqrtRho f` is the sum of the level-set indicator outer products weighted by `wt
f y`. -/
theorem sqrtRho_eq_sum (f : X → Y) :
    sqrtRho f = ∑ y, wt f y • Matrix.vecMulVec (indL f y) (star (indL f y)) := by
  ext x x'
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, sqrtRho,
    Complex.real_smul]
  by_cases h : f x = f x'
  · rw [if_pos h]
    have hsingle : (∑ y, ↑(wt f y) * (indL f y x * (star (indL f y)) x'))
        = ↑(wt f (f x)) * (indL f (f x) x * (star (indL f (f x))) x') := by
      refine Finset.sum_eq_single (f x) ?_ ?_
      · intro y _ hy
        have h0 : indL f y x = 0 := by simp [indL, Ne.symm hy]
        simp [h0]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    rw [hsingle]
    simp [indL, h]
  · rw [if_neg h]
    refine Eq.symm (Finset.sum_eq_zero (fun y _ => ?_))
    by_cases hy : f x = y
    · have hx' : indL f y x' = 0 := by
        simp only [indL]
        rw [if_neg (fun hc => h (hc.trans hy.symm).symm)]
      simp [hx']
    · have hy' : ¬(f x = y) := hy
      simp [indL, hy']

/-- The matrix `sqrtRho f` is positive semidefinite. -/
theorem sqrtRho_posSemidef (f : X → Y) : (sqrtRho f).PosSemidef := by
  rw [sqrtRho_eq_sum]
  refine Matrix.posSemidef_sum Finset.univ ?_
  intro y _
  exact (Matrix.posSemidef_vecMulVec_self_star (indL f y)).smul (a := wt f y) (by
    unfold wt; positivity)

/-- The matrix whose column indexed by `y` is the indicator of `lset f y`. -/
def preB (f : X → Y) : Matrix X Y ℂ := fun x y => indL f y x

/-- The matrix whose row indexed by `y` is the indicator of `lset f y` scaled by `wt f y`. -/
noncomputable def preC (f : X → Y) : Matrix Y X ℂ := fun y x => wt f y • indL f y x

/-- The level-set square-root matrix factors as `preB f * preC f`. -/
theorem sqrtRho_eq_mul (f : X → Y) : sqrtRho f = preB f * preC f := by
  ext x x'
  simp only [Matrix.mul_apply, preB, preC, sqrtRho, Complex.real_smul]
  by_cases h : f x = f x'
  · rw [if_pos h]
    have hsingle : (∑ y, indL f y x * (↑(wt f y) * indL f y x'))
        = indL f (f x) x * (↑(wt f (f x)) * indL f (f x) x') := by
      refine Finset.sum_eq_single (f x) ?_ ?_
      · intro y _ hy
        have h0 : indL f y x = 0 := by simp [indL, Ne.symm hy]
        simp [h0]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    rw [hsingle]
    simp [indL, h]
  · rw [if_neg h]
    refine Eq.symm (Finset.sum_eq_zero (fun y _ => ?_))
    by_cases hy : f x = y
    · have hx' : indL f y x' = 0 := by
        simp only [indL]
        rw [if_neg (fun hc => h (hc.trans hy.symm).symm)]
      simp [hx']
    · have hy' : ¬(f x = y) := hy
      simp [indL, hy']

/-- The rank of the level-set square-root matrix is at most the cardinality of the codomain. -/
theorem rank_sqrtRho_le (f : X → Y) : (sqrtRho f).rank ≤ Fintype.card Y := by
  rw [sqrtRho_eq_mul]
  exact (Matrix.rank_mul_le_left (preB f) (preC f)).trans (Matrix.rank_le_card_width _)

/-- The sum of a level-set indicator equals the complex cast of the level-set cardinality. -/
theorem sum_indL (f : X → Y) (y : Y) :
    (∑ z, indL f y z) = ((lset f y).card : ℂ) := by
  simp [indL, lset]

/-- Summing a fixed complex value times a level-set indicator multiplies that value by the
level-set cardinality. -/
theorem sum_indL_mul (f : X → Y) (y : Y) (c : ℂ) :
    (∑ z, indL f y z * c) = ((lset f y).card : ℂ) * c := by
  rw [← Finset.sum_mul, sum_indL]

/-- The square of `sqrtRho f` is `rho f`. -/
theorem sqrtRho_sq (f : X → Y) : sqrtRho f * sqrtRho f = rho f := by
  ext x x'
  rw [Matrix.mul_apply]
  simp only [rho]
  by_cases h : f x = f x'
  · rw [if_pos h]
    have hstep : ∀ z, sqrtRho f x z * sqrtRho f z x' =
        indL f (f x) z * (↑(wt f (f x)) * ↑(wt f (f x))) := by
      intro z
      by_cases hz : f z = f x
      · have hz' : f z = f x' := hz.trans h
        have hxz : f x = f z := hz.symm
        simp only [sqrtRho, indL]
        rw [if_pos hxz, if_pos hz', if_pos hz, hz]
        ring
      · have hzx : f z ≠ f x' := fun hc => hz (hc.trans h.symm)
        have hxz : f x ≠ f z := fun hc => hz hc.symm
        simp only [sqrtRho, indL]
        rw [if_neg hxz, if_neg hzx, if_neg hz]
        ring
    rw [Finset.sum_congr rfl (fun z _ => hstep z), sum_indL_mul]
    have hLX : (0 : ℝ) < (Fintype.card X : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨x⟩)
    have hL : (0 : ℝ) < ((lset f (f x)).card : ℝ) := by
      exact_mod_cast card_lset_pos f x
    have hreal : ((lset f (f x)).card : ℝ) * (wt f (f x) * wt f (f x))
        = (Fintype.card X : ℝ)⁻¹ := by
      unfold wt
      rw [← mul_inv, Real.mul_self_sqrt (le_of_lt (mul_pos hLX hL)), mul_inv]
      field_simp
    have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
    push_cast at hc
    simpa using hc
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun z _ => ?_)
    by_cases hz : f z = f x
    · have hzx : f z ≠ f x' := fun hc => h (hz.symm.trans hc)
      have hxz : f x = f z := hz.symm
      simp only [sqrtRho]
      rw [if_pos hxz, if_neg hzx]
      ring
    · have hxz : f x ≠ f z := fun hc => hz hc.symm
      simp [sqrtRho, hxz]

/-- The continuous functional calculus square root of `rho f` equals its explicit level-set
square-root matrix. -/
theorem cfc_sqrt_rho (f : X → Y) : CFC.sqrt (rho f) = sqrtRho f :=
  CFC.sqrt_unique (sqrtRho_sq f) (Matrix.PosSemidef.nonneg (sqrtRho_posSemidef f))

/-- The complex indicator that an input lies in both `lset f y` and `lset f' y'`. -/
def ind2 (f f' : X → Y) (y y' : Y) (x : X) : ℂ :=
  if f x = y ∧ f' x = y' then 1 else 0

/-- The complex cast of the overlap cardinality equals the sum of the joint level-set indicator. -/
theorem ovl_eq_sum (f f' : X → Y) (y y' : Y) :
    (ovl f f' y y' : ℂ) = ∑ x, ind2 f f' y y' x := by
  have hsum : (∑ x, ind2 f f' y y' x)
      = ((Finset.univ.filter (fun x => (f x, f' x) = (y, y'))).card : ℂ) := by
    simp only [ind2]
    rw [Finset.sum_boole]
    congr 1
  rw [ovl_eq_card_filter, hsum]

/-- A sum depending only on the pair `(f x, f' x)` can be grouped by that pair, with
multiplicities given by the level-set overlaps. -/
theorem sum_pair_fiber (f f' : X → Y) (h : Y → Y → ℂ) :
    (∑ x, h (f x) (f' x))
      = ∑ y, ∑ y', (ovl f f' y y' : ℂ) * h y y' := by
  have hx : ∀ x : X, h (f x) (f' x) = ∑ y, ∑ y', ind2 f f' y y' x * h y y' := by
    intro x
    have hinner : ∀ y : Y, (∑ y', ind2 f f' y y' x * h y y')
        = ind2 f f' y (f' x) x * h y (f' x) := by
      intro y
      have h0 : ∀ y' ∈ (Finset.univ : Finset Y), y' ≠ f' x →
          ind2 f f' y y' x * h y y' = 0 := by
        intro y' _ hy'
        simp only [ind2]
        rw [if_neg (fun hc => hy' hc.2.symm), zero_mul]
      have h1 : f' x ∉ (Finset.univ : Finset Y) →
          ind2 f f' y (f' x) x * h y (f' x) = 0 :=
        fun hnot => absurd (Finset.mem_univ _) hnot
      rw [Finset.sum_eq_single (f' x) h0 h1]
    rw [Finset.sum_congr rfl (fun y _ => hinner y)]
    have h0 : ∀ y ∈ (Finset.univ : Finset Y), y ≠ f x →
        ind2 f f' y (f' x) x * h y (f' x) = 0 := by
      intro y _ hy
      simp only [ind2]
      rw [if_neg (fun hc => hy hc.1.symm), zero_mul]
    have h1 : f x ∉ (Finset.univ : Finset Y) →
        ind2 f f' (f x) (f' x) x * h (f x) (f' x) = 0 :=
      fun hnot => absurd (Finset.mem_univ _) hnot
    rw [Finset.sum_eq_single (f x) h0 h1]
    have hind : ind2 f f' (f x) (f' x) x = 1 := by simp [ind2]
    rw [hind, one_mul]
  calc (∑ x, h (f x) (f' x))
      = ∑ x, ∑ y, ∑ y', ind2 f f' y y' x * h y y' :=
        Finset.sum_congr rfl (fun x _ => hx x)
    _ = ∑ y, ∑ y', ∑ x, ind2 f f' y y' x * h y y' := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ y, ∑ y', (∑ x, ind2 f f' y y' x) * h y y' := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        refine Finset.sum_congr rfl (fun y' _ => ?_)
        rw [Finset.sum_mul]
    _ = ∑ y, ∑ y', (ovl f f' y y' : ℂ) * h y y' := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        refine Finset.sum_congr rfl (fun y' _ => ?_)
        rw [← ovl_eq_sum]

/-- A diagonal entry of `rho f * rho f'` is the joint-level-set count at that input multiplied
by the inverse square of the domain size. -/
theorem entry_rho_mul (f f' : X → Y) (x : X) :
    (rho f * rho f') x x
      = (Fintype.card X : ℂ)⁻¹ * (Fintype.card X : ℂ)⁻¹ *
          (∑ z, (if f x = f z ∧ f' x = f' z then (1 : ℂ) else 0)) := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  simp only [rho]
  by_cases h1 : f x = f z
  · by_cases h2 : f' z = f' x
    · rw [if_pos h1, if_pos h2,
        if_pos (show f x = f z ∧ f' x = f' z from ⟨h1, h2.symm⟩)]
      ring
    · rw [if_neg h2,
        if_neg (show ¬(f x = f z ∧ f' x = f' z) from fun hh => h2 hh.2.symm)]
      ring
  · rw [if_neg h1,
      if_neg (show ¬(f x = f z ∧ f' x = f' z) from fun hh => h1 hh.1)]
    ring

/-- The trace of the product of two level-set matrices is the complex cast of the sum of squared
overlaps divided by the squared domain size. -/
theorem trace_rho_mul (f f' : X → Y) :
    (rho f * rho f').trace
      = ((((Fintype.card X : ℝ)⁻¹ ^ 2
          * (∑ y, ∑ y', (ovl f f' y y' : ℝ) ^ 2)) : ℝ) : ℂ) := by
  have hsum : (∑ x, ∑ z, (if f x = f z ∧ f' x = f' z then (1 : ℂ) else 0))
      = ∑ y, ∑ y', (ovl f f' y y' : ℂ) * (ovl f f' y y' : ℂ) := by
    have hinner : ∀ x, (∑ z, (if f x = f z ∧ f' x = f' z then (1 : ℂ) else 0))
        = (ovl f f' (f x) (f' x) : ℂ) := by
      intro x
      rw [ovl_eq_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      simp only [ind2]
      by_cases h1 : f x = f z
      · by_cases h2 : f' x = f' z
        · rw [if_pos ⟨h1, h2⟩, if_pos ⟨h1.symm, h2.symm⟩]
        · rw [if_neg (fun hh => h2 hh.2), if_neg (fun hh => h2 hh.2.symm)]
      · rw [if_neg (fun hh => h1 hh.1), if_neg (fun hh => h1 hh.1.symm)]
    rw [Finset.sum_congr rfl (fun x _ => hinner x)]
    exact sum_pair_fiber f f' (fun y y' => (ovl f f' y y' : ℂ))
  have ha : (∑ y, ∑ y', (ovl f f' y y' : ℂ) * (ovl f f' y y' : ℂ))
      = ((∑ y, ∑ y', (ovl f f' y y' : ℝ) ^ 2 : ℝ) : ℂ) := by
    push_cast
    simp [pow_two]
  have hb : (Fintype.card X : ℂ)⁻¹ * (Fintype.card X : ℂ)⁻¹
      = (((Fintype.card X : ℝ)⁻¹ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [pow_two]
  calc (rho f * rho f').trace
      = ∑ x, (rho f * rho f') x x := by simp [Matrix.trace]
    _ = ∑ x, (Fintype.card X : ℂ)⁻¹ * (Fintype.card X : ℂ)⁻¹ *
          (∑ z, (if f x = f z ∧ f' x = f' z then (1 : ℂ) else 0)) :=
        Finset.sum_congr rfl (fun x _ => entry_rho_mul f f' x)
    _ = (Fintype.card X : ℂ)⁻¹ * (Fintype.card X : ℂ)⁻¹ *
          ∑ x, ∑ z, (if f x = f z ∧ f' x = f' z then (1 : ℂ) else 0) := by
        rw [Finset.mul_sum]
    _ = (Fintype.card X : ℂ)⁻¹ * (Fintype.card X : ℂ)⁻¹ *
          ∑ y, ∑ y', (ovl f f' y y' : ℂ) * (ovl f f' y y' : ℂ) := by rw [hsum]
    _ = ((((Fintype.card X : ℝ)⁻¹ ^ 2
          * (∑ y, ∑ y', (ovl f f' y y' : ℝ) ^ 2)) : ℝ) : ℂ) := by
        rw [ha, hb, ← Complex.ofReal_mul]

/-- The real trace of the product of two level-set matrices is the sum of squared overlaps
divided by the squared domain size. -/
theorem trace_rho_mul_re (f f' : X → Y) :
    ((rho f * rho f').trace).re
      = (Fintype.card X : ℝ)⁻¹ ^ 2 * (∑ y, ∑ y', (ovl f f' y y' : ℝ) ^ 2) := by
  have h := congrArg Complex.re (trace_rho_mul f f')
  rw [Complex.ofReal_re] at h
  exact h

/-- If level-set sizes are at most `δ` and at most `β * |Y| ^ 2` pairs have overlap at least `α
≥ 0`, the sum of squared overlaps is at most `(α ^ 2 + β * δ ^ 2) * |Y| ^ 2`. -/
theorem sum_sq_ovl_le (f f' : X → Y) {α δ β : ℝ}
    (hα : 0 ≤ α)
    (hδ : ∀ y, ((lset f y).card : ℝ) ≤ δ)
    (hβ : ((Finset.univ.filter (fun p : Y × Y => α ≤ (ovl f f' p.1 p.2 : ℝ))).card : ℝ)
            ≤ β * (Fintype.card Y : ℝ) ^ 2) :
    (∑ y, ∑ y', (ovl f f' y y' : ℝ) ^ 2)
      ≤ (α ^ 2 + β * δ ^ 2) * (Fintype.card Y : ℝ) ^ 2 := by
  classical
  have hsum_eq : (∑ y, ∑ y', (ovl f f' y y' : ℝ) ^ 2)
      = ∑ p : Y × Y, (ovl f f' p.1 p.2 : ℝ) ^ 2 :=
    (Fintype.sum_prod_type (f := fun p : Y × Y => (ovl f f' p.1 p.2 : ℝ) ^ 2)).symm
  have hbound : ∀ p : Y × Y, (ovl f f' p.1 p.2 : ℝ) ^ 2
      ≤ α ^ 2 + (if α ≤ (ovl f f' p.1 p.2 : ℝ) then δ ^ 2 else 0) := by
    intro p
    have hκ0 : (0 : ℝ) ≤ (ovl f f' p.1 p.2 : ℝ) := Nat.cast_nonneg _
    by_cases hp : α ≤ (ovl f f' p.1 p.2 : ℝ)
    · rw [if_pos hp]
      have hκδ : (ovl f f' p.1 p.2 : ℝ) ≤ δ := by
        have h1 : ovl f f' p.1 p.2 ≤ (lset f p.1).card :=
          Finset.card_le_card Finset.inter_subset_left
        exact le_trans (by exact_mod_cast h1) (hδ p.1)
      nlinarith
    · rw [if_neg hp]
      have hlt : (ovl f f' p.1 p.2 : ℝ) < α := lt_of_not_ge hp
      nlinarith
  have hcard : (Fintype.card (Y × Y) : ℝ) = (Fintype.card Y : ℝ) ^ 2 := by
    rw [Fintype.card_prod]
    push_cast
    ring
  rw [hsum_eq]
  calc ∑ p : Y × Y, (ovl f f' p.1 p.2 : ℝ) ^ 2
      ≤ ∑ p : Y × Y,
          (α ^ 2 + (if α ≤ (ovl f f' p.1 p.2 : ℝ) then δ ^ 2 else 0)) :=
        Finset.sum_le_sum (fun p _ => hbound p)
    _ = (Fintype.card (Y × Y) : ℝ) * α ^ 2
          + ((Finset.univ.filter (fun p : Y × Y => α ≤ (ovl f f' p.1 p.2 : ℝ))).card : ℝ)
              * δ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        simp only [Finset.card_univ]
    _ = (Fintype.card Y : ℝ) ^ 2 * α ^ 2
          + ((Finset.univ.filter (fun p : Y × Y => α ≤ (ovl f f' p.1 p.2 : ℝ))).card : ℝ)
              * δ ^ 2 := by
        rw [hcard]
    _ ≤ (Fintype.card Y : ℝ) ^ 2 * α ^ 2
          + (β * (Fintype.card Y : ℝ) ^ 2) * δ ^ 2 := by
        have hδ2 : (0 : ℝ) ≤ δ ^ 2 := sq_nonneg _
        nlinarith [hβ, hδ2]
    _ = (α ^ 2 + β * δ ^ 2) * (Fintype.card Y : ℝ) ^ 2 := by ring

/-- The squared trace norm of the product of the two level-set matrix square roots is at most
the codomain size times the real trace of `rho f * rho f'`. -/
theorem fidelity_sq_le_cardY_mul_trace (f f' : X → Y) :
    (Matrix.traceNorm (CFC.sqrt (rho f) * CFC.sqrt (rho f'))) ^ 2
      ≤ (Fintype.card Y : ℝ) * ((rho f * rho f').trace).re := by
  rw [cfc_sqrt_rho f, cfc_sqrt_rho f']
  set A : Matrix X X ℂ := sqrtRho f * sqrtRho f' with hA
  have hb :=
    Qatlib.Foundations.MixedFidelity.TraceNormRankBound.traceNorm_sq_le_rank_hilbertSchmidt
      A
  have hr : (A.rank : ℝ) ≤ (Fintype.card Y : ℝ) := by
    have h1 : A.rank ≤ (sqrtRho f).rank := Matrix.rank_mul_le_left _ _
    have h2 : (sqrtRho f).rank ≤ Fintype.card Y := rank_sqrtRho_le f
    exact_mod_cast le_trans h1 h2
  have htrace : (A.conjTranspose * A).trace = (rho f * rho f').trace := by
    have hf : (sqrtRho f).conjTranspose = sqrtRho f :=
      (sqrtRho_posSemidef f).isHermitian
    have hf' : (sqrtRho f').conjTranspose = sqrtRho f' :=
      (sqrtRho_posSemidef f').isHermitian
    rw [hA, Matrix.conjTranspose_mul, hf, hf']
    rw [mul_assoc (sqrtRho f') (sqrtRho f) (sqrtRho f * sqrtRho f')]
    rw [← mul_assoc (sqrtRho f) (sqrtRho f) (sqrtRho f')]
    rw [sqrtRho_sq f]
    rw [Matrix.trace_mul_comm (sqrtRho f') (rho f * sqrtRho f')]
    rw [mul_assoc (rho f) (sqrtRho f') (sqrtRho f')]
    rw [sqrtRho_sq f']
  calc A.traceNorm ^ 2
      ≤ (A.rank : ℝ) * ((A.conjTranspose * A).trace).re := hb
    _ = (A.rank : ℝ) * ((rho f * rho f').trace).re := by rw [htrace]
    _ ≤ (Fintype.card Y : ℝ) * ((rho f * rho f').trace).re := by
        refine mul_le_mul_of_nonneg_right hr ?_
        rw [trace_rho_mul_re]
        exact mul_nonneg (sq_nonneg _)
          (Finset.sum_nonneg (fun y _ => Finset.sum_nonneg (fun y' _ => sq_nonneg _)))

/-- For a nonempty domain, a level-size bound `δ` and at most `β * |Y| ^ 2` overlap pairs of
size at least `α ≥ 0` give squared fidelity at most `(α ^ 2 + β * δ ^ 2) * |Y| ^ 3 / |X| ^
2`. [ChildsSchulmanVazirani2007]. -/
theorem lemma8 [Nonempty X] (f f' : X → Y) {α δ β : ℝ}
    (hα : 0 ≤ α)
    (hδ : ∀ y, ((lset f y).card : ℝ) ≤ δ)
    (hβ : ((Finset.univ.filter (fun p : Y × Y => α ≤ (ovl f f' p.1 p.2 : ℝ))).card : ℝ)
            ≤ β * (Fintype.card Y : ℝ) ^ 2) :
    (Matrix.traceNorm (CFC.sqrt (rho f) * CFC.sqrt (rho f'))) ^ 2
      ≤ (α ^ 2 + β * δ ^ 2) * (Fintype.card Y : ℝ) ^ 3 / (Fintype.card X : ℝ) ^ 2 := by
  have h1 := fidelity_sq_le_cardY_mul_trace f f'
  have h2 := trace_rho_mul_re f f'
  have h3 := sum_sq_ovl_le f f' hα hδ hβ
  have hY : (0 : ℝ) ≤ (Fintype.card Y : ℝ) := Nat.cast_nonneg _
  have hn2 : (0 : ℝ) ≤ (Fintype.card X : ℝ)⁻¹ ^ 2 := sq_nonneg _
  calc (Matrix.traceNorm (CFC.sqrt (rho f) * CFC.sqrt (rho f'))) ^ 2
      ≤ (Fintype.card Y : ℝ) * ((rho f * rho f').trace).re := h1
    _ = (Fintype.card Y : ℝ)
          * ((Fintype.card X : ℝ)⁻¹ ^ 2
              * (∑ y, ∑ y', (ovl f f' y y' : ℝ) ^ 2)) := by rw [h2]
    _ ≤ (Fintype.card Y : ℝ)
          * ((Fintype.card X : ℝ)⁻¹ ^ 2
              * ((α ^ 2 + β * δ ^ 2) * (Fintype.card Y : ℝ) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hY
        exact mul_le_mul_of_nonneg_left h3 hn2
    _ = (α ^ 2 + β * δ ^ 2) * (Fintype.card Y : ℝ) ^ 3 / (Fintype.card X : ℝ) ^ 2 := by
        field_simp

/-- The sum of the squared singular values of a complex square matrix equals the real trace of
its Gram matrix. -/
theorem sum_sq_singularValues_eq_trace (A : Matrix X X ℂ) :
    (∑ i, singularValues A i ^ 2) = ((Aᴴ * A).trace).re := by
  classical
  let hG : (Aᴴ * A).IsHermitian :=
    (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
  let eigenvalue : X → ℝ := hG.eigenvalues
  have hnonneg (i : X) : 0 ≤ eigenvalue i := by
    simpa only [eigenvalue, Matrix.conjTranspose_conjTranspose] using
      Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i
  have hsingular (i : X) : singularValues A i = Real.sqrt (eigenvalue i) := by
    simp only [singularValues, Matrix.conjTranspose_conjTranspose, eigenvalue]
  have htrace : (∑ i : X, eigenvalue i) = ((Aᴴ * A).trace).re := by
    simpa only [eigenvalue, Complex.re_sum, Complex.ofReal_re] using!
      congrArg Complex.re hG.sum_eigenvalues_eq_trace
  calc
    (∑ i, singularValues A i ^ 2) = ∑ i, eigenvalue i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hsingular i, Real.sq_sqrt (hnonneg i)]
    _ = ((Aᴴ * A).trace).re := htrace

/-- The squared trace norm of `A * B` is at most the product of the real traces of `Aᴴ * A` and
`Bᴴ * B`. -/
theorem traceNorm_mul_sq_le_gram_trace (A B : Matrix X X ℂ) :
    (A * B).traceNorm ^ 2 ≤
      ((Aᴴ * A).trace).re * ((Bᴴ * B).trace).re := by
  classical
  have hAB : (∑ i : X, singularValues (A * B) i) =
      ∑ i : Fin (Fintype.card X), singularValuesSorted (A * B) i := by
    simpa only [Real.rpow_one] using
      (sum_singularValues_rpow_eq_sum_sorted (A * B) 1)
  have hpow : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := fun x => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  have hA2 : (∑ i : Fin (Fintype.card X), singularValuesSorted A i ^ 2) =
      ((Aᴴ * A).trace).re := by
    have h := sum_singularValues_rpow_eq_sum_sorted A (2 : ℝ)
    simp only [hpow] at h
    rw [← h]
    exact sum_sq_singularValues_eq_trace A
  have hB2 : (∑ i : Fin (Fintype.card X), singularValuesSorted B i ^ 2) =
      ((Bᴴ * B).trace).re := by
    have h := sum_singularValues_rpow_eq_sum_sorted B (2 : ℝ)
    simp only [hpow] at h
    rw [← h]
    exact sum_sq_singularValues_eq_trace B
  have hsorted := sum_rpow_singularValues_mul_le A B (r := 1) (by norm_num)
  have hprod : (∑ i : Fin (Fintype.card X),
        singularValuesSorted (A * B) i) ≤
      ∑ i : Fin (Fintype.card X),
        singularValuesSorted A i * singularValuesSorted B i := by
    simpa only [Real.rpow_one] using hsorted
  have hABnn : 0 ≤ ∑ i : Fin (Fintype.card X), singularValuesSorted (A * B) i :=
    Finset.sum_nonneg fun i _ => singularValuesSorted_nonneg (A * B) i
  have hCS : (∑ i : Fin (Fintype.card X),
        singularValuesSorted A i * singularValuesSorted B i) ^ 2 ≤
      (∑ i : Fin (Fintype.card X), singularValuesSorted A i ^ 2) *
        (∑ i : Fin (Fintype.card X), singularValuesSorted B i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc
    (A * B).traceNorm ^ 2 = (∑ i : X, singularValues (A * B) i) ^ 2 := by
      rw [Matrix.traceNorm_eq_sum_singularValues]
    _ = (∑ i : Fin (Fintype.card X), singularValuesSorted (A * B) i) ^ 2 := by
      rw [hAB]
    _ ≤ (∑ i : Fin (Fintype.card X),
          singularValuesSorted A i * singularValuesSorted B i) ^ 2 :=
      pow_le_pow_left₀ hABnn hprod 2
    _ ≤ _ := hCS
    _ = ((Aᴴ * A).trace).re * ((Bᴴ * B).trace).re := by rw [hA2, hB2]

/-- The blockwise level-set projector, with entry the inverse size of the common level set when
the function values agree and zero otherwise. -/
noncomputable def suppProj (f : X → Y) : Matrix X X ℂ :=
  fun x x' => if f x = f x' then ((↑((lset f (f x)).card) : ℂ))⁻¹ else 0

/-- The level-set support projector is equal to its conjugate transpose. -/
theorem suppProj_conjTranspose (f : X → Y) : (suppProj f)ᴴ = suppProj f := by
  ext x x'
  rw [Matrix.conjTranspose_apply]
  simp only [suppProj]
  by_cases h : f x = f x'
  · rw [if_pos h.symm, if_pos h]
    simp [h]
  · rw [if_neg (fun hc => h hc.symm), if_neg h, star_zero]

/-- Right multiplication by the level-set support projector leaves `sqrtRho f` unchanged. -/
theorem sqrtRho_mul_suppProj (f : X → Y) :
    sqrtRho f * suppProj f = sqrtRho f := by
  ext x x'
  rw [Matrix.mul_apply]
  by_cases h : f x = f x'
  · have hval : sqrtRho f x x' = (↑(wt f (f x)) : ℂ) := by
      simp only [sqrtRho]
      rw [if_pos h]
    rw [hval]
    have hterm : ∀ z, sqrtRho f x z * suppProj f z x' =
        (↑(wt f (f x)) * ((↑((lset f (f x)).card) : ℂ))⁻¹) * indL f (f x) z := by
      intro z
      by_cases hz : f z = f x
      · have hzx : f z = f x' := hz.trans h
        have hxz : f x = f z := hz.symm
        simp only [sqrtRho, suppProj, indL]
        rw [if_pos hxz, if_pos hzx, if_pos hz, hz]
        ring
      · have hzx : ¬(f z = f x') := fun hc => hz (hc.trans h.symm)
        have hxz : ¬(f x = f z) := fun hc => hz hc.symm
        simp only [sqrtRho, suppProj, indL]
        rw [if_neg hxz, if_neg hzx, if_neg hz]
        ring
    rw [Finset.sum_congr rfl (fun z _ => hterm z)]
    rw [← Finset.mul_sum, sum_indL]
    have hL : ((lset f (f x)).card : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (card_lset_pos f x))
    field_simp
  · have hval : sqrtRho f x x' = 0 := by
      simp only [sqrtRho]
      rw [if_neg h]
    rw [hval]
    refine Finset.sum_eq_zero (fun z _ => ?_)
    by_cases hz : f z = f x
    · have hzx : f z ≠ f x' := fun hc => h (hz.symm.trans hc)
      have hxz : f x = f z := hz.symm
      simp only [sqrtRho, suppProj]
      rw [if_pos hxz, if_neg hzx, mul_zero]
    · have hxz : f x ≠ f z := fun hc => hz hc.symm
      simp only [sqrtRho]
      rw [if_neg hxz]
      simp

/-- Left multiplication by the level-set support projector leaves `sqrtRho f` unchanged. -/
theorem suppProj_mul_sqrtRho (f : X → Y) :
    suppProj f * sqrtRho f = sqrtRho f := by
  ext x x'
  rw [Matrix.mul_apply]
  by_cases h : f x = f x'
  · have hval : sqrtRho f x x' = (↑(wt f (f x)) : ℂ) := by
      simp only [sqrtRho]
      rw [if_pos h]
    rw [hval]
    have hterm : ∀ z, suppProj f x z * sqrtRho f z x' =
        (((↑((lset f (f x)).card) : ℂ))⁻¹ * ↑(wt f (f x))) * indL f (f x) z := by
      intro z
      by_cases hz : f z = f x
      · have hzx : f z = f x' := hz.trans h
        have hxz : f x = f z := hz.symm
        simp only [suppProj, sqrtRho, indL]
        rw [if_pos hxz, if_pos hzx, if_pos hz, hz]
        ring
      · have hzx : ¬(f z = f x') := fun hc => hz (hc.trans h.symm)
        have hxz : ¬(f x = f z) := fun hc => hz hc.symm
        simp only [suppProj, sqrtRho, indL]
        rw [if_neg hxz, if_neg hzx, if_neg hz]
        ring
    rw [Finset.sum_congr rfl (fun z _ => hterm z)]
    rw [← Finset.mul_sum, sum_indL]
    have hL : ((lset f (f x)).card : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (card_lset_pos f x))
    field_simp
  · have hval : sqrtRho f x x' = 0 := by
      simp only [sqrtRho]
      rw [if_neg h]
    rw [hval]
    refine Finset.sum_eq_zero (fun z _ => ?_)
    by_cases hz : f z = f x
    · have hzx : f z ≠ f x' := fun hc => h (hz.symm.trans hc)
      have hxz : f x = f z := hz.symm
      simp only [suppProj, sqrtRho]
      rw [if_pos hxz, if_neg hzx, mul_zero]
    · have hxz : f x ≠ f z := fun hc => hz hc.symm
      simp only [suppProj]
      rw [if_neg hxz]
      simp

/-- The level-set support projector is idempotent. -/
theorem suppProj_mul_self (f : X → Y) :
    suppProj f * suppProj f = suppProj f := by
  ext x x'
  rw [Matrix.mul_apply]
  by_cases h : f x = f x'
  · have hval : suppProj f x x' = ((↑((lset f (f x)).card) : ℂ))⁻¹ := by
      simp only [suppProj]
      rw [if_pos h]
    rw [hval]
    have hterm : ∀ z, suppProj f x z * suppProj f z x' =
        (((↑((lset f (f x)).card) : ℂ))⁻¹ * ((↑((lset f (f x)).card) : ℂ))⁻¹)
          * indL f (f x) z := by
      intro z
      by_cases hz : f z = f x
      · have hzx : f z = f x' := hz.trans h
        have hxz : f x = f z := hz.symm
        simp only [suppProj, indL]
        rw [if_pos hxz, if_pos hzx, if_pos hz, hz]
        ring
      · have hzx : ¬(f z = f x') := fun hc => hz (hc.trans h.symm)
        have hxz : ¬(f x = f z) := fun hc => hz hc.symm
        simp only [suppProj, indL]
        rw [if_neg hxz, if_neg hzx, if_neg hz]
        ring
    rw [Finset.sum_congr rfl (fun z _ => hterm z)]
    rw [← Finset.mul_sum, sum_indL]
    have hL : ((lset f (f x)).card : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (card_lset_pos f x))
    field_simp
  · have hval : suppProj f x x' = 0 := by
      simp only [suppProj]
      rw [if_neg h]
    rw [hval]
    refine Finset.sum_eq_zero (fun z _ => ?_)
    by_cases hz : f z = f x
    · have hzx : f z ≠ f x' := fun hc => h (hz.symm.trans hc)
      have hxz : f x = f z := hz.symm
      simp only [suppProj]
      rw [if_pos hxz, if_neg hzx, mul_zero]
    · have hxz : f x ≠ f z := fun hc => hz hc.symm
      simp only [suppProj]
      rw [if_neg hxz]
      simp

/-- For a nonempty domain, the real trace of `rho f` equals one. -/
theorem trace_rho_re [Nonempty X] (f : X → Y) : ((rho f).trace).re = 1 := by
  have hcard : ((Fintype.card X : ℂ)) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty X›).ne'
  have hterm : ∀ x : X, (rho f) x x = ((Fintype.card X : ℂ))⁻¹ := by
    intro x
    simp [rho]
  calc ((rho f).trace).re
      = (∑ x, ((Fintype.card X : ℂ))⁻¹).re := by
        simp only [Matrix.trace, Matrix.diag_apply]
        exact congrArg Complex.re (Finset.sum_congr rfl (fun x _ => hterm x))
    _ = (((Fintype.card X : ℂ) * ((Fintype.card X : ℂ))⁻¹)).re := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 1 := by
        rw [mul_inv_cancel₀ hcard]
        simp

/-- Summing the overlaps with all level sets of `f'` gives the size of the fixed level set of
`f`. -/
theorem sum_ovl_eq_card (f f' : X → Y) (y : Y) :
    (∑ y', ovl f f' y y') = (lset f y).card := by
  have h := Finset.card_eq_sum_card_fiberwise (s := lset f y)
    (t := (Finset.univ : Finset Y)) (f := f') (fun x _ => Finset.mem_univ (f' x))
  rw [h]
  refine Finset.sum_congr rfl (fun y' _ => ?_)
  unfold ovl lset
  congr 1
  ext x
  simp [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ]

/-- The real trace of `suppProj f * rho f'` equals the domain-size-normalized sum of squared
overlaps divided by the corresponding level-set sizes of `f`. -/
theorem trace_suppProj_mul_rho_re (f f' : X → Y) :
    ((suppProj f * rho f').trace).re
      = (Fintype.card X : ℝ)⁻¹ *
          (∑ y, (∑ y', (ovl f f' y y' : ℝ) ^ 2) / ((lset f y).card : ℝ)) := by
  set S : ℝ :=
    ∑ y, (∑ y', (ovl f f' y y' : ℝ) ^ 2) / ((lset f y).card : ℝ) with hS
  have hentry : ∀ x, (suppProj f * rho f') x x
      = (Fintype.card X : ℂ)⁻¹ * ((↑((lset f (f x)).card) : ℂ))⁻¹ *
          (ovl f f' (f x) (f' x) : ℂ) := by
    intro x
    rw [Matrix.mul_apply]
    have hstep : ∀ z, suppProj f x z * rho f' z x
        = (Fintype.card X : ℂ)⁻¹ * ((↑((lset f (f x)).card) : ℂ))⁻¹ *
            ind2 f f' (f x) (f' x) z := by
      intro z
      simp only [suppProj, rho, ind2]
      by_cases h1 : f x = f z
      · by_cases h2 : f' z = f' x
        · rw [if_pos h1, if_pos h2, if_pos (show f z = f x ∧ f' z = f' x from ⟨h1.symm, h2⟩)]
          ring
        · rw [if_pos h1, if_neg h2,
            if_neg (show ¬(f z = f x ∧ f' z = f' x) from fun hh => h2 hh.2)]
          ring
      · rw [if_neg h1,
          if_neg (show ¬(f z = f x ∧ f' z = f' x) from fun hh => h1 hh.1.symm),
          zero_mul, mul_zero]
    rw [Finset.sum_congr rfl (fun z _ => hstep z)]
    rw [← Finset.mul_sum, ← ovl_eq_sum]
  have hpair : (∑ x, ((↑((lset f (f x)).card) : ℂ))⁻¹ * (ovl f f' (f x) (f' x) : ℂ))
      = ∑ y, ∑ y', (ovl f f' y y' : ℂ) *
          (((↑((lset f y).card) : ℂ))⁻¹ * (ovl f f' y y' : ℂ)) :=
    sum_pair_fiber f f'
      (fun y y' => ((↑((lset f y).card) : ℂ))⁻¹ * (ovl f f' y y' : ℂ))
  have hcast : (∑ y, ∑ y', (ovl f f' y y' : ℂ) *
        (((↑((lset f y).card) : ℂ))⁻¹ * (ovl f f' y y' : ℂ)))
      = ((S : ℝ) : ℂ) := by
    rw [hS, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Complex.ofReal_div, div_eq_mul_inv, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y' _ => ?_)
    rw [Complex.ofReal_pow]
    push_cast
    ring
  have htrace : (suppProj f * rho f').trace
      = (Fintype.card X : ℂ)⁻¹ * ((S : ℝ) : ℂ) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [Finset.sum_congr rfl (fun x _ => hentry x)]
    have hfac : ∀ x, (Fintype.card X : ℂ)⁻¹ *
          ((↑((lset f (f x)).card) : ℂ))⁻¹ * (ovl f f' (f x) (f' x) : ℂ)
        = (Fintype.card X : ℂ)⁻¹ *
          (((↑((lset f (f x)).card) : ℂ))⁻¹ * (ovl f f' (f x) (f' x) : ℂ)) := by
      intro x
      ring
    rw [Finset.sum_congr rfl (fun x _ => hfac x)]
    rw [← Finset.mul_sum]
    congr 1
    rw [hpair, hcast]
  rw [htrace]
  have hEq : (Fintype.card X : ℂ)⁻¹ * ((S : ℝ) : ℂ)
      = (((Fintype.card X : ℝ)⁻¹ * S : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hEq, Complex.ofReal_re]

/-- For a nonempty domain, the squared fidelity of the level-set matrices is at most the real
trace of `suppProj f * rho f'`. -/
theorem fidelity_sq_le_suppProj_trace [Nonempty X] (f f' : X → Y) :
    (Matrix.traceNorm (CFC.sqrt (rho f) * CFC.sqrt (rho f'))) ^ 2
      ≤ ((suppProj f * rho f').trace).re := by
  rw [cfc_sqrt_rho f, cfc_sqrt_rho f']
  set A : Matrix X X ℂ := sqrtRho f * suppProj f with hA
  set B : Matrix X X ℂ := suppProj f * sqrtRho f' with hB
  have hAB : A * B = sqrtRho f * sqrtRho f' := by
    rw [hA, hB]
    rw [Matrix.mul_assoc (sqrtRho f) (suppProj f) (suppProj f * sqrtRho f')]
    rw [← Matrix.mul_assoc (suppProj f) (suppProj f) (sqrtRho f')]
    rw [suppProj_mul_self f]
    rw [← Matrix.mul_assoc (sqrtRho f) (suppProj f) (sqrtRho f')]
    rw [sqrtRho_mul_suppProj f]
  have hmain := traceNorm_mul_sq_le_gram_trace A B
  rw [hAB] at hmain
  have hAherm : Aᴴ = suppProj f * sqrtRho f := by
    rw [hA, Matrix.conjTranspose_mul, (sqrtRho_posSemidef f).isHermitian,
      suppProj_conjTranspose f]
  have hAAsq : Aᴴ * A = suppProj f * rho f * suppProj f := by
    rw [hAherm, hA]
    rw [Matrix.mul_assoc (suppProj f) (sqrtRho f) (sqrtRho f * suppProj f)]
    rw [← Matrix.mul_assoc (sqrtRho f) (sqrtRho f) (suppProj f)]
    rw [sqrtRho_sq f]
    rw [← Matrix.mul_assoc (suppProj f) (rho f) (suppProj f)]
  have hPirho : suppProj f * rho f = rho f := by
    calc suppProj f * rho f = suppProj f * (sqrtRho f * sqrtRho f) := by rw [sqrtRho_sq f]
      _ = (suppProj f * sqrtRho f) * sqrtRho f := by rw [Matrix.mul_assoc]
      _ = sqrtRho f * sqrtRho f := by rw [suppProj_mul_sqrtRho f]
      _ = rho f := by rw [sqrtRho_sq f]
  have htraceA : ((Aᴴ * A).trace).re = ((rho f).trace).re := by
    congr 1
    rw [hAAsq]
    calc (suppProj f * rho f * suppProj f).trace
        = (suppProj f * (suppProj f * rho f)).trace := Matrix.trace_mul_comm _ _
      _ = ((suppProj f * suppProj f) * rho f).trace := by rw [← Matrix.mul_assoc]
      _ = (suppProj f * rho f).trace := by rw [suppProj_mul_self f]
      _ = (rho f).trace := by rw [hPirho]
  have hBherm : Bᴴ = sqrtRho f' * suppProj f := by
    rw [hB, Matrix.conjTranspose_mul, (sqrtRho_posSemidef f').isHermitian,
      suppProj_conjTranspose f]
  have hBBsq : Bᴴ * B = sqrtRho f' * (suppProj f * sqrtRho f') := by
    rw [hBherm, hB]
    rw [Matrix.mul_assoc (sqrtRho f') (suppProj f) (suppProj f * sqrtRho f')]
    rw [← Matrix.mul_assoc (suppProj f) (suppProj f) (sqrtRho f')]
    rw [suppProj_mul_self f]
  have htraceB : ((Bᴴ * B).trace).re = ((suppProj f * rho f').trace).re := by
    congr 1
    rw [hBBsq]
    calc (sqrtRho f' * (suppProj f * sqrtRho f')).trace
        = ((suppProj f * sqrtRho f') * sqrtRho f').trace := Matrix.trace_mul_comm _ _
      _ = (suppProj f * (sqrtRho f' * sqrtRho f')).trace := by rw [← Matrix.mul_assoc]
      _ = (suppProj f * rho f').trace := by rw [sqrtRho_sq f']
  calc (Matrix.traceNorm (sqrtRho f * sqrtRho f')) ^ 2
      ≤ ((Aᴴ * A).trace).re * ((Bᴴ * B).trace).re := hmain
    _ = ((rho f).trace).re * ((suppProj f * rho f').trace).re := by
        rw [htraceA, htraceB]
    _ = 1 * ((suppProj f * rho f').trace).re := by rw [trace_rho_re f]
    _ = ((suppProj f * rho f').trace).re := one_mul _

/-- If every `f`-level set has size at most `δ` and at most `β * |Y|` such level sets have any
overlap of size at least `α ≥ 0`, the sum of squared overlaps divided by the corresponding
level sizes is at most `(α + β * δ) * |Y|`. -/
theorem sum_div_ovl_le [Nonempty X] (f f' : X → Y) {α β δ : ℝ}
    (hα : 0 ≤ α)
    (hδ : ∀ y, ((lset f y).card : ℝ) ≤ δ)
    (hβ : ((Finset.univ.filter (fun y : Y => ∃ y', α ≤ (ovl f f' y y' : ℝ))).card : ℝ)
            ≤ β * (Fintype.card Y : ℝ)) :
    (∑ y, (∑ y', (ovl f f' y y' : ℝ) ^ 2) / ((lset f y).card : ℝ))
      ≤ (α + β * δ) * (Fintype.card Y : ℝ) := by
  classical
  have hδ0 : 0 ≤ δ := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    exact le_trans (by positivity) (hδ (f x))
  set bad : Finset Y :=
    Finset.univ.filter (fun y => ∃ y', α ≤ (ovl f f' y y' : ℝ)) with hbad
  have hβ' : (bad.card : ℝ) ≤ β * (Fintype.card Y : ℝ) := by
    rw [hbad]
    exact hβ
  have hrow : ∀ y, (∑ y', (ovl f f' y y' : ℝ) ^ 2) / ((lset f y).card : ℝ)
      ≤ if y ∈ bad then δ else α := by
    intro y
    by_cases hL0 : (lset f y).card = 0
    · have hsum0 : (∑ y', (ovl f f' y y' : ℝ) ^ 2) = 0 := by
        refine Finset.sum_eq_zero (fun y' _ => ?_)
        have hovl : ovl f f' y y' = 0 := by
          unfold ovl
          exact Nat.eq_zero_of_le_zero
            (hL0 ▸ Finset.card_le_card Finset.inter_subset_left)
        simp [hovl]
      rw [hsum0, zero_div]
      by_cases hy : y ∈ bad
      · rw [if_pos hy]; exact hδ0
      · rw [if_neg hy]; exact hα
    · have hLpos : (0 : ℝ) < ((lset f y).card : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hL0
      have hsum_card : (∑ y', (ovl f f' y y' : ℝ)) = ((lset f y).card : ℝ) := by
        rw [← Nat.cast_sum, sum_ovl_eq_card]
      by_cases hy : y ∈ bad
      · rw [if_pos hy, div_le_iff₀ hLpos]
        have hnn : ∀ y' ∈ (Finset.univ : Finset Y),
            (0 : ℝ) ≤ (ovl f f' y y' : ℝ) := fun y' _ => Nat.cast_nonneg _
        have hsq := Finset.sum_sq_le_sq_sum_of_nonneg hnn
        rw [hsum_card] at hsq
        have hstep : ((lset f y).card : ℝ) ^ 2
            ≤ δ * ((lset f y).card : ℝ) := by
          calc ((lset f y).card : ℝ) ^ 2
              = ((lset f y).card : ℝ) * ((lset f y).card : ℝ) := by ring
            _ ≤ δ * ((lset f y).card : ℝ) :=
                mul_le_mul_of_nonneg_right (hδ y) (Nat.cast_nonneg _)
        linarith
      · rw [if_neg hy, div_le_iff₀ hLpos]
        have hlt : ∀ y', (ovl f f' y y' : ℝ) < α := by
          intro y'
          by_contra hcon
          push_neg at hcon
          exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨y', hcon⟩⟩)
        have hle : ∀ y', (ovl f f' y y' : ℝ) ^ 2 ≤ α * (ovl f f' y y' : ℝ) := by
          intro y'
          have h0 : (0 : ℝ) ≤ (ovl f f' y y' : ℝ) := Nat.cast_nonneg _
          nlinarith [hlt y', hα]
        calc (∑ y', (ovl f f' y y' : ℝ) ^ 2)
            ≤ ∑ y', α * (ovl f f' y y' : ℝ) :=
              Finset.sum_le_sum (fun y' _ => hle y')
          _ = α * (∑ y', (ovl f f' y y' : ℝ)) := by rw [Finset.mul_sum]
          _ = α * ((lset f y).card : ℝ) := by rw [hsum_card]
  calc (∑ y, (∑ y', (ovl f f' y y' : ℝ) ^ 2) / ((lset f y).card : ℝ))
      ≤ ∑ y, (if y ∈ bad then δ else α) := Finset.sum_le_sum (fun y _ => hrow y)
    _ = (bad.card : ℝ) * δ
          + ((Finset.univ.filter (fun y : Y => y ∉ bad)).card : ℝ) * α := by
        have hbad' : (Finset.univ.filter (fun y : Y => y ∈ bad)) = bad := by
          ext y; simp
        rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset Y))
          (p := fun y => y ∈ bad) (f := fun y => if y ∈ bad then δ else α), hbad']
        congr 1
        · rw [Finset.sum_congr rfl (fun y hy => if_pos (by simpa using hy)),
            Finset.sum_const, nsmul_eq_mul]
        · rw [Finset.sum_congr rfl (fun y hy => if_neg (by simpa using hy)),
            Finset.sum_const, nsmul_eq_mul]
    _ ≤ (β * (Fintype.card Y : ℝ)) * δ + (Fintype.card Y : ℝ) * α := by
        have hc2 : ((Finset.univ.filter (fun y : Y => y ∉ bad)).card : ℝ)
            ≤ (Fintype.card Y : ℝ) := by
          rw [← Finset.card_univ]
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        have h1 := mul_le_mul_of_nonneg_right hβ' hδ0
        have h2 := mul_le_mul_of_nonneg_right hc2 hα
        linarith
    _ = (α + β * δ) * (Fintype.card Y : ℝ) := by ring

/-- For a nonempty domain, level sizes at most `δ` and at most `β * |Y|` level sets of `f` with
any overlap at least `α ≥ 0` give squared fidelity at most `(α + β * δ) * |Y| / |X|`.
[ChildsSchulmanVazirani2007]. -/
theorem lemma9 [Nonempty X] (f f' : X → Y) {α β δ : ℝ}
    (hα : 0 ≤ α)
    (hδ : ∀ y, ((lset f y).card : ℝ) ≤ δ)
    (hβ : ((Finset.univ.filter (fun y : Y => ∃ y', α ≤ (ovl f f' y y' : ℝ))).card : ℝ)
            ≤ β * (Fintype.card Y : ℝ)) :
    (Matrix.traceNorm (CFC.sqrt (rho f) * CFC.sqrt (rho f'))) ^ 2
      ≤ (α + β * δ) * (Fintype.card Y : ℝ) / (Fintype.card X : ℝ) := by
  have h1 := fidelity_sq_le_suppProj_trace f f'
  have h2 := trace_suppProj_mul_rho_re f f'
  have h3 := sum_div_ovl_le f f' hα hδ hβ
  have hX : (0 : ℝ) < (Fintype.card X : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty X›
  have hXinv : (0 : ℝ) ≤ (Fintype.card X : ℝ)⁻¹ := inv_nonneg.mpr hX.le
  calc (Matrix.traceNorm (CFC.sqrt (rho f) * CFC.sqrt (rho f'))) ^ 2
      ≤ ((suppProj f * rho f').trace).re := h1
    _ = (Fintype.card X : ℝ)⁻¹ *
          (∑ y, (∑ y', (ovl f f' y y' : ℝ) ^ 2) / ((lset f y).card : ℝ)) := h2
    _ ≤ (Fintype.card X : ℝ)⁻¹ *
          ((α + β * δ) * (Fintype.card Y : ℝ)) :=
        mul_le_mul_of_nonneg_left h3 hXinv
    _ = (α + β * δ) * (Fintype.card Y : ℝ) / (Fintype.card X : ℝ) := by
        rw [div_eq_mul_inv]
        ring

/-- Relabeling function values by a codomain equivalence leaves the level-set matrix unchanged.
[ChildsSchulmanVazirani2007]. -/
theorem rho_comp_equiv (e : Y ≃ Y) (f : X → Y) :
    rho (fun x => e (f x)) = rho f := by
  funext x x'
  simp only [rho, e.apply_eq_iff_eq]

/-- Adding a fixed codomain group element to every function value leaves the level-set matrix
unchanged. -/
theorem rho_add_const [AddGroup Y] (f : X → Y) (b : Y) :
    rho (fun x => f x + b) = rho f := by
  have he : (fun x => f x + b) = fun x => (Equiv.addRight b) (f x) := rfl
  rw [he]
  exact rho_comp_equiv _ f

/-- Multiplying all function values by a nonzero field element leaves the level-set matrix
unchanged. [ChildsSchulmanVazirani2007]. -/
theorem rho_mul_const_of_ne_zero [Field Y] (f : X → Y) {c : Y} (hc : c ≠ 0) :
    rho (fun x => c * f x) = rho f := by
  let e : Y ≃ Y :=
    { toFun := fun y => c * y
      invFun := fun y => c⁻¹ * y
      left_inv := by
        intro y
        show c⁻¹ * (c * y) = y
        rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      right_inv := by
        intro y
        show c * (c⁻¹ * y) = y
        rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul] }
  have he : (fun x => c * f x) = fun x => e (f x) := rfl
  rw [he]
  exact rho_comp_equiv _ f

end Qatlib.Papers.HiddenNonlin07.MainResults.LevelSetFidelity
