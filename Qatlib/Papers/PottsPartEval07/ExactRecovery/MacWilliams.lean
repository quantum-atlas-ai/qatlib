/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Logic.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Order.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# The MacWilliams identity for finite linear codes

The module defines Hamming weight, homogeneous weight enumerators, and the dot-product dual of a
linear code over `ZMod q`. Additive-character orthogonality and coordinatewise summation
establish the MacWilliams transformation, with normalization expressed either by code
cardinality or by dimension [GeraciLidar2008].

## Main statements

* `macWilliams_weightEnum`: The dual weight enumerator is obtained by the MacWilliams
  substitution and division by the code size.
* `macWilliams_finrank`: For prime q, the normalization is q raised to the code dimension.

## References

* [Geraci and Lidar, 2008][GeraciLidar2008]
-/

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.ExactRecovery

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {q : ℕ} [NeZero q]

noncomputable instance codeFintype (C : Submodule (ZMod q) (ι → ZMod q)) : Fintype C := by
  classical
  exact Fintype.subtype (univ.filter (fun v => v ∈ C)) (by simp)

/-- The Hamming weight of a word, counted as the number of its nonzero coordinates. -/
def hammingWeight (v : ι → ZMod q) : ℕ := (univ.filter (fun i => v i ≠ 0)).card

/-- The coordinate factor equal to `x` at zero and `y` at every nonzero symbol. -/
def coordFactor (x y : ℂ) (a : ZMod q) : ℂ := if a = 0 then x else y

/-- The homogeneous weight enumerator obtained by summing `x^(length - weight) * y^weight` over
codewords. -/
def weightEnum (C : Submodule (ZMod q) (ι → ZMod q)) (x y : ℂ) : ℂ := by
  classical
  exact ∑ c : C, x ^ (Fintype.card ι - hammingWeight c.val) * y ^ hammingWeight c.val

/-- The weight enumerator expressed as a sum of coordinate products over ambient words belonging
to the code. -/
def weightEnumProd (C : Submodule (ZMod q) (ι → ZMod q)) (x y : ℂ) : ℂ := by
  classical
  exact ∑ v : ι → ZMod q, if v ∈ C then ∏ i, coordFactor x y (v i) else 0

/-- The ambient-word expression for the weight enumerator equals the sum of coordinate products
over the code subtype. -/
lemma weightEnumProd_eq_subtype (C : Submodule (ZMod q) (ι → ZMod q)) (x y : ℂ) :
    weightEnumProd C x y = ∑ c : C, ∏ i, coordFactor x y (c.val i) := by
  classical
  rw [weightEnumProd, ← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter (fun v => v ∈ C)) (by intro x; simp)
    (fun u => ∏ i, coordFactor x y (u i))

/-- A product of coordinate factors splits into powers of `x` and `y` counting zero and nonzero
coordinates in `s`. -/
lemma prod_coordFactor (s : Finset ι) (v : ι → ZMod q) (x y : ℂ) :
    s.prod (fun i => coordFactor x y (v i)) =
      x ^ (s.filter (fun i => v i = 0)).card * y ^ (s.filter (fun i => v i ≠ 0)).card := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih]
      by_cases h : v a = 0
      · have h0 : ((insert a s).filter (fun i => v i = 0)).card
            = (s.filter (fun i => v i = 0)).card + 1 := by
          rw [Finset.filter_insert, if_pos h, Finset.card_insert_of_notMem]
          simp [ha]
        have hn : ((insert a s).filter (fun i => v i ≠ 0)).card
            = (s.filter (fun i => v i ≠ 0)).card := by
          rw [Finset.filter_insert, if_neg (fun hc => hc h)]
        rw [h0, hn]
        have hca : coordFactor x y (v a) = x := by simp [coordFactor, h]
        rw [hca, pow_succ]
        ring
      · have hne : v a ≠ 0 := h
        have h0 : ((insert a s).filter (fun i => v i = 0)).card
            = (s.filter (fun i => v i = 0)).card := by
          rw [Finset.filter_insert, if_neg h]
        have hn : ((insert a s).filter (fun i => v i ≠ 0)).card
            = (s.filter (fun i => v i ≠ 0)).card + 1 := by
          rw [Finset.filter_insert, if_pos hne, Finset.card_insert_of_notMem]
          simp [ha]
        rw [h0, hn]
        have hca : coordFactor x y (v a) = y := by simp [coordFactor, h]
        rw [hca, pow_succ]
        ring

/-- The number of zero coordinates equals the word length minus its Hamming weight. -/
lemma card_zero_eq (v : ι → ZMod q) :
    (univ.filter (fun i => v i = 0)).card = Fintype.card ι - hammingWeight v := by
  have h := (univ : Finset ι).card_filter_add_card_filter_not (fun i => v i ≠ 0)
  have h' : (univ.filter (fun i => ¬ (v i ≠ 0))).card
      = (univ.filter (fun i => v i = 0)).card := by
    congr 1
    exact Finset.filter_congr (fun i _ => by simp)
  rw [h', Finset.card_univ] at h
  unfold hammingWeight
  omega

/-- The homogeneous and coordinate-product definitions of the weight enumerator coincide. -/
lemma weightEnum_eq_prod (C : Submodule (ZMod q) (ι → ZMod q)) (x y : ℂ) :
    weightEnum C x y = weightEnumProd C x y := by
  classical
  rw [weightEnum, weightEnumProd_eq_subtype]
  refine Finset.sum_congr rfl ?_
  intro c _
  rw [prod_coordFactor, card_zero_eq]
  rfl

/-- The finite-coordinate bilinear dot product of two words over `ZMod q`. -/
def dot (u v : ι → ZMod q) : ZMod q := ∑ i, u i * v i

/-- The dual code consisting of words orthogonal to every word of `C` under `dot`. -/
def dualCode (C : Submodule (ZMod q) (ι → ZMod q)) : Submodule (ZMod q) (ι → ZMod q) where
  carrier := {u | ∀ c ∈ C, dot c u = 0}
  zero_mem' := by
    intro c _
    simp [dot]
  add_mem' := by
    intro u v hu hv c hc
    show dot c (u + v) = 0
    have hu' : (∑ i, c i * u i) = 0 := hu c hc
    have hv' : (∑ i, c i * v i) = 0 := hv c hc
    simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib, hu', hv', add_zero]
  smul_mem' := by
    intro a u hu c hc
    show dot c (a • u) = 0
    have h : dot c (a • u) = a * dot c u := by
      rw [dot, dot, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [h, hu c hc, mul_zero]

/-- Membership in the dual code means that the dot product with every member of the original
code vanishes. -/
@[simp]
lemma mem_dualCode {C : Submodule (ZMod q) (ι → ZMod q)} {u : ι → ZMod q} :
    u ∈ dualCode C ↔ ∀ c ∈ C, dot c u = 0 := Iff.rfl

/-- Dual-code membership is equivalent to vanishing dot product with every element of the code
subtype. -/
lemma mem_dualCode_iff {C : Submodule (ZMod q) (ι → ZMod q)} {u : ι → ZMod q} :
    u ∈ dualCode C ↔ ∀ c : C, dot c.val u = 0 := by
  rw [mem_dualCode]
  constructor
  · intro h c
    exact h c.val c.property
  · intro h c hc
    exact h ⟨c, hc⟩

/-- An additive character sends a finite sum to the product of its values. -/
lemma addChar_map_sum {A : Type*} [AddCommMonoid A] {M : Type*} [CommMonoid M]
    (ψ : AddChar A M) {κ : Type*} (s : Finset κ) (a : κ → A) :
    ψ (s.sum (fun i => a i)) = s.prod (fun i => ψ (a i)) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]

/-- The additive character on `C` obtained by applying the standard character to the dot product
with `u`. -/
def codeChar (C : Submodule (ZMod q) (ι → ZMod q)) (u : ι → ZMod q) : AddChar C ℂ where
  toFun c := ZMod.stdAddChar (dot c.val u)
  map_zero_eq_one' := by
    show ZMod.stdAddChar (dot 0 u) = 1
    have : dot (0 : ι → ZMod q) u = 0 := by
      show (∑ i, (0 : ι → ZMod q) i * u i) = 0
      simp
    rw [this, AddChar.map_zero_eq_one]
  map_add_eq_mul' := by
    intro c d
    show ZMod.stdAddChar (dot (c + d).val u) = _ * _
    have hdot : dot (c + d).val u = dot c.val u + dot d.val u := by
      show (∑ i, ((c + d).val i) * u i) = (∑ i, c.val i * u i) + ∑ i, d.val i * u i
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp only [Submodule.coe_add, Pi.add_apply, add_mul]
    rw [hdot, AddChar.map_add_eq_mul]

/-- The character sum over a code equals its cardinality when every pairing vanishes, and equals
zero otherwise. -/
lemma sum_codeChar (C : Submodule (ZMod q) (ι → ZMod q)) (u : ι → ZMod q) :
    (∑ c : C, ZMod.stdAddChar (dot c.val u)) =
      if (∀ c : C, dot c.val u = 0) then (Fintype.card C : ℂ) else 0 := by
  classical
  by_cases h : ∀ c : C, dot c.val u = 0
  · rw [if_pos h]
    have h1 : ∀ c : C, ZMod.stdAddChar (dot c.val u) = 1 := by
      intro c
      rw [h c, AddChar.map_zero_eq_one]
    rw [Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_const, nsmul_eq_mul, mul_one]
    norm_cast
  · rw [if_neg h]
    have hne : codeChar C u ≠ (1 : AddChar C ℂ) := by
      intro heq
      apply h
      intro c
      have hc : codeChar C u c = (1 : AddChar C ℂ) c := by rw [heq]
      have h2 : ZMod.stdAddChar (dot c.val u) = ZMod.stdAddChar (0 : ZMod q) := by
        simpa using! hc
      exact ZMod.injective_stdAddChar h2
    have := AddChar.sum_eq_zero_of_ne_one (R' := ℂ) hne
    simpa [codeChar] using this

/-- Summing the coordinate factor over `ZMod q` gives `x + (q - 1) * y`. -/
lemma sum_coordFactor (x y : ℂ) :
    (∑ a : ZMod q, coordFactor x y a) = x + ((q : ℂ) - 1) * y := by
  have hsplit : ∀ a : ZMod q,
      coordFactor x y a = y + (if a = 0 then (x - y) else 0) := by
    intro a
    unfold coordFactor
    split_ifs with ha
    · ring
    · ring
  rw [Finset.sum_congr rfl (fun a _ => hsplit a), Finset.sum_add_distrib]
  have h1 : (∑ a : ZMod q, (if a = 0 then (x - y) else 0)) = x - y := by
    rw [Finset.sum_ite_eq' univ (0 : ZMod q) (fun _ => x - y)]
    simp
  have h2 : (∑ _a : ZMod q, y) = (q : ℂ) * y := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [h1, h2, add_comm]
  ring

/-- The coordinate character sum at zero frequency is `x + (q - 1) * y`. -/
lemma coordSum_zero (x y : ℂ) :
    (∑ a : ZMod q, ZMod.stdAddChar ((0 : ZMod q) * a) * coordFactor x y a) =
      x + ((q : ℂ) - 1) * y := by
  have h0 : ∀ a : ZMod q, ZMod.stdAddChar ((0 : ZMod q) * a) = 1 := by
    intro a
    rw [zero_mul, AddChar.map_zero_eq_one]
  simp_rw [h0, one_mul]
  exact sum_coordFactor x y

/-- The coordinate character sum at a nonzero frequency is `x - y`. -/
lemma coordSum_ne_zero {b : ZMod q} (hb : b ≠ 0) (x y : ℂ) :
    (∑ a : ZMod q, ZMod.stdAddChar (b * a) * coordFactor x y a) = x - y := by
  have hsplit : ∀ a : ZMod q,
      ZMod.stdAddChar (b * a) * coordFactor x y a =
        (ZMod.stdAddChar (b * a) * y)
          + ZMod.stdAddChar (b * a) * (if a = 0 then (x - y) else 0) := by
    intro a
    unfold coordFactor
    split_ifs with ha
    · rw [ha]; ring
    · ring
  rw [Finset.sum_congr rfl (fun a _ => hsplit a), Finset.sum_add_distrib]

  have horth : (∑ a : ZMod q, ZMod.stdAddChar (b * a)) = 0 := by
    have h := AddChar.sum_mulShift (R' := ℂ) (b := b)
      (ψ := ZMod.stdAddChar (N := q)) (ZMod.isPrimitive_stdAddChar q)
    have hzero : (∑ a : ZMod q, ZMod.stdAddChar (a * b)) = 0 := by
      rw [h, if_neg hb]
      simp
    rw [← hzero]
    exact Finset.sum_congr rfl (fun a _ => by rw [mul_comm])
  have hfirst : (∑ a : ZMod q, ZMod.stdAddChar (b * a) * y) = 0 := by
    rw [← Finset.sum_mul, horth, zero_mul]
  have hsecond :
      (∑ a : ZMod q, ZMod.stdAddChar (b * a) * (if a = 0 then (x - y) else 0)) = x - y := by
    rw [show (∑ a : ZMod q, ZMod.stdAddChar (b * a) * (if a = 0 then (x - y) else 0))
          = ∑ a : ZMod q, (if a = 0 then ZMod.stdAddChar (b * a) * (x - y) else 0) by
      refine Finset.sum_congr rfl ?_
      intro a _
      split_ifs <;> ring]
    rw [Finset.sum_ite_eq' univ (0 : ZMod q) (fun a => ZMod.stdAddChar (b * a) * (x - y))]
    simp
  rw [hfirst, hsecond, zero_add]

/-- The character-weighted sum over ambient words factors into coordinate terms with the
MacWilliams substitution. -/
lemma sum_char_weight (c : ι → ZMod q) (x y : ℂ) :
    (∑ u : ι → ZMod q, ZMod.stdAddChar (dot c u) * ∏ i, coordFactor x y (u i)) =
      ∏ i, coordFactor (x + ((q : ℂ) - 1) * y) (x - y) (c i) := by

  have hchar : ∀ u : ι → ZMod q,
      ZMod.stdAddChar (dot c u) = ∏ i, ZMod.stdAddChar (c i * u i) := by
    intro u
    rw [dot, addChar_map_sum]
  simp_rw [hchar]
  rw [show (∑ u : ι → ZMod q, (∏ i, ZMod.stdAddChar (c i * u i)) * (∏ i, coordFactor x y (u i)))
      = ∑ u : ι → ZMod q, ∏ i, (ZMod.stdAddChar (c i * u i) * coordFactor x y (u i)) by
    refine Finset.sum_congr rfl ?_
    intro u _
    rw [Finset.prod_mul_distrib]]
  rw [← Fintype.prod_sum (κ := fun _ => ZMod q)
        (f := fun i a => ZMod.stdAddChar (c i * a) * coordFactor x y a)]
  refine Finset.prod_congr rfl ?_
  intro i _
  by_cases hi : c i = 0
  · rw [hi, coordSum_zero]
    simp [coordFactor, hi]
  · rw [coordSum_ne_zero hi]
    simp [coordFactor, hi]

/-- The coordinate-product enumerator of the dual equals the transformed enumerator of `C`
divided by its cardinality. -/
theorem macWilliams (C : Submodule (ZMod q) (ι → ZMod q)) (x y : ℂ) :
    weightEnumProd (dualCode C) x y =
      (Fintype.card C : ℂ)⁻¹ *
        weightEnumProd C (x + ((q : ℂ) - 1) * y) (x - y) := by
  classical
  have hcard : (Fintype.card C : ℂ) ≠ 0 := by
    have : 0 < Fintype.card C := Fintype.card_pos_iff.mpr ⟨⟨0, C.zero_mem⟩⟩
    exact_mod_cast this.ne'

  have hind : ∀ u : ι → ZMod q,
      (∑ c : C, ZMod.stdAddChar (dot c.val u))
        = if u ∈ dualCode C then (Fintype.card C : ℂ) else 0 := by
    intro u
    rw [sum_codeChar]
    by_cases hu : u ∈ dualCode C
    · rw [if_pos ((mem_dualCode_iff).mp hu), if_pos hu]
    · rw [if_neg (fun h => hu ((mem_dualCode_iff).mpr h)), if_neg hu]

  have hcommon :
      (∑ c : C, ∑ u : ι → ZMod q,
          ZMod.stdAddChar (dot c.val u) * ∏ i, coordFactor x y (u i))
        = (Fintype.card C : ℂ) * weightEnumProd (dualCode C) x y := by
    rw [show (∑ c : C, ∑ u : ι → ZMod q,
          ZMod.stdAddChar (dot c.val u) * ∏ i, coordFactor x y (u i))
        = ∑ u : ι → ZMod q,
            (∑ c : C, ZMod.stdAddChar (dot c.val u)) * ∏ i, coordFactor x y (u i) by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro u _
      rw [Finset.sum_mul]]
    simp_rw [hind]
    rw [show (∑ u : ι → ZMod q,
          (if u ∈ dualCode C then (Fintype.card C : ℂ) else 0) * ∏ i, coordFactor x y (u i))
        = (Fintype.card C : ℂ) * ∑ u : ι → ZMod q,
            (if u ∈ dualCode C then (1 : ℂ) else 0) * ∏ i, coordFactor x y (u i) by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro u _
      by_cases hu : u ∈ dualCode C <;> simp [hu]]
    rw [show (∑ u : ι → ZMod q,
          (if u ∈ dualCode C then (1 : ℂ) else 0) * ∏ i, coordFactor x y (u i))
        = ∑ u : ι → ZMod q,
            if u ∈ dualCode C then ∏ i, coordFactor x y (u i) else 0 by
      refine Finset.sum_congr rfl ?_
      intro u _
      by_cases hu : u ∈ dualCode C <;> simp [hu]]
    rw [weightEnumProd]

  have hother : weightEnumProd C (x + ((q : ℂ) - 1) * y) (x - y)
      = ∑ c : C, ∑ u : ι → ZMod q,
          ZMod.stdAddChar (dot c.val u) * ∏ i, coordFactor x y (u i) := by
    rw [weightEnumProd_eq_subtype]
    refine Finset.sum_congr rfl ?_
    intro c _
    exact (sum_char_weight c.val x y).symm
  have hexp : weightEnumProd C (x + ((q : ℂ) - 1) * y) (x - y)
      = (Fintype.card C : ℂ) * weightEnumProd (dualCode C) x y :=
    hother.trans hcommon
  rw [hexp, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- The homogeneous weight enumerator of the dual equals the transformed enumerator of `C`
divided by its cardinality [GeraciLidar2008]. -/
theorem macWilliams_weightEnum (C : Submodule (ZMod q) (ι → ZMod q)) (x y : ℂ) :
    weightEnum (dualCode C) x y =
      (Fintype.card C : ℂ)⁻¹ *
        weightEnum C (x + ((q : ℂ) - 1) * y) (x - y) := by
  rw [weightEnum_eq_prod, weightEnum_eq_prod, macWilliams]

/-- For prime `q`, the dual coordinate-product enumerator is the transformed enumerator of `C`
divided by `q` to its dimension [GeraciLidar2008]. -/
theorem macWilliams_finrank [Fact q.Prime] (C : Submodule (ZMod q) (ι → ZMod q)) (x y : ℂ) :
    weightEnumProd (dualCode C) x y =
      ((q : ℂ) ^ Module.finrank (ZMod q) C)⁻¹ *
        weightEnumProd C (x + ((q : ℂ) - 1) * y) (x - y) := by
  rw [macWilliams C x y]
  have hcard : Fintype.card C = q ^ Module.finrank (ZMod q) C := by
    have h := Module.card_eq_pow_finrank (K := ZMod q) (V := C)
    rw [h, ZMod.card]
  rw [hcard, Nat.cast_pow]

end

end Qatlib.Papers.PottsPartEval07.ExactRecovery
