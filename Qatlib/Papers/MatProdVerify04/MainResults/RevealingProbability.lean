/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

/-!
# Revealing probabilities over finite fields

The module counts roots of affine and bilinear expressions over a finite field.
`affinePairZeros_card_le` bounds the number of zero pairs, and `revealing_pair_mass_ge` gives a
uniform one-quarter lower bound for a nonzero bilinear value. The paper context is
[BuhrmanSpalek2006].

## Main statements

* `affinePairZeros_card_le`: at most `2 * Fintype.card K - 1` zero pairs.
* `revealing_pair_mass_ge`: nonzero probability at least one quarter.

## References

* [Buhrman and Špalek, 2006][BuhrmanSpalek2006]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatProdVerify04.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
set_option warningAsError false

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The uniform distribution on the elements of the finite field `K`. -/
def uniformField : FinDist K where
  prob _ := ((Fintype.card K : ℝ))⁻¹
  nonneg _ := by positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card K : ℝ) ≠ 0 := by
      have hpos : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨0⟩
      exact_mod_cast hpos.ne'
    exact mul_inv_cancel₀ hcard

omit [Fintype K] [DecidableEq K] in

/-- An affine expression with nonzero linear coefficient has at most one root. -/
theorem affine_root_unique {a b : K} (ha : a ≠ 0) {x y : K}
    (hx : a * x + b = 0) (hy : a * y + b = 0) : x = y :=
  mul_left_cancel₀ ha
    ((eq_neg_of_add_eq_zero_left hx).trans (eq_neg_of_add_eq_zero_left hy).symm)

/-- The set of roots of an affine expression with nonzero linear coefficient has cardinality at
most one. See [BuhrmanSpalek2006]. -/
theorem affine_root_card_le_one {a b : K} (ha : a ≠ 0) :
    (Finset.univ.filter (fun x => a * x + b = 0)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  exact affine_root_unique ha (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2

/-- A nonconstant affine expression vanishes on a uniform field element with probability at most
the reciprocal of the field cardinality. See [BuhrmanSpalek2006]. -/
theorem uniform_affine_root_mass_le {a b : K} (ha : a ≠ 0) :
    eventMass (uniformField (K := K)) (fun x => a * x + b = 0)
      ≤ ((Fintype.card K : ℝ))⁻¹ := by
  classical
  have hcard : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨0⟩
  have hcardR : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast hcard
  have hcard_le : ((Finset.univ.filter (fun x => a * x + b = 0)).card : ℝ) ≤ 1 := by
    exact_mod_cast affine_root_card_le_one ha
  unfold eventMass uniformField
  rw [Finset.sum_const, nsmul_eq_mul]
  have hstep : ((Finset.univ.filter (fun x : K => a * x + b = 0)).card : ℝ)
        * (Fintype.card K : ℝ)⁻¹
      ≤ 1 * (Fintype.card K : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_right hcard_le (by positivity)
  linarith

/-- The pairs at which `z.1 * (a * z.2 + c1) + c2 * z.2 + c3` vanishes. -/
def affinePairZeros (a c1 c2 c3 : K) : Finset (K × K) :=
  (Finset.univ : Finset (K × K)).filter
    (fun z : K × K => z.1 * (a * z.2 + c1) + c2 * z.2 + c3 = 0)

/-- When `a ≠ 0`, the bilinear expression defining `affinePairZeros` has at most `2 *
Fintype.card K - 1` zero pairs. See [BuhrmanSpalek2006]. -/
theorem affinePairZeros_card_le (a c1 c2 c3 : K) (ha : a ≠ 0) :
    (affinePairZeros a c1 c2 c3).card ≤ 2 * Fintype.card K - 1 := by
  classical
  have hg1 : 1 ≤ Fintype.card K := Fintype.card_pos_iff.mpr ⟨0⟩
  have hcard : (affinePairZeros a c1 c2 c3).card
      = ∑ y : K, (Finset.univ.filter
          (fun x : K => x * (a * y + c1) + c2 * y + c3 = 0)).card := by
    rw [affinePairZeros, Finset.card_filter,
      show (Finset.univ : Finset (K × K)) = (Finset.univ : Finset K) ×ˢ Finset.univ from
        (Finset.univ_product_univ).symm,
      Finset.sum_product, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun y _ => (Finset.card_filter _ _).symm)
  have hbound : ∀ y : K, (Finset.univ.filter
        (fun x : K => x * (a * y + c1) + c2 * y + c3 = 0)).card
      ≤ (if a * y + c1 = 0 then Fintype.card K else 1) := by
    intro y
    by_cases h : a * y + c1 = 0
    · rw [if_pos h]
      exact le_trans (Finset.card_le_card (Finset.filter_subset _ _))
        (le_of_eq (Finset.card_univ))
    · rw [if_neg h]
      have hset : (Finset.univ.filter (fun x : K => x * (a*y+c1) + c2*y + c3 = 0))
          = (Finset.univ.filter (fun x : K => (a*y+c1) * x + (c2*y + c3) = 0)) := by
        apply Finset.filter_congr
        intro x _
        simp only [mul_comm x (a * y + c1), add_assoc]
      rw [hset]
      exact affine_root_card_le_one (a := a * y + c1) (b := c2 * y + c3) h
  have hroot : (Finset.univ.filter (fun y : K => a * y + c1 = 0)).card ≤ 1 :=
    affine_root_card_le_one ha
  have hpoint : ∀ y : K,
      (if a * y + c1 = 0 then Fintype.card K else 1)
        = 1 + (if a * y + c1 = 0 then (Fintype.card K - 1) else 0) := by
    intro y
    by_cases h : a * y + c1 = 0
    · rw [if_pos h, if_pos h]; omega
    · rw [if_neg h, if_neg h]
  have hsum : (∑ y : K, (if a * y + c1 = 0 then Fintype.card K else 1))
      = Fintype.card K
        + (Finset.univ.filter (fun y : K => a * y + c1 = 0)).card
            * (Fintype.card K - 1) := by
    calc (∑ y : K, (if a * y + c1 = 0 then Fintype.card K else 1))
        = ∑ y : K, (1 + (if a * y + c1 = 0 then (Fintype.card K - 1) else 0)) :=
          Finset.sum_congr rfl (fun y _ => hpoint y)
      _ = (∑ _y : K, (1 : ℕ))
            + ∑ y : K, (if a * y + c1 = 0 then (Fintype.card K - 1) else 0) :=
          Finset.sum_add_distrib
      _ = Fintype.card K
            + ∑ y : K, (if a * y + c1 = 0 then (Fintype.card K - 1) else 0) := by
          simp
      _ = Fintype.card K
            + (Finset.univ.filter (fun y : K => a * y + c1 = 0)).card
                * (Fintype.card K - 1) := by
          rw [← Finset.sum_filter]
          simp
  have hle : Fintype.card K
        + (Finset.univ.filter (fun y : K => a * y + c1 = 0)).card
            * (Fintype.card K - 1) ≤ 2 * Fintype.card K - 1 := by
    have hmul : (Finset.univ.filter (fun y : K => a * y + c1 = 0)).card
          * (Fintype.card K - 1) ≤ 1 * (Fintype.card K - 1) :=
      Nat.mul_le_mul_right _ hroot
    omega
  calc (affinePairZeros a c1 c2 c3).card
      = ∑ y : K, (Finset.univ.filter
          (fun x : K => x * (a * y + c1) + c2 * y + c3 = 0)).card := hcard
    _ ≤ ∑ y : K, (if a * y + c1 = 0 then Fintype.card K else 1) :=
        Finset.sum_le_sum (fun y _ => hbound y)
    _ = Fintype.card K
          + (Finset.univ.filter (fun y : K => a * y + c1 = 0)).card
              * (Fintype.card K - 1) := hsum
    _ ≤ 2 * Fintype.card K - 1 := hle

/-- The uniform distribution on ordered pairs of elements of `K`. -/
def uniformPairField : FinDist (K × K) where
  prob _ := ((Fintype.card (K × K) : ℝ))⁻¹
  nonneg _ := by positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hpos : (0 : ℝ) < (Fintype.card (K × K) : ℝ) := by
      have hc : 0 < Fintype.card (K × K) := Fintype.card_pos_iff.mpr ⟨(0, 0)⟩
      exact_mod_cast hc
    exact mul_inv_cancel₀ hpos.ne'

/-- When the mixed coefficient is nonzero, the zero probability of the bilinear expression is at
most `(2 * Fintype.card K - 1) / (Fintype.card K) ^ 2`. See [BuhrmanSpalek2006]. -/
theorem affinePair_bad_mass_le (a c1 c2 c3 : K) (ha : a ≠ 0) :
    eventMass (uniformPairField (K := K))
        (fun z : K × K => z.1 * (a * z.2 + c1) + c2 * z.2 + c3 = 0)
      ≤ (2 * (Fintype.card K : ℝ) - 1) / (Fintype.card K : ℝ) ^ 2 := by
  classical
  have hg1 : 1 ≤ Fintype.card K := Fintype.card_pos_iff.mpr ⟨0⟩
  have hcardprod : Fintype.card (K × K) = Fintype.card K * Fintype.card K :=
    Fintype.card_prod K K
  have hgR : (0 : ℝ) < (Fintype.card K : ℝ) := by
    have : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast this
  have hcardle : ((Finset.univ.filter
        (fun z : K × K => z.1 * (a * z.2 + c1) + c2 * z.2 + c3 = 0)).card : ℝ)
      ≤ 2 * (Fintype.card K : ℝ) - 1 := by
    have hnat := affinePairZeros_card_le a c1 c2 c3 ha
    rw [affinePairZeros] at hnat
    have hcast : ((2 * Fintype.card K - 1 : ℕ) : ℝ) = 2 * (Fintype.card K : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * Fintype.card K)]
      push_cast
      ring
    have hle : ((Finset.univ.filter
          (fun z : K × K => z.1 * (a * z.2 + c1) + c2 * z.2 + c3 = 0)).card : ℝ)
        ≤ ((2 * Fintype.card K - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    rwa [hcast] at hle
  unfold eventMass uniformPairField
  rw [Finset.sum_const, nsmul_eq_mul, hcardprod]
  have hcast : ((Fintype.card K * Fintype.card K : ℕ) : ℝ)
      = (Fintype.card K : ℝ) * (Fintype.card K : ℝ) := by push_cast; ring
  rw [hcast]
  have hnn : (0 : ℝ) ≤ ((Fintype.card K : ℝ) * (Fintype.card K : ℝ))⁻¹ := by positivity
  calc ((Finset.univ.filter
          (fun z : K × K => z.1 * (a * z.2 + c1) + c2 * z.2 + c3 = 0)).card : ℝ)
        * ((Fintype.card K : ℝ) * (Fintype.card K : ℝ))⁻¹
      ≤ (2 * (Fintype.card K : ℝ) - 1)
          * ((Fintype.card K : ℝ) * (Fintype.card K : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right hcardle hnn
    _ = (2 * (Fintype.card K : ℝ) - 1) / (Fintype.card K : ℝ) ^ 2 := by
        rw [div_eq_mul_inv]
        congr 1
        ring

/-- The masses of an event and its complement sum to one. -/
theorem eventMass_compl {X : Type*} [Fintype X] (p : FinDist X)
    (E : X → Prop) [DecidablePred E] :
    eventMass p E + eventMass p (fun x => ¬ E x) = 1 := by
  classical
  unfold eventMass
  rw [Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := E)
    (f := fun x => p.prob x)]
  exact p.sum_one

/-- A bilinear expression with nonzero mixed coefficient is nonzero on a uniform field pair with
probability at least one quarter. See [BuhrmanSpalek2006]. -/
theorem revealing_pair_mass_ge (a c1 c2 c3 : K) (ha : a ≠ 0) :
    (1 / 4 : ℝ) ≤ 1 - eventMass (uniformPairField (K := K))
        (fun z : K × K => z.1 * (a * z.2 + c1) + c2 * z.2 + c3 = 0) := by
  classical
  have hgR : (0 : ℝ) < (Fintype.card K : ℝ) := by
    have : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast this
  have hbad := affinePair_bad_mass_le a c1 c2 c3 ha

  have hrewrite : (1 : ℝ) - (2 * (Fintype.card K : ℝ) - 1) / (Fintype.card K : ℝ) ^ 2
      = (1 - ((Fintype.card K : ℝ))⁻¹) ^ 2 := by
    have hgne : (Fintype.card K : ℝ) ≠ 0 := hgR.ne'
    field_simp
    ring

  have hg2 : (2 : ℝ) ≤ (Fintype.card K : ℝ) := by
    have hc : 1 < Fintype.card K := Fintype.one_lt_card
    exact_mod_cast hc
  have hinv : ((Fintype.card K : ℝ))⁻¹ ≤ 1 / 2 := by
    have := one_div_le_one_div_of_le (a := (2 : ℝ)) (by norm_num) hg2
    simpa [one_div] using! this
  have hsquare : (1 / 4 : ℝ) ≤ (1 - ((Fintype.card K : ℝ))⁻¹) ^ 2 := by
    nlinarith [hinv]
  linarith [hrewrite, hsquare, hbad]

end Qatlib.Papers.MatProdVerify04.MainResults
