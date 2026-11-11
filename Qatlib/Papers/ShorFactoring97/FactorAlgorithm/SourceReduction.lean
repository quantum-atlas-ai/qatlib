/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.OrderRecovery.RandomBaseFactor
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section
open scoped Classical
open Qatlib.Concepts.PeriodSampling.OrderRecovery

namespace Qatlib.Papers.ShorFactoring97.FactorAlgorithm

/-- The nonzero residue classes sampled before the order-finding reduction. -/
abbrev Residue (N : ℕ) := {x : ZMod N // x ≠ 0}

/-- Extract a proper gcd from a nonunit, or use the exact-order reduction on a unit. -/
def residueFactor (N : ℕ) [NeZero N] (x : ZMod N) : Option ℕ :=
  if h : IsUnit x then orderFactor N h.unit (orderOf h.unit)
  else
    let g := Nat.gcd N x.val
    if 1 < g ∧ g < N ∧ g ∣ N then some g else none

/-- Every returned value is a proper divisor, for either branch of the reduction. -/
theorem residueFactor_sound (N : ℕ) [NeZero N] (x : ZMod N) (d : ℕ)
    (hd : residueFactor N x = some d) : 1 < d ∧ d < N ∧ d ∣ N := by
  classical
  unfold residueFactor at hd
  split at hd
  · exact orderFactor_sound N _ _ d hd
  · dsimp only at hd
    split at hd
    · cases Option.some.inj hd
      assumption
    · simp at hd

/-- A nonzero nonunit supplies a proper gcd, without invoking order finding. -/
theorem nonunit_gcd_success (N : ℕ) [NeZero N] (hN : 1 < N)
    (x : ZMod N) (hx : x ≠ 0) (hu : ¬ IsUnit x) :
    residueFactor N x = some (Nat.gcd N x.val) := by
  classical
  let : Fact (1 < N) := ⟨hN⟩
  have hxpos : 0 < x.val := by
    apply Nat.pos_of_ne_zero
    rw [ZMod.val_ne_zero]
    exact hx
  have hgpos : 0 < Nat.gcd N x.val := Nat.gcd_pos_of_pos_left _ (by omega)
  have hglt : Nat.gcd N x.val < N :=
    (Nat.gcd_le_right N hxpos).trans_lt (ZMod.val_lt x)
  have hgne : Nat.gcd N x.val ≠ 1 := by
    intro h
    apply hu
    have hc : x.val.Coprime N := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
      exact h
    simpa only [ZMod.natCast_zmod_val] using
      (ZMod.isUnit_iff_coprime x.val N).mpr hc
  simp [residueFactor, hu, show 1 < Nat.gcd N x.val by omega,
    hglt, Nat.gcd_dvd_left]

/-- On a unit, the residue reduction is exactly the existing checked reduction. -/
theorem residueFactor_unit (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) :
    residueFactor N (a : ZMod N) = orderFactor N a (orderOf a) := by
  classical
  simp [residueFactor, a.isUnit]

/-- The proportion of nonzero residue classes returning a proper factor. -/
def residueSuccess (N : ℕ) [NeZero N] : ℝ :=
  (Fintype.card (Residue N) : ℝ)⁻¹ *
    ((Finset.univ.filter (fun x : Residue N => (residueFactor N x.val).isSome)).card : ℝ)

/-- A unit is a nonzero residue whenever the modulus is greater than one. -/
def unitResidue (N : ℕ) [NeZero N] (hN : 1 < N) (a : (ZMod N)ˣ) : Residue N := by
  let : Fact (1 < N) := ⟨hN⟩
  exact ⟨a, a.isUnit.ne_zero⟩

/-- Distinct unit inputs remain distinct residue inputs. -/
theorem unitResidue_injective (N : ℕ) [NeZero N] (hN : 1 < N) :
    Function.Injective (unitResidue N hN) := by
  intro a b h
  exact Units.ext (congrArg Subtype.val h)

/-- The failing residues are exactly the embedded failing units. -/
theorem bad_residue_eq_image (N : ℕ) [NeZero N] (hN : 1 < N) :
    Finset.univ.filter (fun x : Residue N => ¬ (residueFactor N x.val).isSome) =
      (Finset.univ.filter (fun a : (ZMod N)ˣ => ¬ randomBaseGood N a)).image
        (unitResidue N hN) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hx
    have hu : IsUnit x.val := by
      by_contra hu
      have hg := nonunit_gcd_success N hN x.val x.property hu
      simp [hg] at hx
    refine ⟨hu.unit, ?_, ?_⟩
    · have hval : (hu.unit : ZMod N) = x.val := hu.unit_spec
      simpa only [randomBaseGood, ← residueFactor_unit, hval] using hx
    · apply Subtype.ext
      exact hu.unit_spec
  · rintro ⟨a, ha, rfl⟩
    simpa only [randomBaseGood, unitResidue, residueFactor_unit] using ha

/-- Gcd preprocessing preserves or improves the uniform-unit success rate. -/
theorem residueSuccess_ge_units (N : ℕ) [NeZero N] (hN : 1 < N) :
    randomBaseSuccess N ≤ residueSuccess N := by
  classical
  let R := Fintype.card (Residue N)
  let U := Fintype.card ((ZMod N)ˣ)
  let br := (Finset.univ.filter (fun x : Residue N => ¬ (residueFactor N x.val).isSome)).card
  let bu := (Finset.univ.filter (fun a : (ZMod N)ˣ => ¬ randomBaseGood N a)).card
  let gr := (Finset.univ.filter (fun x : Residue N => (residueFactor N x.val).isSome)).card
  let gu := (Finset.univ.filter (fun a : (ZMod N)ˣ => randomBaseGood N a)).card
  have hUR : U ≤ R := Fintype.card_le_of_injective _ (unitResidue_injective N hN)
  have hU : 0 < U := Fintype.card_pos
  have hR : 0 < R := lt_of_lt_of_le hU hUR
  have hbad : br = bu := by
    dsimp [br, bu]
    rw [bad_residue_eq_image N hN, Finset.card_image_of_injective _ (unitResidue_injective N hN)]
  have hpartR : gr + br = R := Finset.card_filter_add_card_filter_not _
  have hpartU : gu + bu = U := Finset.card_filter_add_card_filter_not _
  have hUR' : (U : ℝ) ≤ R := by exact_mod_cast hUR
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hbad' : (br : ℝ) = bu := by exact_mod_cast hbad
  have hpartR' : (gr : ℝ) + br = R := by exact_mod_cast hpartR
  have hpartU' : (gu : ℝ) + bu = U := by exact_mod_cast hpartU
  change (U : ℝ)⁻¹ * gu ≤ (R : ℝ)⁻¹ * gr
  rw [← div_eq_inv_mul, ← div_eq_inv_mul, div_le_div_iff₀ hU' hR']
  have hb : (0 : ℝ) ≤ bu := Nat.cast_nonneg _
  nlinarith

/-- The source's CRT success bound holds for uniformly sampled nonzero residues. -/
theorem residue_crt_success (N : ℕ) [NeZero N] (hN : 1 < N) (hodd : Odd N)
    (hk : 2 ≤ N.primeFactors.card) :
    1 - (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ)) ≤ residueSuccess N := by
  exact (random_base_crt_success_bound N hN hodd hk).trans (residueSuccess_ge_units N hN)

end Qatlib.Papers.ShorFactoring97.FactorAlgorithm
