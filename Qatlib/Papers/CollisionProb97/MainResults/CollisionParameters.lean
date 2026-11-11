/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.CollisionExecution
import Qatlib.Papers.CollisionProb97.MainResults.Theorem2RToOne
import Qatlib.Papers.CollisionProb97.MainResults.IntegerParameters
import Qatlib.Papers.CollisionProb97.MainResults.InputSelection

/-!
# Image-size parameters for collision finding

This module rewrites the collision query bound in terms of the image cardinality and selects a
concrete integer cube-root table size. The results apply to the regular collision algorithm of
[BrassardHoyerTapp1998Collision].

The theorem `cube_root_algorithm` supplies a nonempty selected table together with its exact
cardinality and an explicit cube-root expected-cost bound.

## Main statements

* `image_card_quotient`: For a positive regular fiber size, the image cardinality is the domain
  cardinality divided by `r` [BrassardHoyerTapp1998Collision].
* `run_expected_image`: Bounds the expected collision cost by the table size plus `(1 + 4 *
  SourcePhaseConstant l) * sqrt 2 * sqrt (|image F| / K.card)` [BrassardHoyerTapp1998Collision].
* `cube_root_algorithm`: Selects a nonempty table of size `Nat.nthRoot 3 |image F|` and proves
  the stated explicit expected-cost bound proportional to the real cube root of the image size,
  as in [BrassardHoyerTapp1998Collision].

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal Classical
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
namespace Qatlib.Papers.CollisionProb97.MainResults.CollisionParameters
variable {X R : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [AddCommGroup R] [Fintype R] [DecidableEq R]

omit [Nonempty X] [AddCommGroup R] in

/-- For a positive regular fiber size, the image cardinality is the domain cardinality divided
by `r` [BrassardHoyerTapp1998Collision]. -/
theorem image_card_quotient (F : X → R) (r : ℕ) (hr : 0 < r) (hF : RToOne F r) :
    (Finset.univ.image F).card = Fintype.card X/r := by
  rw [card_eq_image_card_mul F r hF]
  simp [hr.ne']

/-- Bounds the expected collision cost by the table size plus `(1 + 4 * SourcePhaseConstant l) *
sqrt 2 * sqrt (|image F| / K.card)` [BrassardHoyerTapp1998Collision]. -/
theorem run_expected_image (F : X → R) (r : ℕ) (hr : 2 ≤ r) (hF : RToOne F r)
    (K : Finset X) (hK : K.Nonempty) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) :
    expectedCost (CollisionExecution.run F r hr hF K hK l hl hl4) ≤
      ENNReal.ofReal ((K.card:ℝ)+(1+4*SourcePhaseConstant l)*Real.sqrt 2*
        Real.sqrt (((Finset.univ.image F).card:ℝ)/K.card)) := by
  have hk : 1 ≤ K.card := Finset.card_pos.mpr hK
  have hs := sqrt_div_rToOne_le (N := (Fintype.card X:ℝ))
    (by exact_mod_cast Fintype.card_pos (α := X)) hr hk
  have hr1 : 1 ≤ r := by omega
  have hN : (Fintype.card X:ℝ) = ((Finset.univ.image F).card:ℝ)*(r:ℝ) := by
    exact_mod_cast card_eq_image_card_mul F r hF
  have hrR : (r:ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hkR : (K.card:ℝ) ≠ 0 := by exact_mod_cast (show K.card ≠ 0 by omega)
  have he : (Fintype.card X:ℝ)/((r:ℝ)*K.card) = ((Finset.univ.image F).card:ℝ)/K.card := by
    rw [hN]
    field_simp
  rw [he] at hs
  have hg : 0 ≤ 1+4*SourcePhaseConstant l := by
    have := search_source_constant_nonneg l hl hl4
    linarith
  have hb := CollisionExecution.run_expected F r hr hF K hK l hl hl4
  calc
    expectedCost (CollisionExecution.run F r hr hF K hK l hl hl4) ≤
        (K.card:ℝ≥0∞)+ENNReal.ofReal ((1+4*SourcePhaseConstant l)*
          Real.sqrt ((Fintype.card X:ℝ)/(((r-1)*K.card:ℕ):ℝ))) := hb
    _ = ENNReal.ofReal ((K.card:ℝ)+(1+4*SourcePhaseConstant l)*
          Real.sqrt ((Fintype.card X:ℝ)/(((r-1)*K.card:ℕ):ℝ))) := by
      rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (mul_nonneg hg (Real.sqrt_nonneg _)),
        ENNReal.ofReal_natCast]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply add_le_add le_rfl
      rw [Nat.cast_mul, Nat.cast_sub hr1, Nat.cast_one]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hg

/-- Selects a nonempty table of size `Nat.nthRoot 3 |image F|` and proves the stated explicit
expected-cost bound proportional to the real cube root of the image size, as in
[BrassardHoyerTapp1998Collision]. -/
theorem cube_root_algorithm (F : X → R) (r : ℕ) (hr : 2 ≤ r) (hF : RToOne F r)
    (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) :
    ∃ (K : Finset X) (hK : K.Nonempty),
      K = InputSelection.select (Nat.nthRoot 3 (Finset.univ.image F).card) ∧
      K.card = Nat.nthRoot 3 (Finset.univ.image F).card ∧
      expectedCost (CollisionExecution.run F r hr hF K hK l hl hl4) ≤
        ENNReal.ofReal ((1+3*(1+4*SourcePhaseConstant l)*Real.sqrt 2)*
          ((Finset.univ.image F).card:ℝ)^(1/3:ℝ)) := by
  let m := (Finset.univ.image F).card
  let k := Nat.nthRoot 3 m
  have hm : 1 ≤ m := Finset.card_pos.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
  obtain ⟨hk,hpow,_⟩ := IntegerParameters.cube_root_bounds m hm
  change 1 ≤ k at hk
  change k^3 ≤ m at hpow
  have hkm : k ≤ m := by nlinarith [Nat.mul_self_le_mul_self hk]
  have hmN : m ≤ Fintype.card X := (Finset.card_image_le).trans_eq Finset.card_univ
  let K := InputSelection.select (X := X) k
  have hcard : K.card = k := InputSelection.select_card k (hkm.trans hmN)
  have hK : K.Nonempty := InputSelection.select_nonempty k hk (hkm.trans hmN)
  refine ⟨K,hK,rfl,hcard,?_⟩
  have hb := run_expected_image F r hr hF K hK l hl hl4
  rw [hcard] at hb
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hs := IntegerParameters.cube_root_search_bound m hm
  have hkroot := (IntegerParameters.cube_root_real_window m).1
  have hg : 0 ≤ (1+4*SourcePhaseConstant l)*Real.sqrt 2 := by
    have := search_source_constant_nonneg l hl hl4
    positivity
  have hp := mul_le_mul_of_nonneg_left hs hg
  have hkp :=
      mul_le_mul_of_nonneg_left hkroot
      (show 0 ≤ 1+3*((1+4*SourcePhaseConstant l)*Real.sqrt 2) by positivity)
  change (k:ℝ)+(1+4*SourcePhaseConstant l)*Real.sqrt 2*Real.sqrt ((m:ℝ)/k) ≤ _
  change Real.sqrt ((m:ℝ)/k) ≤ 3*(k:ℝ) at hs
  nlinarith

end Qatlib.Papers.CollisionProb97.MainResults.CollisionParameters
