module

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

public import Qatlib.Papers.GaussSumEst02.RingEstimate.ImprimitiveLift
public import Qatlib.Papers.GaussSumEst02.GaloisAction.CyclotomicBoundary

@[expose] public section

/-!
# Concrete consumer for the corrected imprimitive lift and Section 5.2 boundary

This ordinary-module consumer runs the new top-level theorems on explicit
non-degenerate instances: the quadratic Dirichlet character modulo `3` lifted to
modulo `9` (so `p = 3`, `r = 2`, `s = 1`), and the fifth cyclotomic field with
unit exponent `2` and non-unit exponent `5`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace QatlibTests.GaussSumEst02ImprimitiveLiftRegression

open Qatlib.Papers.GaussSumEst02.MainResults.Source
open Qatlib.Papers.GaussSumEst02.RingEstimate
open Qatlib.Papers.GaussSumEst02.RingEstimate.ImprimitiveLift
open Qatlib.Papers.GaussSumEst02.GaloisAction.CyclotomicBoundary

instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The integer-valued quadratic character modulo `3`; its complex version below
is the Dirichlet character consumed by the lift theorem. -/
def legendreThreeQ (x : ZMod 3) : ℤ := if x = 0 then 0 else if x = 1 then 1 else -1

/-- A unit of `ZMod 9` has residue value not divisible by `3`. -/
private theorem zmod_nine_unit_val {x : ZMod 9} (hx : IsUnit x) : ¬ 3 ∣ x.val := by
  have hx2 := hx
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime] at hx2
  intro hnd
  have hc3 : x.val.Coprime 3 :=
    ((Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 3 x.val).mp (Nat.coprime_comm.mp hx2)).symm
  exact ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mp (Nat.coprime_comm.mp hc3)) hnd

/-- A nonunit of `ZMod 9` has residue value divisible by `3`. -/
private theorem zmod_nine_nonunit_val {x : ZMod 9} (hx : ¬ IsUnit x) : 3 ∣ x.val := by
  have hx2 := hx
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime] at hx2
  by_contra hnd
  refine hx2 ?_
  show x.val.Coprime (3 ^ 2)
  exact ((Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 3 x.val).mpr
    ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr hnd)).symm

/-- The unique nontrivial Dirichlet character modulo `3` (the Legendre symbol). -/
def legendreThree : DirichletChar 3 where
  toFun := fun x => (legendreThreeQ x : ℂ)
  map_one' := by
    rw [show legendreThreeQ 1 = 1 from by decide]
    simp
  map_zero_of_not_unit := by
    intro x hx
    have hx0 : x = 0 := by
      by_contra hne
      exact hx (isUnit_iff_ne_zero.mpr hne)
    rw [hx0, show legendreThreeQ 0 = 0 from by decide]
    simp
  map_mul_of_unit := by
    intro x y _ _
    rw [show legendreThreeQ (x * y) = legendreThreeQ x * legendreThreeQ y from by
      have hx1 : x = ((x.val : ℕ) : ZMod 3) := (ZMod.natCast_zmod_val x).symm
      have hy1 : y = ((y.val : ℕ) : ZMod 3) := (ZMod.natCast_zmod_val y).symm
      rw [hx1, hy1]
      exact (by decide : ∀ v ∈ Finset.range 3, ∀ w ∈ Finset.range 3,
        legendreThreeQ (((v : ℕ) : ZMod 3) * ((w : ℕ) : ZMod 3))
          = legendreThreeQ ((v : ℕ) : ZMod 3) * legendreThreeQ ((w : ℕ) : ZMod 3))
        x.val (Finset.mem_range.mpr x.val_lt) y.val (Finset.mem_range.mpr y.val_lt)]
    push_cast
    ring
  norm_eq_one := by
    intro x hx
    have hne : x ≠ 0 := IsUnit.ne_zero hx
    have key : legendreThreeQ x = 1 ∨ legendreThreeQ x = -1 := by
      have hx0 : x.val ≠ 0 := fun h0 =>
        absurd (by rw [← ZMod.natCast_zmod_val x, h0]; decide) hne
      have hx1 : x = ((x.val : ℕ) : ZMod 3) := (ZMod.natCast_zmod_val x).symm
      rw [hx1]
      exact (by decide : ∀ v ∈ Finset.range 3, v ≠ 0 →
        legendreThreeQ ((v : ℕ) : ZMod 3) = 1 ∨ legendreThreeQ ((v : ℕ) : ZMod 3) = -1)
        x.val (Finset.mem_range.mpr x.val_lt) hx0
    clear hne
    rcases key with h1 | h1
    · rw [h1]
      simp
    · rw [h1]
      simp

/-- The integer-valued Dirichlet character modulo `9` induced by
`legendreThreeQ` modulo `3`. -/
def inducedNineQ (x : ZMod 9) : ℤ := legendreThreeQ ((x.val : ℕ) : ZMod 3)

/-- The Dirichlet character modulo `9` induced by `legendreThree` modulo `3`. -/
def inducedNine : DirichletChar 9 where
  toFun := fun x => (inducedNineQ x : ℂ)
  map_one' := by
    rw [show inducedNineQ 1 = 1 from by decide]
    simp
  map_zero_of_not_unit := by
    intro x hx
    have hz : ((x.val : ℕ) : ZMod 3) = 0 :=
      (ZMod.natCast_eq_zero_iff x.val 3).mpr (zmod_nine_nonunit_val hx)
    rw [show inducedNineQ x = 0 from by
      show legendreThreeQ ((x.val : ℕ) : ZMod 3) = 0
      rw [hz]
      decide]
    simp
  map_mul_of_unit := by
    intro x y hx hy
    have hux := zmod_nine_unit_val hx
    have huy := zmod_nine_unit_val hy
    rw [show inducedNineQ (x * y) = inducedNineQ x * inducedNineQ y from by
      have hx1 : x = ((x.val : ℕ) : ZMod 9) := (ZMod.natCast_zmod_val x).symm
      have hy1 : y = ((y.val : ℕ) : ZMod 9) := (ZMod.natCast_zmod_val y).symm
      rw [hx1, hy1]
      exact (by decide : ∀ v ∈ Finset.range 9, ∀ w ∈ Finset.range 9, (¬ 3 ∣ v) → (¬ 3 ∣ w) →
        inducedNineQ (((v : ℕ) : ZMod 9) * ((w : ℕ) : ZMod 9))
          = inducedNineQ ((v : ℕ) : ZMod 9) * inducedNineQ ((w : ℕ) : ZMod 9))
        x.val (Finset.mem_range.mpr x.val_lt) y.val (Finset.mem_range.mpr y.val_lt) hux huy]
    push_cast
    ring
  norm_eq_one := by
    intro x hx
    have key : legendreThreeQ ((x.val : ℕ) : ZMod 3) = 1
        ∨ legendreThreeQ ((x.val : ℕ) : ZMod 3) = -1 := by
      have hux := zmod_nine_unit_val hx
      exact (by decide : ∀ v : ZMod 9, (¬ 3 ∣ v.val) →
        legendreThreeQ ((v.val : ℕ) : ZMod 3) = 1
          ∨ legendreThreeQ ((v.val : ℕ) : ZMod 3) = -1) x hux
    rcases key with h1 | h1
    · show ‖((legendreThreeQ ((x.val : ℕ) : ZMod 3) : ℤ) : ℂ)‖ = 1
      rw [h1]
      simp
    · show ‖((legendreThreeQ ((x.val : ℕ) : ZMod 3) : ℤ) : ℂ)‖ = 1
      rw [h1]
      simp

/-- `inducedNine` is induced by `legendreThree` in the sense of `IsInducedBy`. -/
theorem inducedNine_isInducedBy : IsInducedBy (p := 3) (r := 2) (s := 1) inducedNine legendreThree := by
  intro x
  show ((inducedNineQ x : ℤ) : ℂ) = ((legendreThreeQ ((x.val : ℕ) : ZMod 3) : ℤ) : ℂ)
  rfl

instance : NeZero (3 ^ 2) := ⟨by norm_num⟩
instance : NeZero (3 ^ (2 - 1)) := ⟨by norm_num⟩
instance : NeZero (3 ^ 1) := ⟨by norm_num⟩

/-- The corrected Fact 11 lift at `β = 3 = 3 * 1` for the concrete induced
character modulo `9`: the imprimitive Gauss sum equals `3` times the Gauss sum
of the Legendre character modulo `3` at `b = 1`. -/
theorem imprimitive_lift_nine_at_three :
    ringGaussSum inducedNine (zmodAddChar (3 ^ 2) (by norm_num)) ((3 : ℕ) : ZMod (3 ^ 2))
      = (3 : ℂ) * ringGaussSum legendreThree (zmodAddChar (3 ^ (2 - 1)) (by norm_num))
        ((1 : ℕ) : ZMod (3 ^ (2 - 1))) := by
  have h := (ringGaussSum_induced (p := 3) (r := 2) (s := 1)
    (by decide : Nat.Prime 3) (by norm_num : 0 < 1) (by norm_num : 1 < 2)
    inducedNine legendreThree inducedNine_isInducedBy).2
  rw [h ((3 : ℕ) : ZMod (3 ^ 2)) ((1 : ℕ) : ZMod (3 ^ (2 - 1))) (by decide)]
  norm_num

/-- The corrected Fact 11 vanishing branch at `β = 1` for the concrete induced
character modulo `9`: `3` does not divide the frequency, so the imprimitive
Gauss sum is zero. -/
theorem imprimitive_lift_nine_vanish :
    ringGaussSum inducedNine (zmodAddChar (3 ^ 2) (by norm_num)) ((1 : ℕ) : ZMod (3 ^ 2)) = 0 := by
  have h := (ringGaussSum_induced (p := 3) (r := 2) (s := 1)
    (by decide : Nat.Prime 3) (by norm_num : 0 < 1) (by norm_num : 1 < 2)
    inducedNine legendreThree inducedNine_isInducedBy).1
  exact h ((1 : ℕ) : ZMod (3 ^ 2)) (by decide)

instance : NeZero 5 := ⟨by norm_num⟩

/-- The corrected Section 5.2 boundary at `m = 5`: the automorphism sending
`ζ₅ ↦ ζ₅²` exists since `2` is a unit modulo `5`. -/
theorem cyclotomic_boundary_five_unit :
    ∃ σ : CyclotomicField 5 ℚ ≃ₐ[ℚ] CyclotomicField 5 ℚ,
      σ (zetaRat 5) = zetaRat 5 ^ 2 := by
  exact (section52_cyclotomic_boundary 5 2 (by norm_num : 2 ≤ 5)).1
    (by norm_num : Nat.Coprime 2 5)

/-- The corrected Section 5.2 boundary at `m = 5`: no endomorphism sends
`ζ₅ ↦ ζ₅⁵` since `gcd(5, 5) = 5 > 1`. -/
theorem cyclotomic_boundary_five_nonunit
    (σ : CyclotomicField 5 ℚ →ₐ[ℚ] CyclotomicField 5 ℚ) :
    σ (zetaRat 5) ≠ zetaRat 5 ^ 5 := by
  exact (section52_cyclotomic_boundary 5 5 (by norm_num : 2 ≤ 5)).2.1 σ
    (by norm_num : ¬ Nat.Coprime 5 5)

/-- The fifth cyclotomic field has ℚ-dimension `φ(5) = 4`. -/
theorem cyclotomic_finrank_five :
    Module.finrank ℚ (CyclotomicField 5 ℚ) = 4 := by
  have h := (section52_cyclotomic_boundary 5 2 (by norm_num : 2 ≤ 5)).2.2
  rw [h]
  decide

end QatlibTests.GaussSumEst02ImprimitiveLiftRegression
