/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinBool08.MainResults.BentCore.Basic

/-!
# Maiorana-McFarland bent functions and their duals

Defines the Maiorana-McFarland function `mm`, its dual formula `mmDual`, and the Walsh transform
on pairs of binary vectors. Summation over one component gives a flat spectrum with signs
prescribed by the dual formula. See [Roetteler2008].

## Main statements

* `lemma4_maiorana_mcfarland`: the Maiorana-McFarland function is bent and has the displayed
  Walsh spectrum.

## References

* [Roetteler, 2008][Roetteler2008]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.NonlinBool08.MainResults.MaioranaMcFarland

open Qatlib.Papers.NonlinBool08.MainResults.BentCore

/-- Every binary vector sums with itself to zero. -/
lemma add_self_bvec {n : ℕ} (u : BVec n) : u + u = 0 := by
  funext i
  rcases zmod2_cases (u i) with h | h <;>
    simp [Pi.add_apply, h, one_add_one_zmod2]

/-- Every binary vector is its own additive inverse. -/
lemma neg_bvec {n : ℕ} (u : BVec n) : -u = u := by
  funext i
  rcases zmod2_cases (u i) with h | h <;>
    simp [Pi.neg_apply, h, neg_one_zmod2]

/-- The Maiorana-McFarland Boolean function `(x, y) ↦ dot x (π y) + g y`. -/
def mm {n : ℕ} (π : Equiv.Perm (BVec n)) (g : BVec n → ZMod 2)
    (p : BVec n × BVec n) : ZMod 2 :=
  dot p.1 (π p.2) + g p.2

/-- The Maiorana-McFarland dual formula `dot (π.symm u) v + g (π.symm u)`. -/
def mmDual {n : ℕ} (π : Equiv.Perm (BVec n)) (g : BVec n → ZMod 2)
    (u v : BVec n) : ZMod 2 :=
  dot (π.symm u) v + g (π.symm u)

/-- The unnormalized Walsh coefficient of a Boolean function on a pair of binary vector spaces. -/
def pwalsh {n : ℕ} (F : BVec n × BVec n → ZMod 2) (u v : BVec n) : ℤ :=
  ∑ y : BVec n, ∑ x : BVec n, eps (dot u x + dot v y) * eps (F (x, y))

/-- The condition that every squared pair-space Walsh coefficient equals `2 ^ (2 * n)`. -/
def Bent2 {n : ℕ} (F : BVec n × BVec n → ZMod 2) : Prop :=
  ∀ u v, pwalsh F u v ^ 2 = (2 : ℤ) ^ (2 * n)

/-- The Maiorana-McFarland function is bent on the pair space, with Walsh coefficient `2 ^ n *
eps (mmDual π g u v)`. See [Roetteler, Lemma 4][Roetteler2008]. -/
theorem lemma4_maiorana_mcfarland {n : ℕ} (π : Equiv.Perm (BVec n))
    (g : BVec n → ZMod 2) :
    Bent2 (mm π g) ∧
    (∀ u v, pwalsh (mm π g) u v = (2 : ℤ) ^ n * eps (mmDual π g u v)) := by

  have hinner : ∀ (u v y : BVec n),
      (∑ x : BVec n, eps (dot u x + dot v y) * eps (mm π g (x, y)))
        = (if u + π y = 0 then 2 ^ n else 0) * eps (dot v y + g y) := by
    intro u v y
    have hterm : ∀ x : BVec n,
        eps (dot u x + dot v y) * eps (mm π g (x, y))
          = eps (dot (u + π y) x) * eps (dot v y + g y) := by
      intro x
      show eps (dot u x + dot v y) * eps (dot x (π y) + g y)
          = eps (dot (u + π y) x) * eps (dot v y + g y)
      have h1 : dot u x + dot x (π y) = dot (u + π y) x := by
        show dotProduct u x + dotProduct x (π y) = dotProduct (u + π y) x
        rw [dotProduct_comm x (π y), ← add_dotProduct]
      calc eps (dot u x + dot v y) * eps (dot x (π y) + g y)
          = (eps (dot u x) * eps (dot v y)) *
              (eps (dot x (π y)) * eps (g y)) := by rw [eps_add, eps_add]
        _ = (eps (dot u x) * eps (dot x (π y))) *
              (eps (dot v y) * eps (g y)) := by ring
        _ = eps (dot u x + dot x (π y)) * eps (dot v y + g y) := by
              rw [← eps_add, ← eps_add]
        _ = eps (dot (u + π y) x) * eps (dot v y + g y) := by rw [h1]
    calc (∑ x : BVec n, eps (dot u x + dot v y) * eps (mm π g (x, y)))
        = ∑ x : BVec n, eps (dot (u + π y) x) * eps (dot v y + g y) := by
            apply Finset.sum_congr rfl
            intro x _
            exact hterm x
      _ = (∑ x : BVec n, eps (dot (u + π y) x)) * eps (dot v y + g y) := by
            rw [Finset.sum_mul]
      _ = (if u + π y = 0 then 2 ^ n else 0) * eps (dot v y + g y) := by
            rw [sum_eps_dot]

  have houter : ∀ (u v : BVec n),
      (∑ y : BVec n, (if u + π y = 0 then 2 ^ n else 0) * eps (dot v y + g y))
        = (2 : ℤ) ^ n * eps (mmDual π g u v) := by
    intro u v
    calc (∑ y : BVec n, (if u + π y = 0 then 2 ^ n else 0) * eps (dot v y + g y))
        = (if u + π (π.symm u) = 0 then 2 ^ n else 0) *
            eps (dot v (π.symm u) + g (π.symm u)) := by
          apply Fintype.sum_eq_single (π.symm u)
          intro y hy
          have hne : u + π y ≠ 0 := by
            intro h0
            have hpu : π y = u := by
              have h1 : -u = π y := add_eq_zero_iff_neg_eq.mp h0
              rw [← h1, neg_bvec u]
            exact hy (by rw [← π.symm_apply_apply y, hpu])
          rw [if_neg hne, zero_mul]
      _ = (2 : ℤ) ^ n * eps (mmDual π g u v) := by
          rw [π.apply_symm_apply, add_self_bvec, if_pos rfl]
          have harg : dot v (π.symm u) + g (π.symm u)
              = dot (π.symm u) v + g (π.symm u) := by
            show dotProduct v (π.symm u) + g (π.symm u)
                = dotProduct (π.symm u) v + g (π.symm u)
            rw [dotProduct_comm]
          rw [harg]
          simp only [mmDual]
  have hformula : ∀ u v,
      pwalsh (mm π g) u v = (2 : ℤ) ^ n * eps (mmDual π g u v) := by
    intro u v
    rw [pwalsh]
    simp only [hinner]
    exact houter u v
  refine ⟨?_, hformula⟩
  intro u v
  rw [hformula u v, mul_pow, eps_sq, mul_one, ← pow_mul, Nat.mul_comm]

end Qatlib.Papers.NonlinBool08.MainResults.MaioranaMcFarland
