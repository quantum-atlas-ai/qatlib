/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Shear Commutator Algebra

Shear Commutator Algebra constructions and identities for Spinor Sampling.
-/
set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Model

-- V = Rz(pi), W = Ry(pi/2), s = cos(pi/4) = sin(pi/4).
-- The four real coordinates are (Re z0, Im z0, Re z1, Im z1).
/-- When `2 * s^2 = 1`, the four coordinate operations of the commutator send `(a, b, c, d)` to
`(c, d, -a, -b)`. -/
theorem commutator_coordinates (a b c d s : ℝ) (hs : 2*s^2=1) :
    (let a1 := s*a+s*c
     let b1 := s*b+s*d
     let c1 := -s*a+s*c
     let d1 := -s*b+s*d
     let a2 := -b1
     let b2 := a1
     let c2 := d1
     let d2 := -c1
     let a3 := s*a2-s*c2
     let b3 := s*b2-s*d2
     let c3 := s*a2+s*c2
     let d3 := s*b2+s*d2
     let a4 := b3
     let b4 := -a3
     let c4 := -d3
     let d4 := c3
     a4=c ∧ b4=d ∧ c4=-a ∧ d4=-b) := by
  dsimp
  constructor
  · linear_combination c*hs
  constructor
  · linear_combination d*hs
  constructor
  · linear_combination -a*hs
  · linear_combination -b*hs

/-- Construction for half Turn in the shear commutator algebra model. -/
def halfTurn (q : ℝ × ℝ) : ℝ × ℝ := (q.2,-q.1)

/-- Construction for real Spinor At in the shear commutator algebra model. -/
def realSpinorAt : ℕ → (ℝ × ℝ) → (ℝ × ℝ)
  | 0,q => q
  | n+1,q => halfTurn (realSpinorAt n q)

/-- Any number of iterations of `(x, y) ↦ (y, -x)` preserves the sum of the squared real
amplitudes. -/
theorem repeated_halfTurn_normalization (n : ℕ) (x y : ℝ) :
    (realSpinorAt n (x,y)).1^2 + (realSpinorAt n (x,y)).2^2 = x^2+y^2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (realSpinorAt n (x,y)).2^2 + (-(realSpinorAt n (x,y)).1)^2 = x^2+y^2
    simpa only [neg_sq,add_comm] using ih

/-- After `n` iterations of `(x, y) ↦ (y, -x)`, the population difference is the initial
difference `x^2 - y^2` multiplied by `(-1)^n`. -/
theorem repeated_halfTurn_population (n : ℕ) (x y : ℝ) :
    (realSpinorAt n (x,y)).1^2 - (realSpinorAt n (x,y)).2^2 =
      (-1 : ℝ)^n * (x^2-y^2) := by
  induction n with
  | zero => simp [realSpinorAt]
  | succ n ih =>
    change (realSpinorAt n (x,y)).2^2 - (-(realSpinorAt n (x,y)).1)^2 =
      (-1 : ℝ)^(n+1) * (x^2-y^2)
    rw [neg_sq,pow_succ]
    linear_combination -ih

#print axioms Qatlib.Concepts.SpinorSampling.Model.commutator_coordinates
#print axioms Qatlib.Concepts.SpinorSampling.Model.repeated_halfTurn_normalization
#print axioms Qatlib.Concepts.SpinorSampling.Model.repeated_halfTurn_population
#eval Lean.versionString
end Qatlib.Concepts.SpinorSampling.Model
