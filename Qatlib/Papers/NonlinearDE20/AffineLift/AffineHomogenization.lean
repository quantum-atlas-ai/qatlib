/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# Homogeneous-coordinate lift of affine dynamics

Adds a constant coordinate with `homogenize` and represents the affine vector field by the
linear matrix `affineMatrix`. The lift is compatible with Euler steps and derivatives, and its
original coordinates and squared norm have explicit formulas. See [LloydEtAl2020].

## Main statements

* `affine_euler`: a homogeneous linear Euler step realizes the affine update.
* `affine_hasDerivAt`: an affine trajectory lifts to the corresponding linear differential
  equation.
* `homogenize_normSq`: the new coordinate adds one to the squared norm.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
open Matrix

namespace Qatlib.Papers.NonlinearDE20.AffineLift.Model

/-- Adds a constant coordinate equal to one at `none`, retaining `x i` at each `some i`. -/
def homogenize {I : Type} (x : I→ℂ) : Option I→ℂ := fun j=>j.elim 1 x

/-- The homogeneous-coordinate matrix with block `A`, forcing column `b`, and zero row for the
constant coordinate. -/
def affineMatrix {I : Type} (A : Matrix I I ℂ) (b : I→ℂ) : Matrix (Option I) (Option I) ℂ
  | some i,some j=>A i j
  | some i,none=>b i
  | none,_=>0

/-- On an original coordinate, the homogeneous matrix applied to `homogenize x` equals `A *ᵥ x +
b`. -/
theorem affineMatrix_some {I : Type} [Fintype I] (A : Matrix I I ℂ) (b x : I→ℂ) (i : I) :
    (affineMatrix A b*ᵥ homogenize x) (some i)=(A*ᵥ x+b) i := by
  simp [Matrix.mulVec,dotProduct,Fintype.sum_option,affineMatrix,homogenize,add_comm]

/-- The constant coordinate of the homogeneous matrix action on `homogenize x` is zero. -/
theorem affineMatrix_none {I : Type} [Fintype I] (A : Matrix I I ℂ) (b x : I→ℂ) :
    (affineMatrix A b*ᵥ homogenize x) none=0 := by
  simp [Matrix.mulVec,dotProduct,affineMatrix]

/-- Applying the homogeneous Euler matrix to `homogenize x` yields the homogenization of the
affine Euler update. See [LloydEtAl2020]. -/
theorem affine_euler {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (b x : I→ℂ) (dt : ℂ) :
    (1+dt • affineMatrix A b)*ᵥ homogenize x=homogenize (x+dt • (A*ᵥ x+b)) := by
  rw [Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec]
  funext j
  cases j with
  | none => simp [homogenize,affineMatrix_none]
  | some i => simp [homogenize,affineMatrix_some,mul_add]

/-- A trajectory with derivative `A *ᵥ x t + b` has a homogenized trajectory whose derivative is
the homogeneous matrix action at time `t`. -/
theorem affine_hasDerivAt {I : Type} [Fintype I] (A : Matrix I I ℂ) (b : I→ℂ)
    (x : ℝ→I→ℂ) (t : ℝ) (hx : HasDerivAt x (A*ᵥ x t+b) t) :
    HasDerivAt (fun s=>homogenize (x s)) (affineMatrix A b*ᵥ homogenize (x t)) t := by
  rw [hasDerivAt_pi]
  intro j
  cases j with
  | none =>
    simpa only [homogenize,Option.elim_none,affineMatrix_none] using (hasDerivAt_const t (1:ℂ))
  | some i =>
    simpa only [homogenize,Option.elim_some,affineMatrix_some] using (hasDerivAt_pi.mp hx i)

/-- Restricts a homogeneous-coordinate vector to the coordinates indexed by `some i`. -/
def originalCoordinates {I : Type} (y : Option I→ℂ) : I→ℂ :=fun i=>y (some i)

/-- Restricting a homogenized vector to its original coordinates recovers that vector. -/
theorem originalCoordinates_homogenize {I : Type} (x : I→ℂ) :
    originalCoordinates (homogenize x)=x := rfl

/-- The sum of squared norms of a homogenized vector equals one plus the corresponding sum for
the original vector. -/
theorem homogenize_normSq {I : Type} [Fintype I] (x : I→ℂ) :
    (∑ j : Option I,Complex.normSq (homogenize x j))=1+∑ i,Complex.normSq (x i) := by
  simp [Fintype.sum_option,homogenize]

end Qatlib.Papers.NonlinearDE20.AffineLift.Model
