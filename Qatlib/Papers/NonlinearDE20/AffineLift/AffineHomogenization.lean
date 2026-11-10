/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
open Matrix

namespace Qatlib.Papers.NonlinearDE20.AffineLift.Model

def homogenize {I : Type} (x : I→ℂ) : Option I→ℂ := fun j=>j.elim 1 x

def affineMatrix {I : Type} (A : Matrix I I ℂ) (b : I→ℂ) : Matrix (Option I) (Option I) ℂ
  | some i,some j=>A i j
  | some i,none=>b i
  | none,_=>0

theorem affineMatrix_some {I : Type} [Fintype I] (A : Matrix I I ℂ) (b x : I→ℂ) (i : I) :
    (affineMatrix A b*ᵥ homogenize x) (some i)=(A*ᵥ x+b) i := by
  simp [Matrix.mulVec,dotProduct,Fintype.sum_option,affineMatrix,homogenize,add_comm]

theorem affineMatrix_none {I : Type} [Fintype I] (A : Matrix I I ℂ) (b x : I→ℂ) :
    (affineMatrix A b*ᵥ homogenize x) none=0 := by
  simp [Matrix.mulVec,dotProduct,affineMatrix]

theorem affine_euler {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (b x : I→ℂ) (dt : ℂ) :
    (1+dt • affineMatrix A b)*ᵥ homogenize x=homogenize (x+dt • (A*ᵥ x+b)) := by
  rw [Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec]
  funext j
  cases j with
  | none => simp [homogenize,affineMatrix_none]
  | some i => simp [homogenize,affineMatrix_some,mul_add]

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

def originalCoordinates {I : Type} (y : Option I→ℂ) : I→ℂ :=fun i=>y (some i)

theorem originalCoordinates_homogenize {I : Type} (x : I→ℂ) :
    originalCoordinates (homogenize x)=x := rfl

theorem homogenize_normSq {I : Type} [Fintype I] (x : I→ℂ) :
    (∑ j : Option I,Complex.normSq (homogenize x j))=1+∑ i,Complex.normSq (x i) := by
  simp [Fintype.sum_option,homogenize]

end Qatlib.Papers.NonlinearDE20.AffineLift.Model
