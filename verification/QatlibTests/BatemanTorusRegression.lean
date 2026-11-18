/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.Charges.ModalHelicity

/-! Regression consumers for compatible and incompatible Bateman pairs and weighted scaling. -/

@[expose] public section
set_option autoImplicit false

open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.KnotLight13.Bateman
open Qatlib.Papers.KnotLight13.TorusFamily

example : dot3 (fun j => (cross3 (![1, Complex.I, 0] : Fin 3 → ℂ) ![0, 0, 1] j).re)
    (fun j => (cross3 (![1, Complex.I, 0] : Fin 3 → ℂ) ![0, 0, 1] j).im) = 0 ∧
    squaredLength (fun j => (cross3 (![1, Complex.I, 0] : Fin 3 → ℂ) ![0, 0, 1] j).re) =
    squaredLength (fun j => (cross3 (![1, Complex.I, 0] : Fin 3 → ℂ) ![0, 0, 1] j).im) := by
  apply bateman_real_invariants _ _ 0 (-1)
  funext j
  fin_cases j <;> norm_num [cross3, Complex.I_sq]

example : dot3 (cross3 (![1, 0, 0] : Fin 3 → ℂ) ![0, 1, 0])
    (cross3 (![1, 0, 0] : Fin 3 → ℂ) ![0, 1, 0]) ≠ 0 := arbitrary_cross_not_null

example (x y z t : ℝ) : alphaSquared x y z t + betaSquared x y z t = 1 :=
  rational_pair_unit x y z t

example (s : ℂ) : torusPolynomial 2 3 (s ^ 3) (s ^ 2) = 0 := parametrized_zero 2 3 s

example (l a b : ℂ) : torusPolynomial 2 3 (l ^ 3 * a) (l ^ 2 * b) =
    l ^ 6 * torusPolynomial 2 3 a b := weighted_homogeneity 2 3 l a b

example : torusPolynomial 2 3 1 0 ≠ 0 := by norm_num [torusPolynomial]

example : poyntingVelocity (rescaledElectric 1 1 ![1, 0, 0] ![0, 1, 0])
    (rescaledMagnetic 1 1 ![1, 0, 0] ![0, 1, 0]) =
    poyntingVelocity ![1, 0, 0] ![0, 1, 0] :=
  poynting_velocity_invariant 1 1 _ _ (by norm_num)
    (by norm_num [squaredLength, dot3])

example : Qatlib.Papers.KnotLight13.Charges.modalCharge 2 3
    (fun _ : Fin 1 => 1) (fun _ => 1) = 1 / 5 := by
  norm_num [Qatlib.Papers.KnotLight13.Charges.modalCharge, Fin.sum_univ_succ]
