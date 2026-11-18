/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.Madelung.PolarCurrent

/-! Regression consumers for phase-charge cancellation and nonzero exact helicity density. -/

@[expose] public section
set_option autoImplicit false

open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.SuperfluidHel18.VanishCharge

example (rate : ℝ) :
    Qatlib.Papers.SuperfluidHel18.Madelung.polarCurrent 2 7 rate Complex.I / 2 ^ 2 = rate :=
  Qatlib.Papers.SuperfluidHel18.Madelung.normalized_polar_current 2 7 rate Complex.I
    (by norm_num) (by norm_num)

example (dphase tangent : Fin 3 → ℝ) :
    eulerCharge (fun j => dphase j / 2) tangent + phaseCharge 2 dphase tangent = 0 :=
  madelung_charge_cancels 2 (by norm_num) dphase tangent

example (alpha : ℝ) (a b : Fin 3 → ℝ) :
    dot3 (clebschVelocity alpha 0 b) (cross3 a b) = 0 :=
  simple_clebsch_helicity_zero alpha a b

example : dot3 (clebschVelocity 0 ![0, 0, 1] ![0, 1, 0])
    (cross3 ![1, 0, 0] ![0, 1, 0]) = 1 := by
  norm_num [clebschVelocity, dot3, cross3]

example : centerlineHelicity (fun _ : Fin 2 => 1)
    (fun _ _ => 1) (fun _ => 0) = 2 := by
  norm_num [centerlineHelicity, linkingPart, writhePart, Fin.sum_univ_succ]

example : centerlineHelicity (fun _ : Fin 1 => 2)
    (fun _ _ => 100) (fun _ => 3) = 12 := by
  norm_num [centerlineHelicity, linkingPart, writhePart, Fin.sum_univ_succ]

example (phi alpha : ℝ) (p a b : Fin 3 → ℝ) :
    dot3 (clebschVelocity alpha p b) (cross3 a b) =
      divergenceJet (helicityFluxJacobian phi p a b 0 0) :=
  helicity_is_divergence phi alpha p a b 0 0 (by intro i j; rfl) (by intro i j; rfl)
