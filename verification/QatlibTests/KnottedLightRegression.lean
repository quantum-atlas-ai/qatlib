/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HelicitySpec.Balance

/-! Regression consumers for null invariants, Hopf coordinates and helicity balance. -/

@[expose] public section
set_option autoImplicit false

open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.KnottedLight08.HelicitySpec

example : dot3 (riemannSilberstein ![1, 0, 0] ![0, 1, 0])
    (riemannSilberstein ![1, 0, 0] ![0, 1, 0]) = 0 := by
  apply (null_iff _ _).mpr
  norm_num [dot3, squaredLength]

example : dot3 (riemannSilberstein ![1, 0, 0] ![1, 0, 0])
    (riemannSilberstein ![1, 0, 0] ![1, 0, 0]) ≠ 0 := by
  intro h
  have horth := ((null_iff _ _).mp h).1
  norm_num [dot3] at horth

example (x y z : ℝ) : squaredLength (hopf (stereo x y z)) = 1 :=
  hopf_unit _ (stereo_unit x y z)

example (q : Fin 4 → ℝ) : hopf (phaseRotate (3 / 5) (4 / 5) q) = hopf q :=
  hopf_phase_invariant _ _ q (by norm_num)

example (A B : Fin 3 → ℝ) :
    dot3 (dualRotation A) (dualRotation B) = dot3 A B := dual_pairing A B

example : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 ∧
    HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 0 ∧ (1 : ℝ) ≠ 2 := by
  exact ⟨hasDerivAt_const 0 1, hasDerivAt_const 0 2, by norm_num⟩

example (t : ℝ) : (7 : ℝ) = (7 : ℝ) :=
  null_magnetic_conserved (fun _ => 7) (fun _ => 0)
    (fun x => by simpa using (hasDerivAt_const x (7 : ℝ)))
    (fun _ => rfl) 0 t

example (s t : ℝ) : 2 * s + (3 - 2 * s) = 2 * t + (3 - 2 * t) := by
  apply total_helicity_conserved (fun x => 2 * x) (fun x => 3 - 2 * x) (fun _ => -1)
  · intro x
    simpa using (hasDerivAt_id x).const_mul 2
  · intro x
    simpa using HasDerivAt.fun_sub (hasDerivAt_const x (3 : ℝ))
      ((hasDerivAt_id x).const_mul 2)
