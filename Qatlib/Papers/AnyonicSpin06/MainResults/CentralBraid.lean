/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AnyonicSpin06.MainResults.QuaternionBraid

@[expose] public section

/-!
# The central-scalar branch of the quaternion braid relation

A nonzero scalar quaternion commutes with the other generator. The
braid equation for two nonzero commuting generators requires equality,
which determines the scalar and pure parts in the central branch.
-/

set_option autoImplicit false

namespace Qatlib.Papers.AnyonicSpin06.MainResults

open scoped Quaternion
open Qatlib.Papers.AnyonicSpin06.MainResults.QuaternionBraid
open Quaternion

/-- In the branch `b = 0`, both generators must be the same scalar quaternion. -/
theorem central_braid (a b c d : ℝ) (u v g h : ℍ[ℝ])
    (_hu : u.re = 0) (hv : v.re = 0) (_hnu : normSq u = 1) (hnv : normSq v = 1)
    (hg : g = (a : ℍ[ℝ]) + (b : ℍ[ℝ]) * u)
    (hh : h = (c : ℍ[ℝ]) + (d : ℍ[ℝ]) * v)
    (ha : a ^ 2 + b ^ 2 = 1) (hc : c ^ 2 + d ^ 2 = 1) (hb : b = 0) :
    (g * h * g = h * g * h) ↔ c = a ∧ d = 0 := by
  have hg' : g = (a : ℍ[ℝ]) := by simpa [hb] using hg
  have hg0 : g ≠ 0 := by
    intro hzero
    have hzero' : a = 0 := by
      simpa using congrArg (fun q : ℍ[ℝ] => q.re) (hg'.symm.trans hzero)
    simp [hzero', hb] at ha
  have hh0 : h ≠ 0 := by
    intro hzero
    have hn : normSq h = 1 := by rw [hh, normSq_add_mul hv hnv, hc]
    simp [hzero] at hn
  have hv0 : v ≠ 0 := by
    intro hvz
    simp [hvz] at hnv
  constructor
  · intro hbraid
    have hcomm : h * g = g * h := by rw [hg']; exact (Quaternion.coe_commutes a h).symm
    have hmul : g * (g * h) = h * (g * h) := by
      calc
        g * (g * h) = g * (h * g) := by rw [hcomm]
        _ = g * h * g := (mul_assoc g h g).symm
        _ = h * g * h := hbraid
        _ = h * (g * h) := mul_assoc h g h
    have heq : g = h := mul_right_cancel₀ (mul_ne_zero hg0 hh0) hmul
    have hparts : (c : ℍ[ℝ]) + (d : ℍ[ℝ]) * v = (a : ℍ[ℝ]) := hh.symm.trans (heq.symm.trans hg')
    have hca : c = a := by
      simpa [Quaternion.coe_mul_eq_smul, hv] using congrArg (fun q : ℍ[ℝ] => q.re) hparts
    have hdv : (d : ℍ[ℝ]) * v = 0 := by
      apply add_left_cancel (a := (a : ℍ[ℝ]))
      simpa [hca] using hparts
    have hd0 : (d : ℍ[ℝ]) = 0 := (mul_eq_zero.mp hdv).resolve_right hv0
    exact ⟨hca, by simpa using congrArg (fun q : ℍ[ℝ] => q.re) hd0⟩
  · rintro ⟨hca, hd⟩
    have hsame : h = g := by simp [hh, hca, hd, hg']
    rw [hsame]

end Qatlib.Papers.AnyonicSpin06.MainResults
