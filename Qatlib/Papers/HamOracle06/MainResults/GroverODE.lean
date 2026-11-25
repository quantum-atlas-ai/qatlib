/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamOracle06.MainResults.ContinuousGrover
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

/-!
# Continuous search on its physical time interval

Equations (43)--(45) of Mochon's Hamiltonian Oracles give an ODE with a
nonnegative square root. Verify it for the squared-cosine path through the
zero-error stopping time, where the phase stays in the first quadrant.
-/

set_option autoImplicit false

open Qatlib.Papers.HamOracle06.MainResults

namespace Qatlib.Papers.HamOracle06.MainResults

/-- The squared-cosine path from Eq. (44) solves the negative-root branch of Eq. (43)
through the zero-error stopping time of Eq. (45). -/
theorem continuousGrover_solves_ode {N t : ℝ} (hN : 1 < N)
    (ht : t ∈ Set.Icc (0 : ℝ) (continuousGroverTime N)) :
    HasDerivWithinAt (fun s : ℝ => Real.cos (Real.pi * Real.sqrt (N - 1) / N * s) ^ 2)
      (-2 * (Real.pi * Real.sqrt (N - 1) / N) *
        Real.sqrt (Real.cos (Real.pi * Real.sqrt (N - 1) / N * t) ^ 2 *
          (1 - Real.cos (Real.pi * Real.sqrt (N - 1) / N * t) ^ 2)))
      (Set.Icc 0 (continuousGroverTime N)) t := by
  let a := Real.pi * Real.sqrt (N - 1) / N
  have hN0 : 0 < N := by linarith
  have hs : 0 < Real.sqrt (N - 1) := Real.sqrt_pos.mpr (by linarith)
  have ha : 0 < a := div_pos (mul_pos Real.pi_pos hs) hN0
  have hstop : a * continuousGroverTime N = Real.arccos (1 / Real.sqrt N) := by
    unfold a continuousGroverTime
    field_simp [Real.pi_ne_zero, hN0.ne', hs.ne']
  have hphase0 : 0 ≤ a * t := mul_nonneg ha.le ht.1
  have hphase : a * t ≤ Real.pi / 2 := calc
    a * t ≤ a * continuousGroverTime N := mul_le_mul_of_nonneg_left ht.2 ha.le
    _ = Real.arccos (1 / Real.sqrt N) := hstop
    _ ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr (by positivity)
  have hsin : 0 ≤ Real.sin (a * t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hphase0 (by linarith [Real.pi_pos])
  have hcos : 0 ≤ Real.cos (a * t) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hphase⟩
  have hroot : Real.sqrt (Real.cos (a * t) ^ 2 * (1 - Real.cos (a * t) ^ 2)) =
      Real.cos (a * t) * Real.sin (a * t) := by
    have heq : 1 - Real.cos (a * t) ^ 2 = Real.sin (a * t) ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq (a * t)]
    rw [heq, ← mul_pow, Real.sqrt_sq (mul_nonneg hcos hsin)]
  have hlin : HasDerivAt (fun s : ℝ => a * s) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  have hcosDeriv : HasDerivAt (fun s : ℝ => Real.cos (a * s)) (-Real.sin (a * t) * a) t :=
    (Real.hasDerivAt_cos (a * t)).comp t hlin
  have hder : HasDerivAt (fun s : ℝ => Real.cos (a * s) ^ 2)
      (2 * Real.cos (a * t) * (-Real.sin (a * t) * a)) t := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hcosDeriv.fun_pow 2
  change HasDerivWithinAt (fun s : ℝ => Real.cos (a * s) ^ 2)
    (-2 * a * Real.sqrt (Real.cos (a * t) ^ 2 * (1 - Real.cos (a * t) ^ 2)))
    (Set.Icc 0 (continuousGroverTime N)) t
  rw [hroot]
  convert hder.hasDerivWithinAt using 1
  ring

end Qatlib.Papers.HamOracle06.MainResults
