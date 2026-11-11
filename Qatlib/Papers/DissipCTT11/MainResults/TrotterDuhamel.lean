/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DissipCTT11.MainResults.LiouvillianPropagator

set_option backward.isDefEq.respectTransparency false

/-!
# Duhamel comparison of Liouvillian propagators

Kliesch--Barthel--Gogolin--Kastoryano--Eisert,
"A dissipative quantum Church-Turing theorem", fixed arXiv:1105.3986v4.

Theorem 5 of the appendix bounds the Trotter error
`T_{K+L}(t,s) - T_K(t,s) T_L(t,s)` through the integrated commutator
`[K_u, L_r]`.  Its proof starts from the fundamental-theorem-of-calculus identity
for a product of propagators.  This module formalizes the variation-of-constants
(Duhamel) identity that underlies that argument, together with the resulting norm
estimate.  The end-to-end commutator bound is not claimed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace Qatlib.Papers.DissipCTT11.MainResults.TrotterDuhamel

open Matrix
open scoped Matrix.Norms.L2Operator

open Qatlib.Papers.DissipCTT11.MainResults.LiouvillianPropagator

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The enorm instance for matrices induced by the L2 operator norm, used so that
matrix-valued interval integrals satisfy the `IntervalIntegrable` side conditions.
All norm estimates in this file use the same L2 operator norm `‖·‖`. -/
noncomputable local instance instENormedAddMonoidMatrix : ENormedAddMonoid (Matrix I I ℂ) :=
  NormedAddGroup.toENormedAddMonoid

/-- The propagator, as a function of its initial time, has the generator acting on
the right: `d/ds T(t,s) = -T(t,s) * L_s`. -/
theorem propagator_hasDerivAt_start (L : ℝ → Matrix I I ℂ) (hL : Continuous L) (s t : ℝ) :
    HasDerivAt (fun u => propagator L u s) (propagator L t s * (-L t)) t := by
  have h := Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution_hasDerivAt_start
    (fun r => -L r) hL.neg s t
  simpa [propagator] using h

/-- Duhamel identity: adding a generator `B` to `A` changes the propagator by the
integral of `B` transported by the partial propagators. -/
theorem duhamel_identity (A B : ℝ → Matrix I I ℂ) (hA : Continuous A) (hB : Continuous B)
    {s t : ℝ} (_hst : s ≤ t) :
    propagator (A + B) s t - propagator A s t =
      ∫ r in s..t, propagator (A + B) r t * B r * propagator A s r := by
  have hAB : Continuous (A + B) := hA.add hB
  have hder : ∀ r ∈ Set.uIcc s t,
      HasDerivAt (fun r => propagator (A + B) r t * propagator A s r)
        (-(propagator (A + B) r t * B r * propagator A s r)) r := by
    intro r _
    have h1 := propagator_hasDerivAt_start (A + B) hAB t r
    have h2 := propagator_hasDerivAt A hA s r
    have h := h1.mul h2
    convert h using 1
    simp only [Pi.add_apply]
    noncomm_ring
  have hint : IntervalIntegrable
      (fun r => propagator (A + B) r t * B r * propagator A s r) MeasureTheory.volume s t := by
    have h1 : Continuous fun r => propagator (A + B) r t :=
      continuous_iff_continuousAt.mpr fun r =>
        (propagator_hasDerivAt_start (A + B) hAB t r).continuousAt
    have h2 : Continuous fun r => propagator A s r :=
      continuous_iff_continuousAt.mpr fun r => (propagator_hasDerivAt A hA s r).continuousAt
    exact ((h1.mul hB).mul h2).intervalIntegrable s t
  have hderH : ∀ r ∈ Set.uIcc s t,
      HasDerivAt (fun r => -(propagator (A + B) r t * propagator A s r))
        (propagator (A + B) r t * B r * propagator A s r) r :=
    fun r hr => by simpa only [Pi.neg_def, neg_neg] using (hder r hr).neg
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderH hint
  have ht : propagator (A + B) t t * propagator A s t = propagator A s t := by simp
  have hs : propagator (A + B) s t * propagator A s s = propagator (A + B) s t := by simp
  rw [ht, hs] at h
  rw [eq_comm]
  simpa [sub_eq_add_neg, add_comm] using h

/-- Norm form of the Duhamel identity. -/
theorem duhamel_norm_le (A B : ℝ → Matrix I I ℂ) (hA : Continuous A) (hB : Continuous B)
    {s t : ℝ} (hst : s ≤ t) :
    ‖propagator (A + B) s t - propagator A s t‖ ≤
      ∫ r in s..t, ‖propagator (A + B) r t‖ * ‖B r‖ * ‖propagator A s r‖ := by
  rw [duhamel_identity A B hA hB hst]
  have hAB : Continuous (A + B) := hA.add hB
  have hcont : Continuous
      (fun r => propagator (A + B) r t * B r * propagator A s r) := by
    have h1 : Continuous fun r => propagator (A + B) r t :=
      continuous_iff_continuousAt.mpr fun r =>
        (propagator_hasDerivAt_start (A + B) hAB t r).continuousAt
    have h2 : Continuous fun r => propagator A s r :=
      continuous_iff_continuousAt.mpr fun r => (propagator_hasDerivAt A hA s r).continuousAt
    exact (h1.mul hB).mul h2
  have hint : IntervalIntegrable
      (fun r => ‖propagator (A + B) r t * B r * propagator A s r‖) MeasureTheory.volume s t :=
    hcont.norm.intervalIntegrable s t
  have hrhs : IntervalIntegrable
      (fun r => ‖propagator (A + B) r t‖ * ‖B r‖ * ‖propagator A s r‖)
      MeasureTheory.volume s t := by
    have h1 : Continuous fun r => ‖propagator (A + B) r t‖ :=
      (continuous_iff_continuousAt.mpr fun r =>
        (propagator_hasDerivAt_start (A + B) hAB t r).continuousAt).norm
    have h2 : Continuous fun r => ‖propagator A s r‖ :=
      (continuous_iff_continuousAt.mpr fun r => (propagator_hasDerivAt A hA s r).continuousAt).norm
    exact ((h1.mul hB.norm).mul h2).intervalIntegrable s t
  calc ‖∫ r in s..t, propagator (A + B) r t * B r * propagator A s r‖
      ≤ ∫ r in s..t, ‖propagator (A + B) r t * B r * propagator A s r‖ :=
        intervalIntegral.norm_integral_le_integral_norm hst
    _ ≤ ∫ r in s..t, ‖propagator (A + B) r t‖ * ‖B r‖ * ‖propagator A s r‖ := by
        apply intervalIntegral.integral_mono_on hst hint hrhs
        intro r _
        calc ‖propagator (A + B) r t * B r * propagator A s r‖
            ≤ ‖propagator (A + B) r t * B r‖ * ‖propagator A s r‖ := norm_mul_le _ _
          _ ≤ (‖propagator (A + B) r t‖ * ‖B r‖) * ‖propagator A s r‖ := by
              exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)

/-- First-order Trotter comparison: the difference between the full propagator and
the sequential one is bounded by the integrated product of the partial propagator
norms and the norm of the split generator. -/
theorem trotter_sequential_norm_le (K L : ℝ → Matrix I I ℂ) (hK : Continuous K)
    (hL : Continuous L) {s t : ℝ} (hst : s ≤ t) :
    ‖propagator K s t - propagator (K + L) s t‖ ≤
      ∫ r in s..t, ‖propagator (K + L) r t‖ * ‖L r‖ * ‖propagator K s r‖ := by
  have h := duhamel_norm_le K L hK hL hst
  simpa [add_comm, norm_sub_rev] using h

end Qatlib.Papers.DissipCTT11.MainResults.TrotterDuhamel
