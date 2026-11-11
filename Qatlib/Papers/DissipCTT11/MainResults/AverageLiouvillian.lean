/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DissipCTT11.MainResults.TrotterDuhamel

set_option backward.isDefEq.respectTransparency false

/-!
# The average Liouvillian and constant-generator propagators

Kliesch--Barthel--Gogolin--Kastoryano--Eisert,
"A dissipative quantum Church-Turing theorem", fixed arXiv:1105.3986v4.

Theorem 7 of the appendix replaces the time-ordered propagator by the exponential
of the average Liouvillian of Eq. (33).  This module formalizes the two structural
ingredients of that step: the propagator of a constant generator is the matrix
exponential, and the average-Liouvillian comparison is an instance of the Duhamel
identity.  The quantitative `(1/3) b (t-s)^2` bound is not claimed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace Qatlib.Papers.DissipCTT11.MainResults.AverageLiouvillian

open Matrix
open scoped Matrix.Norms.L2Operator

open Qatlib.Papers.DissipCTT11.MainResults.LiouvillianPropagator
open Qatlib.Papers.DissipCTT11.MainResults.TrotterDuhamel

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The average Liouvillian of Eq. (33),
`K^av = (1/(t-s)) ∫_s^t K_r dr`, as a constant matrix superoperator. -/
noncomputable def averageLiouvillian (K : ℝ → Matrix I I ℂ) (s t : ℝ) : Matrix I I ℂ :=
  (1 / (t - s)) • ∫ r in s..t, K r

/-- The propagator of a constant Liouvillian is the matrix exponential of the
elapsed time times the generator. -/
theorem propagator_const (A : Matrix I I ℂ) (s t : ℝ) :
    propagator (fun _ => A) s t = NormedSpace.exp ((t - s) • A) := by
  have hfun : propagator (fun _ => A) s = fun u => NormedSpace.exp ((u - s) • A) := by
    apply Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.ordered_matrix_ode_unique
      (fun _ => -A) continuous_const _ _ s
    · simp [propagator]
    · intro u
      have h := propagator_hasDerivAt (fun _ => A) continuous_const s u
      simpa using h
    · intro u
      have hsub : HasDerivAt (fun x : ℝ => x - s) 1 u := by
        simpa using (hasDerivAt_id u).sub_const s
      have h := (hasDerivAt_exp_smul_const A (u - s)).scomp u hsub
      have hcomm : A * NormedSpace.exp ((u - s) • A) = NormedSpace.exp ((u - s) • A) * A :=
        (((Commute.refl A).smul_right (u - s)).exp_right).eq
      convert h using 1 <;> simp [Function.comp_def, neg_mul, hcomm]
  exact congrFun hfun t

/-- Duhamel comparison with the average Liouvillian: the difference between the
time-ordered propagator and the exponential of the average generator is an integral
of the generator's deviation from its average, transported by the two propagators. -/
theorem averageLiouvillian_duhamel (K : ℝ → Matrix I I ℂ) (hK : Continuous K)
    (Kav : Matrix I I ℂ) {s t : ℝ} (hst : s ≤ t) :
    propagator K s t - NormedSpace.exp ((t - s) • Kav) =
      ∫ r in s..t, propagator K r t * (K r - Kav) * NormedSpace.exp ((r - s) • Kav) := by
  have h := duhamel_identity (fun _ => Kav) (fun r => K r - Kav) continuous_const
    (hK.sub continuous_const) hst
  have hAB : (fun _ => Kav) + (fun r => K r - Kav) = K := by
    funext r
    simp only [Pi.add_apply]
    abel
  rw [hAB] at h
  simpa only [propagator_const] using h

end Qatlib.Papers.DissipCTT11.MainResults.AverageLiouvillian
