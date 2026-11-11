/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RandCertLiu25.MainResults.EventProbabilityTools
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 15: ℓ∞ approximation of the device distribution in Step 1

Formalises Lemma 15 of Liu--Shaydulin--Niroula et al., *Certified randomness
using a trapped-ion quantum processor*, fixed arXiv:2503.20498v1, Lemma 15 and
Eq. I.43, p. 7.

Step 1 of the sampling process draws `K` i.i.d. samples from the device output
distribution `p_{A(C)}` and forms the empirical distribution
`p̃_{A(C)}(z)`.  Hoeffding gives, for each `z`,

  `Pr[ |p̃(z) - p(z)| > δ/2 ] ≤ η / (2·2^{nk})`,     (I.43)

and a union bound over the `2^{nk}` outcomes gives

  `Pr[ ‖p̃ - p‖_∞ > δ/2 ] ≤ η/2`,

i.e. with probability at least `1 - η/2` the estimate is within `δ/2` in
ℓ∞-distance.  We formalise the union-bound step for an arbitrary finite
outcome type; the per-point Hoeffding estimate is the hypothesis `hpoint`
(already a theorem of Mathlib/ProbabilityInterfaces, not restated here).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.RandCertLiu25.MainResults.HoeffdingApproximation

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.RandCertLiu25.MainResults.EventProbabilityTools

/-- **Lemma 15** (union-bound step of Eq. I.43): if every outcome has failure
probability at most `η/(2·|X|)`, then the ℓ∞-approximation event has
probability at least `1 - η/2`. -/
theorem lemma15_l_infty_union_bound {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (P : FinDist X) (K : ℕ) (phat : (Fin K → X) → X → ℝ)
    (delta eta : ℝ) (heta : 0 ≤ eta)
    (hpoint : ∀ x, P.probEvent (fun ω => delta / 2 < |phat ω x - P.prob x|) ≤
      eta / (2 * (Fintype.card X : ℝ))) :
    1 - eta / 2 ≤ P.probEvent (fun ω => ∀ x, |phat ω x - P.prob x| ≤ delta / 2) := by
  classical
  have hcard : (0 : ℝ) < (Fintype.card X : ℝ) := by
    exact_mod_cast Fintype.card_pos
  -- Union bound over the failing outcomes.
  have hunion : P.probEvent (fun ω => ∃ x, delta / 2 < |phat ω x - P.prob x|) ≤
      ∑ x : X, eta / (2 * (Fintype.card X : ℝ)) := by
    refine le_trans (probEvent_exists_le_sum P
      (fun x ω => delta / 2 < |phat ω x - P.prob x|)) ?_
    exact Finset.sum_le_sum (fun x _ => hpoint x)
  have hsum : ∑ _x : X, eta / (2 * (Fintype.card X : ℝ)) = eta / 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hcard.ne']
  have hcompl : P.probEvent (fun ω => ∀ x, |phat ω x - P.prob x| ≤ delta / 2) =
      P.probEvent (fun ω => ¬ ∃ x, delta / 2 < |phat ω x - P.prob x|) := by
    apply probEvent_congr P (L := K)
    intro ω
    constructor
    · intro h ⟨x, hx⟩
      exact absurd (h x) (not_le.mpr hx)
    · intro h x
      by_contra hx
      exact h ⟨x, lt_of_not_ge hx⟩
  rw [hcompl, probEvent_compl]
  have hb : P.probEvent (fun ω => ∃ x, delta / 2 < |phat ω x - P.prob x|) ≤ eta / 2 := by
    simpa [hsum] using hunion
  linarith

end Qatlib.Papers.RandCertLiu25.MainResults.HoeffdingApproximation
