/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EnsembleQSP26.EnsembleQSP.Theorem14

set_option backward.isDefEq.respectTransparency false

/-!
# EnsembleQSP26 — Theorem 15 (quartic observable estimation, Algorithm 4)

Fixed version: arXiv:2601.20073v1 (first submitted 2026-01-27), Theorem 15 (Eqs. (C21)–(C24)).

Algorithm 4 estimates `⟨ψ| p(A)† O p(A) |ψ⟩`.  It forms a four-fold Hadamard-test
estimator from independent noisy QSP blocks `P̃_k(A)`.  The two ingredients are:

* the *mean identity* (C22)–(C24): the estimator's ensemble mean equals
  `(∏_j E cos e_j)^2 · ⟨ψ| p(A)† O p(A) |ψ⟩`, which is the content of
  `theorem12_average_block`/`theorem12_ensemble_mean` applied to the four
  independent blocks; and
* the *concentration* (C21): the `[0,1]`-bounded single-run Hadamard statistic
  concentrates by finite Hoeffding at `M = O(log(1/δ)/ε²)`, which is
  `theorem14_hadamard_test`.

The claim `theorem15_quartic_observable` below states the concentration step in the
form the paper reduces to Theorem 14; the mean identity is supplied by Theorem 12.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix BigOperators

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace Qatlib.Papers.EnsembleQSP26.EnsembleQSP

attribute [local instance] Classical.propDecidable

/-- **Theorem 15 / Theorem 14 reduction (arXiv:2601.20073v1 p.15, Eq. (C21)).**
`Algorithm 4` outputs a single-run Hadamard statistic `o` bounded in `[-1,1]` whose
mean is the target observable (by the mean identity (C22)–(C24) of Theorem 12).
Then `M = O(log(1/δ)/ε²)` independent runs estimate the target up to `ε` with
probability at least `1 - δ`.  This is exactly the concentration reduction stated in
the proof of Theorem 15 ("the claimed query complexities can be derived by
Theorem 14"). -/
theorem theorem15_quartic_observable
    {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (o : X → ℝ) (target ε δ : ℝ)
    (hbound : ∀ x, |o x| ≤ 1) (hmean : p.expect o = target)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ 4 * Real.log (2 / δ) / ε ^ 2 + 2 ∧
      p.probEvent (fun seeds : Fin M → X => ε ≤ |FinDist.avg o seeds - target|) ≤ δ :=
  theorem14_hadamard_test p o target ε δ hbound hmean hε hδ hδ1

end Qatlib.Papers.EnsembleQSP26.EnsembleQSP
