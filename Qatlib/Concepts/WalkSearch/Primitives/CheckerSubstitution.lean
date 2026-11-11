/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.QuantumAccess.ResidualDiagnosticContracts
import Qatlib.Concepts.WalkSearch.Primitives.AdaptiveCheckerObstruction

/-!
# Limits of checker substitution

Refutes the universal `CheckerSubstitution` proposition and proves that `th4Alg` is unchanged
when its noisy-search argument is replaced by another having the same `κ`. These results isolate
the role of the checker argument in the local graph-search construction; for bounded-error
search background, see [HoyerMoscaDeWolf2003].

## Main statements

* `checkerSubstitution_obstruction`: The universal checker-substitution proposition
  `CheckerSubstitution` is false.
* `th4Alg_checker_run_irrelevant`: Replacing the noisy-search argument of `th4Alg` by another
  with the same `κ` leaves the algorithm's result unchanged for every choice of the remaining
  inputs and tapes.

## References

* [Hoyer, Mosca and de Wolf, 2003][HoyerMoscaDeWolf2003]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.WalkSearch.QuantumAccess.Walk
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

set_option autoImplicit false

namespace Qatlib.Concepts.WalkSearch.Primitives

/-- The universal checker-substitution proposition `CheckerSubstitution` is false. -/
theorem checkerSubstitution_obstruction : ¬ CheckerSubstitution := by
  intro h
  obtain ⟨r, r', _hr, _hl, _hu, _hr', _hl', _hu', hcheck, _rest⟩ :=
    h 3 (by decide) threeVertexTriangle (by decide) (by decide)
      oneBadCollisionSolver failingTestNoisySearch positiveNullGrover
      (by decide) (by decide) (by decide)
  exact triCheckSpecCorrected_adaptive_obstruction r' hcheck

/-- Replacing the noisy-search argument of `th4Alg` by another with the same `κ` leaves the
algorithm's result unchanged for every choice of the remaining inputs and tapes. -/
theorem th4Alg_checker_run_irrelevant {n : ℕ} (adj : Fin n → Fin n → Bool)
    (kcs : KCollisionSolver) (ncs ncs' : NoisySearch) (sgs : Qatlib.Concepts.WalkSearch.WalkAlgorithms.SafeGrover)
    (hκ : ncs.κ = ncs'.κ) (r r' c₀ : ℕ)
    (stape : ℕ → kcs.seed) (gtape : ℕ → sgs.seed) :
    th4Alg adj kcs ncs sgs r r' c₀ stape gtape =
      th4Alg adj kcs ncs' sgs r r' c₀ stape gtape := by
  simp only [th4Alg, cCOf, hκ]

end Qatlib.Concepts.WalkSearch.Primitives
