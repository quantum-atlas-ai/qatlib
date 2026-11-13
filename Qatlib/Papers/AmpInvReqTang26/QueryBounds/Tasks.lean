/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.AccessModel.Defs

/-!
# Diagonal query circuits and the twisted distinguishing task

The recursion `runDiag` alternates arbitrary interleaving steps with a diagonal oracle acting on
the data register. Its Boolean output probabilities define `problem41Success`, the equally
weighted success probability for distinguishing a biased ensemble from its fixed phase twist.
This development supports the treatment in [TangWright2025].

## Main statements

* `queryDiag`: the diagonal query on data and ancilla registers.
* `distProbDiag`: ensemble-averaged Boolean output probability.
* `problem41Success`: success probability for Problem 4.1.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.QueryBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.AmpInvReqTang26.AccessModel

/-- The diagonal oracle matrix acting by `D` on the data register and identically on the ancilla
index. -/
def queryDiag {d a : ℕ} (D : Fin d → ℂ) :
    Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ :=
  diagonal (fun p => D p.1)

/-- The state obtained by interleaving `n` uses of a diagonal oracle with the algorithm's step
matrices. -/
def runDiag {d a : ℕ} (Alg : ForwardQueryAlgorithm d a) :
    ℕ → (Fin d → ℂ) → (Fin d × Fin a) → ℂ
  | 0, _ => Alg.step 0 *ᵥ Alg.init
  | n + 1, D => Alg.step (n + 1) *ᵥ (queryDiag D *ᵥ runDiag Alg n D)

/-- The sum of squared output amplitudes whose Boolean label equals `b` in the diagonal-oracle
circuit. -/
def outProbDiag {d a : ℕ} (Alg : ForwardQueryAlgorithm d a) (n : ℕ)
    (D : Fin d → ℂ) (b : Bool) : ℝ :=
  ∑ x : Fin d × Fin a, if Alg.good x = b then ‖runDiag Alg n D x‖ ^ 2 else 0

/-- The expectation of a diagonal-oracle Boolean output probability over a finite input
ensemble. -/
def distProbDiag {d a : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist (Fin d → X)) (D : (Fin d → X) → Fin d → ℂ)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (b : Bool) : ℝ :=
  p.expect (fun U => outProbDiag Alg n (D U) b)

/-- The equally weighted success probability for distinguishing the biased diagonal ensemble
from its fixed root-phase twist, with outputs false and true respectively [TangWright2025]. -/
def problem41Success {d a : ℕ} (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (Alg : ForwardQueryAlgorithm d a) (n : ℕ) : ℝ :=
  (1 / 2) *
    (distProbDiag (ensemble1 d q ε hq hε0 hε1)
        (fun U i => phaseEps q (U i)) Alg n false +
      distProbDiag (ensemble1 d q ε hq hε0 hε1)
        (fun U i => phaseEps q (U i) * omega d ^ (i : ℕ)) Alg n true)

/-- A natural root order bounded below by `1/ε^2` is positive when `ε > 0`. -/
theorem one_div_sq_pos_cast {ε : ℝ} (hε : 0 < ε) {q : ℕ}
    (hq : 1 / ε ^ 2 ≤ (q : ℝ)) : 0 < q := by
  have h : (0 : ℝ) < 1 / ε ^ 2 := by positivity
  exact_mod_cast lt_of_lt_of_le h hq

end Qatlib.Papers.AmpInvReqTang26.QueryBounds
