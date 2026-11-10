/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.AccessModel.Defs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.QueryBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.AmpInvReqTang26.AccessModel

def queryDiag {d a : ℕ} (D : Fin d → ℂ) :
    Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ :=
  diagonal (fun p => D p.1)

def runDiag {d a : ℕ} (Alg : ForwardQueryAlgorithm d a) :
    ℕ → (Fin d → ℂ) → (Fin d × Fin a) → ℂ
  | 0, _ => Alg.step 0 *ᵥ Alg.init
  | n + 1, D => Alg.step (n + 1) *ᵥ (queryDiag D *ᵥ runDiag Alg n D)

def outProbDiag {d a : ℕ} (Alg : ForwardQueryAlgorithm d a) (n : ℕ)
    (D : Fin d → ℂ) (b : Bool) : ℝ :=
  ∑ x : Fin d × Fin a, if Alg.good x = b then ‖runDiag Alg n D x‖ ^ 2 else 0

def distProbDiag {d a : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist (Fin d → X)) (D : (Fin d → X) → Fin d → ℂ)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (b : Bool) : ℝ :=
  p.expect (fun U => outProbDiag Alg n (D U) b)

def problem41Success {d a : ℕ} (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (Alg : ForwardQueryAlgorithm d a) (n : ℕ) : ℝ :=
  (1 / 2) *
    (distProbDiag (ensemble1 d q ε hq hε0 hε1)
        (fun U i => phaseEps q (U i)) Alg n false +
      distProbDiag (ensemble1 d q ε hq hε0 hε1)
        (fun U i => phaseEps q (U i) * omega d ^ (i : ℕ)) Alg n true)

theorem one_div_sq_pos_cast {ε : ℝ} (hε : 0 < ε) {q : ℕ}
    (hq : 1 / ε ^ 2 ≤ (q : ℝ)) : 0 < q := by
  have h : (0 : ℝ) < 1 / ε ^ 2 := by positivity
  exact_mod_cast lt_of_lt_of_le h hq

end Qatlib.Papers.AmpInvReqTang26.QueryBounds
