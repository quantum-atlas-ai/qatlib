/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.ForwardHist.DensityBridge
import Qatlib.Papers.AmpInvReqTang26.ForwardHist.ActualTwistBias
import Qatlib.Papers.AmpInvReqTang26.QueryBounds.Tasks

/-!
# Transport of the twisted source query bound

These identities connect diagonal-oracle output probabilities with the phase-evaluation circuit
and its twisted algorithm. The equality `sourceProblem41_eq_twisted` transfers the weighted
ensemble bound to the success probability of Problem 4.1. This development supports the
treatment in [TangWright2025].

## Main statements

* `runDiag_eq_run`: agreement of the two circuit recursions.
* `sourceProblem41_eq_twisted`: agreement of source and weighted success probabilities.
* `actual_source_twist_lower_bound`: the query lower bound for Problem 4.1.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.ForwardHist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.AmpInvReqTang26.AccessModel
open Qatlib.Papers.AmpInvReqTang26.QueryBounds
open Qatlib.Concepts.MixedFidelity.FidelityMetric.Domination

/-- The diagonal-oracle circuit recursion agrees with `run` for the identity phase map. -/
theorem runDiag_eq_run {d a : ℕ} (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (D : Fin d → ℂ) :
    runDiag Alg n D=run id Alg n D := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [runDiag,run,queryDiag,queryMat,ih,id_eq]

/-- Diagonal output probabilities for the evaluated phase assignment agree with the phase-map
output probabilities. -/
private theorem source_outProbDiag_plain {d a : ℕ} {S : Type} (phi : S → ℂ)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (U : Fin d → S) (b : Bool) :
    outProbDiag Alg n (fun i => phi (U i)) b=outProb phi Alg n U b := by
  unfold outProbDiag outProb
  rw [runDiag_eq_run,← run_assignment phi Alg n U]

/-- Multiplying the oracle phases by fixed unit phases gives the output probabilities of the
correspondingly twisted algorithm. -/
private theorem source_outProbDiag_twist {d a : ℕ} {S : Type} (phi : S → ℂ)
    (D : Fin d → ℂ) (hD : ∀i,‖D i‖=1) (Alg : ForwardQueryAlgorithm d a)
    (n : ℕ) (U : Fin d → S) (b : Bool) :
    outProbDiag Alg n (fun i => phi (U i)*D i) b=outProb phi (twistedAlgorithm D hD Alg) n U b := by
  have hr : runDiag Alg n (fun i => phi (U i)*D i)=run phi (twistedAlgorithm D hD Alg) n U := by
    rw [runDiag_eq_run,twistedAlgorithm_run]
    congr 1
    funext i
    ring
  unfold outProbDiag outProb
  rw [hr]
  rfl

/-- Averaging diagonal output probabilities over an ensemble agrees with the phase-map ensemble
probability. -/
private theorem source_distProbDiag_plain {d a : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (p : FinDist (Fin d → S)) (phi : S → ℂ) (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (b : Bool) :
    distProbDiag p (fun U i => phi (U i)) Alg n b=distProb p phi Alg n b := by
  unfold distProbDiag distProb
  apply congrArg p.expect
  funext U
  exact source_outProbDiag_plain phi Alg n U b

/-- Ensemble probabilities for a fixed phase twist agree with the phase-map probabilities of the
twisted algorithm. -/
private theorem source_distProbDiag_twist {d a : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (p : FinDist (Fin d → S)) (phi : S → ℂ) (D : Fin d → ℂ) (hD : ∀i,‖D i‖=1)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (b : Bool) :
    distProbDiag p (fun U i => phi (U i)*D i) Alg n b=
      distProb p phi (twistedAlgorithm D hD Alg) n b := by
  unfold distProbDiag distProb
  apply congrArg p.expect
  funext U
  exact source_outProbDiag_twist phi D hD Alg n U b

/-- For `q > 1` and bias in `[0, 1]`, the source Problem 4.1 success equals the weighted success
for the root-phase twist. -/
theorem sourceProblem41_eq_twisted {d a : ℕ} (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0≤eps) (he1 : eps≤1) (Alg : ForwardQueryAlgorithm d a) (n : ℕ) :
    problem41Success q (by omega) eps he0 he1 Alg n=
      twistedWeightedSuccess eps q (phase d) (norm_phase d) Alg n := by
  let p := ensemble1 d q eps (by omega) he0 he1
  have hb0 := sourceDensity_born p (phaseEps q) Alg n false
  rw [sourceDensity_biased eps q hq he0 he1] at hb0
  have hb1 :=
      sourceDensity_born p (phaseEps q) (twistedAlgorithm (phase d) (norm_phase d) Alg) n true
  rw [sourceDensity_biased eps q hq he0 he1] at hb1
  change bornMass (weightedCircuitDensity eps q (twistedAlgorithm (phase d) (norm_phase d) Alg) n)
      Alg.good true=distProb p (phaseEps q) (twistedAlgorithm (phase d) (norm_phase d) Alg) n true at hb1
  change (1/2:ℝ)*(distProbDiag p (fun U i => phaseEps q (U i)) Alg n false+
    distProbDiag p (fun U i => phaseEps q (U i)*phase d i) Alg n true)=_
  rw [source_distProbDiag_plain,source_distProbDiag_twist p (phaseEps q) (phase d) (norm_phase d),← hb0,← hb1]
  unfold twistedWeightedSuccess
  ring

/-- Under `0 < eps < 1/2` and `q ≥ 1/eps^2`, success at least `5/6` in Problem 4.1 requires at
least `1/(12 * eps^2)` forward queries. -/
theorem actual_source_twist_lower_bound {d a q : ℕ} (eps : ℝ) (he0 : 0<eps)
    (he1 : eps<1/2) (hq : 1/eps^2≤(q:ℝ)) (Alg : ForwardQueryAlgorithm d a) (n : ℕ)
    (hsucc : (5/6:ℝ)≤problem41Success q (Nat.zero_lt_of_lt (actual_q_order he0 he1 hq))
      eps he0.le (by linarith) Alg n) : 1/(12*eps^2)≤(n:ℝ) := by
  rw [sourceProblem41_eq_twisted eps q (actual_q_order he0 he1 hq) he0.le (by linarith)] at hsucc
  exact actual_twisted_weighted_lower_bound eps he0 he1 hq (phase d) (norm_phase d) Alg n hsucc

end Qatlib.Papers.AmpInvReqTang26.ForwardHist
