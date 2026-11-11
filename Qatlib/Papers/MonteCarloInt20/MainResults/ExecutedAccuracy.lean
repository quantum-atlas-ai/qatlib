/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.ActualNested
import Qatlib.Papers.MonteCarloInt20.CostModels.NestedReceipts
import Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit

/-!
# Accuracy of the executed nested circuit

This module connects the evaluated nested circuit word to the finite Monte Carlo target
associated with [KanekoEtAl2020]. `executed_finite_accuracy` gives a Born-probability guarantee
including both the outer estimation window and the smooth inner payoff bias.

`actual_term_call_hierarchy` expands the forward and backward body accesses into an exact count
of underlying term queries.

## Main statements

* `executed_finite_accuracy`: bounds the target error of the executed circuit with probability
  at least `8 / π²`.
* `actual_term_call_hierarchy`: counts the underlying term calls in the nested word.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open Matrix Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedAccuracy
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedWord
open Qatlib.Papers.MonteCarloInt20.CostModels.NestedReceipts
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
open Qatlib.Papers.MonteCarloInt20.MainResults.ActualNested
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit
open Qatlib.Papers.MonteCarloInt20.PrnJump.Compiled
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AmplitudeCore.PreparedReadout

namespace Qatlib.Papers.MonteCarloInt20.MainResults.ExecutedAccuracy

noncomputable local instance bodyDecision (n s d p : ℕ) : DecidableEq (BodyReg n s d p) :=
    instDecidableEqProd
noncomputable local instance dataDecision (n M : ℕ) (I : Type) [DecidableEq I] :
    DecidableEq ((Reg n × Inner M I) × Bool) := instDecidableEqProd
noncomputable local instance fullDecision (n M N : ℕ) (I : Type) [DecidableEq I] :
    DecidableEq (Inner N ((Reg n × Inner M I) × Bool)) := instDecidableEqProd

/-- Under the stated smoothness and payoff-range hypotheses, with positive coordinate width,
even `M ≥ 2`, and `N ≥ 2`, the executed nested circuit estimates `finiteTarget` within
`outerWindow` plus `finiteBudget` with Born probability at least `8 / π²` [KanekoEtAl2020]. -/
theorem executed_finite_accuracy {n s d p : ℕ} (hd : 0 < d)
    (M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N) (hEven : 2 ∣ M)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1))
    (D : ℝ) (g gp : ℝ → ℝ) (K : NNReal)
    (hg : ∀ x,HasDerivAt g (gp x) x) (hgp : LipschitzWith K gp)
    (hrange : ∀ k : Fin M,g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1) :
    8/Real.pi^2 ≤ MeasureProb (I:=OuterReg s M N (BodyReg n s d p))
      (ApplyGate (I:=OuterReg s M N (BodyReg n s d p))
        (wordEval (G:=Matrix (OuterReg s M N (BodyReg n s d p)) (OuterReg s M N (BodyReg n s d p)) ℂ)
          (nestedWord s M N (by omega) (innerBody a c seed termCode) (bodySeed n s d p seed)
            (fun _ => bodyGood n s d p) D g))
        (Ket (I:=OuterReg s M N (BodyReg n s d p))
          (innerSeed N (by omega) ((ZeroStr s,innerSeed M (by omega) (bodySeed n s d p seed)),false))))
      (Finset.univ.filter (fun z => |aeEstimate N z.1-finiteTarget a c seed termCode D g| ≤
        outerWindow N (finiteMean M hM a c seed termCode D g)+finiteBudget M a c seed termCode D gp K)) := by
  have he := nestedWord_event (I:=BodyReg n s d p) s M N hM hN (innerBody a c seed termCode)
    (bodySeed n s d p seed) (fun _ => bodyGood n s d p) (innerBody_unitary a c seed termCode)
    D g hrange (fun z => |aeEstimate N z-finiteTarget a c seed termCode D g| ≤
      outerWindow N (finiteMean M hM a c seed termCode D g)+finiteBudget M a c seed termCode D gp K)
  exact (finite_nested_total_error hd M N hM hN hEven a c seed termCode D g gp K hg hgp hrange).trans_eq he.symm

/-- For positive `M` and `N`, the total forward and backward body-access count multiplied by the
body query count equals `2 * ((2 * N - 1) * (2 * M - 1))`. -/
theorem actual_term_call_hierarchy {n s d p : ℕ}
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (D : ℝ) (g : ℝ → ℝ) :
    (accessCount .inputForward (nestedWord s M N hM (innerBody a c seed termCode)
        (bodySeed n s d p seed) (fun _ => bodyGood n s d p) D g)+
      accessCount .inputBackward (nestedWord s M N hM (innerBody a c seed termCode)
        (bodySeed n s d p seed) (fun _ => bodyGood n s d p) D g))*
      QueryCount (bodyCircuit (d:=d) (p:=p) a c seed (ZeroStr s))=
        2*((2*N-1)*(2*M-1)) := by
  rw [nested_total_source_accesses s M N hM hN,
      (bodyCircuit_counts (d:=d) (p:=p) a c seed (ZeroStr s)).1]
  omega

end Qatlib.Papers.MonteCarloInt20.MainResults.ExecutedAccuracy
