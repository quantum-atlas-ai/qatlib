/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.WildcardSrch12.MainResults.Model.SourceModel
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification

set_option backward.isDefEq.respectTransparency false

/-!
# WildcardSrch12 — readout model for the algorithm-level claims

The paper's Theorems 1–2 and Lemmas 4, 6 speak about *algorithms* that query the
wildcard / CGT oracle and output the hidden string.  This module fixes that
interface on the library's counted-query observed-circuit model
(`ObservedCircuit`, `observedTraces`, `observedAcceptance`, `observedQueryDepth`):

* `outputMass` — the Born mass of the basis vectors whose register readout equals
  a prescribed string `x`;
* `programSuccessMass` / `programCGTSuccessMass` — the accepted-branch mass of a
  program whose output on each accepted branch is read out classically (the
  paper's "the algorithm outputs `x̃`" event);
* `SolvesWildcardWith` / `SolvesCGTWith` — the solver predicates: one fixed
  program, working from a normalized initial state, succeeds with probability at
  least `p` on every input `x` (the paper's worst-case success parameter);
* `programQueries` — the oracle-free syntactic path query count
  (`observedQueryDepth`), the quantity bounded by the lower-bound statements.

Boundary: the readout is a classical function of the final register; no gate
synthesis or efficient implementation is asserted, and mid-branch adaptive
readout is already covered by the `ObservedCircuit` tree.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery

open Qatlib.Concepts.MbqcFlow.FlowDecision

namespace Qatlib.Papers.WildcardSrch12.MainResults

/-- The probability that a computational-basis measurement of `v` returns a
register whose readout equals `x`. -/
noncomputable def outputMass {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (readOut : I → BitStr n) (x : BitStr n) (v : QState I) : ℝ :=
  MeasureProb v (Finset.univ.filter (fun i => readOut i = x))

/-- Accepted-branch success mass of a program running against the wildcard oracle. -/
noncomputable def programSuccessMass (n r : ℕ) (readOut : WildcardReg n r → BitStr n)
    (P : ObservedCircuit (WildcardReg n r)) (ψ : QState (WildcardReg n r))
    (x : BitStr n) : ℝ :=
  (observedTraces (wildcardOracle n r x) P ψ).foldl
    (fun total t => if t.accepted then total + outputMass readOut x t.state else total) 0

/-- Accepted-branch success mass of a program running against the CGT oracle. -/
noncomputable def programCGTSuccessMass (n r : ℕ) (readOut : CGTReg n r → BitStr n)
    (P : ObservedCircuit (CGTReg n r)) (ψ : QState (CGTReg n r))
    (x : BitStr n) : ℝ :=
  (observedTraces (cgtOracle n r x) P ψ).foldl
    (fun total t => if t.accepted then total + outputMass readOut x t.state else total) 0

/-- Worst-case `p`-success of a program solving search with wildcards: for every
hidden string `x` and every normalized initial state, the accepted output mass on
`x` is at least `p`. -/
def SolvesWildcardWith (n r : ℕ) (readOut : WildcardReg n r → BitStr n)
    (P : ObservedCircuit (WildcardReg n r)) (p : ℝ) : Prop :=
  observedWellFormed P ∧
    ∀ (x : BitStr n) (ψ : QState (WildcardReg n r)),
      Normalized ψ → p ≤ programSuccessMass n r readOut P ψ x

/-- Worst-case `p`-success of a program solving combinatorial group testing. -/
def SolvesCGTWith (n r : ℕ) (readOut : CGTReg n r → BitStr n)
    (P : ObservedCircuit (CGTReg n r)) (p : ℝ) : Prop :=
  observedWellFormed P ∧
    ∀ (x : BitStr n) (ψ : QState (CGTReg n r)),
      Normalized ψ → p ≤ programCGTSuccessMass n r readOut P ψ x

/-- Worst-case `p`-success from a *fixed* initial state `ψ₀` (the paper's
algorithm starts in a prescribed state, e.g. the all-zero register). -/
def SolvesWildcardFrom (n r : ℕ) (readOut : WildcardReg n r → BitStr n)
    (P : ObservedCircuit (WildcardReg n r)) (ψ₀ : QState (WildcardReg n r))
    (p : ℝ) : Prop :=
  observedWellFormed P ∧
    ∀ x : BitStr n, p ≤ programSuccessMass n r readOut P ψ₀ x

/-- Worst-case `p`-success for CGT from a fixed initial state. -/
def SolvesCGTFrom (n r : ℕ) (readOut : CGTReg n r → BitStr n)
    (P : ObservedCircuit (CGTReg n r)) (ψ₀ : QState (CGTReg n r))
    (p : ℝ) : Prop :=
  observedWellFormed P ∧
    ∀ x : BitStr n, p ≤ programCGTSuccessMass n r readOut P ψ₀ x

/-- CGT success restricted to inputs of Hamming weight at most `k`, the promise of
the combinatorial group testing problem. -/
def SolvesCGTWeightFrom (n r : ℕ) (k : ℕ) (readOut : CGTReg n r → BitStr n)
    (P : ObservedCircuit (CGTReg n r)) (ψ₀ : QState (CGTReg n r))
    (p : ℝ) : Prop :=
  observedWellFormed P ∧
    ∀ x : BitStr n, bitWeight x ≤ k → p ≤ programCGTSuccessMass n r readOut P ψ₀ x

/-- The all-zero initial register of the wildcard model on `n` bits, with `r + 1`
workspace qubits (so the register is inhabited). -/
def zeroReg (n r : ℕ) : WildcardReg n (r + 1) :=
  ((∅, fun _ => false, false), (0 : Fin (r + 1)))

/-- The all-zero initial register of the CGT model. -/
def zeroRegCGT (n r : ℕ) : CGTReg n (r + 1) :=
  ((∅, false), (0 : Fin (r + 1)))

/-- The syntactic worst-case number of oracle calls along any branch. -/
def programQueries {I : Type} (P : ObservedCircuit I) : ℕ := observedQueryDepth P

/-- The paper's "queries on average": the expected number of wildcard-oracle calls
of a program run from the all-zero register against the oracle of `x`
(`expectedObservedQueries` of the observed-circuit model). -/
noncomputable def expectedWildcardQueries (n r : ℕ)
    (P : ObservedCircuit (WildcardReg n (r + 1))) (x : BitStr n) : ℝ :=
  expectedObservedQueries (wildcardOracle n (r + 1) x) P (Ket (zeroReg n r))

/-- The expected number of CGT-oracle calls of a program run from the all-zero
register against the oracle of `x`. -/
noncomputable def expectedCGTQueries (n r : ℕ)
    (P : ObservedCircuit (CGTReg n (r + 1))) (x : BitStr n) : ℝ :=
  expectedObservedQueries (cgtOracle n (r + 1) x) P (Ket (zeroRegCGT n r))

end Qatlib.Papers.WildcardSrch12.MainResults
