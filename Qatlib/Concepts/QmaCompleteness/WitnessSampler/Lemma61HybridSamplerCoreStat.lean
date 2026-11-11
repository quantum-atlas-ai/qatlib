/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.WitnessSampler.TwoOracleDefs

/-!
# Hybrid witness-sampler specification

This module defines `Lemma6_1HybridSamplerCore`, the proposition relating a circuit's ability to
distinguish a predicate from a subpredicate to its query-state mass on their difference. The
statement uses a two-thirds versus one-third measurement gap and an upper bound `t` on the
number of first-oracle queries.

The specification isolates the quantitative conclusion of a quantum query hybrid argument, as in
the general method of [BennettEtAl1997].

## Main statements

* `Lemma6_1HybridSamplerCore`: the average controlled difference mass is at least `1 / (36 * (t
  : ℝ) ^ 2)`.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QmaCompleteness.WitnessSampler

open Qatlib

/-- The proposition that any circuit with unitary gates and a normalized initial state, using at
most `t` queries to the first oracle, must have summed `controlFiberMass` along its `Δ`
execution divided by `t` at least `1 / (36 * t ^ 2)` whenever `Δ` is contained in `S` and an
event has acceptance at least `2 / 3` under `S` and at most `1 / 3` under `Δ`. -/
def Lemma6_1HybridSamplerCore : Prop :=
  ∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] (S Δ U : Reg n → Bool) (t : ℕ)
    (C : TOCircuit (ForrSpace n W)) (ψ : QState (ForrSpace n W))
    (E : Finset (ForrSpace n W)),
    IsUnitaryTOCircuit C →
    Normalized ψ →
    (∀ x, Δ x → S x) →
    TOQueryCountS C ≤ t →
    2 / 3 ≤
        MeasureProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ) E →
    MeasureProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) E ≤ 1 / 3 →
    1 / (t : ℝ) *
        ((sQueryStates (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ).map
          (controlFiberMass n S Δ W)).sum ≥
      1 / (36 * (t : ℝ) ^ 2)

end Qatlib.Concepts.QmaCompleteness.WitnessSampler
