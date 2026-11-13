/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.WitnessSampler.TwoOracleDefs

/-!
# Cumulative witness-sampler specification

This module defines the query-state transition mass `directTransitionMass`, the recursive
fresh-element mass `cumDirectSuccess`, and its witness-family average
`cumulativeSamplerSuccess`. The recursion keeps only elements satisfying `S` that have not yet
appeared in the history.

The proposition `Theorem6_2CumulativeSampler` specifies the cumulative lower bound and the query
counts after hardcoding the history predicate. The underlying quantum query hybrid method is
described in [BennettEtAl1997].

## Main statements

* `cumDirectSuccess`: cumulative mass of successive fresh elements of `S`.
* `cumulativeSamplerSuccess`: uniform average over the indexed witness family.
* `Theorem6_2CumulativeSampler`: success lower bound and hardcoded query-count specification.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QmaCompleteness.WitnessSampler

open Qatlib

/-- The sum of `sQueryBornMass` at address `x` over the states preceding first oracle queries,
divided by `TOQueryCountS C`, when the first phase oracle uses `regOfList n hist` and the
second uses `U`. This is zero when there are no first oracle queries. -/
noncomputable def directTransitionMass (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (S U : Reg n → Bool)
    (C : TOCircuit (ForrSpace n W)) (ψ : QState (ForrSpace n W)) (hist : List (Reg n))
    (x : Reg n) : ℝ :=
  1 / (TOQueryCountS C : ℝ) *
    ((sQueryStates (forrPhaseOracleS n (regOfList n hist) W) (forrPhaseOracleU n U W) C ψ).map
      (fun φ => sQueryBornMass n W φ x)).sum

/-- The recursive mass of obtaining `v` new distinct addresses satisfying `S` from history
`hist`, using `directTransitionMass` and prepending each selected address to the history;
zero further samples have mass one. -/
noncomputable def cumDirectSuccess (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] (S U : Reg n → Bool)
    (C : TOCircuit (ForrSpace n W)) (ψ : QState (ForrSpace n W)) :
    ℕ → List (Reg n) → ℝ
  | 0, _ => 1
  | v + 1, hist =>
      ∑ x : Reg n,
        (if S x ∧ x ∉ hist then directTransitionMass n W S U C ψ hist x else 0) *
          cumDirectSuccess n W S U C ψ v (x :: hist)

/-- The uniform average of `cumDirectSuccess` for `v` samples from empty history over the
initial state family `ψfam` indexed by `q` Boolean witness bits. -/
noncomputable def cumulativeSamplerSuccess (n q : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (S U : Reg n → Bool)
    (C : TOCircuit (ForrSpace n W)) (ψfam : (Fin q → Bool) → QState (ForrSpace n W))
    (v : ℕ) : ℝ :=
  1 / (Fintype.card (Fin q → Bool) : ℝ) *
    ∑ w, cumDirectSuccess n W S U C (ψfam w) v []

/-- The proposition that a circuit with unitary gates, normalized witness states, and at most
`t` queries to each oracle has `cumulativeSamplerSuccess ≥ 1 / (2 ^ q) * (1 / (36 * t ^ 2))
^ v` when every distinct history in `S` of length at most `v` gives acceptance at most `1 /
3` for all witnesses, while some witness gives acceptance at least `2 / 3` for the full `S`
oracle. It also requires `hardcodeS` with each history oracle to remove first oracle queries
and preserve the second oracle query count. -/
def Theorem6_2CumulativeSampler : Prop :=
  ∀ (n q t v : ℕ) (W : Type) [Fintype W] [DecidableEq W] (S U : Reg n → Bool)
    (C : TOCircuit (ForrSpace n W)) (ψfam : (Fin q → Bool) → QState (ForrSpace n W))
    (E : Finset (ForrSpace n W)),
    IsUnitaryTOCircuit C →
    (∀ w, Normalized (ψfam w)) →
    TOQueryCountS C ≤ t →
    TOQueryCountU C ≤ t →
    (∀ hist : List (Reg n), hist.Nodup → (∀ x ∈ hist, S x) → hist.length ≤ v →
      ∀ w', MeasureProb
          (TORun (forrPhaseOracleS n (regOfList n hist) W) (forrPhaseOracleU n U W) C
            (ψfam w')) E ≤
        1 / 3) →
    (∃ w₀, 2 / 3 ≤
        MeasureProb
          (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C (ψfam w₀)) E) →
    cumulativeSamplerSuccess n q W S U C ψfam v ≥
        1 / (2 ^ q : ℝ) * (1 / (36 * (t : ℝ) ^ 2)) ^ v ∧
    ∀ hist : List (Reg n),
      TOQueryCountS (hardcodeS (forrPhaseOracleS n (regOfList n hist) W) C) = 0 ∧
      TOQueryCountU (hardcodeS (forrPhaseOracleS n (regOfList n hist) W) C) = TOQueryCountU C

end Qatlib.Concepts.QmaCompleteness.WitnessSampler
