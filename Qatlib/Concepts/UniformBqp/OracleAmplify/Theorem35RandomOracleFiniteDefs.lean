/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude

/-!
# Finite random-oracle decision data

`bitQueryOf` expresses a string-valued oracle as coordinate queries on `QueryRegister`.
`acceptProb` and `decidesAtAllOnes` formulate bounded-error recognition of whether the all-ones
string occurs in the oracle image, as used in [BennettEtAl1997]. The background is described in
[BennettEtAl1997].

## Main statements

* `acceptProb`: acceptance probability for coordinate access to a finite oracle.
* `decidesAtAllOnes`: the two-sided bounded-error decision criterion.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option warningAsError false

open Qatlib

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.UniformBqp.OracleAmplify

/-- The constant Boolean string whose value at every coordinate is true. -/
def allOnes {K : Type} : K → Bool := fun _ => true

/-- The Boolean query returning coordinate `p.2` of the oracle output at input `p.1`. -/
def bitQueryOf {K : Type} (A : (K → Bool) → (K → Bool)) :
    ((K → Bool) × K) → Bool := fun p => A p.1 p.2

/-- The register consisting of a Boolean-string oracle input, an output-coordinate index, a
query-answer bit, and a workspace. -/
abbrev QueryRegister (K W : Type) := ((((K → Bool) × K) × Bool) × W)

/-- The measurement probability of event `E` after running `C` from `ψ` with coordinate access
to oracle `A`. -/
noncomputable def acceptProb {K W : Type} [Fintype K] [DecidableEq K] [Fintype W]
    [DecidableEq W] (C : Circuit (QueryRegister K W)) (ψ : QState (QueryRegister K W))
    (E : Finset (QueryRegister K W)) (A : (K → Bool) → (K → Bool)) : ℝ :=
  MeasureProb (Run (workspaceBitOracle (W := W) (bitQueryOf A)) C ψ) E

/-- The bounded-error decision condition that `p ≥ 2/3` when the all-ones string occurs in the
oracle image and `p ≤ 1/3` otherwise. -/
def decidesAtAllOnes {K : Type} [Fintype K] [DecidableEq K] (p : ℝ)
    (A : (K → Bool) → (K → Bool)) : Prop :=
  ((allOnes ∈ Finset.univ.image A) → 2 / 3 ≤ p) ∧
    ((allOnes ∉ Finset.univ.image A) → p ≤ 1 / 3)
end Qatlib.Concepts.UniformBqp.OracleAmplify
