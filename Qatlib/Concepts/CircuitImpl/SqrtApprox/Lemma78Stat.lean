/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.MultiKnownQubitControl
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis

/-!
# Full-matrix specification for multi-controlled synthesis

`Lemma7_8` states the full-register operator-norm formulation of approximate multi-controlled
single-qubit synthesis, following Lemma 7.8 of [BarencoEtAl1995]. It compares a legal query-free
program with an ideal unitary that applies `U` exactly when all specified controls are true.

## Main definitions

* `Lemma7_8`: an approximation error at most `π / 2^k` and a gate bound `(240 * (m + 1) + 20) *
  k`.

## References

* [Barenco et al., 1995, Section 7][BarencoEtAl1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.SqrtApprox

open scoped Matrix.Norms.L2Operator

/-- The specification of a legal query-free approximation to an ideal multi-controlled unitary,
with full-register operator-norm error at most `π / 2^k` and the stated gate bound
[BarencoEtAl1995]. -/
def Lemma7_8 : Prop :=
  ∀ (N m k : ℕ) (c : ℕ → Fin N) (t : Fin N),
    Set.InjOn c (Set.Iio m) → (∀ i < m, c i ≠ t) →
    ∀ (U : Matrix Bool Bool ℂ), U ∈ Matrix.unitaryGroup Bool ℂ →
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧
      gs.length ≤ (240 * (m + 1) + 20) * k ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∃ G : Matrix (Reg N) (Reg N) ℂ, G ∈ Matrix.unitaryGroup (Reg N) ℂ ∧
        ‖reflectionProgramMatrix gs - G‖ ≤ Real.pi / (2 ^ k : ℝ) ∧
        ∀ (x : Reg N) (φ : QState Bool), ApplyGate G (multiWireState t x φ) =
          multiWireState t x
            (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) m then U else 1) φ)

end Qatlib.Concepts.CircuitImpl.SqrtApprox
