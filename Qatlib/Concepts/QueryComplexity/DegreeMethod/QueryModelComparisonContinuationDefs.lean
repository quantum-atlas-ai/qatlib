/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryModelComparison
import Mathlib.Tactic.Linarith

/-!
# Query conventions and search programs

This module packages quantum and classical decision conventions in `ComparisonConvention` and
`ClassicalConvention`, together with implication relations and minimum query counts within a
finite machine class. The decision and search viewpoints follow the query model of
[BealsEtAl2001].

`SearchProgram` specifies a circuit, initial state, and decoder; `SearchClass` records finite
families and the least realized query count at a prescribed success threshold.

## Main statements

* `ConventionHolds`: interpret a quantum decision convention.
* `ConventionMinQueries`: minimize query counts among programs satisfying a convention.
* `SearchClass.minSearchQueries`: minimize successful search query counts.

## References

* [Beals et al., 2001][BealsEtAl2001]
* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix
open scoped Classical BigOperators ENNReal

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- The exact, bounded-error, success-threshold, and parameterized inconclusive conventions for
quantum decision programs. -/
inductive ComparisonConvention where
  | exact
  | bounded
  | success
  | zeroErrorInconclusive (threshold : ℝ)
  deriving DecidableEq

/-- Interpret a comparison convention as a correctness predicate on a quantum decision program
for `f`. -/
def ConventionHolds (c : ComparisonConvention) (P : DecisionProgram I W)
    (f : (I → Bool) → Bool) : Prop :=
  match c with
  | .exact => P.ExactFor f
  | .bounded => P.BoundedFor f
  | .success => P.SuccessFor f
  | .zeroErrorInconclusive t => P.ZeroErrorInconclusiveFor f t

/-- A convention is stronger than another when it implies the latter for every decision program
and Boolean target function. -/
def ConventionStronger (c c' : ComparisonConvention) : Prop :=
  ∀ (P : DecisionProgram I W) (f : (I → Bool) → Bool),
    ConventionHolds c P f → ConventionHolds c' P f

/-- The default inconclusive threshold, equal to `1 / 3`. -/
def inconclusiveBudget : ℝ := 1 / 3

/-- The zero-error threshold, equal to zero. -/
def zeroErrorBudget : ℝ := 0

/-- The finite set of query counts of programs in `M` satisfying convention `c` for `f`. -/
def ConventionCountSet (M : MachineClass I W) (c : ComparisonConvention)
    (f : (I → Bool) → Bool) : Finset ℕ :=
  (M.programs.filter (fun P => decide (ConventionHolds c P f))).map
    (fun P => QueryCount P.circuit) |>.toFinset

/-- The least query count realized in `M` by a program satisfying convention `c` for `f`, given
existence of such a count. -/
noncomputable def ConventionMinQueries (M : MachineClass I W) (c : ComparisonConvention)
    (f : (I → Bool) → Bool) (h : ∃ n, n ∈ ConventionCountSet M c f) : ℕ :=
  finsetMinNat (ConventionCountSet M c f) h

/-- Success-threshold, zero-error, and parameterized inconclusive conventions for classical
randomized programs. -/
inductive ClassicalConvention where
  | success (threshold : ℝ≥0∞)
  | zeroError
  | zeroErrorInconclusive (threshold : ℝ≥0∞)
  deriving DecidableEq

/-- Interpret a classical convention as the corresponding correctness predicate for a program
computing `f`. -/
def ClassicalConventionHolds (c : ClassicalConvention) (prog : ClassicalProgram I Bool)
    (f : (I → Bool) → Bool) : Prop :=
  match c with
  | .success t => prog.ComputesWithSuccess f t
  | .zeroError => prog.ComputesZeroError f
  | .zeroErrorInconclusive t => prog.ComputesZeroErrorInconclusive f t

/-- A classical convention is stronger than another when its correctness predicate implies the
latter for every program and target function. -/
def ClassicalConventionStronger (c c' : ClassicalConvention) : Prop :=
  ∀ (prog : ClassicalProgram I Bool) (f : (I → Bool) → Bool),
    ClassicalConventionHolds c prog f → ClassicalConventionHolds c' prog f

/-- A finite set of marked indices together with its specified cardinality. -/
structure SearchInstance (N : ℕ) where
  marked : Finset (Fin N)
  solutions : ℕ
  card_marked : marked.card = solutions

/-- A quantum search program consisting of a circuit, an initial state, and a workspace decoder
that may return no index. -/
structure SearchProgram (N : ℕ) (W : Type) where
  circuit : Circuit (PolynomialWorkspace (Fin N) W)
  initial : QState (PolynomialWorkspace (Fin N) W)
  decode : W → Option (Fin N)

/-- The measurement weight of workspace outcomes decoding to an index in `S` after running the
search circuit with Boolean oracle `g`. -/
noncomputable def SearchProgram.successProb {N : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (P : SearchProgram N W) (g : Fin N → Bool) (S : Finset (Fin N)) : ℝ :=
  MeasureProb (Run (TensorGate (BitOracleOn g) (1 : Matrix W W ℂ)) P.circuit P.initial)
    {z | ∃ j, z.2 = j ∧ ∃ i, P.decode j = some i ∧ i ∈ S}

/-- The number of indices at which the Boolean oracle is true. -/
def markedCount {N : ℕ} (g : Fin N → Bool) : ℕ :=
  (Finset.univ.filter (fun i => g i = true)).card

/-- The number of oracle queries in a search program's circuit. -/
def SearchProgram.queryCount {N : ℕ} {W : Type} (P : SearchProgram N W) : ℕ :=
  QueryCount P.circuit

/-- A nonempty finite list of quantum search programs. -/
structure SearchClass (N : ℕ) (W : Type) where
  programs : List (SearchProgram N W)
  nonempty : programs ≠ []

/-- The finite set of query counts of programs whose success weight on the marked set reaches
`threshold`. -/
def SearchClass.realizedCountSet {N : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : SearchClass N W) (inst : SearchInstance N) (threshold : ℝ) : Finset ℕ :=
  let filtered : List (SearchProgram N W) :=
    C.programs.filter (fun (P : SearchProgram N W) =>
      decide (threshold ≤ P.successProb (fun i => decide (i ∈ inst.marked)) inst.marked))
  (filtered.map (fun (P : SearchProgram N W) => QueryCount P.circuit)).toFinset

/-- The least realized query count for searching `inst` with success weight at least
`threshold`, given a qualifying program. -/
noncomputable def SearchClass.minSearchQueries {N : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : SearchClass N W) (inst : SearchInstance N) (threshold : ℝ)
    (h : ∃ k, k ∈ C.realizedCountSet inst threshold) : ℕ :=
  finsetMinNat (C.realizedCountSet inst threshold) h

end Qatlib.Concepts.QueryComplexity.DegreeMethod
