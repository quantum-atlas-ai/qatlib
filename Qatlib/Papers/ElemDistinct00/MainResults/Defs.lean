/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.GraphQuery.EdgeQuery.GraphSpectralDefs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Query models for element distinctness and claw finding

This module defines comparison query algorithms and correctness predicates for claw finding,
element distinctness, and triangle finding. It includes versions restricted to monotone inputs,
exact and bounded error success conditions, and uniform constant factor query bound predicates.
Evaluation query algorithms and the parity collision, no collision, and no range relations
supply the remaining problem interfaces.

The mathematical setting follows [BuhrmanEtAl2005].

## Main statements

* `ClawAlgorithm`, `ElemDistinctAlgorithm`, and `TriangleAlgorithm`: comparison and graph query
  algorithm data.
* `ClawBoundedError`, `EDExact`, and related predicates: success specifications.
* `EvalAlgorithm` and `evalComputes`: evaluation query algorithms and their success condition.

## References

* [Buhrman et al., 2005][BuhrmanEtAl2005]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ElemDistinct00.MainResults.Defs

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.PureStateMath

open scoped Classical

/-- A query index and Boolean answer register paired with a work register. -/
abbrev ComparisonWorkspace (I W : Type*) := (I × Bool) × W

/-- The condition that `f` and `g` take the same value at some pair of inputs. -/
def HasClaw {X Y Z : Type*} (f : X → Z) (g : Y → Z) : Prop :=
  ∃ x y, f x = g y

/-- The condition that `f` takes the same value at two distinct inputs. -/
def HasCollision {X Z : Type*} (f : X → Z) : Prop :=
  ∃ x y, x ≠ y ∧ f x = f y

/-- The condition that `f` has no collision between distinct inputs. -/
def ElementDistinct {X Z : Type*} (f : X → Z) : Prop :=
  ¬ HasCollision f

/-- The Boolean value of the comparison `f p.1 ≤ g p.2`. -/
def comparisonBit {X Y Z : Type*} [LinearOrder Z] (f : X → Z) (g : Y → Z)
    (p : X × Y) : Bool :=
  decide (f p.1 ≤ g p.2)

/-- The Boolean value comparing `f` at the two components of an input pair. -/
def selfComparisonBit {X Z : Type*} [LinearOrder Z] (f : X → Z)
    (p : X × X) : Bool :=
  decide (f p.1 ≤ f p.2)

/-- A comparison query circuit with a normalized initial state, unitary gates, and a work
register decoder producing an optional pair of inputs. -/
structure ClawAlgorithm (X Y Z W : Type*) [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype W] [DecidableEq W] where

  circuit : Circuit (ComparisonWorkspace (X × Y) W)

  init : QState (ComparisonWorkspace (X × Y) W)

  decoder : W → Option (X × Y)

  unitary : IsUnitaryCircuit circuit

  norm : Normalized init

variable {X Y Z W : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [LinearOrder Z] [Fintype W] [DecidableEq W]

/-- The final state of a claw algorithm executed with the comparison bit oracle for `f` and `g`. -/
def clawRun (A : ClawAlgorithm X Y Z W) (f : X → Z) (g : Y → Z) :
    QState (ComparisonWorkspace (X × Y) W) :=
  Run (TensorGate (BitOracleOn (comparisonBit f g)) 1) A.circuit A.init

/-- The measurement outcomes whose decoded pair is a claw of `f` and `g`. -/
def clawSuccessSet (A : ClawAlgorithm X Y Z W) (f : X → Z) (g : Y → Z) :
    Finset (ComparisonWorkspace (X × Y) W) :=
  Finset.univ.filter fun q => ∃ a b, A.decoder q.2 = some (a, b) ∧ f a = g b

/-- The measurement outcomes whose work register decodes to `none`. -/
def clawNoneSet (A : ClawAlgorithm X Y Z W) :
    Finset (ComparisonWorkspace (X × Y) W) :=
  Finset.univ.filter fun q => A.decoder q.2 = none

/-- The condition that every input possessing a claw yields a correct claw with probability at
least two thirds. -/
def ClawBoundedError (A : ClawAlgorithm X Y Z W) : Prop :=
  ∀ (f : X → Z) (g : Y → Z), HasClaw f g →
    (2 / 3 : ℝ) ≤ MeasureProb (clawRun A f g) (clawSuccessSet A f g)

/-- The condition that every claw input yields a correct claw with probability one and every
input without a claw yields `none` with probability one. -/
def ClawExact (A : ClawAlgorithm X Y Z W) : Prop :=
  (∀ (f : X → Z) (g : Y → Z), HasClaw f g →
      MeasureProb (clawRun A f g) (clawSuccessSet A f g) = 1) ∧
  (∀ (f : X → Z) (g : Y → Z), ¬ HasClaw f g →
      MeasureProb (clawRun A f g) (clawNoneSet A) = 1)

/-- A uniform positive constant multiple of `g N M` lower bounds the query count of every
bounded error claw algorithm for `0 < N ≤ M`. -/
def ClawQ2LowerBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N M : ℕ), 0 < N → N ≤ M →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin M) ℤ W),
      ClawBoundedError A → c * g N M ≤ (QueryCount A.circuit : ℝ)

/-- For every `0 < N ≤ M`, a bounded error claw algorithm exists with query count bounded by a
uniform positive constant times `g N M`. -/
def ClawQ2UpperBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N M : ℕ), 0 < N → N ≤ M →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin M) ℤ W),
      ClawBoundedError A ∧ (QueryCount A.circuit : ℝ) ≤ c * g N M

/-- A uniform positive constant multiple of `g N M` lower bounds the query count of every exact
claw algorithm for `0 < N ≤ M`. -/
def ClawQeLowerBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N M : ℕ), 0 < N → N ≤ M →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin M) ℤ W),
      ClawExact A → c * g N M ≤ (QueryCount A.circuit : ℝ)

/-- For every `0 < N ≤ M`, an exact claw algorithm exists with query count bounded by a uniform
positive constant times `g N M`. -/
def ClawQeUpperBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N M : ℕ), 0 < N → N ≤ M →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin M) ℤ W),
      ClawExact A ∧ (QueryCount A.circuit : ℝ) ≤ c * g N M

/-- A self-comparison query circuit with a normalized initial state, unitary gates, and a
decoder producing an optional pair of inputs. -/
structure ElemDistinctAlgorithm (X Z W : Type*) [Fintype X] [DecidableEq X]
    [Fintype W] [DecidableEq W] where
  circuit : Circuit (ComparisonWorkspace (X × X) W)
  init : QState (ComparisonWorkspace (X × X) W)
  decoder : W → Option (X × X)
  unitary : IsUnitaryCircuit circuit
  norm : Normalized init

variable {X Z W : Type*} [Fintype X] [DecidableEq X] [LinearOrder Z]
  [Fintype W] [DecidableEq W]

/-- The final state of an element distinctness algorithm executed with the self-comparison
oracle of `f`. -/
def edRun (A : ElemDistinctAlgorithm X Z W) (f : X → Z) :
    QState (ComparisonWorkspace (X × X) W) :=
  Run (TensorGate (BitOracleOn (selfComparisonBit f)) 1) A.circuit A.init

/-- The measurement outcomes whose decoded pair consists of distinct inputs with the same `f`
value. -/
def edSuccessSet (A : ElemDistinctAlgorithm X Z W) (f : X → Z) :
    Finset (ComparisonWorkspace (X × X) W) :=
  Finset.univ.filter fun q =>
    ∃ a b, A.decoder q.2 = some (a, b) ∧ a ≠ b ∧ f a = f b

/-- The measurement outcomes whose element distinctness decoder returns `none`. -/
def edNoneSet (A : ElemDistinctAlgorithm X Z W) :
    Finset (ComparisonWorkspace (X × X) W) :=
  Finset.univ.filter fun q => A.decoder q.2 = none

/-- The condition that every function with a collision yields a correct collision with
probability at least two thirds. -/
def EDBoundedError (A : ElemDistinctAlgorithm X Z W) : Prop :=
  ∀ (f : X → Z), HasCollision f →
    (2 / 3 : ℝ) ≤ MeasureProb (edRun A f) (edSuccessSet A f)

/-- The condition that collisions are returned with probability one when they exist and `none`
is returned with probability one otherwise. -/
def EDExact (A : ElemDistinctAlgorithm X Z W) : Prop :=
  (∀ (f : X → Z), HasCollision f →
      MeasureProb (edRun A f) (edSuccessSet A f) = 1) ∧
  (∀ (f : X → Z), ¬ HasCollision f →
      MeasureProb (edRun A f) (edNoneSet A) = 1)

/-- A uniform positive constant multiple of `g N` lower bounds the query count of every bounded
error element distinctness algorithm on a positive domain size. -/
def EDQ2LowerBound (g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ), 0 < N →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ElemDistinctAlgorithm (Fin N) ℤ W),
      EDBoundedError A → c * g N ≤ (QueryCount A.circuit : ℝ)

/-- For every positive domain size `N`, a bounded error element distinctness algorithm exists
with query count at most a uniform positive constant times `g N`. -/
def EDQ2UpperBound (g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ), 0 < N →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ElemDistinctAlgorithm (Fin N) ℤ W),
      EDBoundedError A ∧ (QueryCount A.circuit : ℝ) ≤ c * g N

/-- A uniform positive constant multiple of `g N` lower bounds the query count of every exact
element distinctness algorithm on a positive domain size. -/
def EDQeLowerBound (g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ), 0 < N →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ElemDistinctAlgorithm (Fin N) ℤ W),
      EDExact A → c * g N ≤ (QueryCount A.circuit : ℝ)

/-- For every positive domain size `N`, an exact element distinctness algorithm exists with
query count at most a uniform positive constant times `g N`. -/
def EDQeUpperBound (g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ), 0 < N →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ElemDistinctAlgorithm (Fin N) ℤ W),
      EDExact A ∧ (QueryCount A.circuit : ℝ) ≤ c * g N

section Ordered

variable [Preorder X]

/-- The condition that a claw is returned with probability at least two thirds whenever the
first function is monotone and a claw exists. -/
def OrderedClawBoundedError (A : ClawAlgorithm X Y Z W) : Prop :=
  ∀ (f : X → Z) (g : Y → Z), Monotone f → HasClaw f g →
    (2 / 3 : ℝ) ≤ MeasureProb (clawRun A f g) (clawSuccessSet A f g)

/-- Exact claw finding and exact reporting of `none` on inputs whose first function is monotone. -/
def OrderedClawExact (A : ClawAlgorithm X Y Z W) : Prop :=
  (∀ (f : X → Z) (g : Y → Z), Monotone f → HasClaw f g →
      MeasureProb (clawRun A f g) (clawSuccessSet A f g) = 1) ∧
  (∀ (f : X → Z) (g : Y → Z), Monotone f → ¬ HasClaw f g →
      MeasureProb (clawRun A f g) (clawNoneSet A) = 1)

/-- A uniform positive constant multiple of `g N M` lower bounds the query count of every
bounded error claw algorithm restricted to a monotone first function, for positive `N` and
`M`. -/
def OrderedClawQ2LowerBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N M : ℕ), 0 < N → 0 < M →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin M) ℤ W),
      OrderedClawBoundedError A → c * g N M ≤ (QueryCount A.circuit : ℝ)

/-- For all positive `N` and `M`, a claw algorithm correct with bounded error for a monotone
first function exists with query count at most a uniform positive constant times `g N M`. -/
def OrderedClawQ2UpperBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N M : ℕ), 0 < N → 0 < M →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin M) ℤ W),
      OrderedClawBoundedError A ∧ (QueryCount A.circuit : ℝ) ≤ c * g N M

/-- A uniform positive constant multiple of `g N M` lower bounds the query count of every exact
claw algorithm restricted to a monotone first function, for positive `N` and `M`. -/
def OrderedClawQeLowerBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N M : ℕ), 0 < N → 0 < M →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin M) ℤ W),
      OrderedClawExact A → c * g N M ≤ (QueryCount A.circuit : ℝ)

/-- For all positive `N` and `M`, an exact claw algorithm for a monotone first function exists
with query count at most a uniform positive constant times `g N M`. -/
def OrderedClawQeUpperBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N M : ℕ), 0 < N → 0 < M →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin M) ℤ W),
      OrderedClawExact A ∧ (QueryCount A.circuit : ℝ) ≤ c * g N M

end Ordered

section BothOrdered

variable [Preorder X] [Preorder Y]

/-- The condition that a claw is returned with probability at least two thirds whenever both
functions are monotone and a claw exists. -/
def BothOrderedClawBoundedError (A : ClawAlgorithm X Y Z W) : Prop :=
  ∀ (f : X → Z) (g : Y → Z), Monotone f → Monotone g → HasClaw f g →
    (2 / 3 : ℝ) ≤ MeasureProb (clawRun A f g) (clawSuccessSet A f g)

/-- Exact claw finding and exact reporting of `none` on inputs where both functions are
monotone. -/
def BothOrderedClawExact (A : ClawAlgorithm X Y Z W) : Prop :=
  (∀ (f : X → Z) (g : Y → Z), Monotone f → Monotone g → HasClaw f g →
      MeasureProb (clawRun A f g) (clawSuccessSet A f g) = 1) ∧
  (∀ (f : X → Z) (g : Y → Z), Monotone f → Monotone g → ¬ HasClaw f g →
      MeasureProb (clawRun A f g) (clawNoneSet A) = 1)

/-- A uniform positive constant multiple of `bound N` lower bounds the query count of every
bounded error claw algorithm for two monotone functions on domains of the same positive size
`N`. -/
def BothOrderedQ2LowerBound (bound : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin N) ℤ W),
      BothOrderedClawBoundedError A → c * bound N ≤ (QueryCount A.circuit : ℝ)

/-- For every positive `N`, a bounded error claw algorithm for two monotone functions on domains
of size `N` exists with query count at most a uniform positive constant times `bound N`. -/
def BothOrderedQ2UpperBound (bound : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin N) ℤ W),
      BothOrderedClawBoundedError A ∧ (QueryCount A.circuit : ℝ) ≤ c * bound N

/-- A uniform positive constant multiple of `bound N` lower bounds the query count of every
exact claw algorithm for two monotone functions on domains of the same positive size `N`. -/
def BothOrderedQeLowerBound (bound : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin N) ℤ W),
      BothOrderedClawExact A → c * bound N ≤ (QueryCount A.circuit : ℝ)

/-- For every positive `N`, an exact claw algorithm for two monotone functions on domains of
size `N` exists with query count at most a uniform positive constant times `bound N`. -/
def BothOrderedQeUpperBound (bound : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin N) ℤ W),
      BothOrderedClawExact A ∧ (QueryCount A.circuit : ℝ) ≤ c * bound N

end BothOrdered

/-- The condition that `a`, `b`, and `c` are pairwise distinct vertices with all three edges
present in `G`. -/
def IsTriangle {V : Type*} (G : SimpleGraph V) (a b c : V) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/-- The condition that `G` contains three vertices forming a triangle. -/
def HasTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c, IsTriangle G a b c

/-- An edge query circuit with a normalized initial state, unitary gates, and a work register
decoder producing an optional triple of vertices. -/
structure TriangleAlgorithm (V W : Type*) [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] where
  circuit : Circuit (ComparisonWorkspace (V × V) W)
  init : QState (ComparisonWorkspace (V × V) W)
  decoder : W → Option (V × V × V)
  unitary : IsUnitaryCircuit circuit
  norm : Normalized init

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- The final state of a triangle algorithm executed with the edge bit oracle of `G`. -/
def triRun (A : TriangleAlgorithm V W) (G : SimpleGraph V) [DecidableRel G.Adj] :
    QState (ComparisonWorkspace (V × V) W) :=
  Run (TensorGate (BitOracleOn
    (fun p : V × V => Qatlib.Concepts.GraphQuery.EdgeQuery.edgeBit G p)) 1)
    A.circuit A.init

/-- The measurement outcomes whose decoded triple forms a triangle in `G`. -/
def triSuccessSet (A : TriangleAlgorithm V W) (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (ComparisonWorkspace (V × V) W) :=
  Finset.univ.filter fun q => ∃ a b c, A.decoder q.2 = some (a, b, c) ∧ IsTriangle G a b c

/-- The measurement outcomes whose triangle decoder returns `none`. -/
def triNoneSet (A : TriangleAlgorithm V W) :
    Finset (ComparisonWorkspace (V × V) W) :=
  Finset.univ.filter fun q => A.decoder q.2 = none

/-- The condition that every graph containing a triangle yields a correct triangle with
probability at least two thirds. -/
def TriangleBoundedError (A : TriangleAlgorithm V W) : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj], HasTriangle G →
    (2 / 3 : ℝ) ≤ MeasureProb (triRun A G) (triSuccessSet A G)

/-- The condition that a correct triangle is returned with probability one when one exists and
`none` is returned with probability one otherwise. -/
def TriangleExact (A : TriangleAlgorithm V W) : Prop :=
  (∀ (G : SimpleGraph V) [DecidableRel G.Adj], HasTriangle G →
      MeasureProb (triRun A G) (triSuccessSet A G) = 1) ∧
  (∀ (G : SimpleGraph V) [DecidableRel G.Adj], ¬ HasTriangle G →
      MeasureProb (triRun A G) (triNoneSet A) = 1)

/-- The condition that the finite edge set of `G` has cardinality `m`. -/
def HasEdgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) : Prop :=
  G.edgeFinset.card = m

/-- The condition that every graph with exactly `m` edges and a triangle yields a correct
triangle with probability at least two thirds. -/
def TriangleBoundedErrorOn (A : TriangleAlgorithm V W) (m : ℕ) : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj], HasEdgeCount G m → HasTriangle G →
    (2 / 3 : ℝ) ≤ MeasureProb (triRun A G) (triSuccessSet A G)

/-- Exact triangle finding and exact reporting of `none`, restricted to graphs with exactly `m`
edges. -/
def TriangleExactOn (A : TriangleAlgorithm V W) (m : ℕ) : Prop :=
  (∀ (G : SimpleGraph V) [DecidableRel G.Adj], HasEdgeCount G m → HasTriangle G →
      MeasureProb (triRun A G) (triSuccessSet A G) = 1) ∧
  (∀ (G : SimpleGraph V) [DecidableRel G.Adj], HasEdgeCount G m → ¬ HasTriangle G →
      MeasureProb (triRun A G) (triNoneSet A) = 1)

/-- A uniform positive constant multiple of `g n m` lower bounds the query count of every
bounded error triangle algorithm on graphs with `n` vertices and `m` edges when `0 < n ≤ m`. -/
def TriangleQ2LowerBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ), 0 < n → n ≤ m →
    ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : TriangleAlgorithm V W),
      (Fintype.card V = n) → TriangleBoundedErrorOn A m →
      c * g n m ≤ (QueryCount A.circuit : ℝ)

/-- For every nonempty finite vertex type and edge count `m`, a bounded error triangle algorithm
exists with query count at most a uniform positive constant times `g` of the vertex and edge
counts. -/
def TriangleQ2UpperBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (m : ℕ),
    0 < Fintype.card V →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : TriangleAlgorithm V W),
      TriangleBoundedErrorOn A m ∧
        (QueryCount A.circuit : ℝ) ≤ c * g (Fintype.card V) m

/-- A uniform positive constant multiple of `g n m` lower bounds the query count of every exact
triangle algorithm on graphs with `n` vertices and `m` edges when `0 < n ≤ m`. -/
def TriangleQeLowerBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ), 0 < n → n ≤ m →
    ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : TriangleAlgorithm V W),
      (Fintype.card V = n) → TriangleExactOn A m →
      c * g n m ≤ (QueryCount A.circuit : ℝ)

/-- For every nonempty finite vertex type and edge count `m`, an exact triangle algorithm exists
with query count at most a uniform positive constant times `g` of the vertex and edge
counts. -/
def TriangleQeUpperBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (m : ℕ),
    0 < Fintype.card V →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : TriangleAlgorithm V W),
      TriangleExactOn A m ∧
        (QueryCount A.circuit : ℝ) ≤ c * g (Fintype.card V) m

/-- The evaluation query workspace consisting of an input index, Boolean register, value
register, and work register. -/
abbrev EvalWorkspace (N : ℕ) (W : Type*) := (Fin N × Bool) × (Fin N × W)

/-- Adds `f` of the input index to the value register modulo `N`, retaining the other registers. -/
def evalShift {N : ℕ} {W : Type*} (hN : 0 < N) (f : Fin N → Fin N)
    (q : EvalWorkspace N W) : EvalWorkspace N W :=
  ((q.1.1, q.1.2),
   (⟨(q.2.1.val + (f q.1.1).val) % N, Nat.mod_lt _ hN⟩, q.2.2))

/-- The matrix of the evaluation shift, with entry one exactly when the output basis index is
the shifted input index. -/
noncomputable def evalOracleMatrix {N : ℕ} {W : Type*} [DecidableEq W]
    (hN : 0 < N) (f : Fin N → Fin N) :
    Matrix (EvalWorkspace N W) (EvalWorkspace N W) ℂ :=
  fun a b => if a = evalShift hN f b then (1 : ℂ) else 0

/-- An evaluation query circuit with a normalized initial state, unitary gates, and a work
register decoder producing an optional answer. -/
structure EvalAlgorithm (N : ℕ) (W : Type*) (Ans : Type*) [Fintype W] [DecidableEq W] where
  circuit : Circuit (EvalWorkspace N W)
  init : QState (EvalWorkspace N W)
  decoder : W → Option Ans
  unitary : IsUnitaryCircuit circuit
  norm : Normalized init

variable {N : ℕ} {W Ans : Type*} [Fintype W] [DecidableEq W]

/-- The final state of an evaluation algorithm executed with the modular evaluation oracle for
`f`. -/
def evalRun (hN : 0 < N) (A : EvalAlgorithm N W Ans) (f : Fin N → Fin N) :
    QState (EvalWorkspace N W) :=
  Run (evalOracleMatrix hN f) A.circuit A.init

/-- The probability that execution on `f` decodes an answer satisfying `P`. -/
noncomputable def evalSuccessProb (hN : 0 < N) (A : EvalAlgorithm N W Ans)
    (f : Fin N → Fin N) (P : Ans → Prop) : ℝ :=
  MeasureProb (evalRun hN A f)
    (Finset.univ.filter fun q => ∃ a, A.decoder q.2.2 = some a ∧ P a)

/-- The condition that, for every `f`, the algorithm returns an answer satisfying the relation
`P f` with probability at least two thirds. -/
def evalComputes (hN : 0 < N) (A : EvalAlgorithm N W Ans)
    (P : (Fin N → Fin N) → Ans → Prop) : Prop :=
  ∀ f : Fin N → Fin N, (2 / 3 : ℝ) ≤ evalSuccessProb hN A f (P f)

/-- The number of pairs of indices `i < j` with equal `f` values. -/
def collisionCount {N : ℕ} (f : Fin N → Fin N) : ℕ :=
  (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2 ∧ f p.1 = f p.2).card

/-- The relation requiring the output bit to equal the parity of the number of colliding index
pairs. -/
def ParityCollisionProblem {N : ℕ} (f : Fin N → Fin N) (a : Fin 2) : Prop :=
  (a : ℕ) = collisionCount f % 2

/-- The relation requiring `x` to be the unique input having value `f x`. -/
def NoCollisionProblem {N : ℕ} (f : Fin N → Fin N) (x : Fin N) : Prop :=
  ∀ y : Fin N, f y = f x → y = x

/-- The relation requiring the output `z` to lie outside the range of `f`. -/
def NoRangeProblem {N : ℕ} (f : Fin N → Fin N) (z : Fin N) : Prop :=
  ∀ x : Fin N, f x ≠ z

/-- A uniform positive constant multiple of `bound N` lower bounds the query count of every
evaluation algorithm computing collision parity on positive sizes divisible by four. -/
def ParityCollisionLowerBound (bound : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (hN : 0 < N), 4 ∣ N →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : EvalAlgorithm N W (Fin 2)),
      evalComputes hN A (fun f a => ParityCollisionProblem f a) →
      c * bound N ≤ (QueryCount A.circuit : ℝ)

/-- A uniform positive constant multiple of `bound N` lower bounds the query count of every
evaluation algorithm finding an input with a unique image on positive odd sizes. -/
def NoCollisionLowerBound (bound : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (hN : 0 < N), Odd N →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : EvalAlgorithm N W (Fin N)),
      evalComputes hN A (fun f x => NoCollisionProblem f x) →
      c * bound N ≤ (QueryCount A.circuit : ℝ)

/-- A uniform positive constant multiple of `bound N` lower bounds the query count of every
evaluation algorithm finding a value outside the range on positive sizes. -/
def NoRangeLowerBound (bound : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (hN : 0 < N),
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : EvalAlgorithm N W (Fin N)),
      evalComputes hN A (fun f z => NoRangeProblem f z) →
      c * bound N ≤ (QueryCount A.circuit : ℝ)

end Qatlib.Papers.ElemDistinct00.MainResults.Defs
