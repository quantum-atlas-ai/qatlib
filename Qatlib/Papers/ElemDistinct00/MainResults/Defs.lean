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

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ElemDistinct00.MainResults.Defs

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.PureStateMath

open scoped Classical

abbrev ComparisonWorkspace (I W : Type*) := (I × Bool) × W

def HasClaw {X Y Z : Type*} (f : X → Z) (g : Y → Z) : Prop :=
  ∃ x y, f x = g y

def HasCollision {X Z : Type*} (f : X → Z) : Prop :=
  ∃ x y, x ≠ y ∧ f x = f y

def ElementDistinct {X Z : Type*} (f : X → Z) : Prop :=
  ¬ HasCollision f

def comparisonBit {X Y Z : Type*} [LinearOrder Z] (f : X → Z) (g : Y → Z)
    (p : X × Y) : Bool :=
  decide (f p.1 ≤ g p.2)

def selfComparisonBit {X Z : Type*} [LinearOrder Z] (f : X → Z)
    (p : X × X) : Bool :=
  decide (f p.1 ≤ f p.2)

structure ClawAlgorithm (X Y Z W : Type*) [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype W] [DecidableEq W] where

  circuit : Circuit (ComparisonWorkspace (X × Y) W)

  init : QState (ComparisonWorkspace (X × Y) W)

  decoder : W → Option (X × Y)

  unitary : IsUnitaryCircuit circuit

  norm : Normalized init

variable {X Y Z W : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [LinearOrder Z] [Fintype W] [DecidableEq W]

def clawRun (A : ClawAlgorithm X Y Z W) (f : X → Z) (g : Y → Z) :
    QState (ComparisonWorkspace (X × Y) W) :=
  Run (TensorGate (BitOracleOn (comparisonBit f g)) 1) A.circuit A.init

def clawSuccessSet (A : ClawAlgorithm X Y Z W) (f : X → Z) (g : Y → Z) :
    Finset (ComparisonWorkspace (X × Y) W) :=
  Finset.univ.filter fun q => ∃ a b, A.decoder q.2 = some (a, b) ∧ f a = g b

def clawNoneSet (A : ClawAlgorithm X Y Z W) :
    Finset (ComparisonWorkspace (X × Y) W) :=
  Finset.univ.filter fun q => A.decoder q.2 = none

def ClawBoundedError (A : ClawAlgorithm X Y Z W) : Prop :=
  ∀ (f : X → Z) (g : Y → Z), HasClaw f g →
    (2 / 3 : ℝ) ≤ MeasureProb (clawRun A f g) (clawSuccessSet A f g)

def ClawExact (A : ClawAlgorithm X Y Z W) : Prop :=
  (∀ (f : X → Z) (g : Y → Z), HasClaw f g →
      MeasureProb (clawRun A f g) (clawSuccessSet A f g) = 1) ∧
  (∀ (f : X → Z) (g : Y → Z), ¬ HasClaw f g →
      MeasureProb (clawRun A f g) (clawNoneSet A) = 1)

def ClawQ2LowerBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N M : ℕ), 0 < N → N ≤ M →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin M) ℤ W),
      ClawBoundedError A → c * g N M ≤ (QueryCount A.circuit : ℝ)

def ClawQ2UpperBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N M : ℕ), 0 < N → N ≤ M →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin M) ℤ W),
      ClawBoundedError A ∧ (QueryCount A.circuit : ℝ) ≤ c * g N M

def ClawQeLowerBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N M : ℕ), 0 < N → N ≤ M →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin M) ℤ W),
      ClawExact A → c * g N M ≤ (QueryCount A.circuit : ℝ)

def ClawQeUpperBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N M : ℕ), 0 < N → N ≤ M →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin M) ℤ W),
      ClawExact A ∧ (QueryCount A.circuit : ℝ) ≤ c * g N M

structure ElemDistinctAlgorithm (X Z W : Type*) [Fintype X] [DecidableEq X]
    [Fintype W] [DecidableEq W] where
  circuit : Circuit (ComparisonWorkspace (X × X) W)
  init : QState (ComparisonWorkspace (X × X) W)
  decoder : W → Option (X × X)
  unitary : IsUnitaryCircuit circuit
  norm : Normalized init

variable {X Z W : Type*} [Fintype X] [DecidableEq X] [LinearOrder Z]
  [Fintype W] [DecidableEq W]

def edRun (A : ElemDistinctAlgorithm X Z W) (f : X → Z) :
    QState (ComparisonWorkspace (X × X) W) :=
  Run (TensorGate (BitOracleOn (selfComparisonBit f)) 1) A.circuit A.init

def edSuccessSet (A : ElemDistinctAlgorithm X Z W) (f : X → Z) :
    Finset (ComparisonWorkspace (X × X) W) :=
  Finset.univ.filter fun q =>
    ∃ a b, A.decoder q.2 = some (a, b) ∧ a ≠ b ∧ f a = f b

def edNoneSet (A : ElemDistinctAlgorithm X Z W) :
    Finset (ComparisonWorkspace (X × X) W) :=
  Finset.univ.filter fun q => A.decoder q.2 = none

def EDBoundedError (A : ElemDistinctAlgorithm X Z W) : Prop :=
  ∀ (f : X → Z), HasCollision f →
    (2 / 3 : ℝ) ≤ MeasureProb (edRun A f) (edSuccessSet A f)

def EDExact (A : ElemDistinctAlgorithm X Z W) : Prop :=
  (∀ (f : X → Z), HasCollision f →
      MeasureProb (edRun A f) (edSuccessSet A f) = 1) ∧
  (∀ (f : X → Z), ¬ HasCollision f →
      MeasureProb (edRun A f) (edNoneSet A) = 1)

def EDQ2LowerBound (g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ), 0 < N →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ElemDistinctAlgorithm (Fin N) ℤ W),
      EDBoundedError A → c * g N ≤ (QueryCount A.circuit : ℝ)

def EDQ2UpperBound (g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ), 0 < N →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ElemDistinctAlgorithm (Fin N) ℤ W),
      EDBoundedError A ∧ (QueryCount A.circuit : ℝ) ≤ c * g N

def EDQeLowerBound (g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ), 0 < N →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ElemDistinctAlgorithm (Fin N) ℤ W),
      EDExact A → c * g N ≤ (QueryCount A.circuit : ℝ)

def EDQeUpperBound (g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ), 0 < N →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ElemDistinctAlgorithm (Fin N) ℤ W),
      EDExact A ∧ (QueryCount A.circuit : ℝ) ≤ c * g N

section Ordered

variable [Preorder X]

def OrderedClawBoundedError (A : ClawAlgorithm X Y Z W) : Prop :=
  ∀ (f : X → Z) (g : Y → Z), Monotone f → HasClaw f g →
    (2 / 3 : ℝ) ≤ MeasureProb (clawRun A f g) (clawSuccessSet A f g)

def OrderedClawExact (A : ClawAlgorithm X Y Z W) : Prop :=
  (∀ (f : X → Z) (g : Y → Z), Monotone f → HasClaw f g →
      MeasureProb (clawRun A f g) (clawSuccessSet A f g) = 1) ∧
  (∀ (f : X → Z) (g : Y → Z), Monotone f → ¬ HasClaw f g →
      MeasureProb (clawRun A f g) (clawNoneSet A) = 1)

def OrderedClawQ2LowerBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N M : ℕ), 0 < N → 0 < M →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin M) ℤ W),
      OrderedClawBoundedError A → c * g N M ≤ (QueryCount A.circuit : ℝ)

def OrderedClawQ2UpperBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N M : ℕ), 0 < N → 0 < M →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin M) ℤ W),
      OrderedClawBoundedError A ∧ (QueryCount A.circuit : ℝ) ≤ c * g N M

def OrderedClawQeLowerBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N M : ℕ), 0 < N → 0 < M →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin M) ℤ W),
      OrderedClawExact A → c * g N M ≤ (QueryCount A.circuit : ℝ)

def OrderedClawQeUpperBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N M : ℕ), 0 < N → 0 < M →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin M) ℤ W),
      OrderedClawExact A ∧ (QueryCount A.circuit : ℝ) ≤ c * g N M

end Ordered

section BothOrdered

variable [Preorder X] [Preorder Y]

def BothOrderedClawBoundedError (A : ClawAlgorithm X Y Z W) : Prop :=
  ∀ (f : X → Z) (g : Y → Z), Monotone f → Monotone g → HasClaw f g →
    (2 / 3 : ℝ) ≤ MeasureProb (clawRun A f g) (clawSuccessSet A f g)

def BothOrderedClawExact (A : ClawAlgorithm X Y Z W) : Prop :=
  (∀ (f : X → Z) (g : Y → Z), Monotone f → Monotone g → HasClaw f g →
      MeasureProb (clawRun A f g) (clawSuccessSet A f g) = 1) ∧
  (∀ (f : X → Z) (g : Y → Z), Monotone f → Monotone g → ¬ HasClaw f g →
      MeasureProb (clawRun A f g) (clawNoneSet A) = 1)

def BothOrderedQ2LowerBound (bound : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin N) ℤ W),
      BothOrderedClawBoundedError A → c * bound N ≤ (QueryCount A.circuit : ℝ)

def BothOrderedQ2UpperBound (bound : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin N) ℤ W),
      BothOrderedClawBoundedError A ∧ (QueryCount A.circuit : ℝ) ≤ c * bound N

def BothOrderedQeLowerBound (bound : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin N) ℤ W),
      BothOrderedClawExact A → c * bound N ≤ (QueryCount A.circuit : ℝ)

def BothOrderedQeUpperBound (bound : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ClawAlgorithm (Fin N) (Fin N) ℤ W),
      BothOrderedClawExact A ∧ (QueryCount A.circuit : ℝ) ≤ c * bound N

end BothOrdered

def IsTriangle {V : Type*} (G : SimpleGraph V) (a b c : V) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

def HasTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c, IsTriangle G a b c

structure TriangleAlgorithm (V W : Type*) [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] where
  circuit : Circuit (ComparisonWorkspace (V × V) W)
  init : QState (ComparisonWorkspace (V × V) W)
  decoder : W → Option (V × V × V)
  unitary : IsUnitaryCircuit circuit
  norm : Normalized init

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def triRun (A : TriangleAlgorithm V W) (G : SimpleGraph V) [DecidableRel G.Adj] :
    QState (ComparisonWorkspace (V × V) W) :=
  Run (TensorGate (BitOracleOn
    (fun p : V × V => Qatlib.Concepts.GraphQuery.EdgeQuery.edgeBit G p)) 1)
    A.circuit A.init

def triSuccessSet (A : TriangleAlgorithm V W) (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (ComparisonWorkspace (V × V) W) :=
  Finset.univ.filter fun q => ∃ a b c, A.decoder q.2 = some (a, b, c) ∧ IsTriangle G a b c

def triNoneSet (A : TriangleAlgorithm V W) :
    Finset (ComparisonWorkspace (V × V) W) :=
  Finset.univ.filter fun q => A.decoder q.2 = none

def TriangleBoundedError (A : TriangleAlgorithm V W) : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj], HasTriangle G →
    (2 / 3 : ℝ) ≤ MeasureProb (triRun A G) (triSuccessSet A G)

def TriangleExact (A : TriangleAlgorithm V W) : Prop :=
  (∀ (G : SimpleGraph V) [DecidableRel G.Adj], HasTriangle G →
      MeasureProb (triRun A G) (triSuccessSet A G) = 1) ∧
  (∀ (G : SimpleGraph V) [DecidableRel G.Adj], ¬ HasTriangle G →
      MeasureProb (triRun A G) (triNoneSet A) = 1)

def HasEdgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) : Prop :=
  G.edgeFinset.card = m

def TriangleBoundedErrorOn (A : TriangleAlgorithm V W) (m : ℕ) : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj], HasEdgeCount G m → HasTriangle G →
    (2 / 3 : ℝ) ≤ MeasureProb (triRun A G) (triSuccessSet A G)

def TriangleExactOn (A : TriangleAlgorithm V W) (m : ℕ) : Prop :=
  (∀ (G : SimpleGraph V) [DecidableRel G.Adj], HasEdgeCount G m → HasTriangle G →
      MeasureProb (triRun A G) (triSuccessSet A G) = 1) ∧
  (∀ (G : SimpleGraph V) [DecidableRel G.Adj], HasEdgeCount G m → ¬ HasTriangle G →
      MeasureProb (triRun A G) (triNoneSet A) = 1)

def TriangleQ2LowerBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ), 0 < n → n ≤ m →
    ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : TriangleAlgorithm V W),
      (Fintype.card V = n) → TriangleBoundedErrorOn A m →
      c * g n m ≤ (QueryCount A.circuit : ℝ)

def TriangleQ2UpperBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (m : ℕ),
    0 < Fintype.card V →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : TriangleAlgorithm V W),
      TriangleBoundedErrorOn A m ∧
        (QueryCount A.circuit : ℝ) ≤ c * g (Fintype.card V) m

def TriangleQeLowerBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ), 0 < n → n ≤ m →
    ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : TriangleAlgorithm V W),
      (Fintype.card V = n) → TriangleExactOn A m →
      c * g n m ≤ (QueryCount A.circuit : ℝ)

def TriangleQeUpperBound (g : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (m : ℕ),
    0 < Fintype.card V →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : TriangleAlgorithm V W),
      TriangleExactOn A m ∧
        (QueryCount A.circuit : ℝ) ≤ c * g (Fintype.card V) m

abbrev EvalWorkspace (N : ℕ) (W : Type*) := (Fin N × Bool) × (Fin N × W)

def evalShift {N : ℕ} {W : Type*} (hN : 0 < N) (f : Fin N → Fin N)
    (q : EvalWorkspace N W) : EvalWorkspace N W :=
  ((q.1.1, q.1.2),
   (⟨(q.2.1.val + (f q.1.1).val) % N, Nat.mod_lt _ hN⟩, q.2.2))

noncomputable def evalOracleMatrix {N : ℕ} {W : Type*} [DecidableEq W]
    (hN : 0 < N) (f : Fin N → Fin N) :
    Matrix (EvalWorkspace N W) (EvalWorkspace N W) ℂ :=
  fun a b => if a = evalShift hN f b then (1 : ℂ) else 0

structure EvalAlgorithm (N : ℕ) (W : Type*) (Ans : Type*) [Fintype W] [DecidableEq W] where
  circuit : Circuit (EvalWorkspace N W)
  init : QState (EvalWorkspace N W)
  decoder : W → Option Ans
  unitary : IsUnitaryCircuit circuit
  norm : Normalized init

variable {N : ℕ} {W Ans : Type*} [Fintype W] [DecidableEq W]

def evalRun (hN : 0 < N) (A : EvalAlgorithm N W Ans) (f : Fin N → Fin N) :
    QState (EvalWorkspace N W) :=
  Run (evalOracleMatrix hN f) A.circuit A.init

noncomputable def evalSuccessProb (hN : 0 < N) (A : EvalAlgorithm N W Ans)
    (f : Fin N → Fin N) (P : Ans → Prop) : ℝ :=
  MeasureProb (evalRun hN A f)
    (Finset.univ.filter fun q => ∃ a, A.decoder q.2.2 = some a ∧ P a)

def evalComputes (hN : 0 < N) (A : EvalAlgorithm N W Ans)
    (P : (Fin N → Fin N) → Ans → Prop) : Prop :=
  ∀ f : Fin N → Fin N, (2 / 3 : ℝ) ≤ evalSuccessProb hN A f (P f)

def collisionCount {N : ℕ} (f : Fin N → Fin N) : ℕ :=
  (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2 ∧ f p.1 = f p.2).card

def ParityCollisionProblem {N : ℕ} (f : Fin N → Fin N) (a : Fin 2) : Prop :=
  (a : ℕ) = collisionCount f % 2

def NoCollisionProblem {N : ℕ} (f : Fin N → Fin N) (x : Fin N) : Prop :=
  ∀ y : Fin N, f y = f x → y = x

def NoRangeProblem {N : ℕ} (f : Fin N → Fin N) (z : Fin N) : Prop :=
  ∀ x : Fin N, f x ≠ z

def ParityCollisionLowerBound (bound : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (hN : 0 < N), 4 ∣ N →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : EvalAlgorithm N W (Fin 2)),
      evalComputes hN A (fun f a => ParityCollisionProblem f a) →
      c * bound N ≤ (QueryCount A.circuit : ℝ)

def NoCollisionLowerBound (bound : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (hN : 0 < N), Odd N →
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : EvalAlgorithm N W (Fin N)),
      evalComputes hN A (fun f x => NoCollisionProblem f x) →
      c * bound N ≤ (QueryCount A.circuit : ℝ)

def NoRangeLowerBound (bound : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (hN : 0 < N),
    ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : EvalAlgorithm N W (Fin N)),
      evalComputes hN A (fun f z => NoRangeProblem f z) →
      c * bound N ≤ (QueryCount A.circuit : ℝ)

end Qatlib.Papers.ElemDistinct00.MainResults.Defs
