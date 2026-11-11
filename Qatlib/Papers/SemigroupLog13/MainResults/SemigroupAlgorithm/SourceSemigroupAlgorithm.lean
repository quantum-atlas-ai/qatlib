/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemigroupLog13.MainResults.SemigroupCore.SourceSemigroupCore
import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBounds
import Qatlib.Foundations.PureStateMath.BornBridge.BornDistribution
import Mathlib.Data.Nat.Log
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.Finset.Dedup

set_option backward.isDefEq.respectTransparency false

/-!
# Black-box access and cost vocabulary for SemigroupLog13

Fixed paper: Childs--Ivanyos, *Quantum computation of discrete logarithms in
semigroups*, arXiv:1310.6238v2 (1 Nov 2013).

The paper works in the black-box semigroup model: elements have a unique
encoding and the semigroup operation is an efficiently available reversible
oracle.  This file fixes that model once, so that every algorithmic claim of the
paper can be stated as an ordinary existence/upper-bound/lower-bound statement.

* `MulOracleAccess S mul clean` is the reversible multiplication oracle on the
  fixed computational basis `Option (S × S × S × S)`: the clean-ancilla state
  `some (x, y, clean)` is sent to `some (x, y, mul x y)` (the oracle is a unitary
  on the whole basis).  The multiplication function is an explicit parameter, so
  the same program type can be used against different multiplication tables
  (needed for the hard-instance family behind Theorem 2).
* `inputLaw` is the real output PMF of one fixed circuit (`QueryAlgorithm`)
  started from an externally supplied encoded input state.  The classical input
  of the algorithm is the index of the encoded state, exactly as in the paper:
  the circuit is fixed, while the input state and the oracle vary.
* `pmfEventProb` is the Born mass of a readout event; it is a `tsum`, so
  infinite output types such as `ℕ × ℕ` and `Fin k → ℕ` are allowed.
* `UniformSuccess` requires one fixed program, one fixed input encoding, and
  success probability at least `2/3` for *every* admissible multiplication
  oracle and *every* input.  This is non-vacuous: the circuit and readout are
  fixed before the oracle and the input, so a constant readout cannot pass.
* `InstanceUniformSuccess` / `InstanceQueryLowerBound` lift the same semantics to
  a family of instances with instance-dependent multiplication, clean ancilla
  and input encoding; this is the form used by the hard-instance lower bound of
  Theorem 2.
* `PolyLogBudget`, `PolyLogQueries`, `SubExpTimeBudget`, `Theorem3TimeBudget`,
  `Theorem3QueryBudget` spell out the paper's resource bounds.

The model records the paper's mathematical object (a reversible multiplication
oracle on a unique encoding) and the algorithm's fixed circuit/readout/input
interface.  It does not synthesize the oracle from elementary gates, does not
model elementary-gate costs, and does not claim uniformity over semigroup sizes.
Those are outside the paper's stated results and are not used below.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBounds
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped ENNReal

namespace Qatlib.Papers.SemigroupLog13.MainResults

/-! ## §1. The reversible multiplication oracle -/

/-- A reversible black-box oracle for an explicit multiplication `mul` of `S` on
the fixed basis `Option (S × S × S × S)`.  The clean-ancilla state
`some (x, y, clean)` is mapped to `some (x, y, mul x y)`; the oracle is a unitary
on the whole basis. -/
structure MulOracleAccess (S : Type) [Fintype S] [DecidableEq S]
    (mul : S → S → S) (clean : S) where
  /-- The reversible multiplication oracle. -/
  oracle : Matrix (Option (S × S × S × S)) (Option (S × S × S × S)) ℂ
  /-- The oracle is unitary on the full computational basis. -/
  unitary : oracle ∈ Matrix.unitaryGroup (Option (S × S × S × S)) ℂ
  /-- Query semantics: `some (x, y, z, clean)` is sent to `some (x, y, mul x y, z)`:
  the product of the first two registers is written to the third, and the
  clean-ancilla register is preserved. -/
  action : ∀ x y z : S,
    oracle *ᵥ Ket (some (x, y, z, clean)) = Ket (some (x, y, mul x y, z))

/-- The oracle-access family induced by the admissible multiplication oracles. -/
def mulAccess (S : Type) [Fintype S] [DecidableEq S]
    (mul : S → S → S) (clean : S) :
    OracleAccess (MulOracleAccess S mul clean) (Option (S × S × S × S)) where
  oracle M := M.oracle
  unitary M := M.unitary

/-- The real output PMF of one fixed circuit started from an externally supplied
encoded input state, with the real multiplication oracle. -/
def inputLaw {S Out : Type} [Fintype S] [DecidableEq S]
    (mul : S → S → S) (clean : S) (P : MeasuredProgram (Option (S × S × S × S)) Out)
    (M : MulOracleAccess S mul clean) (input : QState (Option (S × S × S × S)))
    (hinput : Normalized input) : PMF Out :=
  (bornDistribution (Run M.oracle P.algorithm.circuit input)
    (P.algorithm.unitary.normalized_run M.unitary hinput)).map P.readout

/-- The Born probability of a readout event.  `tsum` allows infinite output
types (`Option ℕ`, `ℕ × ℕ`, `Fin k → ℕ`). -/
def pmfEventProb {Y : Type} (p : PMF Y) (E : Y → Prop) : ENNReal := by
  classical
  exact ∑' y, if E y then p y else 0

/-- One fixed program, one fixed input encoding, success probability at least
`2/3` for every admissible multiplication oracle and every input. -/
def UniformSuccess {S X Out : Type} [Fintype S] [DecidableEq S]
    (mul : S → S → S) (clean : S)
    (P : MeasuredProgram (Option (S × S × S × S)) Out) (B : Budget)
    (encode : X → QState (Option (S × S × S × S)))
    (henc : ∀ x : X, Normalized (encode x)) (ok : X → Out → Prop) : Prop :=
  Within P B ∧ ∀ (M : MulOracleAccess S mul clean) (x : X),
    (2 / 3 : ENNReal) ≤ pmfEventProb (inputLaw mul clean P M (encode x) (henc x)) (ok x)

/-- Instance family version of `UniformSuccess`: one fixed program must succeed
for all instances, all oracles of each instance, and all inputs. -/
def InstanceUniformSuccess {S Inst Out : Type} [Fintype S] [DecidableEq S]
    (mulOf : Inst → S → S → S) (cleanOf : Inst → S)
    (encodeOf : Inst → Unit → QState (Option (S × S × S × S)))
    (hencOf : ∀ (i : Inst) (u : Unit), Normalized (encodeOf i u))
    (P : MeasuredProgram (Option (S × S × S × S)) Out) (B : Budget)
    (okOf : Inst → Out → Prop) : Prop :=
  Within P B ∧ ∀ (i : Inst) (M : MulOracleAccess S (mulOf i) (cleanOf i)) (u : Unit),
    (2 / 3 : ENNReal) ≤
      pmfEventProb (inputLaw (mulOf i) (cleanOf i) P M (encodeOf i u) (hencOf i u)) (okOf i)

/-- Universal query lower bound over an instance family: every fixed measured
program that succeeds on the whole family needs at least `work i` queries on
some instance `i`. -/
def InstanceQueryLowerBound {S Inst Out : Type} [Fintype S] [DecidableEq S]
    (mulOf : Inst → S → S → S) (cleanOf : Inst → S)
    (encodeOf : Inst → Unit → QState (Option (S × S × S × S)))
    (hencOf : ∀ (i : Inst) (u : Unit), Normalized (encodeOf i u))
    (okOf : Inst → Out → Prop) (work : Inst → ℝ) : Prop :=
  ∀ (P : MeasuredProgram (Option (S × S × S × S)) Out) (B : Budget),
    InstanceUniformSuccess mulOf cleanOf encodeOf hencOf P B okOf →
      ∃ i : Inst, work i ≤ (B.queries : ℝ)

/-! ## §2. Cost predicates -/

/-- The paper's `poly(log N)` time and query bound (Section 2, page 2). -/
def PolyLogBudget (B : Budget) (N : ℕ) : Prop :=
  ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    B.queries ≤ c * (Nat.log 2 N + 1) ^ d ∧
    B.macroGates ≤ c * (Nat.log 2 N + 1) ^ d ∧
    B.depth ≤ c * (Nat.log 2 N + 1) ^ d

/-- Only the query ledger is polylogarithmic (paper's "poly(log |S|) quantum
queries"). -/
def PolyLogQueries (B : Budget) (N : ℕ) : Prop :=
  ∃ c d : ℕ, 0 < c ∧ 0 < d ∧ B.queries ≤ c * (Nat.log 2 N + 1) ^ d

/-- `2^{O(√(log N))}` time: bounded by `N^ε` for every `ε > 0` (Lemma 2). -/
def SubExpTimeBudget (B : Budget) (N : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → (B.macroGates : ℝ) ≤ (N : ℝ) ^ ε

/-- Theorem 3's time bound `|S|^{1/2 - 1/(2k) + o(1)}`: for every `ε > 0`,
`time ≤ |S|^{1/2 - 1/(2k) + ε}`. -/
def Theorem3TimeBudget (k N : ℕ) (B : Budget) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (B.macroGates : ℝ) ≤ (N : ℝ) ^ ((1 / 2 : ℝ) - 1 / (2 * (k : ℝ)) + ε)

/-- Theorem 3's query bound `|S|^{1/2 - 1/(2k)} poly(log |S|)`. -/
def Theorem3QueryBudget (k N : ℕ) (B : Budget) : Prop :=
  ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    (B.queries : ℝ) ≤
      (N : ℝ) ^ ((1 / 2 : ℝ) - 1 / (2 * (k : ℝ))) *
        ((c * (Nat.log 2 N + 1) ^ d : ℕ) : ℝ)

end Qatlib.Papers.SemigroupLog13.MainResults
