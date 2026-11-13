/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.LocalCapability
import Qatlib.Foundations.QueryWordCore.HamiltonianQuery

/-!
# Compositional circuit resource accounting

`ResourceCost` records query counts, macro and basic gate counts, depth, peak space, Hamiltonian
evolution time, and classical bits. `derive` combines gate profiles along sequential circuits,
adding cumulative costs and taking the maximum of space costs. These quantities refine the
circuit resources discussed in [NielsenChuang2010].

`derivePar` accounts for synchronized tensor-product layers, while `compileCircuit` replaces
macro gates by certified query-free implementations. The module proves semantic preservation and
exact resource identities for sequencing, repetition, parallel execution, compilation, and
Hamiltonian query programs.

## Main statements

* `derive_append`: resource accounting respects sequential composition.
* `derive_repeatCircuit`: repetition corresponds to repeated resource composition.
* `run_parToCircuit`: parallel execution factors on tensor-product states.
* `GateCompiler.certified_semantics_cost`: compiled circuits preserve semantics, queries, and
  certified gate costs.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.QueryWordCore.HamiltonianQuery

namespace Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

open Matrix
open scoped ENNReal

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Resource counts for queries, macro gates, basic gates, depth, peak space, Hamiltonian time,
and classical bits. Sequential composition adds every component except peak space, which
uses the maximum. -/
@[ext]
structure ResourceCost where

  queries : ℕ

  macroGates : ℕ

  basicGates : ℕ

  depth : ℕ

  peakSpace : ℕ

  hamiltonianTime : ℝ≥0∞

  classicalBits : ℕ

instance : Zero ResourceCost := ⟨⟨0, 0, 0, 0, 0, 0, 0⟩⟩

instance : Add ResourceCost :=
  ⟨fun a b => ⟨a.queries + b.queries, a.macroGates + b.macroGates,
    a.basicGates + b.basicGates, a.depth + b.depth, max a.peakSpace b.peakSpace,
    a.hamiltonianTime + b.hamiltonianTime, a.classicalBits + b.classicalBits⟩⟩

/-- The zero resource cost has zero query count. -/
@[simp] theorem ResourceCost.zero_queries : (0 : ResourceCost).queries = 0 := rfl

/-- The zero resource cost has zero macro-gate count. -/
@[simp] theorem ResourceCost.zero_macroGates : (0 : ResourceCost).macroGates = 0 := rfl

/-- The zero resource cost has zero basic gate count. -/
@[simp] theorem ResourceCost.zero_basicGates : (0 : ResourceCost).basicGates = 0 := rfl

/-- The zero resource cost has zero depth. -/
@[simp] theorem ResourceCost.zero_depth : (0 : ResourceCost).depth = 0 := rfl

/-- The zero resource cost has zero peak space. -/
@[simp] theorem ResourceCost.zero_peakSpace : (0 : ResourceCost).peakSpace = 0 := rfl

/-- The zero resource cost has zero Hamiltonian time. -/
@[simp] theorem ResourceCost.zero_hamiltonianTime :
    (0 : ResourceCost).hamiltonianTime = 0 := rfl

/-- The zero resource cost has zero classical bit cost. -/
@[simp] theorem ResourceCost.zero_classicalBits :
    (0 : ResourceCost).classicalBits = 0 := rfl

/-- Sequential resource composition adds the two query count components. -/
@[simp] theorem ResourceCost.add_queries (a b : ResourceCost) :
    (a + b).queries = a.queries + b.queries := rfl

/-- Sequential resource composition adds the two macro-gate count components. -/
@[simp] theorem ResourceCost.add_macroGates (a b : ResourceCost) :
    (a + b).macroGates = a.macroGates + b.macroGates := rfl

/-- Sequential resource composition adds the two basic gate count components. -/
@[simp] theorem ResourceCost.add_basicGates (a b : ResourceCost) :
    (a + b).basicGates = a.basicGates + b.basicGates := rfl

/-- Sequential resource composition adds the two depth components. -/
@[simp] theorem ResourceCost.add_depth (a b : ResourceCost) :
    (a + b).depth = a.depth + b.depth := rfl

/-- Sequential resource composition takes the maximum of the two peak spaces. -/
@[simp] theorem ResourceCost.add_peakSpace (a b : ResourceCost) :
    (a + b).peakSpace = max a.peakSpace b.peakSpace := rfl

/-- Sequential resource composition adds the two Hamiltonian time components. -/
@[simp] theorem ResourceCost.add_hamiltonianTime (a b : ResourceCost) :
    (a + b).hamiltonianTime = a.hamiltonianTime + b.hamiltonianTime := rfl

/-- Sequential resource composition adds the two classical bit cost components. -/
@[simp] theorem ResourceCost.add_classicalBits (a b : ResourceCost) :
    (a + b).classicalBits = a.classicalBits + b.classicalBits := rfl

/-- Zero resource cost is a left identity for sequential resource composition. -/
@[simp] theorem ResourceCost.zero_add (a : ResourceCost) : 0 + a = a := by
  ext <;> simp

/-- Zero resource cost is a right identity for sequential resource composition. -/
@[simp] theorem ResourceCost.add_zero (a : ResourceCost) : a + 0 = a := by
  ext <;> simp

/-- Sequential composition of resource costs is associative. -/
theorem ResourceCost.add_assoc (a b c : ResourceCost) : a + b + c = a + (b + c) := by
  ext
  all_goals simp only [ResourceCost.add_queries, ResourceCost.add_macroGates,
    ResourceCost.add_basicGates, ResourceCost.add_depth, ResourceCost.add_peakSpace,
    ResourceCost.add_hamiltonianTime, ResourceCost.add_classicalBits]
  all_goals first
  | omega
  | ring

/-- Resource-cost composition is commutative. -/
theorem ResourceCost.add_comm (a b : ResourceCost) : a + b = b + a := by
  ext
  all_goals simp only [ResourceCost.add_queries, ResourceCost.add_macroGates,
    ResourceCost.add_basicGates, ResourceCost.add_depth, ResourceCost.add_peakSpace,
    ResourceCost.add_hamiltonianTime, ResourceCost.add_classicalBits]
  all_goals first
  | omega
  | ring

/-- The basic gate count, workspace size, evolution time, and classical bit cost assigned to one
macro gate. -/
structure StepProfile where

  basicGates : ℕ

  space : ℕ

  evolve : ℝ≥0∞

  classicalBits : ℕ

/-- The step profile with zero basic gates, workspace, evolution time, and classical bits. -/
def StepProfile.zero : StepProfile := ⟨0, 0, 0, 0⟩

/-- The zero step profile has zero basic gate count. -/
@[simp] theorem StepProfile.zero_basicGates : StepProfile.zero.basicGates = 0 := rfl

/-- The zero step profile has zero workspace size. -/
@[simp] theorem StepProfile.zero_space : StepProfile.zero.space = 0 := rfl

/-- The zero step profile has zero evolution time. -/
@[simp] theorem StepProfile.zero_evolve : StepProfile.zero.evolve = 0 := rfl

/-- The zero step profile has zero classical bit cost. -/
@[simp] theorem StepProfile.zero_classicalBits :
    StepProfile.zero.classicalBits = 0 := rfl

/-- The cost of one macro gate with the given profile, charging one unit of depth and no oracle
queries. -/
def ResourceCost.ofMacroStep (p : StepProfile) : ResourceCost :=
  ⟨0, 1, p.basicGates, 1, p.space, p.evolve, p.classicalBits⟩

/-- The cost of one oracle query, charging one unit of depth and zero in all other components. -/
def ResourceCost.ofOracleStep : ResourceCost := ⟨1, 0, 0, 1, 0, 0, 0⟩

/-- The query count of a macro step with profile `p` is zero. -/
@[simp] theorem ResourceCost.ofMacroStep_queries (p : StepProfile) :
    (ResourceCost.ofMacroStep p).queries = 0 := rfl

/-- The macro-gate count of a macro step with profile `p` is one. -/
@[simp] theorem ResourceCost.ofMacroStep_macroGates (p : StepProfile) :
    (ResourceCost.ofMacroStep p).macroGates = 1 := rfl

/-- The basic gate count of a macro step with profile `p` is `p.basicGates`. -/
@[simp] theorem ResourceCost.ofMacroStep_basicGates (p : StepProfile) :
    (ResourceCost.ofMacroStep p).basicGates = p.basicGates := rfl

/-- The depth of a macro step with profile `p` is one. -/
@[simp] theorem ResourceCost.ofMacroStep_depth (p : StepProfile) :
    (ResourceCost.ofMacroStep p).depth = 1 := rfl

/-- The peak space of a macro step with profile `p` is `p.space`. -/
@[simp] theorem ResourceCost.ofMacroStep_peakSpace (p : StepProfile) :
    (ResourceCost.ofMacroStep p).peakSpace = p.space := rfl

/-- The Hamiltonian time of a macro step with profile `p` is `p.evolve`. -/
@[simp] theorem ResourceCost.ofMacroStep_hamiltonianTime (p : StepProfile) :
    (ResourceCost.ofMacroStep p).hamiltonianTime = p.evolve := rfl

/-- The classical bit cost of a macro step with profile `p` is `p.classicalBits`. -/
@[simp] theorem ResourceCost.ofMacroStep_classicalBits (p : StepProfile) :
    (ResourceCost.ofMacroStep p).classicalBits = p.classicalBits := rfl

/-- The unit oracle step has query count equal to one. -/
@[simp] theorem ResourceCost.ofOracleStep_queries :
    ResourceCost.ofOracleStep.queries = 1 := rfl

/-- The unit oracle step has macro-gate count equal to zero. -/
@[simp] theorem ResourceCost.ofOracleStep_macroGates :
    ResourceCost.ofOracleStep.macroGates = 0 := rfl

/-- The unit oracle step has basic gate count equal to zero. -/
@[simp] theorem ResourceCost.ofOracleStep_basicGates :
    ResourceCost.ofOracleStep.basicGates = 0 := rfl

/-- The unit oracle step has depth equal to one. -/
@[simp] theorem ResourceCost.ofOracleStep_depth :
    ResourceCost.ofOracleStep.depth = 1 := rfl

/-- The unit oracle step has peak space equal to zero. -/
@[simp] theorem ResourceCost.ofOracleStep_peakSpace :
    ResourceCost.ofOracleStep.peakSpace = 0 := rfl

/-- The unit oracle step has Hamiltonian time equal to zero. -/
@[simp] theorem ResourceCost.ofOracleStep_hamiltonianTime :
    ResourceCost.ofOracleStep.hamiltonianTime = 0 := rfl

/-- The unit oracle step has classical bit cost equal to zero. -/
@[simp] theorem ResourceCost.ofOracleStep_classicalBits :
    ResourceCost.ofOracleStep.classicalBits = 0 := rfl

/-- Derives the resource cost of a circuit by sequentially composing the supplied macro-gate
profiles and unit oracle-query costs. -/
def derive (κ : Matrix I I ℂ → StepProfile) : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I → ResourceCost
  | [] => 0
  | Step.gate U :: C => ResourceCost.ofMacroStep (κ U) + derive κ C
  | Step.query :: C => ResourceCost.ofOracleStep + derive κ C

omit [Fintype I] [DecidableEq I] in

/-- The empty circuit has zero derived resource cost. -/
@[simp] theorem derive_nil (κ : Matrix I I ℂ → StepProfile) : derive κ [] = 0 := rfl

omit [Fintype I] [DecidableEq I] in

/-- Prepending a gate adds its profiled macro-step cost to the cost of the remaining circuit. -/
@[simp] theorem derive_gate (κ : Matrix I I ℂ → StepProfile) (U : Matrix I I ℂ)
    (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    derive κ (Step.gate U :: C) = ResourceCost.ofMacroStep (κ U) + derive κ C := rfl

omit [Fintype I] [DecidableEq I] in

/-- Prepending a query adds the unit oracle-step cost to the cost of the remaining circuit. -/
@[simp] theorem derive_query (κ : Matrix I I ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    derive κ (Step.query :: C) = ResourceCost.ofOracleStep + derive κ C := rfl

omit [Fintype I] [DecidableEq I] in

/-- The query component of the derived cost equals the circuit query count. -/
theorem derive_queries (κ : Matrix I I ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive κ C).queries = Qatlib.Foundations.QueryWordCore.Circuit.QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => simp [derive, ih]
    | query => simp [derive, ih, Nat.add_comm]

omit [Fintype I] [DecidableEq I] in

/-- The macro-gate component of the derived cost equals the circuit gate count. -/
theorem derive_macroGates (κ : Matrix I I ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive κ C).macroGates = Qatlib.Foundations.QueryWordCore.Circuit.GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => simp [derive, ih, Nat.add_comm]
    | query => simp [derive, ih]

omit [Fintype I] [DecidableEq I] in

/-- The derived sequential depth equals the number of circuit steps. -/
theorem derive_depth (κ : Matrix I I ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive κ C).depth = Qatlib.Foundations.QueryWordCore.Circuit.Size C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => simp [derive, ih, Nat.add_comm]
    | query => simp [derive, ih, Nat.add_comm]

omit [Fintype I] [DecidableEq I] in

/-- Assigning the zero profile to every gate gives zero derived classical bit cost. -/
theorem derive_zeroProfile (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive (fun _ => StepProfile.zero) C).classicalBits = 0 := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [derive, ih]

omit [Fintype I] [DecidableEq I] in

/-- The derived cost of concatenated circuits is the composition of their derived costs. -/
theorem derive_append (κ : Matrix I I ℂ → StepProfile) (C D : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    derive κ (C ++ D) = derive κ C + derive κ D := by
  induction C generalizing D with
  | nil => simp
  | cons s C ih =>
    cases s <;> simp only [List.cons_append, derive_gate, derive_query, ih,
      ResourceCost.add_assoc]

/-- Concatenation runs the first circuit before the second and composes their resource costs. -/
theorem seq_semantics_cost (κ : Matrix I I ℂ → StepProfile) (W : Matrix I I ℂ)
    (C D : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) (ψ : Qatlib.Foundations.PureStateMath.QState I) :
    Run W (C ++ D) ψ = Run W D (Run W C ψ) ∧
      derive κ (C ++ D) = derive κ C + derive κ D :=
  ⟨run_append W C D ψ, derive_append κ C D⟩

/-- The peak space of a sequential composition is the maximum of the two component peak spaces. -/
theorem seq_peakSpace (κ : Matrix I I ℂ → StepProfile) (C D : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive κ (C ++ D)).peakSpace
      = max (derive κ C).peakSpace (derive κ D).peakSpace := by
  rw [derive_append]; rfl

/-- The Hamiltonian time of a sequential composition is the sum of the two component times. -/
theorem seq_hamiltonianTime (κ : Matrix I I ℂ → StepProfile) (C D : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive κ (C ++ D)).hamiltonianTime
      = (derive κ C).hamiltonianTime + (derive κ D).hamiltonianTime := by
  rw [derive_append]; rfl

/-- There exist gate profiles and sequential circuits whose peak space is strictly less than the
sum of the component peak spaces. -/
theorem peakSpace_seq_add_overestimates :
    ∃ (κ : Matrix Bool Bool ℂ → StepProfile) (C D : Qatlib.Foundations.QueryWordCore.Circuit.Circuit Bool),
      (derive κ (C ++ D)).peakSpace < (derive κ C).peakSpace + (derive κ D).peakSpace := by
  refine ⟨fun _ => ⟨0, 3, 0, 0⟩, [Step.gate 1], [Step.gate 1], ?_⟩
  simp only [List.cons_append, List.nil_append, derive_gate, derive_nil,
    ResourceCost.add_zero, ResourceCost.add_peakSpace,
    ResourceCost.ofMacroStep_peakSpace]
  decide

/-- There exists a profiled circuit with zero queries and strictly positive Hamiltonian time. -/
theorem cost_queries_zero_hamiltonianTime_pos :
    ∃ (κ : Matrix Bool Bool ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit Bool),
      (derive κ C).queries = 0 ∧ 0 < (derive κ C).hamiltonianTime := by
  refine ⟨fun _ => ⟨0, 0, 3, 0⟩, [Step.gate 1], rfl, ?_⟩
  norm_num [derive, ResourceCost.ofMacroStep_hamiltonianTime]

/-- There exists a profiled circuit with exactly one query and zero Hamiltonian time. -/
theorem cost_queries_pos_hamiltonianTime_zero :
    ∃ (κ : Matrix Bool Bool ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit Bool),
      (derive κ C).queries = 1 ∧ (derive κ C).hamiltonianTime = 0 := by
  refine ⟨fun _ => StepProfile.zero, [Step.query], ?_, ?_⟩ <;> simp [derive]

/-- Composes a resource cost with itself a specified number of times, using zero cost for zero
repetitions. -/
def repeatCost (r : ResourceCost) : ℕ → ResourceCost
  | 0 => 0
  | k + 1 => repeatCost r k + r

/-- Zero repetitions of a resource cost give zero cost. -/
@[simp] theorem repeatCost_zero (r : ResourceCost) : repeatCost r 0 = 0 := rfl

/-- One further repetition composes the previous repeated cost with one copy of the original
cost. -/
@[simp] theorem repeatCost_succ (k : ℕ) (r : ResourceCost) :
    repeatCost r (k + 1) = repeatCost r k + r := rfl

/-- Repeating a resource cost `k` times multiplies its query count by `k`. -/
theorem repeatCost_queries (k : ℕ) (r : ResourceCost) :
    (repeatCost r k).queries = k * r.queries := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, Nat.succ_mul]

/-- Repeating a resource cost `k` times multiplies its macro-gate count by `k`. -/
theorem repeatCost_macroGates (k : ℕ) (r : ResourceCost) :
    (repeatCost r k).macroGates = k * r.macroGates := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, Nat.succ_mul]

/-- Repeating a resource cost `k` times multiplies its basic gate count by `k`. -/
theorem repeatCost_basicGates (k : ℕ) (r : ResourceCost) :
    (repeatCost r k).basicGates = k * r.basicGates := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, Nat.succ_mul]

/-- Repeating a resource cost `k` times multiplies its depth by `k`. -/
theorem repeatCost_depth (k : ℕ) (r : ResourceCost) :
    (repeatCost r k).depth = k * r.depth := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, Nat.succ_mul]

/-- Repeating a resource cost `k` times multiplies its classical bit cost by `k`. -/
theorem repeatCost_classicalBits (k : ℕ) (r : ResourceCost) :
    (repeatCost r k).classicalBits = k * r.classicalBits := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, Nat.succ_mul]

/-- Repeating a resource cost `k` times multiplies its Hamiltonian time by `k`. -/
theorem repeatCost_hamiltonianTime (k : ℕ) (r : ResourceCost) :
    (repeatCost r k).hamiltonianTime = (k : ℝ≥0∞) * r.hamiltonianTime := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [repeatCost_succ, ResourceCost.add_hamiltonianTime, ih, Nat.cast_succ]
    ring

/-- The peak space of any repeated cost is bounded by the original peak space. -/
theorem repeatCost_peakSpace_le (k : ℕ) (r : ResourceCost) :
    (repeatCost r k).peakSpace ≤ r.peakSpace := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [repeatCost_succ, ResourceCost.add_peakSpace]
    exact max_le ih (le_refl _)

/-- A positive number of repetitions preserves the original peak space. -/
theorem repeatCost_succ_peakSpace (k : ℕ) (r : ResourceCost) :
    (repeatCost r (k + 1)).peakSpace = r.peakSpace := by
  rw [repeatCost_succ, ResourceCost.add_peakSpace]
  exact Nat.max_eq_right (repeatCost_peakSpace_le k r)

/-- Running a repeated circuit equals iterating its state transformation the same number of
times. -/
theorem run_repeatCircuit (W : Matrix I I ℂ) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) (k : ℕ) (ψ : Qatlib.Foundations.PureStateMath.QState I) :
    Run W (Qatlib.Foundations.QueryWordCore.Circuit.RepeatCircuit C k) ψ = (fun x => Run W C x)^[k] ψ := by
  induction k generalizing ψ with
  | zero => rfl
  | succ k ih => rw [Qatlib.Foundations.QueryWordCore.Circuit.RepeatCircuit, run_append, Function.iterate_succ]; exact ih _

/-- The derived cost of a repeated circuit is the corresponding repetition of its derived cost. -/
theorem derive_repeatCircuit (κ : Matrix I I ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) (k : ℕ) :
    derive κ (Qatlib.Foundations.QueryWordCore.Circuit.RepeatCircuit C k) = repeatCost (derive κ C) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Qatlib.Foundations.QueryWordCore.Circuit.RepeatCircuit, derive_append, ih,
        ResourceCost.add_comm, repeatCost_succ]

/-- Repeating a circuit `k` times multiplies its query count by `k`. -/
theorem derive_repeatCircuit_queries (κ : Matrix I I ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I)
    (k : ℕ) : (derive κ (Qatlib.Foundations.QueryWordCore.Circuit.RepeatCircuit C k)).queries = k * Qatlib.Foundations.QueryWordCore.Circuit.QueryCount C := by
  rw [derive_repeatCircuit, repeatCost_queries, derive_queries]

/-- Repeating a circuit a nonzero number of times preserves its derived peak space. -/
theorem derive_repeatCircuit_peakSpace (κ : Matrix I I ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I)
    {k : ℕ} (hk : k ≠ 0) :
    (derive κ (Qatlib.Foundations.QueryWordCore.Circuit.RepeatCircuit C k)).peakSpace = (derive κ C).peakSpace := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [derive_repeatCircuit, repeatCost_succ_peakSpace]

/-- A synchronized two-register step consisting of a pair of data gates or one shared query
step. -/
inductive ParStep (I J : Type*) where

  | gates : Matrix I I ℂ → Matrix J J ℂ → ParStep I J

  | query : ParStep I J

/-- A list of synchronized two-register steps. -/
abbrev ParCircuit (I J : Type*) := List (ParStep I J)

/-- Converts synchronized steps to a product-register circuit by tensoring paired gates and
retaining query steps. -/
noncomputable def parToCircuit : ParCircuit I J → Qatlib.Foundations.QueryWordCore.Circuit.Circuit (I × J)
  | [] => []
  | ParStep.gates U V :: L => Step.gate (Qatlib.Foundations.PureStateMath.TensorGate U V) :: parToCircuit L
  | ParStep.query :: L => Step.query :: parToCircuit L

/-- Projects a synchronized circuit to its left-register gates and query steps. -/
def parLeft : ParCircuit I J → Qatlib.Foundations.QueryWordCore.Circuit.Circuit I
  | [] => []
  | ParStep.gates U _ :: L => Step.gate U :: parLeft L
  | ParStep.query :: L => Step.query :: parLeft L

/-- Projects a synchronized circuit to its right-register gates and query steps. -/
def parRight : ParCircuit I J → Qatlib.Foundations.QueryWordCore.Circuit.Circuit J
  | [] => []
  | ParStep.gates _ V :: L => Step.gate V :: parRight L
  | ParStep.query :: L => Step.query :: parRight L

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- Converting an empty synchronized circuit gives an empty product-register circuit. -/
@[simp] theorem parToCircuit_nil : parToCircuit ([] : ParCircuit I J) = [] := rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- The left projection of an empty synchronized circuit is empty. -/
@[simp] theorem parLeft_nil : parLeft ([] : ParCircuit I J) = [] := rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- The right projection of an empty synchronized circuit is empty. -/
@[simp] theorem parRight_nil : parRight ([] : ParCircuit I J) = [] := rfl

/-- A tensor-product gate factors as the product of its left and right local gates. -/
theorem parStep_gates_eq_mul_local (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    Qatlib.Foundations.PureStateMath.TensorGate U V = Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ) * Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix I I ℂ) V := by
  rw [Qatlib.Foundations.PureStateMath.tensorGate_mul, Matrix.mul_one, Matrix.one_mul]

/-- The two tensor-extended component gates act on their respective registers and commute. -/
theorem parLayer_local_commute (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.ActsOnLeft (Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ)) ∧
      Qatlib.Concepts.QueryComplexity.DegreeMethod.ActsOnRight (Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix I I ℂ) V) ∧
      Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ) * Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix I I ℂ) V
        = Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix I I ℂ) V * Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ) := by
  exact ⟨⟨U, rfl⟩, ⟨V, rfl⟩,
    Qatlib.Concepts.QueryComplexity.DegreeMethod.commute_actsOnLeft_actsOnRight ⟨U, rfl⟩ ⟨V, rfl⟩⟩

/-- A paired gate possesses left-local and right-local factors whose products in both orders
equal the tensor-product gate. -/
theorem parStep_gates_disjoint_certificate (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    ∃ WL WR : Matrix (I × J) (I × J) ℂ,
      Qatlib.Concepts.QueryComplexity.DegreeMethod.ActsOnLeft WL ∧ Qatlib.Concepts.QueryComplexity.DegreeMethod.ActsOnRight WR ∧
        WL * WR = Qatlib.Foundations.PureStateMath.TensorGate U V ∧ WR * WL = Qatlib.Foundations.PureStateMath.TensorGate U V := by
  refine ⟨Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ), Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix I I ℂ) V,
    ⟨U, rfl⟩, ⟨V, rfl⟩, (Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.parStep_gates_eq_mul_local U V).symm, ?_⟩
  exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.commute_actsOnLeft_actsOnRight ⟨U, rfl⟩ ⟨V, rfl⟩).symm.trans
    (Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.parStep_gates_eq_mul_local U V).symm

/-- With a tensor-product oracle, a synchronized circuit maps a tensor-product input to the
tensor product of the two projected circuit outputs. -/
theorem run_parToCircuit (W : Matrix I I ℂ) (V : Matrix J J ℂ) (L : ParCircuit I J)
    (ψ : Qatlib.Foundations.PureStateMath.QState I) (χ : Qatlib.Foundations.PureStateMath.QState J) :
    Run (Qatlib.Foundations.PureStateMath.TensorGate W V) (parToCircuit L) (Qatlib.Foundations.PureStateMath.TensorState ψ χ)
      = Qatlib.Foundations.PureStateMath.TensorState (Run W (parLeft L) ψ) (Run V (parRight L) χ) := by
  induction L generalizing ψ χ with
  | nil => rfl
  | cons l L ih =>
    cases l with
    | gates U V' =>
      simp only [parToCircuit, parLeft, parRight,
          Qatlib.Foundations.QueryWordCore.Circuit.run_gate, Qatlib.Foundations.PureStateMath.applyGate_tensorGate]
      exact ih _ _
    | query =>
      simp only [parToCircuit, parLeft, parRight,
          Qatlib.Foundations.QueryWordCore.Circuit.run_query, Qatlib.Foundations.PureStateMath.applyGate_tensorGate]
      exact ih _ _

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- The left projection has one step for each synchronized layer. -/
theorem size_parLeft (L : ParCircuit I J) : Qatlib.Foundations.QueryWordCore.Circuit.Size (parLeft L) = L.length := by
  induction L with
  | nil => rfl
  | cons l L ih => cases l <;> simp [parLeft, ih]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- The right projection has one step for each synchronized layer. -/
theorem size_parRight (L : ParCircuit I J) : Qatlib.Foundations.QueryWordCore.Circuit.Size (parRight L) = L.length := by
  induction L with
  | nil => rfl
  | cons l L ih => cases l <;> simp [parRight, ih]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- The product-register circuit has one step for each synchronized layer. -/
theorem size_parToCircuit (L : ParCircuit I J) : Qatlib.Foundations.QueryWordCore.Circuit.Size (parToCircuit L) = L.length := by
  induction L with
  | nil => rfl
  | cons l L ih => cases l <;> simp [parToCircuit, ih]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- The product-register circuit and its left projection have equal query counts. -/
theorem queryCount_parToCircuit_parLeft (L : ParCircuit I J) :
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (parToCircuit L) = Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (parLeft L) := by
  induction L with
  | nil => rfl
  | cons l L ih => cases l <;> simp [parToCircuit, parLeft, ih]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- The product-register circuit and its left projection have equal gate counts. -/
theorem gateCount_parToCircuit_parLeft (L : ParCircuit I J) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (parToCircuit L) = Qatlib.Foundations.QueryWordCore.Circuit.GateCount (parLeft L) := by
  induction L with
  | nil => rfl
  | cons l L ih => cases l <;> simp [parToCircuit, parLeft, ih]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- The left and right projections of a synchronized circuit have equal query counts. -/
theorem queryCount_parLeft_parRight (L : ParCircuit I J) :
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (parLeft L) = Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (parRight L) := by
  induction L with
  | nil => rfl
  | cons l L ih => cases l <;> simp [parLeft, parRight, ih]

/-- Forms a query-free circuit from a list of gate matrices. -/
def Circuit.ofGates (gs : List (Matrix I I ℂ)) :
    Qatlib.Foundations.QueryWordCore.Circuit.Circuit I := gs.map Step.gate

omit [Fintype I] [DecidableEq I] in

/-- The circuit formed from an empty gate list is empty. -/
@[simp] theorem Circuit.ofGates_nil : Circuit.ofGates ([] : List (Matrix I I ℂ)) = [] := rfl

omit [Fintype I] [DecidableEq I] in

/-- Forming a circuit from a nonempty gate list prepends the first gate to the circuit of the
remaining gates. -/
@[simp] theorem Circuit.ofGates_cons (U : Matrix I I ℂ) (gs : List (Matrix I I ℂ)) :
    Circuit.ofGates (U :: gs) = Step.gate U :: Circuit.ofGates gs := rfl

omit [Fintype I] [DecidableEq I] in

/-- The circuit formed from a gate list has size equal to the list length. -/
theorem Circuit.size_ofGates (gs : List (Matrix I I ℂ)) :
    Qatlib.Foundations.QueryWordCore.Circuit.Size (Circuit.ofGates gs) = gs.length := by
  simp [Circuit.ofGates, Qatlib.Foundations.QueryWordCore.Circuit.Size]

/-- A circuit formed solely from a gate list has zero queries. -/
theorem Circuit.queryCount_ofGates (gs : List (Matrix I I ℂ)) :
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Circuit.ofGates gs) = 0 := by
  induction gs with
  | nil => rfl
  | cons U gs ih => rw [Circuit.ofGates_cons, Qatlib.Foundations.QueryWordCore.Circuit.queryCount_gate, ih]

/-- The gate count of a circuit formed from a gate list equals the list length. -/
theorem Circuit.gateCount_ofGates (gs : List (Matrix I I ℂ)) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Circuit.ofGates gs) = gs.length := by
  induction gs with
  | nil => rfl
  | cons U gs ih =>
    rw [Circuit.ofGates_cons, Qatlib.Foundations.QueryWordCore.Circuit.gateCount_gate, ih,
        List.length_cons]

/-- Pairs two gate lists into synchronized layers, padding the shorter list with identity gates. -/
def parOfGates : List (Matrix I I ℂ) → List (Matrix J J ℂ) → ParCircuit I J
  | [], [] => []
  | U :: gs, V :: hs => ParStep.gates U V :: parOfGates gs hs
  | U :: gs, [] => ParStep.gates U (1 : Matrix J J ℂ) :: parOfGates gs []
  | [], V :: hs => ParStep.gates (1 : Matrix I I ℂ) V :: parOfGates [] hs

omit [Fintype I] [Fintype J] in

/-- Pairing two empty gate lists gives an empty synchronized circuit. -/
@[simp] theorem parOfGates_nil_nil :
    parOfGates ([] : List (Matrix I I ℂ)) ([] : List (Matrix J J ℂ)) = [] := by
  simp only [parOfGates]

omit [Fintype I] [Fintype J] in

/-- Pairing two nonempty gate lists places their leading gates in the first layer. -/
@[simp] theorem parOfGates_cons_cons (U : Matrix I I ℂ) (gs : List (Matrix I I ℂ))
    (V : Matrix J J ℂ) (hs : List (Matrix J J ℂ)) :
    parOfGates (U :: gs) (V :: hs) = ParStep.gates U V :: parOfGates gs hs := by
  simp only [parOfGates]

omit [Fintype I] [Fintype J] in

/-- Pairing a nonempty left gate list with an empty right list pads the first right gate with
the identity. -/
@[simp] theorem parOfGates_cons_nil (U : Matrix I I ℂ) (gs : List (Matrix I I ℂ)) :
    parOfGates (U :: gs) ([] : List (Matrix J J ℂ))
      = ParStep.gates U (1 : Matrix J J ℂ) :: parOfGates gs [] := by
  simp only [parOfGates]

omit [Fintype I] [Fintype J] in

/-- Pairing an empty left gate list with a nonempty right list pads the first left gate with the
identity. -/
@[simp] theorem parOfGates_nil_cons (V : Matrix J J ℂ) (hs : List (Matrix J J ℂ)) :
    parOfGates ([] : List (Matrix I I ℂ)) (V :: hs)
      = ParStep.gates (1 : Matrix I I ℂ) V :: parOfGates [] hs := by
  simp only [parOfGates]

/-- The number of paired layers is the maximum of the two gate-list lengths. -/
theorem parOfGates_length (gs : List (Matrix I I ℂ)) (hs : List (Matrix J J ℂ)) :
    (parOfGates gs hs).length = max gs.length hs.length := by
  induction gs generalizing hs with
  | nil =>
    induction hs with
    | nil => simp
    | cons V hs ih =>
      rw [parOfGates_nil_cons, List.length_cons, ih, List.length_cons, List.length_nil]
      omega
  | cons U gs ih =>
    cases hs with
    | nil =>
      rw [parOfGates_cons_nil, List.length_cons, ih, List.length_cons, List.length_nil]
      omega
    | cons V hs =>
      rw [parOfGates_cons_cons]
      simp only [List.length_cons]
      rw [ih]
      omega

/-- The product-register circuit obtained by pairing gate lists contains no queries. -/
theorem queryCount_parOfGates (gs : List (Matrix I I ℂ)) (hs : List (Matrix J J ℂ)) :
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (parToCircuit (parOfGates gs hs)) = 0 := by
  induction gs generalizing hs with
  | nil =>
    induction hs with
    | nil => simp
    | cons V hs ih =>
      simp only [parOfGates_nil_cons, parToCircuit,
          Qatlib.Foundations.QueryWordCore.Circuit.queryCount_gate, ih]
  | cons U gs ih =>
    cases hs with
    | nil => simp only [parOfGates_cons_nil, parToCircuit, Qatlib.Foundations.QueryWordCore.Circuit.queryCount_gate, ih]
    | cons V hs => simp only [parOfGates_cons_cons, parToCircuit, Qatlib.Foundations.QueryWordCore.Circuit.queryCount_gate, ih]

/-- Running paired gate lists on a tensor-product state equals running each gate list on its own
factor. -/
theorem run_parOfGates (W : Matrix I I ℂ) (V : Matrix J J ℂ) :
    ∀ (gs : List (Matrix I I ℂ)) (hs : List (Matrix J J ℂ)) (ψ : Qatlib.Foundations.PureStateMath.QState I) (χ : Qatlib.Foundations.PureStateMath.QState J),
    Run (Qatlib.Foundations.PureStateMath.TensorGate W V) (parToCircuit (parOfGates gs hs)) (Qatlib.Foundations.PureStateMath.TensorState ψ χ)
      = Qatlib.Foundations.PureStateMath.TensorState (Run W (Circuit.ofGates gs) ψ) (Run V (Circuit.ofGates hs) χ) := by
  intro gs
  induction gs with
  | nil =>
    intro hs
    induction hs with
    | nil => intro ψ χ; simp
    | cons V' hs ih =>
      intro ψ χ
      simp only [parOfGates_nil_cons, parToCircuit, Qatlib.Foundations.QueryWordCore.Circuit.run_gate, Circuit.ofGates_cons,
        Circuit.ofGates_nil, Qatlib.Foundations.QueryWordCore.Circuit.run_nil, Qatlib.Foundations.PureStateMath.applyGate_tensorGate, Qatlib.Foundations.PureStateMath.applyGate_one]
      exact ih ψ (Qatlib.Foundations.PureStateMath.ApplyGate V' χ)
  | cons U gs ih =>
    intro hs ψ χ
    cases hs with
    | nil =>
      simp only [parOfGates_cons_nil, parToCircuit, Qatlib.Foundations.QueryWordCore.Circuit.run_gate, Circuit.ofGates_cons,
        Circuit.ofGates_nil, Qatlib.Foundations.QueryWordCore.Circuit.run_nil, Qatlib.Foundations.PureStateMath.applyGate_tensorGate, Qatlib.Foundations.PureStateMath.applyGate_one]
      exact ih [] (Qatlib.Foundations.PureStateMath.ApplyGate U ψ) χ
    | cons V' hs =>
      simp only [parOfGates_cons_cons, parToCircuit, Qatlib.Foundations.QueryWordCore.Circuit.run_gate, Circuit.ofGates_cons,
        Qatlib.Foundations.PureStateMath.applyGate_tensorGate]
      exact ih hs (Qatlib.Foundations.PureStateMath.ApplyGate U ψ)
          (Qatlib.Foundations.PureStateMath.ApplyGate V' χ)

/-- The cost of a paired gate layer, charging one macro gate and one depth unit while summing
the two profiles in the other components. -/
def parGateStep (p q : StepProfile) : ResourceCost :=
  ⟨0, 1, p.basicGates + q.basicGates, 1, p.space + q.space, p.evolve + q.evolve,
    p.classicalBits + q.classicalBits⟩

/-- The query count of a paired gate layer is zero. -/
@[simp] theorem parGateStep_queries (p q : StepProfile) :
    (parGateStep p q).queries = 0 := rfl

/-- The macro-gate count of a paired gate layer is one. -/
@[simp] theorem parGateStep_macroGates (p q : StepProfile) :
    (parGateStep p q).macroGates = 1 := rfl

/-- The basic gate count of a paired gate layer is `p.basicGates + q.basicGates`. -/
@[simp] theorem parGateStep_basicGates (p q : StepProfile) :
    (parGateStep p q).basicGates = p.basicGates + q.basicGates := rfl

/-- The depth of a paired gate layer is one. -/
@[simp] theorem parGateStep_depth (p q : StepProfile) :
    (parGateStep p q).depth = 1 := rfl

/-- The peak space of a paired gate layer is `p.space + q.space`. -/
@[simp] theorem parGateStep_peakSpace (p q : StepProfile) :
    (parGateStep p q).peakSpace = p.space + q.space := rfl

/-- The Hamiltonian time of a paired gate layer is `p.evolve + q.evolve`. -/
@[simp] theorem parGateStep_hamiltonianTime (p q : StepProfile) :
    (parGateStep p q).hamiltonianTime = p.evolve + q.evolve := rfl

/-- The classical bit cost of a paired gate layer is `p.classicalBits + q.classicalBits`. -/
@[simp] theorem parGateStep_classicalBits (p q : StepProfile) :
    (parGateStep p q).classicalBits = p.classicalBits + q.classicalBits := rfl

/-- Derives synchronized-circuit resource costs using paired-gate layer costs and unit query
costs. -/
def derivePar (κI : Matrix I I ℂ → StepProfile) (κJ : Matrix J J ℂ → StepProfile) :
    ParCircuit I J → ResourceCost
  | [] => 0
  | ParStep.gates U V :: L => parGateStep (κI U) (κJ V) + derivePar κI κJ L
  | ParStep.query :: L => ResourceCost.ofOracleStep + derivePar κI κJ L

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- The empty synchronized circuit has zero derived cost. -/
@[simp] theorem derivePar_nil (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) : derivePar κI κJ [] = 0 := rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- Prepending paired gates composes their layer cost with the cost of the remaining
synchronized circuit. -/
@[simp] theorem derivePar_gates (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (U : Matrix I I ℂ) (V : Matrix J J ℂ)
    (L : ParCircuit I J) :
    derivePar κI κJ (ParStep.gates U V :: L)
      = parGateStep (κI U) (κJ V) + derivePar κI κJ L := rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- Prepending a synchronized query composes its unit query cost with the cost of the remaining
layers. -/
@[simp] theorem derivePar_query (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (L : ParCircuit I J) :
    derivePar κI κJ (ParStep.query :: L)
      = ResourceCost.ofOracleStep + derivePar κI κJ L := rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- The synchronized derived query cost equals the query count of the product-register circuit. -/
theorem derivePar_queries (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (L : ParCircuit I J) :
    (derivePar κI κJ L).queries = Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (parToCircuit L) := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    cases l with
    | gates U V => simp [parToCircuit, derivePar, ih]
    | query => simp [parToCircuit, derivePar, ih, Nat.add_comm]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- The synchronized derived macro-gate cost equals the gate count of the product-register
circuit. -/
theorem derivePar_macroGates (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (L : ParCircuit I J) :
    (derivePar κI κJ L).macroGates = Qatlib.Foundations.QueryWordCore.Circuit.GateCount (parToCircuit L) := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    cases l with
    | gates U V => simp [parToCircuit, derivePar, ih, Nat.add_comm]
    | query => simp [parToCircuit, derivePar, ih]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- The synchronized derived depth equals the number of layers. -/
theorem derivePar_depth (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (L : ParCircuit I J) :
    (derivePar κI κJ L).depth = L.length := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    cases l with
    | gates U V => simp [derivePar, ih, Nat.add_comm]
    | query => simp [derivePar, ih, Nat.add_comm]

/-- The synchronized derived depth equals the maximum size of the two projected circuits. -/
theorem depth_par_eq_max (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (L : ParCircuit I J) :
    (derivePar κI κJ L).depth = max (Qatlib.Foundations.QueryWordCore.Circuit.Size (parLeft L)) (Qatlib.Foundations.QueryWordCore.Circuit.Size (parRight L)) := by
  rw [derivePar_depth, size_parLeft, size_parRight, Nat.max_self]

/-- The derived depth of paired gate lists equals the maximum size of their separate gate
circuits. -/
theorem depth_parOfGates (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (gs : List (Matrix I I ℂ))
    (hs : List (Matrix J J ℂ)) :
    (derivePar κI κJ (parOfGates gs hs)).depth
      = max (Qatlib.Foundations.QueryWordCore.Circuit.Size (Circuit.ofGates gs)) (Qatlib.Foundations.QueryWordCore.Circuit.Size (Circuit.ofGates hs)) := by
  rw [derivePar_depth, parOfGates_length, Circuit.size_ofGates, Circuit.size_ofGates]

/-- For two nonempty gate lists, the paired depth is strictly less than the sum of their
separate circuit sizes. -/
theorem depth_parOfGates_lt_sum (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (gs : List (Matrix I I ℂ))
    (hs : List (Matrix J J ℂ)) (hgs : gs ≠ []) (hhs : hs ≠ []) :
    (derivePar κI κJ (parOfGates gs hs)).depth
      < Qatlib.Foundations.QueryWordCore.Circuit.Size (Circuit.ofGates gs) + Qatlib.Foundations.QueryWordCore.Circuit.Size (Circuit.ofGates hs) := by
  have h1 : 0 < gs.length := by
    by_contra hcon
    exact hgs (List.length_eq_zero_iff.mp (by omega))
  have h2 : 0 < hs.length := by
    by_contra hcon
    exact hhs (List.length_eq_zero_iff.mp (by omega))
  rw [depth_parOfGates, Circuit.size_ofGates, Circuit.size_ofGates]
  omega

/-- For a nonempty synchronized circuit, its derived depth is strictly less than the sum of its
projection sizes. -/
theorem depth_par_lt_sum (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (L : ParCircuit I J) (hL : L ≠ []) :
    (derivePar κI κJ L).depth < Qatlib.Foundations.QueryWordCore.Circuit.Size (parLeft L) + Qatlib.Foundations.QueryWordCore.Circuit.Size (parRight L) := by
  cases L with
  | nil => exact absurd rfl hL
  | cons l L' =>
    rw [derivePar_depth, size_parLeft, size_parRight, List.length_cons]
    omega

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- The basic gate cost of synchronized execution is the sum of the derived basic gate costs of
its projections. -/
theorem derivePar_basicGates (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (L : ParCircuit I J) :
    (derivePar κI κJ L).basicGates
      = (derive κI (parLeft L)).basicGates + (derive κJ (parRight L)).basicGates := by
  induction L with
  | nil => simp
  | cons l L ih =>
    cases l with
    | gates U V =>
      simp only [parLeft, parRight, derive_gate, derivePar_gates,
        ResourceCost.add_basicGates, ResourceCost.ofMacroStep_basicGates,
        parGateStep_basicGates, ih]
      omega
    | query =>
      simp only [parLeft, parRight, derive_query, derivePar_query,
        ResourceCost.add_basicGates, ResourceCost.ofOracleStep_basicGates, ih]
      omega

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- The peak space of synchronized execution is at most the sum of the peak spaces of its
projections. -/
theorem peakSpace_par_le_add (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (L : ParCircuit I J) :
    (derivePar κI κJ L).peakSpace
      ≤ (derive κI (parLeft L)).peakSpace + (derive κJ (parRight L)).peakSpace := by
  induction L with
  | nil => simp
  | cons l L ih =>
    cases l with
    | gates U V =>
      simp only [parLeft, parRight, derive_gate, derivePar_gates,
        ResourceCost.add_peakSpace, ResourceCost.ofMacroStep_peakSpace,
        parGateStep_peakSpace]
      exact max_le
        (Nat.add_le_add (le_max_left _ _) (le_max_left _ _))
        (ih.trans (Nat.add_le_add (le_max_right _ _) (le_max_right _ _)))
    | query =>
      simp only [parLeft, parRight, derive_query, derivePar_query,
        ResourceCost.add_peakSpace, ResourceCost.ofOracleStep_peakSpace]
      exact max_le (Nat.zero_le _)
        (ih.trans (Nat.add_le_add (Nat.le_max_right _ _) (Nat.le_max_right _ _)))

/-- A constant gate profile bounds the derived peak space of every circuit by that profile's
workspace size. -/
theorem derive_constant_peakSpace_le (p : StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive (fun _ => p) C).peakSpace ≤ p.space := by
  induction C with
  | nil => simp
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [derive_gate, ResourceCost.add_peakSpace, ResourceCost.ofMacroStep_peakSpace]
      exact max_le (le_refl _) ih
    | query =>
      rw [derive_query, ResourceCost.add_peakSpace, ResourceCost.ofOracleStep_peakSpace]
      exact max_le (Nat.zero_le _) ih

/-- With a constant profile, a circuit beginning with a gate has peak space equal to the
profile's workspace size. -/
theorem derive_constant_gate_peakSpace (p : StepProfile) (U : Matrix I I ℂ)
    (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive (fun _ => p) (Step.gate U :: C)).peakSpace = p.space := by
  rw [derive_gate, ResourceCost.add_peakSpace, ResourceCost.ofMacroStep_peakSpace]
  exact Nat.max_eq_left (derive_constant_peakSpace_le p C)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- For constant profiles, a synchronized circuit beginning with paired gates has peak space
equal to the sum of the two workspace sizes. -/
theorem peakSpace_par_eq_add_of_constant (p q : StepProfile) (U : Matrix I I ℂ)
    (V : Matrix J J ℂ) (L : ParCircuit I J) :
    (derivePar (fun _ => p) (fun _ => q) (ParStep.gates U V :: L)).peakSpace
      = p.space + q.space := by
  have hle : ∀ M : ParCircuit I J,
      (derivePar (fun _ => p) (fun _ => q) M).peakSpace ≤ p.space + q.space := by
    intro M
    induction M with
    | nil => simp
    | cons m M ih =>
      cases m with
      | gates U' V' =>
        simp only [derivePar_gates, ResourceCost.add_peakSpace, parGateStep_peakSpace]
        exact max_le (le_refl _) ih
      | query => simpa [derivePar] using ih
  simp only [derivePar_gates, ResourceCost.add_peakSpace, parGateStep_peakSpace]
  exact Nat.max_eq_left (hle L)

/-- For constant profiles of positive workspace size, a circuit beginning with paired gates has
peak space strictly above the maximum projection peak space. -/
theorem peakSpace_par_gt_max_of_constant (p q : StepProfile) (hp : 0 < p.space)
    (hq : 0 < q.space) (U : Matrix I I ℂ) (V : Matrix J J ℂ) (L : ParCircuit I J) :
    max (derive (fun _ => p) (parLeft (ParStep.gates U V :: L))).peakSpace
        (derive (fun _ => q) (parRight (ParStep.gates U V :: L))).peakSpace
      < (derivePar (fun _ => p) (fun _ => q) (ParStep.gates U V :: L)).peakSpace := by
  rw [peakSpace_par_eq_add_of_constant p q U V L,
    show parLeft (ParStep.gates U V :: L) = Step.gate U :: parLeft L from rfl,
    show parRight (ParStep.gates U V :: L) = Step.gate V :: parRight L from rfl,
    derive_constant_gate_peakSpace p U (parLeft L),
    derive_constant_gate_peakSpace q V (parRight L)]
  omega

/-- There exist profiles and a synchronized circuit whose peak space is strictly below the sum
of the projection peak spaces. -/
theorem peakSpace_par_lt_add_misaligned :
    ∃ (κI : Matrix Bool Bool ℂ → StepProfile) (κJ : Matrix Bool Bool ℂ → StepProfile)
      (L : ParCircuit Bool Bool),
      (derivePar κI κJ L).peakSpace
        < (derive κI (parLeft L)).peakSpace + (derive κJ (parRight L)).peakSpace := by
  classical
  have hZ : Qatlib.Foundations.PureStateMath.PauliZ ≠ (1 : Matrix Bool Bool ℂ) := by
    intro h
    have e := congrFun (congrFun h true) true
    simp only [Qatlib.Foundations.PureStateMath.PauliZ, Matrix.one_apply] at e
    norm_num at e
  have h1 : (1 : Matrix Bool Bool ℂ) ≠ Qatlib.Foundations.PureStateMath.PauliZ :=
      fun ee => hZ ee.symm
  set κ : Matrix Bool Bool ℂ → StepProfile :=
    fun W => if W = Qatlib.Foundations.PureStateMath.PauliZ then ⟨0, 5, 0, 0⟩ else ⟨0, 0, 0, 0⟩ with hκ
  have eZ : κ Qatlib.Foundations.PureStateMath.PauliZ = ⟨0, 5, 0, 0⟩ := by simp [hκ]
  have eOne : κ (1 : Matrix Bool Bool ℂ) = ⟨0, 0, 0, 0⟩ := by simp [hκ, h1]
  refine ⟨κ, κ,
      [ParStep.gates Qatlib.Foundations.PureStateMath.PauliZ 1,
      ParStep.gates 1 Qatlib.Foundations.PureStateMath.PauliZ], ?_⟩
  simp only [parLeft, parRight, derive_gate, derive_nil, ResourceCost.add_zero,
    ResourceCost.add_peakSpace, ResourceCost.ofMacroStep_peakSpace, derivePar_gates,
    parGateStep_peakSpace, eZ, eOne]
  decide

/-- A query-free circuit implementing a specified gate on every state and for every oracle
matrix. -/
structure GateCompilation (U : Matrix I I ℂ) where

  circuit : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I

  query_free : Qatlib.Foundations.QueryWordCore.Circuit.QueryCount circuit = 0

  semantics : ∀ (W : Matrix I I ℂ) (ψ : Qatlib.Foundations.PureStateMath.QState I), Run W circuit ψ = Qatlib.Foundations.PureStateMath.ApplyGate U ψ

/-- A choice of query-free circuit implementation for every gate matrix, together with exact
semantic correctness. -/
structure GateCompiler (I : Type*) [Fintype I] [DecidableEq I] where

  compile : Matrix I I ℂ → Qatlib.Foundations.QueryWordCore.Circuit.Circuit I

  query_free : ∀ U, Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (compile U) = 0

  semantics : ∀ (U W : Matrix I I ℂ) (ψ : Qatlib.Foundations.PureStateMath.QState I), Run W (compile U) ψ = Qatlib.Foundations.PureStateMath.ApplyGate U ψ

/-- Replaces each circuit gate by its compiler implementation and leaves oracle queries as query
steps. -/
def compileCircuit (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I → Qatlib.Foundations.QueryWordCore.Circuit.Circuit I
  | [] => []
  | Step.gate U :: C => c.compile U ++ compileCircuit c C
  | Step.query :: C => Step.query :: compileCircuit c C

/-- Compiling the empty circuit gives the empty circuit. -/
@[simp] theorem compileCircuit_nil (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) : compileCircuit c [] = [] := rfl

/-- Compiling a leading gate concatenates its implementation with the compiled remaining
circuit. -/
@[simp] theorem compileCircuit_gate (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) (U : Matrix I I ℂ)
    (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    compileCircuit c (Step.gate U :: C) = c.compile U ++ compileCircuit c C := rfl

/-- Compiling a leading query retains that query before the compiled remaining circuit. -/
@[simp] theorem compileCircuit_query (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    compileCircuit c (Step.query :: C) = Step.query :: compileCircuit c C := rfl

/-- Gate compilation preserves circuit execution on every state for every oracle matrix. -/
theorem run_compileCircuit (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) (W : Matrix I I ℂ) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I)
    (ψ : Qatlib.Foundations.PureStateMath.QState I) : Run W (compileCircuit c C) ψ = Run W C ψ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      simp only [compileCircuit_gate, run_append, c.semantics,
          Qatlib.Foundations.QueryWordCore.Circuit.run_gate]
      exact ih _
    | query =>
      simp only [compileCircuit_query, Qatlib.Foundations.QueryWordCore.Circuit.run_query]
      exact ih _

/-- Query-free gate compilation preserves the circuit query count. -/
theorem queryCount_compileCircuit (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (compileCircuit c C) = Qatlib.Foundations.QueryWordCore.Circuit.QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [compileCircuit_gate, queryCount_append, c.query_free U, zero_add, ih,
        Qatlib.Foundations.QueryWordCore.Circuit.queryCount_gate]
    | query => simp only [compileCircuit_query, queryCount_query, ih]

/-- Gate compilation preserves the query component of every profiled resource derivation. -/
theorem derive_compileCircuit_queries (κ : Matrix I I ℂ → StepProfile) (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I)
    (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive κ (compileCircuit c C)).queries = (derive κ C).queries := by
  rw [derive_queries, queryCount_compileCircuit, derive_queries]

omit [Fintype I] [DecidableEq I] in

/-- Circuit size is the sum of its gate count and query count. -/
theorem size_eq_gateCount_add_queryCount (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    Qatlib.Foundations.QueryWordCore.Circuit.Size C = Qatlib.Foundations.QueryWordCore.Circuit.GateCount C + Qatlib.Foundations.QueryWordCore.Circuit.QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp only [size_cons, Qatlib.Foundations.QueryWordCore.Circuit.gateCount_gate, gateCount_query, Qatlib.Foundations.QueryWordCore.Circuit.queryCount_gate,
      queryCount_query, ih] <;> omega

/-- A circuit with zero queries has gate count equal to its size. -/
theorem gateCount_eq_size_of_queryFree {D : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I} (hD : Qatlib.Foundations.QueryWordCore.Circuit.QueryCount D = 0) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount D = Qatlib.Foundations.QueryWordCore.Circuit.Size D := by
  rw [size_eq_gateCount_add_queryCount, hD, Nat.add_zero]

/-- The constant profile charging one basic gate and zero workspace, evolution time, and
classical bits per macro gate. -/
def basicGateProfile (I : Type*) [Fintype I] [DecidableEq I] :
    Matrix I I ℂ → StepProfile := fun _ => ⟨1, 0, 0, 0⟩

/-- Under the basic gate profile, derived basic gate cost equals circuit gate count. -/
theorem derive_basicGateProfile_basicGates (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive (basicGateProfile I) C).basicGates = Qatlib.Foundations.QueryWordCore.Circuit.GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => simp [derive, basicGateProfile, ih, Nat.add_comm]
    | query => simp [derive, ih]

/-- If every compiled gate has size at most `b`, the compiled basic gate cost is at most `b`
times the original gate count. -/
theorem derive_compileCircuit_basicGates_le (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) (b : ℕ)
    (hb : ∀ U, Qatlib.Foundations.QueryWordCore.Circuit.Size (c.compile U) ≤ b) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive (basicGateProfile I) (compileCircuit c C)).basicGates
      ≤ b * Qatlib.Foundations.QueryWordCore.Circuit.GateCount C := by
  induction C with
  | nil => simp
  | cons s C ih =>
    cases s with
    | gate U =>
      have hsplit : (derive (basicGateProfile I)
          (compileCircuit c (Step.gate U :: C))).basicGates
          = Qatlib.Foundations.QueryWordCore.Circuit.GateCount (c.compile U)
            + (derive (basicGateProfile I) (compileCircuit c C)).basicGates := by
        rw [compileCircuit_gate, derive_append, ResourceCost.add_basicGates,
          derive_basicGateProfile_basicGates]
      have hU : Qatlib.Foundations.QueryWordCore.Circuit.GateCount (c.compile U) ≤ b := by
        rw [gateCount_eq_size_of_queryFree (c.query_free U)]
        exact hb U
      have hmul : b * Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Step.gate U :: C) = b * Qatlib.Foundations.QueryWordCore.Circuit.GateCount C + b := by
        rw [Qatlib.Foundations.QueryWordCore.Circuit.gateCount_gate]
        ring
      rw [hsplit]
      omega
    | query =>
      rw [compileCircuit_query, derive_query, gateCount_query]
      simpa using ih

/-- The compiler implementing each gate by the singleton circuit containing that same gate. -/
def identityCompiler (I : Type*) [Fintype I] [DecidableEq I] : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I where
  compile U := [Step.gate U]
  query_free := fun _ => rfl
  semantics := fun _ _ _ => rfl

/-- The identity compiler leaves every circuit unchanged. -/
@[simp] theorem compileCircuit_identityCompiler (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    compileCircuit (identityCompiler I) C = C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      show (identityCompiler I).compile U ++ compileCircuit (identityCompiler I) C
        = Step.gate U :: C
      rw [ih]
      rfl
    | query =>
      rw [compileCircuit_query, ih]

/-- Identity compilation with the basic gate profile gives the original gate count as basic gate
cost. -/
theorem basicGates_identityCompiler (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive (basicGateProfile I) (compileCircuit (identityCompiler I) C)).basicGates
      = Qatlib.Foundations.QueryWordCore.Circuit.GateCount C := by
  rw [compileCircuit_identityCompiler, derive_basicGateProfile_basicGates]

/-- Implements a tensor-product gate by two successive gates acting on the separate registers. -/
noncomputable def parLayerCompilation (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    GateCompilation (Qatlib.Foundations.PureStateMath.TensorGate U V) where
  circuit := [Step.gate (Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ)),
    Step.gate (Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix I I ℂ) V)]
  query_free := rfl
  semantics := by
    intro W ψ
    simp only [Qatlib.Foundations.QueryWordCore.Circuit.run_gate, Qatlib.Foundations.QueryWordCore.Circuit.run_nil, ← applyGate_mul, Qatlib.Foundations.PureStateMath.tensorGate_mul, Matrix.one_mul,
      Matrix.mul_one]

/-- The separate-register implementation of a paired gate has circuit size two. -/
@[simp] theorem parLayerCompilation_size (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    Qatlib.Foundations.QueryWordCore.Circuit.Size (parLayerCompilation U V).circuit = 2 := rfl

/-- A tensor-product gate counts as one macro gate, whereas its separate-register compilation
counts as two basic gates. -/
theorem parLayerCompilation_macro_vs_basic (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    (derive (basicGateProfile (I × J)) [Step.gate (Qatlib.Foundations.PureStateMath.TensorGate U V)]).macroGates = 1 ∧
      (derive (basicGateProfile (I × J)) (parLayerCompilation U V).circuit).basicGates
        = 2 ∧ (1 : ℕ) ≠ 2 := by
  refine ⟨rfl, ?_, by decide⟩
  simp only [parLayerCompilation, derive_gate, derive_nil, ResourceCost.add_zero,
    basicGateProfile]
  rfl

/-- Every gate occurring in the circuit belongs to the specified matrix set. -/
def Circuit.UsesGateSet (G : Set (Matrix I I ℂ)) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) : Prop :=
  ∀ U, Step.gate U ∈ C → U ∈ G

omit [Fintype I] [DecidableEq I] in

/-- The empty circuit uses every specified gate set. -/
@[simp] theorem Circuit.usesGateSet_nil (G : Set (Matrix I I ℂ)) :
    Circuit.UsesGateSet G [] := by
  intro U h
  simp at h

omit [Fintype I] [DecidableEq I] in

/-- A concatenated circuit uses a gate set exactly when both component circuits use it. -/
@[simp] theorem Circuit.usesGateSet_append (G : Set (Matrix I I ℂ)) (C D : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    Circuit.UsesGateSet G (C ++ D) ↔ Circuit.UsesGateSet G C ∧ Circuit.UsesGateSet G D := by
  constructor
  · intro h
    exact ⟨fun U hU => h U (List.mem_append.mpr (Or.inl hU)),
      fun U hU => h U (List.mem_append.mpr (Or.inr hU))⟩
  · rintro ⟨hC, hD⟩ U hU
    exact (List.mem_append.mp hU).elim (hC U) (hD U)

/-- A circuit using only gates from a unitary gate set satisfies `IsUnitaryCircuit`. -/
theorem Circuit.UsesGateSet.isUnitaryCircuit {G : Set (Matrix I I ℂ)} {C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I}
    (hC : Circuit.UsesGateSet G C) (hG : ∀ U ∈ G, U ∈ Matrix.unitaryGroup I ℂ) :
    IsUnitaryCircuit C := fun U hU => hG U (hC U hU)

/-- Every gate implementation needed for the given circuit uses the specified gate set. -/
def GateCompiler.UsesGateSetOn (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) (G : Set (Matrix I I ℂ))
    (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) : Prop :=
  ∀ U, Step.gate U ∈ C → Circuit.UsesGateSet G (c.compile U)

/-- If the compiler uses a gate set on the original circuit, the compiled circuit uses that gate
set. -/
theorem GateCompiler.compile_usesGateSet (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) (G : Set (Matrix I I ℂ))
    (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) (hC : c.UsesGateSetOn G C) :
    Circuit.UsesGateSet G (compileCircuit c C) := by
  induction C with
  | nil => exact Circuit.usesGateSet_nil G
  | cons s C ih =>
    have ht : c.UsesGateSetOn G C :=
      fun U hU => hC U (List.mem_cons_of_mem s hU)
    cases s with
    | gate U =>
      rw [compileCircuit_gate, Circuit.usesGateSet_append]
      exact ⟨hC U List.mem_cons_self, ih ht⟩
    | query =>
      intro U hU
      rcases List.mem_cons.mp hU with hU | hU
      · cases hU
      · exact ih ht U hU

/-- Assigns each macro gate its compiled gate count as basic gate cost and zero in the remaining
step-profile components. -/
def GateCompiler.profile (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) : Matrix I I ℂ → StepProfile :=
  fun U => ⟨Qatlib.Foundations.QueryWordCore.Circuit.GateCount (c.compile U), 0, 0, 0⟩

/-- The compiler profile derives exactly the gate count of the compiled circuit as basic gate
cost. -/
theorem GateCompiler.profile_basicGates_eq (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive c.profile C).basicGates = Qatlib.Foundations.QueryWordCore.Circuit.GateCount (compileCircuit c C) := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      simp only [derive_gate, ResourceCost.add_basicGates, ResourceCost.ofMacroStep_basicGates,
        GateCompiler.profile, compileCircuit_gate, gateCount_append, ih]
    | query =>
      simpa only [derive_query, ResourceCost.add_basicGates,
        ResourceCost.ofOracleStep_basicGates, Nat.zero_add, compileCircuit_query,
        gateCount_query] using ih

/-- Derived basic gate cost plus query cost under the compiler profile equals compiled circuit
size. -/
theorem GateCompiler.profile_basicGates_add_queries (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive c.profile C).basicGates + (derive c.profile C).queries
      = Qatlib.Foundations.QueryWordCore.Circuit.Size (compileCircuit c C) := by
  rw [c.profile_basicGates_eq, derive_queries, size_eq_gateCount_add_queryCount,
    queryCount_compileCircuit]

/-- Compilation into a unitary gate set preserves execution and queries, uses that gate set, and
realizes the exact basic gate count assigned by the compiler profile. -/
theorem GateCompiler.certified_semantics_cost (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I)
    (G : Set (Matrix I I ℂ)) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) (hC : c.UsesGateSetOn G C)
    (hG : ∀ U ∈ G, U ∈ Matrix.unitaryGroup I ℂ)
    (W : Matrix I I ℂ) (ψ : Qatlib.Foundations.PureStateMath.QState I) :
    Run W (compileCircuit c C) ψ = Run W C ψ ∧
      Circuit.UsesGateSet G (compileCircuit c C) ∧
      IsUnitaryCircuit (compileCircuit c C) ∧
      (derive c.profile C).basicGates = Qatlib.Foundations.QueryWordCore.Circuit.GateCount (compileCircuit c C) ∧
      Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (compileCircuit c C) = Qatlib.Foundations.QueryWordCore.Circuit.QueryCount C := by
  have hm := c.compile_usesGateSet G C hC
  exact ⟨run_compileCircuit c W C ψ, hm, hm.isUnitaryCircuit hG,
    c.profile_basicGates_eq C, queryCount_compileCircuit c C⟩

/-- A query-free implementation containing no gates forces the implemented gate to fix every
state. -/
theorem GateCompilation.run_eq_self_of_gateCount_zero {U : Matrix I I ℂ}
    (c : GateCompilation U) (h : Qatlib.Foundations.QueryWordCore.Circuit.GateCount c.circuit = 0) (ψ : Qatlib.Foundations.PureStateMath.QState I) :
    Qatlib.Foundations.PureStateMath.ApplyGate U ψ = ψ := by
  have hs : Qatlib.Foundations.QueryWordCore.Circuit.Size c.circuit = 0 := by
    rw [size_eq_gateCount_add_queryCount, h, c.query_free]
  have hn : c.circuit = [] := List.length_eq_zero_iff.mp hs
  have he := c.semantics 1 ψ
  simpa only [hn, Qatlib.Foundations.QueryWordCore.Circuit.run_nil] using he.symm

/-- A query-free implementation of a gate that changes a given state must contain at least one
gate. -/
theorem GateCompilation.gateCount_pos_of_changes_state {U : Matrix I I ℂ}
    (c : GateCompilation U) {ψ : Qatlib.Foundations.PureStateMath.QState I} (hψ : Qatlib.Foundations.PureStateMath.ApplyGate U ψ ≠ ψ) :
    0 < Qatlib.Foundations.QueryWordCore.Circuit.GateCount c.circuit := by
  by_contra h
  exact hψ (c.run_eq_self_of_gateCount_zero (Nat.eq_zero_of_not_pos h) ψ)

/-- The paired-gate compilation uses only the tensor-extended left gate and tensor-extended
right gate. -/
theorem parLayerCompilation_usesGateSet (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    Circuit.UsesGateSet
      ({Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ), Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix I I ℂ) V} :
        Set (Matrix (I × J) (I × J) ℂ))
      (parLayerCompilation U V).circuit := by
  intro A hA
  simp only [parLayerCompilation, List.mem_cons, List.not_mem_nil, or_false,
    Step.gate.injEq] at hA
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hA

/-- Counts explicit gate steps in a Hamiltonian query program, excluding evolution steps. -/
def hamiltonianGateCount : List (HamiltonianQueryStep I) → ℕ
  | [] => 0
  | HamiltonianQueryStep.gate _ :: P => hamiltonianGateCount P + 1
  | HamiltonianQueryStep.evolve _ :: P => hamiltonianGateCount P

/-- Records a Hamiltonian program's query count, explicit gate count, step count, and total
absolute evolution time, with the remaining costs set to zero. -/
noncomputable def deriveHamiltonian (P : List (HamiltonianQueryStep I)) : ResourceCost :=
  ⟨HamiltonianQueryCount P, hamiltonianGateCount P, 0, P.length, 0,
    ENNReal.ofReal (HamiltonianEvolutionTime P), 0⟩

omit [Fintype I] [DecidableEq I] in

/-- Explicit Hamiltonian-program gate counts add under concatenation. -/
theorem hamiltonianGateCount_append (P Q : List (HamiltonianQueryStep I)) :
    hamiltonianGateCount (P ++ Q)
      = hamiltonianGateCount P + hamiltonianGateCount Q := by
  induction P with
  | nil => simp [hamiltonianGateCount]
  | cons s P ih =>
    cases s with
    | gate U =>
      simp only [List.cons_append, hamiltonianGateCount, ih]
      omega
    | evolve t => simp [hamiltonianGateCount, ih]

omit [Fintype I] [DecidableEq I] in

/-- Total absolute Hamiltonian evolution time adds under concatenation. -/
theorem hamiltonianEvolutionTime_append (P Q : List (HamiltonianQueryStep I)) :
    HamiltonianEvolutionTime (P ++ Q)
      = HamiltonianEvolutionTime P + HamiltonianEvolutionTime Q := by
  induction P with
  | nil => simp [HamiltonianEvolutionTime]
  | cons s P ih =>
    cases s <;> simp only [List.cons_append, HamiltonianEvolutionTime, ih]
    ring

/-- Hamiltonian resource derivation respects concatenation of programs. -/
theorem deriveHamiltonian_append (P Q : List (HamiltonianQueryStep I)) :
    deriveHamiltonian (P ++ Q) = deriveHamiltonian P + deriveHamiltonian Q := by
  have hP := hamiltonianEvolutionTime_nonneg P
  have hQ := hamiltonianEvolutionTime_nonneg Q
  ext <;> simp [deriveHamiltonian, hamiltonianQueryCount_append,
    hamiltonianGateCount_append, hamiltonianEvolutionTime_append,
    ENNReal.ofReal_add hP hQ, List.length_append]

omit [Fintype I] [DecidableEq I] in

/-- The query component of Hamiltonian resource derivation equals `HamiltonianQueryCount`. -/
theorem deriveHamiltonian_queries (P : List (HamiltonianQueryStep I)) :
    (deriveHamiltonian P).queries = HamiltonianQueryCount P := rfl

omit [Fintype I] [DecidableEq I] in

/-- Prepending an evolution step adds one query and adds the absolute value of its time
parameter to total evolution time. -/
theorem deriveHamiltonian_evolve_queries_and_time (t : ℝ) (P : List (HamiltonianQueryStep I)) :
    (deriveHamiltonian (HamiltonianQueryStep.evolve t :: P)).queries
      = 1 + HamiltonianQueryCount P ∧
      (deriveHamiltonian (HamiltonianQueryStep.evolve t :: P)).hamiltonianTime
      = ENNReal.ofReal (|t| + HamiltonianEvolutionTime P) := by
  exact ⟨rfl, rfl⟩

end Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
