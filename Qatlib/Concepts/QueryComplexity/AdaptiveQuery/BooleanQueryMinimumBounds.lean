/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveClassicalSimulationBeal
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.InterruptedCall

/-!
# Bounds for Boolean quantum query minima

This module embeds a circuit with a final event into an observed circuit via `circuitEvent`,
then applies adaptive block sensitivity and classical simulation bounds to Boolean query
programs. It derives quadratic block sensitivity bounds and sixth power deterministic query
bounds for exact, bounded error, and zero error minima.

The theorem `complete_clause67` collects feasibility, comparisons, degree bounds, and
deterministic simulation bounds for the three query models. The underlying polynomial method is
developed in [BealsEtAl2001].

## Main statements

* `minimum_bs_bounds`: block sensitivity bounds for exact and bounded error minima.
* `minimum_classical_bounds`: deterministic complexity bounds in terms of quantum minima.
* `zeroError_minimum_bounds`: degree, sensitivity, and simulation bounds for both zero error
  conventions.
* `complete_clause67`: the combined feasibility and complexity statements.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs.Coin
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.QueryComplexity.DecisionTrees
open Qatlib
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
open scoped Classical BigOperators
set_option autoImplicit false
noncomputable section

variable {J : Type} [Fintype J] [DecidableEq J]

/-- Turn a circuit followed by the event test `E` into an observed circuit that accepts exactly
the true projective outcome. -/
def circuitEvent (C : Circuit J) (E : Finset J) : ObservedCircuit J :=
  observedOfCircuit C (.project (Projector E) (.halt false) (.halt true))

/-- The traces of `circuitEvent C E` are the rejecting and accepting projective branches of the
final circuit state, each with the circuit's query and gate counts and one recorded
measurement. -/
theorem circuitEvent_traces (O : Matrix J J ℂ) (C : Circuit J)
    (E : Finset J) (ψ : QState J) :
    observedTraces O (circuitEvent C E) ψ =
      [{state:=ProjectiveBranch (Projector E) false (Run O C ψ),accepted:=false,
        queries:=QueryCount C,gates:=GateCount C,measurements:=1,outcomes:=[(2,0)]},
       {state:=ProjectiveBranch (Projector E) true (Run O C ψ),accepted:=true,
        queries:=QueryCount C,gates:=GateCount C,measurements:=1,outcomes:=[(2,1)]}] := by
  unfold circuitEvent
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih => cases s <;>
      simp [observedOfCircuit,observedTraces,Run,QueryCount,GateCount,ih]

/-- The acceptance of `circuitEvent C E` equals the probability of measuring `E` after running
`C`. -/
theorem circuitEvent_acceptance (O : Matrix J J ℂ) (C : Circuit J)
    (E : Finset J) (ψ : QState J) :
    observedAcceptance O (circuitEvent C E) ψ=MeasureProb (Run O C ψ) E := by
  rw [observedAcceptance_eq_sum,circuitEvent_traces]
  simp [branchMass,measureProb_collapse]

/-- A unitary circuit followed by an event test is a well formed observed circuit. -/
theorem circuitEvent_wellFormed (C : Circuit J) (E : Finset J) :
    IsUnitaryCircuit C → observedWellFormed (circuitEvent C E) := by
  unfold circuitEvent
  induction C with
  | nil =>
      intro _
      exact ⟨projector_isOrthogonalProjector E,trivial,trivial⟩
  | cons s C ih =>
      intro hC
      cases s with
      | gate U =>
          obtain ⟨hU,hC'⟩ := (isUnitaryCircuit_gate U C).mp hC
          exact ⟨hU,ih hC'⟩
      | query => exact ih ((isUnitaryCircuit_query C).mp hC)

omit [Fintype J] in

/-- The observed query depth of a circuit followed by an event test equals the original
circuit's query count. -/
theorem circuitEvent_queryDepth (C : Circuit J) (E : Finset J) :
    observedQueryDepth (circuitEvent C E)=QueryCount C := by
  unfold circuitEvent
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;>
      simp [observedOfCircuit,observedQueryDepth,QueryCount,ih]

variable {n : ℕ}

/-- A constant Boolean function has block sensitivity zero. -/
theorem constant_blockSensitivity (f : (Fin n→Bool)→Bool) (b : Bool) (hf : ∀x,f x=b) :
    blockSensitivity f=0 := by
  unfold blockSensitivity
  apply (Finset.sup_eq_bot_iff _ _).2
  intro k hk
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hk
  change blockSensitivityAt f x=0
  unfold blockSensitivityAt
  apply (Finset.sup_eq_bot_iff _ _).2
  intro F hF
  have hF0 : F=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro B hB
    have hs : f x ≠ f (flipBlock x B) := (Finset.mem_filter.mp hF).2.1 B hB
    exact hs ((hf x).trans (hf (flipBlock x B)).symm)
  simp [hF0]

/-- The halting tree returning the constant value computes a constant Boolean function and uses
zero queries. -/
theorem constant_halt_tree (f : (Fin n→Bool)→Bool) (b : Bool) (hf : ∀x,f x=b) :
    (∀x:Fin n→Bool,(Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x (BoolQueryTree.halt b)).1=f x) ∧
      (BoolQueryTree.halt b : BoolQueryTree (Fin n) Bool).MaxQueries=0 := by
  exact ⟨fun x => (hf x).symm,rfl⟩

/-- A constant Boolean function has deterministic query complexity zero. -/
theorem constant_deterministicQueryComplexity (f : (Fin n→Bool)→Bool) (b : Bool)
    (hf : ∀x,f x=b) : deterministicQueryComplexity f=0 := by
  apply Nat.eq_zero_of_le_zero
  unfold deterministicQueryComplexity
  apply Nat.sInf_le
  exact ⟨⟨BoolQueryTree.halt b,(constant_halt_tree f b hf).1⟩,rfl⟩

variable {W : Type} [Fintype W] [DecidableEq W]

/-- A bounded error Boolean query program has block sensitivity at most sixteen times the square
of its query count. -/
theorem bounded_program_bs (P : Program n W) (f : (Fin n→Bool)→Bool) (h : Bounded P f) :
    blockSensitivity f≤16*QueryCount P.circuit^2 := by
  cases n with
  | zero =>
      have hf := congrFun (empty_function_constant f)
      rw [constant_blockSensitivity f (f emptyInput) hf]
      omega
  | succ m =>
      letI : Nonempty W := ⟨P.clean⟩
      have ho : ∀x, |observedAcceptance (workspaceBitOracle x)
          (circuitEvent P.circuit P.accept) (initial P)-(if f x then (1:ℝ) else 0)|≤1/3 := by
        intro x
        rw [circuitEvent_acceptance]
        exact h x
      have hb := (adaptiveBlockSensitivityQueryBound (m+1) W
        (circuitEvent P.circuit P.accept) (initial P) f
        (circuitEvent_wellFormed _ _ P.unitary) (normalized_ket _)).1 ho
      simpa only [circuitEvent_queryDepth] using! hb

/-- An exact Boolean query program has block sensitivity at most eight times the square of its
query count. -/
theorem exact_program_bs (P : Program n W) (f : (Fin n→Bool)→Bool) (h : Exact P f) :
    blockSensitivity f≤8*QueryCount P.circuit^2 := by
  cases n with
  | zero =>
      rw [constant_blockSensitivity f (f emptyInput) (congrFun (empty_function_constant f))]
      omega
  | succ m =>
      letI : Nonempty W := ⟨P.clean⟩
      have ho : ∀x, observedAcceptance (workspaceBitOracle x)
          (circuitEvent P.circuit P.accept) (initial P)=(if f x then (1:ℝ) else 0) := by
        intro x
        rw [circuitEvent_acceptance]
        exact h x
      have hb := (adaptiveBlockSensitivityQueryBound (m+1) W
        (circuitEvent P.circuit P.accept) (initial P) f
        (circuitEvent_wellFormed _ _ P.unitary) (normalized_ket _)).2 ho
      simpa only [circuitEvent_queryDepth] using! hb

/-- A bounded error program with `T` queries yields an exact deterministic tree of cost at most
`4096T⁶` and the same bound on deterministic query complexity. -/
theorem bounded_program_classical (P : Program n W) (f : (Fin n→Bool)→Bool)
    (h : Bounded P f) :
    (∃t : BoolQueryTree (Fin n) Bool, (∀x,(Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x t).1=f x) ∧
      t.MaxQueries≤4096*QueryCount P.circuit^6) ∧
      deterministicQueryComplexity f≤4096*QueryCount P.circuit^6 := by
  cases n with
  | zero =>
      have hf := congrFun (empty_function_constant f)
      refine ⟨⟨.halt (f emptyInput),fun x => (hf x).symm,by simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]⟩,?_⟩
      rw [constant_deterministicQueryComplexity f (f emptyInput) hf]
      omega
  | succ m =>
      letI : Nonempty W := ⟨P.clean⟩
      have ho : ∀x, |observedAcceptance (workspaceBitOracle x)
          (circuitEvent P.circuit P.accept) (initial P)-(if f x then (1:ℝ) else 0)|≤1/3 := by
        intro x
        rw [circuitEvent_acceptance]
        exact h x
      have hc := adaptiveClassicalSimulation (m+1) W
        (circuitEvent P.circuit P.accept) (initial P) f
        (circuitEvent_wellFormed _ _ P.unitary) (normalized_ket _) ho
      simpa only [circuitEvent_queryDepth] using! hc

/-- Block sensitivity is at most eight times the square of the exact quantum query minimum and
sixteen times the square of the bounded error minimum. See [Beals et al., Theorem
4.13][BealsEtAl2001]. -/
theorem minimum_bs_bounds (f : (Fin n→Bool)→Bool) :
    blockSensitivity f≤8*exactMinimum f^2 ∧ blockSensitivity f≤16*boundedMinimum f^2 := by
  constructor
  · obtain ⟨S,hS,dS,P,hq,hp⟩ := exactMinimum_attained f
    letI := hS
    letI := dS
    simpa only [hq] using! exact_program_bs P f hp
  · obtain ⟨S,hS,dS,P,hq,hp⟩ := boundedMinimum_attained f
    letI := hS
    letI := dS
    simpa only [hq] using! bounded_program_bs P f hp

/-- Deterministic query complexity is at most `4096` times the sixth power of either the exact
or the bounded error quantum query minimum. See [Beals et al., Theorem 5.4][BealsEtAl2001]. -/
theorem minimum_classical_bounds (f : (Fin n→Bool)→Bool) :
    deterministicQueryComplexity f≤4096*exactMinimum f^6 ∧
      deterministicQueryComplexity f≤4096*boundedMinimum f^6 := by
  constructor
  · obtain ⟨S,hS,dS,P,hq,hp⟩ := exactMinimum_attained f
    letI := hS
    letI := dS
    simpa only [hq] using! (bounded_program_classical P f (exact_bounded P f hp)).2
  · obtain ⟨S,hS,dS,P,hq,hp⟩ := boundedMinimum_attained f
    letI := hS
    letI := dS
    simpa only [hq] using! (bounded_program_classical P f hp).2

/-- There exists an exact deterministic tree with cost at most `4096` times the sixth power of
the bounded error quantum query minimum. -/
theorem minimum_classical_tree (f : (Fin n→Bool)→Bool) :
    ∃t : BoolQueryTree (Fin n) Bool, (∀x,(Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x t).1=f x) ∧
      t.MaxQueries≤4096*boundedMinimum f^6 := by
  obtain ⟨S,hS,dS,P,hq,hp⟩ := boundedMinimum_attained f
  letI := hS
  letI := dS
  simpa only [hq] using! (bounded_program_classical P f hp).1

/-- A zero error program in either convention has block sensitivity at most `16T²` and possesses
an exact deterministic simulation of cost at most `4096T⁶`, where `T` is its query count. -/
theorem zeroError_program_bounds (strict : Bool) (P : Program n W)
    (E0 : Finset (Space n W)) (f : (Fin n→Bool)→Bool) (h : ZeroError strict P E0 f) :
    blockSensitivity f≤16*QueryCount P.circuit^2 ∧
      (∃t : BoolQueryTree (Fin n) Bool, (∀x,(Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x t).1=f x) ∧
        t.MaxQueries≤4096*QueryCount P.circuit^6) ∧
      deterministicQueryComplexity f≤4096*QueryCount P.circuit^6 := by
  have hw : ZeroError false P E0 f := by
    cases strict with
    | false => exact h
    | true => exact zeroError_strict_weak P E0 f h
  have hb := zeroError_guess_bounded P E0 f hw
  have hbs := bounded_program_bs (guessProgram P E0) f hb
  have hc := bounded_program_classical (guessProgram P E0) f hb
  simpa only [(guessProgram_counts P E0).1] using! And.intro hbs hc

/-- For either zero error convention, approximate degree is at most twice the quantum query
minimum, block sensitivity is at most sixteen times its square, and an exact deterministic
simulation and deterministic complexity are bounded by `4096` times its sixth power. -/
theorem zeroError_minimum_bounds (strict : Bool) (f : (Fin n→Bool)→Bool) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.approxDegree f≤2*zeroErrorMinimum strict f ∧
      blockSensitivity f≤16*zeroErrorMinimum strict f^2 ∧
      (∃t : BoolQueryTree (Fin n) Bool, (∀x,(Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x t).1=f x) ∧
        t.MaxQueries≤4096*zeroErrorMinimum strict f^6) ∧
      deterministicQueryComplexity f≤4096*zeroErrorMinimum strict f^6 := by
  obtain ⟨S,hS,dS,P,E0,hq,hp⟩ := zeroErrorMinimum_attained strict f
  letI := hS
  letI := dS
  have hw : ZeroError false P E0 f := by
    cases strict with
    | false => exact hp
    | true => exact zeroError_strict_weak P E0 f hp
  have hd := approximate_degree_program (guessProgram P E0) f (zeroError_guess_bounded P E0 f hw)
  have hr := zeroError_program_bounds strict P E0 f hp
  simpa only [(guessProgram_counts P E0).1,hq] using! And.intro hd hr

/-- Collect the quadratic block sensitivity and sixth power deterministic query bounds for
exact, bounded error, and both zero error quantum query minima. -/
theorem frontier3 (f : (Fin n→Bool)→Bool) :
    blockSensitivity f≤8*exactMinimum f^2 ∧
      blockSensitivity f≤16*boundedMinimum f^2 ∧
      deterministicQueryComplexity f≤4096*exactMinimum f^6 ∧
      deterministicQueryComplexity f≤4096*boundedMinimum f^6 ∧
      (∀strict : Bool, blockSensitivity f≤16*zeroErrorMinimum strict f^2 ∧
        deterministicQueryComplexity f≤4096*zeroErrorMinimum strict f^6) := by
  refine ⟨(minimum_bs_bounds f).1,(minimum_bs_bounds f).2,
    (minimum_classical_bounds f).1,(minimum_classical_bounds f).2,?_⟩
  intro strict
  exact ⟨(zeroError_minimum_bounds strict f).2.1,(zeroError_minimum_bounds strict f).2.2.2⟩

/-- Collect feasibility and ordering of exact, bounded error, and zero error minima, their
degree bounds, quadratic block sensitivity bounds, and sixth power deterministic simulation
bounds. These comparisons implement the polynomial method framework of [BealsEtAl2001]. -/
theorem complete_clause67 (n : ℕ) (f : (Fin n → Bool) → Bool) :
    (ExactFeasible f (exactMinimum f) ∧ BoundedFeasible f (boundedMinimum f) ∧
      boundedMinimum f ≤ exactMinimum f ∧ exactMinimum f ≤ n ∧
      Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f ≤ 2 * exactMinimum f ∧
      Qatlib.Concepts.QueryComplexity.DegreeMethod.approxDegree f ≤ 2 * boundedMinimum f) ∧
    (ZeroErrorFeasible false f (zeroErrorMinimum false f) ∧
      ZeroErrorFeasible true f (zeroErrorMinimum true f) ∧
      boundedMinimum f ≤ zeroErrorMinimum false f ∧
      zeroErrorMinimum false f ≤ zeroErrorMinimum true f ∧
      zeroErrorMinimum true f ≤ exactMinimum f ∧ exactMinimum f ≤ n) ∧
    (blockSensitivity f ≤ 8 * exactMinimum f ^ 2 ∧
      blockSensitivity f ≤ 16 * boundedMinimum f ^ 2 ∧
      deterministicQueryComplexity f ≤ 4096 * exactMinimum f ^ 6 ∧
      deterministicQueryComplexity f ≤ 4096 * boundedMinimum f ^ 6 ∧
      (∀ strict : Bool, blockSensitivity f ≤ 16 * zeroErrorMinimum strict f ^ 2 ∧
        deterministicQueryComplexity f ≤ 4096 * zeroErrorMinimum strict f ^ 6)) ∧
    (∀ strict : Bool,
      Qatlib.Concepts.QueryComplexity.DegreeMethod.approxDegree f ≤ 2 * zeroErrorMinimum strict f) :=
  ⟨Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs.frontier1 f,
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs.frontier2 f,
    frontier3 f, fun strict => (zeroError_minimum_bounds strict f).1⟩

end
end Qatlib.Concepts.QueryComplexity.AdaptiveQuery
