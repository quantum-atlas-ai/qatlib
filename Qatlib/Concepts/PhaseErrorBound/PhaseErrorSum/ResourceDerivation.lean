/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.LocalCapability
import Qatlib.Foundations.QueryWordCore.HamiltonianQuery
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.QueryWordCore.HamiltonianQuery

namespace Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

open Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

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

@[simp] theorem ResourceCost.zero_queries : (0 : ResourceCost).queries = 0 := rfl

@[simp] theorem ResourceCost.zero_macroGates : (0 : ResourceCost).macroGates = 0 := rfl

@[simp] theorem ResourceCost.zero_basicGates : (0 : ResourceCost).basicGates = 0 := rfl

@[simp] theorem ResourceCost.zero_depth : (0 : ResourceCost).depth = 0 := rfl

@[simp] theorem ResourceCost.zero_peakSpace : (0 : ResourceCost).peakSpace = 0 := rfl

@[simp] theorem ResourceCost.zero_hamiltonianTime :
    (0 : ResourceCost).hamiltonianTime = 0 := rfl

@[simp] theorem ResourceCost.zero_classicalBits :
    (0 : ResourceCost).classicalBits = 0 := rfl

@[simp] theorem ResourceCost.add_queries (a b : ResourceCost) :
    (a + b).queries = a.queries + b.queries := rfl

@[simp] theorem ResourceCost.add_macroGates (a b : ResourceCost) :
    (a + b).macroGates = a.macroGates + b.macroGates := rfl

@[simp] theorem ResourceCost.add_basicGates (a b : ResourceCost) :
    (a + b).basicGates = a.basicGates + b.basicGates := rfl

@[simp] theorem ResourceCost.add_depth (a b : ResourceCost) :
    (a + b).depth = a.depth + b.depth := rfl

@[simp] theorem ResourceCost.add_peakSpace (a b : ResourceCost) :
    (a + b).peakSpace = max a.peakSpace b.peakSpace := rfl

@[simp] theorem ResourceCost.add_hamiltonianTime (a b : ResourceCost) :
    (a + b).hamiltonianTime = a.hamiltonianTime + b.hamiltonianTime := rfl

@[simp] theorem ResourceCost.add_classicalBits (a b : ResourceCost) :
    (a + b).classicalBits = a.classicalBits + b.classicalBits := rfl

@[simp] theorem ResourceCost.zero_add (a : ResourceCost) : 0 + a = a := by
  ext <;> simp

@[simp] theorem ResourceCost.add_zero (a : ResourceCost) : a + 0 = a := by
  ext <;> simp

theorem ResourceCost.add_assoc (a b c : ResourceCost) : a + b + c = a + (b + c) := by
  ext
  all_goals simp only [ResourceCost.add_queries, ResourceCost.add_macroGates,
    ResourceCost.add_basicGates, ResourceCost.add_depth, ResourceCost.add_peakSpace,
    ResourceCost.add_hamiltonianTime, ResourceCost.add_classicalBits]
  all_goals first
  | omega
  | ring

theorem ResourceCost.add_comm (a b : ResourceCost) : a + b = b + a := by
  ext
  all_goals simp only [ResourceCost.add_queries, ResourceCost.add_macroGates,
    ResourceCost.add_basicGates, ResourceCost.add_depth, ResourceCost.add_peakSpace,
    ResourceCost.add_hamiltonianTime, ResourceCost.add_classicalBits]
  all_goals first
  | omega
  | ring

structure StepProfile where

  basicGates : ℕ

  space : ℕ

  evolve : ℝ≥0∞

  classicalBits : ℕ

def StepProfile.zero : StepProfile := ⟨0, 0, 0, 0⟩

@[simp] theorem StepProfile.zero_basicGates : StepProfile.zero.basicGates = 0 := rfl

@[simp] theorem StepProfile.zero_space : StepProfile.zero.space = 0 := rfl

@[simp] theorem StepProfile.zero_evolve : StepProfile.zero.evolve = 0 := rfl

@[simp] theorem StepProfile.zero_classicalBits :
    StepProfile.zero.classicalBits = 0 := rfl

def ResourceCost.ofMacroStep (p : StepProfile) : ResourceCost :=
  ⟨0, 1, p.basicGates, 1, p.space, p.evolve, p.classicalBits⟩

def ResourceCost.ofOracleStep : ResourceCost := ⟨1, 0, 0, 1, 0, 0, 0⟩

@[simp] theorem ResourceCost.ofMacroStep_queries (p : StepProfile) :
    (ResourceCost.ofMacroStep p).queries = 0 := rfl

@[simp] theorem ResourceCost.ofMacroStep_macroGates (p : StepProfile) :
    (ResourceCost.ofMacroStep p).macroGates = 1 := rfl

@[simp] theorem ResourceCost.ofMacroStep_basicGates (p : StepProfile) :
    (ResourceCost.ofMacroStep p).basicGates = p.basicGates := rfl

@[simp] theorem ResourceCost.ofMacroStep_depth (p : StepProfile) :
    (ResourceCost.ofMacroStep p).depth = 1 := rfl

@[simp] theorem ResourceCost.ofMacroStep_peakSpace (p : StepProfile) :
    (ResourceCost.ofMacroStep p).peakSpace = p.space := rfl

@[simp] theorem ResourceCost.ofMacroStep_hamiltonianTime (p : StepProfile) :
    (ResourceCost.ofMacroStep p).hamiltonianTime = p.evolve := rfl

@[simp] theorem ResourceCost.ofMacroStep_classicalBits (p : StepProfile) :
    (ResourceCost.ofMacroStep p).classicalBits = p.classicalBits := rfl

@[simp] theorem ResourceCost.ofOracleStep_queries :
    ResourceCost.ofOracleStep.queries = 1 := rfl

@[simp] theorem ResourceCost.ofOracleStep_macroGates :
    ResourceCost.ofOracleStep.macroGates = 0 := rfl

@[simp] theorem ResourceCost.ofOracleStep_basicGates :
    ResourceCost.ofOracleStep.basicGates = 0 := rfl

@[simp] theorem ResourceCost.ofOracleStep_depth :
    ResourceCost.ofOracleStep.depth = 1 := rfl

@[simp] theorem ResourceCost.ofOracleStep_peakSpace :
    ResourceCost.ofOracleStep.peakSpace = 0 := rfl

@[simp] theorem ResourceCost.ofOracleStep_hamiltonianTime :
    ResourceCost.ofOracleStep.hamiltonianTime = 0 := rfl

@[simp] theorem ResourceCost.ofOracleStep_classicalBits :
    ResourceCost.ofOracleStep.classicalBits = 0 := rfl

def derive (κ : Matrix I I ℂ → StepProfile) : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I → ResourceCost
  | [] => 0
  | Step.gate U :: C => ResourceCost.ofMacroStep (κ U) + derive κ C
  | Step.query :: C => ResourceCost.ofOracleStep + derive κ C

@[simp] theorem derive_nil (κ : Matrix I I ℂ → StepProfile) : derive κ [] = 0 := rfl

@[simp] theorem derive_gate (κ : Matrix I I ℂ → StepProfile) (U : Matrix I I ℂ)
    (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    derive κ (Step.gate U :: C) = ResourceCost.ofMacroStep (κ U) + derive κ C := rfl

@[simp] theorem derive_query (κ : Matrix I I ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    derive κ (Step.query :: C) = ResourceCost.ofOracleStep + derive κ C := rfl

theorem derive_queries (κ : Matrix I I ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive κ C).queries = Qatlib.Foundations.QueryWordCore.Circuit.QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => simp [derive, ih]
    | query => simp [derive, ih, Nat.add_comm]

theorem derive_macroGates (κ : Matrix I I ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive κ C).macroGates = Qatlib.Foundations.QueryWordCore.Circuit.GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => simp [derive, ih, Nat.add_comm]
    | query => simp [derive, ih]

theorem derive_depth (κ : Matrix I I ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive κ C).depth = Qatlib.Foundations.QueryWordCore.Circuit.Size C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => simp [derive, ih, Nat.add_comm]
    | query => simp [derive, ih, Nat.add_comm]

theorem derive_zeroProfile (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive (fun _ => StepProfile.zero) C).classicalBits = 0 := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [derive, ih]

theorem derive_append (κ : Matrix I I ℂ → StepProfile) (C D : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    derive κ (C ++ D) = derive κ C + derive κ D := by
  induction C generalizing D with
  | nil => simp
  | cons s C ih =>
    cases s <;> simp only [List.cons_append, derive_gate, derive_query, ih,
      ResourceCost.add_assoc]

theorem seq_semantics_cost (κ : Matrix I I ℂ → StepProfile) (W : Matrix I I ℂ)
    (C D : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) (ψ : Qatlib.Foundations.PureStateMath.QState I) :
    Run W (C ++ D) ψ = Run W D (Run W C ψ) ∧
      derive κ (C ++ D) = derive κ C + derive κ D :=
  ⟨run_append W C D ψ, derive_append κ C D⟩

theorem seq_peakSpace (κ : Matrix I I ℂ → StepProfile) (C D : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive κ (C ++ D)).peakSpace
      = max (derive κ C).peakSpace (derive κ D).peakSpace := by
  rw [derive_append]; rfl

theorem seq_hamiltonianTime (κ : Matrix I I ℂ → StepProfile) (C D : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive κ (C ++ D)).hamiltonianTime
      = (derive κ C).hamiltonianTime + (derive κ D).hamiltonianTime := by
  rw [derive_append]; rfl

theorem peakSpace_seq_add_overestimates :
    ∃ (κ : Matrix Bool Bool ℂ → StepProfile) (C D : Qatlib.Foundations.QueryWordCore.Circuit.Circuit Bool),
      (derive κ (C ++ D)).peakSpace < (derive κ C).peakSpace + (derive κ D).peakSpace := by
  refine ⟨fun _ => ⟨0, 3, 0, 0⟩, [Step.gate 1], [Step.gate 1], ?_⟩
  simp only [List.cons_append, List.nil_append, derive_gate, derive_nil,
    ResourceCost.add_zero, ResourceCost.add_peakSpace,
    ResourceCost.ofMacroStep_peakSpace]
  decide

theorem cost_queries_zero_hamiltonianTime_pos :
    ∃ (κ : Matrix Bool Bool ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit Bool),
      (derive κ C).queries = 0 ∧ 0 < (derive κ C).hamiltonianTime := by
  refine ⟨fun _ => ⟨0, 0, 3, 0⟩, [Step.gate 1], rfl, ?_⟩
  norm_num [derive, ResourceCost.ofMacroStep_hamiltonianTime]

theorem cost_queries_pos_hamiltonianTime_zero :
    ∃ (κ : Matrix Bool Bool ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit Bool),
      (derive κ C).queries = 1 ∧ (derive κ C).hamiltonianTime = 0 := by
  refine ⟨fun _ => StepProfile.zero, [Step.query], ?_, ?_⟩ <;> simp [derive]

def repeatCost (r : ResourceCost) : ℕ → ResourceCost
  | 0 => 0
  | k + 1 => repeatCost r k + r

@[simp] theorem repeatCost_zero (r : ResourceCost) : repeatCost r 0 = 0 := rfl

@[simp] theorem repeatCost_succ (k : ℕ) (r : ResourceCost) :
    repeatCost r (k + 1) = repeatCost r k + r := rfl

theorem repeatCost_queries (k : ℕ) (r : ResourceCost) :
    (repeatCost r k).queries = k * r.queries := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, Nat.succ_mul]

theorem repeatCost_macroGates (k : ℕ) (r : ResourceCost) :
    (repeatCost r k).macroGates = k * r.macroGates := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, Nat.succ_mul]

theorem repeatCost_basicGates (k : ℕ) (r : ResourceCost) :
    (repeatCost r k).basicGates = k * r.basicGates := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, Nat.succ_mul]

theorem repeatCost_depth (k : ℕ) (r : ResourceCost) :
    (repeatCost r k).depth = k * r.depth := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, Nat.succ_mul]

theorem repeatCost_classicalBits (k : ℕ) (r : ResourceCost) :
    (repeatCost r k).classicalBits = k * r.classicalBits := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, Nat.succ_mul]

theorem repeatCost_hamiltonianTime (k : ℕ) (r : ResourceCost) :
    (repeatCost r k).hamiltonianTime = (k : ℝ≥0∞) * r.hamiltonianTime := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [repeatCost_succ, ResourceCost.add_hamiltonianTime, ih, Nat.cast_succ]
    ring

theorem repeatCost_peakSpace_le (k : ℕ) (r : ResourceCost) :
    (repeatCost r k).peakSpace ≤ r.peakSpace := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [repeatCost_succ, ResourceCost.add_peakSpace]
    exact max_le ih (le_refl _)

theorem repeatCost_succ_peakSpace (k : ℕ) (r : ResourceCost) :
    (repeatCost r (k + 1)).peakSpace = r.peakSpace := by
  rw [repeatCost_succ, ResourceCost.add_peakSpace]
  exact Nat.max_eq_right (repeatCost_peakSpace_le k r)

theorem run_repeatCircuit (W : Matrix I I ℂ) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) (k : ℕ) (ψ : Qatlib.Foundations.PureStateMath.QState I) :
    Run W (Qatlib.Foundations.QueryWordCore.Circuit.RepeatCircuit C k) ψ = (fun x => Run W C x)^[k] ψ := by
  induction k generalizing ψ with
  | zero => rfl
  | succ k ih => rw [Qatlib.Foundations.QueryWordCore.Circuit.RepeatCircuit, run_append, Function.iterate_succ]; exact ih _

theorem derive_repeatCircuit (κ : Matrix I I ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) (k : ℕ) :
    derive κ (Qatlib.Foundations.QueryWordCore.Circuit.RepeatCircuit C k) = repeatCost (derive κ C) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Qatlib.Foundations.QueryWordCore.Circuit.RepeatCircuit, derive_append, ih,
        ResourceCost.add_comm, repeatCost_succ]

theorem derive_repeatCircuit_queries (κ : Matrix I I ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I)
    (k : ℕ) : (derive κ (Qatlib.Foundations.QueryWordCore.Circuit.RepeatCircuit C k)).queries = k * Qatlib.Foundations.QueryWordCore.Circuit.QueryCount C := by
  rw [derive_repeatCircuit, repeatCost_queries, derive_queries]

theorem derive_repeatCircuit_peakSpace (κ : Matrix I I ℂ → StepProfile) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I)
    {k : ℕ} (hk : k ≠ 0) :
    (derive κ (Qatlib.Foundations.QueryWordCore.Circuit.RepeatCircuit C k)).peakSpace = (derive κ C).peakSpace := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [derive_repeatCircuit, repeatCost_succ_peakSpace]

inductive ParStep (I J : Type*) where

  | gates : Matrix I I ℂ → Matrix J J ℂ → ParStep I J

  | query : ParStep I J

abbrev ParCircuit (I J : Type*) := List (ParStep I J)

noncomputable def parToCircuit : ParCircuit I J → Qatlib.Foundations.QueryWordCore.Circuit.Circuit (I × J)
  | [] => []
  | ParStep.gates U V :: L => Step.gate (Qatlib.Foundations.PureStateMath.TensorGate U V) :: parToCircuit L
  | ParStep.query :: L => Step.query :: parToCircuit L

def parLeft : ParCircuit I J → Qatlib.Foundations.QueryWordCore.Circuit.Circuit I
  | [] => []
  | ParStep.gates U _ :: L => Step.gate U :: parLeft L
  | ParStep.query :: L => Step.query :: parLeft L

def parRight : ParCircuit I J → Qatlib.Foundations.QueryWordCore.Circuit.Circuit J
  | [] => []
  | ParStep.gates _ V :: L => Step.gate V :: parRight L
  | ParStep.query :: L => Step.query :: parRight L

@[simp] theorem parToCircuit_nil : parToCircuit ([] : ParCircuit I J) = [] := rfl

@[simp] theorem parLeft_nil : parLeft ([] : ParCircuit I J) = [] := rfl

@[simp] theorem parRight_nil : parRight ([] : ParCircuit I J) = [] := rfl

theorem parStep_gates_eq_mul_local (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    Qatlib.Foundations.PureStateMath.TensorGate U V = Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ) * Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix I I ℂ) V := by
  rw [Qatlib.Foundations.PureStateMath.tensorGate_mul, Matrix.mul_one, Matrix.one_mul]

theorem parLayer_local_commute (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.ActsOnLeft (Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ)) ∧
      Qatlib.Concepts.QueryComplexity.DegreeMethod.ActsOnRight (Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix I I ℂ) V) ∧
      Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ) * Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix I I ℂ) V
        = Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix I I ℂ) V * Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ) := by
  exact ⟨⟨U, rfl⟩, ⟨V, rfl⟩,
    Qatlib.Concepts.QueryComplexity.DegreeMethod.commute_actsOnLeft_actsOnRight ⟨U, rfl⟩ ⟨V, rfl⟩⟩

theorem parStep_gates_disjoint_certificate (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    ∃ WL WR : Matrix (I × J) (I × J) ℂ,
      Qatlib.Concepts.QueryComplexity.DegreeMethod.ActsOnLeft WL ∧ Qatlib.Concepts.QueryComplexity.DegreeMethod.ActsOnRight WR ∧
        WL * WR = Qatlib.Foundations.PureStateMath.TensorGate U V ∧ WR * WL = Qatlib.Foundations.PureStateMath.TensorGate U V := by
  refine ⟨Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ), Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix I I ℂ) V,
    ⟨U, rfl⟩, ⟨V, rfl⟩, (Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.parStep_gates_eq_mul_local U V).symm, ?_⟩
  exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.commute_actsOnLeft_actsOnRight ⟨U, rfl⟩ ⟨V, rfl⟩).symm.trans
    (Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.parStep_gates_eq_mul_local U V).symm

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

theorem size_parLeft (L : ParCircuit I J) : Qatlib.Foundations.QueryWordCore.Circuit.Size (parLeft L) = L.length := by
  induction L with
  | nil => rfl
  | cons l L ih => cases l <;> simp [parLeft, ih]

theorem size_parRight (L : ParCircuit I J) : Qatlib.Foundations.QueryWordCore.Circuit.Size (parRight L) = L.length := by
  induction L with
  | nil => rfl
  | cons l L ih => cases l <;> simp [parRight, ih]

theorem size_parToCircuit (L : ParCircuit I J) : Qatlib.Foundations.QueryWordCore.Circuit.Size (parToCircuit L) = L.length := by
  induction L with
  | nil => rfl
  | cons l L ih => cases l <;> simp [parToCircuit, ih]

theorem queryCount_parToCircuit_parLeft (L : ParCircuit I J) :
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (parToCircuit L) = Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (parLeft L) := by
  induction L with
  | nil => rfl
  | cons l L ih => cases l <;> simp [parToCircuit, parLeft, ih]

theorem gateCount_parToCircuit_parLeft (L : ParCircuit I J) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (parToCircuit L) = Qatlib.Foundations.QueryWordCore.Circuit.GateCount (parLeft L) := by
  induction L with
  | nil => rfl
  | cons l L ih => cases l <;> simp [parToCircuit, parLeft, ih]

theorem queryCount_parLeft_parRight (L : ParCircuit I J) :
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (parLeft L) = Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (parRight L) := by
  induction L with
  | nil => rfl
  | cons l L ih => cases l <;> simp [parLeft, parRight, ih]

def Circuit.ofGates (gs : List (Matrix I I ℂ)) :
    Qatlib.Foundations.QueryWordCore.Circuit.Circuit I := gs.map Step.gate

@[simp] theorem Circuit.ofGates_nil : Circuit.ofGates ([] : List (Matrix I I ℂ)) = [] := rfl

@[simp] theorem Circuit.ofGates_cons (U : Matrix I I ℂ) (gs : List (Matrix I I ℂ)) :
    Circuit.ofGates (U :: gs) = Step.gate U :: Circuit.ofGates gs := rfl

theorem Circuit.size_ofGates (gs : List (Matrix I I ℂ)) :
    Qatlib.Foundations.QueryWordCore.Circuit.Size (Circuit.ofGates gs) = gs.length := by
  simp [Circuit.ofGates, Qatlib.Foundations.QueryWordCore.Circuit.Size]

theorem Circuit.queryCount_ofGates (gs : List (Matrix I I ℂ)) :
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Circuit.ofGates gs) = 0 := by
  induction gs with
  | nil => rfl
  | cons U gs ih => rw [Circuit.ofGates_cons, Qatlib.Foundations.QueryWordCore.Circuit.queryCount_gate, ih]

theorem Circuit.gateCount_ofGates (gs : List (Matrix I I ℂ)) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Circuit.ofGates gs) = gs.length := by
  induction gs with
  | nil => rfl
  | cons U gs ih =>
    rw [Circuit.ofGates_cons, Qatlib.Foundations.QueryWordCore.Circuit.gateCount_gate, ih,
        List.length_cons]

def parOfGates : List (Matrix I I ℂ) → List (Matrix J J ℂ) → ParCircuit I J
  | [], [] => []
  | U :: gs, V :: hs => ParStep.gates U V :: parOfGates gs hs
  | U :: gs, [] => ParStep.gates U (1 : Matrix J J ℂ) :: parOfGates gs []
  | [], V :: hs => ParStep.gates (1 : Matrix I I ℂ) V :: parOfGates [] hs

@[simp] theorem parOfGates_nil_nil :
    parOfGates ([] : List (Matrix I I ℂ)) ([] : List (Matrix J J ℂ)) = [] := by
  simp only [parOfGates]

@[simp] theorem parOfGates_cons_cons (U : Matrix I I ℂ) (gs : List (Matrix I I ℂ))
    (V : Matrix J J ℂ) (hs : List (Matrix J J ℂ)) :
    parOfGates (U :: gs) (V :: hs) = ParStep.gates U V :: parOfGates gs hs := by
  simp only [parOfGates]

@[simp] theorem parOfGates_cons_nil (U : Matrix I I ℂ) (gs : List (Matrix I I ℂ)) :
    parOfGates (U :: gs) ([] : List (Matrix J J ℂ))
      = ParStep.gates U (1 : Matrix J J ℂ) :: parOfGates gs [] := by
  simp only [parOfGates]

@[simp] theorem parOfGates_nil_cons (V : Matrix J J ℂ) (hs : List (Matrix J J ℂ)) :
    parOfGates ([] : List (Matrix I I ℂ)) (V :: hs)
      = ParStep.gates (1 : Matrix I I ℂ) V :: parOfGates [] hs := by
  simp only [parOfGates]

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

def parGateStep (p q : StepProfile) : ResourceCost :=
  ⟨0, 1, p.basicGates + q.basicGates, 1, p.space + q.space, p.evolve + q.evolve,
    p.classicalBits + q.classicalBits⟩

@[simp] theorem parGateStep_queries (p q : StepProfile) :
    (parGateStep p q).queries = 0 := rfl

@[simp] theorem parGateStep_macroGates (p q : StepProfile) :
    (parGateStep p q).macroGates = 1 := rfl

@[simp] theorem parGateStep_basicGates (p q : StepProfile) :
    (parGateStep p q).basicGates = p.basicGates + q.basicGates := rfl

@[simp] theorem parGateStep_depth (p q : StepProfile) :
    (parGateStep p q).depth = 1 := rfl

@[simp] theorem parGateStep_peakSpace (p q : StepProfile) :
    (parGateStep p q).peakSpace = p.space + q.space := rfl

@[simp] theorem parGateStep_hamiltonianTime (p q : StepProfile) :
    (parGateStep p q).hamiltonianTime = p.evolve + q.evolve := rfl

@[simp] theorem parGateStep_classicalBits (p q : StepProfile) :
    (parGateStep p q).classicalBits = p.classicalBits + q.classicalBits := rfl

def derivePar (κI : Matrix I I ℂ → StepProfile) (κJ : Matrix J J ℂ → StepProfile) :
    ParCircuit I J → ResourceCost
  | [] => 0
  | ParStep.gates U V :: L => parGateStep (κI U) (κJ V) + derivePar κI κJ L
  | ParStep.query :: L => ResourceCost.ofOracleStep + derivePar κI κJ L

@[simp] theorem derivePar_nil (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) : derivePar κI κJ [] = 0 := rfl

@[simp] theorem derivePar_gates (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (U : Matrix I I ℂ) (V : Matrix J J ℂ)
    (L : ParCircuit I J) :
    derivePar κI κJ (ParStep.gates U V :: L)
      = parGateStep (κI U) (κJ V) + derivePar κI κJ L := rfl

@[simp] theorem derivePar_query (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (L : ParCircuit I J) :
    derivePar κI κJ (ParStep.query :: L)
      = ResourceCost.ofOracleStep + derivePar κI κJ L := rfl

theorem derivePar_queries (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (L : ParCircuit I J) :
    (derivePar κI κJ L).queries = Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (parToCircuit L) := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    cases l with
    | gates U V => simp [parToCircuit, derivePar, ih]
    | query => simp [parToCircuit, derivePar, ih, Nat.add_comm]

theorem derivePar_macroGates (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (L : ParCircuit I J) :
    (derivePar κI κJ L).macroGates = Qatlib.Foundations.QueryWordCore.Circuit.GateCount (parToCircuit L) := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    cases l with
    | gates U V => simp [parToCircuit, derivePar, ih, Nat.add_comm]
    | query => simp [parToCircuit, derivePar, ih]

theorem derivePar_depth (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (L : ParCircuit I J) :
    (derivePar κI κJ L).depth = L.length := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    cases l with
    | gates U V => simp [derivePar, ih, Nat.add_comm]
    | query => simp [derivePar, ih, Nat.add_comm]

theorem depth_par_eq_max (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (L : ParCircuit I J) :
    (derivePar κI κJ L).depth = max (Qatlib.Foundations.QueryWordCore.Circuit.Size (parLeft L)) (Qatlib.Foundations.QueryWordCore.Circuit.Size (parRight L)) := by
  rw [derivePar_depth, size_parLeft, size_parRight, Nat.max_self]

theorem depth_parOfGates (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (gs : List (Matrix I I ℂ))
    (hs : List (Matrix J J ℂ)) :
    (derivePar κI κJ (parOfGates gs hs)).depth
      = max (Qatlib.Foundations.QueryWordCore.Circuit.Size (Circuit.ofGates gs)) (Qatlib.Foundations.QueryWordCore.Circuit.Size (Circuit.ofGates hs)) := by
  rw [derivePar_depth, parOfGates_length, Circuit.size_ofGates, Circuit.size_ofGates]

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

theorem depth_par_lt_sum (κI : Matrix I I ℂ → StepProfile)
    (κJ : Matrix J J ℂ → StepProfile) (L : ParCircuit I J) (hL : L ≠ []) :
    (derivePar κI κJ L).depth < Qatlib.Foundations.QueryWordCore.Circuit.Size (parLeft L) + Qatlib.Foundations.QueryWordCore.Circuit.Size (parRight L) := by
  cases L with
  | nil => exact absurd rfl hL
  | cons l L' =>
    rw [derivePar_depth, size_parLeft, size_parRight, List.length_cons]
    omega

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

theorem derive_constant_gate_peakSpace (p : StepProfile) (U : Matrix I I ℂ)
    (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive (fun _ => p) (Step.gate U :: C)).peakSpace = p.space := by
  rw [derive_gate, ResourceCost.add_peakSpace, ResourceCost.ofMacroStep_peakSpace]
  exact Nat.max_eq_left (derive_constant_peakSpace_le p C)

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

structure GateCompilation (U : Matrix I I ℂ) where

  circuit : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I

  query_free : Qatlib.Foundations.QueryWordCore.Circuit.QueryCount circuit = 0

  semantics : ∀ (W : Matrix I I ℂ) (ψ : Qatlib.Foundations.PureStateMath.QState I), Run W circuit ψ = Qatlib.Foundations.PureStateMath.ApplyGate U ψ

structure GateCompiler (I : Type*) [Fintype I] [DecidableEq I] where

  compile : Matrix I I ℂ → Qatlib.Foundations.QueryWordCore.Circuit.Circuit I

  query_free : ∀ U, Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (compile U) = 0

  semantics : ∀ (U W : Matrix I I ℂ) (ψ : Qatlib.Foundations.PureStateMath.QState I), Run W (compile U) ψ = Qatlib.Foundations.PureStateMath.ApplyGate U ψ

def compileCircuit (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I → Qatlib.Foundations.QueryWordCore.Circuit.Circuit I
  | [] => []
  | Step.gate U :: C => c.compile U ++ compileCircuit c C
  | Step.query :: C => Step.query :: compileCircuit c C

@[simp] theorem compileCircuit_nil (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) : compileCircuit c [] = [] := rfl

@[simp] theorem compileCircuit_gate (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) (U : Matrix I I ℂ)
    (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    compileCircuit c (Step.gate U :: C) = c.compile U ++ compileCircuit c C := rfl

@[simp] theorem compileCircuit_query (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    compileCircuit c (Step.query :: C) = Step.query :: compileCircuit c C := rfl

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

theorem derive_compileCircuit_queries (κ : Matrix I I ℂ → StepProfile) (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I)
    (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive κ (compileCircuit c C)).queries = (derive κ C).queries := by
  rw [derive_queries, queryCount_compileCircuit, derive_queries]

theorem size_eq_gateCount_add_queryCount (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    Qatlib.Foundations.QueryWordCore.Circuit.Size C = Qatlib.Foundations.QueryWordCore.Circuit.GateCount C + Qatlib.Foundations.QueryWordCore.Circuit.QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp only [size_cons, Qatlib.Foundations.QueryWordCore.Circuit.gateCount_gate, gateCount_query, Qatlib.Foundations.QueryWordCore.Circuit.queryCount_gate,
      queryCount_query, ih] <;> omega

theorem gateCount_eq_size_of_queryFree {D : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I} (hD : Qatlib.Foundations.QueryWordCore.Circuit.QueryCount D = 0) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount D = Qatlib.Foundations.QueryWordCore.Circuit.Size D := by
  rw [size_eq_gateCount_add_queryCount, hD, Nat.add_zero]

def basicGateProfile (I : Type*) [Fintype I] [DecidableEq I] :
    Matrix I I ℂ → StepProfile := fun _ => ⟨1, 0, 0, 0⟩

theorem derive_basicGateProfile_basicGates (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive (basicGateProfile I) C).basicGates = Qatlib.Foundations.QueryWordCore.Circuit.GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => simp [derive, basicGateProfile, ih, Nat.add_comm]
    | query => simp [derive, ih]

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

def identityCompiler (I : Type*) [Fintype I] [DecidableEq I] : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I where
  compile U := [Step.gate U]
  query_free := fun _ => rfl
  semantics := fun _ _ _ => rfl

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

theorem basicGates_identityCompiler (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive (basicGateProfile I) (compileCircuit (identityCompiler I) C)).basicGates
      = Qatlib.Foundations.QueryWordCore.Circuit.GateCount C := by
  rw [compileCircuit_identityCompiler, derive_basicGateProfile_basicGates]

noncomputable def parLayerCompilation (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    GateCompilation (Qatlib.Foundations.PureStateMath.TensorGate U V) where
  circuit := [Step.gate (Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ)),
    Step.gate (Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix I I ℂ) V)]
  query_free := rfl
  semantics := by
    intro W ψ
    simp only [Qatlib.Foundations.QueryWordCore.Circuit.run_gate, Qatlib.Foundations.QueryWordCore.Circuit.run_nil, ← applyGate_mul, Qatlib.Foundations.PureStateMath.tensorGate_mul, Matrix.one_mul,
      Matrix.mul_one]

@[simp] theorem parLayerCompilation_size (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    Qatlib.Foundations.QueryWordCore.Circuit.Size (parLayerCompilation U V).circuit = 2 := rfl

theorem parLayerCompilation_macro_vs_basic (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    (derive (basicGateProfile (I × J)) [Step.gate (Qatlib.Foundations.PureStateMath.TensorGate U V)]).macroGates = 1 ∧
      (derive (basicGateProfile (I × J)) (parLayerCompilation U V).circuit).basicGates
        = 2 ∧ (1 : ℕ) ≠ 2 := by
  refine ⟨rfl, ?_, by decide⟩
  simp only [parLayerCompilation, derive_gate, derive_nil, ResourceCost.add_zero,
    basicGateProfile]
  rfl

def Circuit.UsesGateSet (G : Set (Matrix I I ℂ)) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) : Prop :=
  ∀ U, Step.gate U ∈ C → U ∈ G

@[simp] theorem Circuit.usesGateSet_nil (G : Set (Matrix I I ℂ)) :
    Circuit.UsesGateSet G [] := by
  intro U h
  simp at h

@[simp] theorem Circuit.usesGateSet_append (G : Set (Matrix I I ℂ)) (C D : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    Circuit.UsesGateSet G (C ++ D) ↔ Circuit.UsesGateSet G C ∧ Circuit.UsesGateSet G D := by
  constructor
  · intro h
    exact ⟨fun U hU => h U (List.mem_append.mpr (Or.inl hU)),
      fun U hU => h U (List.mem_append.mpr (Or.inr hU))⟩
  · rintro ⟨hC, hD⟩ U hU
    exact (List.mem_append.mp hU).elim (hC U) (hD U)

theorem Circuit.UsesGateSet.isUnitaryCircuit {G : Set (Matrix I I ℂ)} {C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I}
    (hC : Circuit.UsesGateSet G C) (hG : ∀ U ∈ G, U ∈ Matrix.unitaryGroup I ℂ) :
    IsUnitaryCircuit C := fun U hU => hG U (hC U hU)

def GateCompiler.UsesGateSetOn (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) (G : Set (Matrix I I ℂ))
    (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) : Prop :=
  ∀ U, Step.gate U ∈ C → Circuit.UsesGateSet G (c.compile U)

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

def GateCompiler.profile (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) : Matrix I I ℂ → StepProfile :=
  fun U => ⟨Qatlib.Foundations.QueryWordCore.Circuit.GateCount (c.compile U), 0, 0, 0⟩

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

theorem GateCompiler.profile_basicGates_add_queries (c : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.GateCompiler I) (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit I) :
    (derive c.profile C).basicGates + (derive c.profile C).queries
      = Qatlib.Foundations.QueryWordCore.Circuit.Size (compileCircuit c C) := by
  rw [c.profile_basicGates_eq, derive_queries, size_eq_gateCount_add_queryCount,
    queryCount_compileCircuit]

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

theorem GateCompilation.run_eq_self_of_gateCount_zero {U : Matrix I I ℂ}
    (c : GateCompilation U) (h : Qatlib.Foundations.QueryWordCore.Circuit.GateCount c.circuit = 0) (ψ : Qatlib.Foundations.PureStateMath.QState I) :
    Qatlib.Foundations.PureStateMath.ApplyGate U ψ = ψ := by
  have hs : Qatlib.Foundations.QueryWordCore.Circuit.Size c.circuit = 0 := by
    rw [size_eq_gateCount_add_queryCount, h, c.query_free]
  have hn : c.circuit = [] := List.length_eq_zero_iff.mp hs
  have he := c.semantics 1 ψ
  simpa only [hn, Qatlib.Foundations.QueryWordCore.Circuit.run_nil] using he.symm

theorem GateCompilation.gateCount_pos_of_changes_state {U : Matrix I I ℂ}
    (c : GateCompilation U) {ψ : Qatlib.Foundations.PureStateMath.QState I} (hψ : Qatlib.Foundations.PureStateMath.ApplyGate U ψ ≠ ψ) :
    0 < Qatlib.Foundations.QueryWordCore.Circuit.GateCount c.circuit := by
  by_contra h
  exact hψ (c.run_eq_self_of_gateCount_zero (Nat.eq_zero_of_not_pos h) ψ)

theorem parLayerCompilation_usesGateSet (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    Circuit.UsesGateSet
      ({Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ), Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix I I ℂ) V} :
        Set (Matrix (I × J) (I × J) ℂ))
      (parLayerCompilation U V).circuit := by
  intro A hA
  simp only [parLayerCompilation, List.mem_cons, List.not_mem_nil, or_false,
    Step.gate.injEq] at hA
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hA

def hamiltonianGateCount : List (HamiltonianQueryStep I) → ℕ
  | [] => 0
  | HamiltonianQueryStep.gate _ :: P => hamiltonianGateCount P + 1
  | HamiltonianQueryStep.evolve _ :: P => hamiltonianGateCount P

noncomputable def deriveHamiltonian (P : List (HamiltonianQueryStep I)) : ResourceCost :=
  ⟨HamiltonianQueryCount P, hamiltonianGateCount P, 0, P.length, 0,
    ENNReal.ofReal (HamiltonianEvolutionTime P), 0⟩

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

theorem hamiltonianEvolutionTime_append (P Q : List (HamiltonianQueryStep I)) :
    HamiltonianEvolutionTime (P ++ Q)
      = HamiltonianEvolutionTime P + HamiltonianEvolutionTime Q := by
  induction P with
  | nil => simp [HamiltonianEvolutionTime]
  | cons s P ih =>
    cases s <;> simp only [List.cons_append, HamiltonianEvolutionTime, ih]
    ring

theorem deriveHamiltonian_append (P Q : List (HamiltonianQueryStep I)) :
    deriveHamiltonian (P ++ Q) = deriveHamiltonian P + deriveHamiltonian Q := by
  have hP := hamiltonianEvolutionTime_nonneg P
  have hQ := hamiltonianEvolutionTime_nonneg Q
  ext <;> simp [deriveHamiltonian, hamiltonianQueryCount_append,
    hamiltonianGateCount_append, hamiltonianEvolutionTime_append,
    ENNReal.ofReal_add hP hQ, List.length_append]

theorem deriveHamiltonian_queries (P : List (HamiltonianQueryStep I)) :
    (deriveHamiltonian P).queries = HamiltonianQueryCount P := rfl

theorem deriveHamiltonian_evolve_queries_and_time (t : ℝ) (P : List (HamiltonianQueryStep I)) :
    (deriveHamiltonian (HamiltonianQueryStep.evolve t :: P)).queries
      = 1 + HamiltonianQueryCount P ∧
      (deriveHamiltonian (HamiltonianQueryStep.evolve t :: P)).hamiltonianTime
      = ENNReal.ofReal (|t| + HamiltonianEvolutionTime P) := by
  exact ⟨rfl, rfl⟩

end Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
