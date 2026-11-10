/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryModelComparison
import Mathlib.Tactic.Linarith
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

inductive ComparisonConvention where
  | exact
  | bounded
  | success
  | zeroErrorInconclusive (threshold : ℝ)
  deriving DecidableEq

def ConventionHolds (c : ComparisonConvention) (P : DecisionProgram I W)
    (f : (I → Bool) → Bool) : Prop :=
  match c with
  | .exact => P.ExactFor f
  | .bounded => P.BoundedFor f
  | .success => P.SuccessFor f
  | .zeroErrorInconclusive t => P.ZeroErrorInconclusiveFor f t

def ConventionStronger (c c' : ComparisonConvention) : Prop :=
  ∀ (P : DecisionProgram I W) (f : (I → Bool) → Bool),
    ConventionHolds c P f → ConventionHolds c' P f

def inconclusiveBudget : ℝ := 1 / 3

def zeroErrorBudget : ℝ := 0

def ConventionCountSet (M : MachineClass I W) (c : ComparisonConvention)
    (f : (I → Bool) → Bool) : Finset ℕ :=
  (M.programs.filter (fun P => decide (ConventionHolds c P f))).map
    (fun P => QueryCount P.circuit) |>.toFinset

noncomputable def ConventionMinQueries (M : MachineClass I W) (c : ComparisonConvention)
    (f : (I → Bool) → Bool) (h : ∃ n, n ∈ ConventionCountSet M c f) : ℕ :=
  finsetMinNat (ConventionCountSet M c f) h

inductive ClassicalConvention where
  | success (threshold : ℝ≥0∞)
  | zeroError
  | zeroErrorInconclusive (threshold : ℝ≥0∞)
  deriving DecidableEq

def ClassicalConventionHolds (c : ClassicalConvention) (prog : ClassicalProgram I Bool)
    (f : (I → Bool) → Bool) : Prop :=
  match c with
  | .success t => prog.ComputesWithSuccess f t
  | .zeroError => prog.ComputesZeroError f
  | .zeroErrorInconclusive t => prog.ComputesZeroErrorInconclusive f t

def ClassicalConventionStronger (c c' : ClassicalConvention) : Prop :=
  ∀ (prog : ClassicalProgram I Bool) (f : (I → Bool) → Bool),
    ClassicalConventionHolds c prog f → ClassicalConventionHolds c' prog f

structure SearchInstance (N : ℕ) where
  marked : Finset (Fin N)
  solutions : ℕ
  card_marked : marked.card = solutions

structure SearchProgram (N : ℕ) (W : Type) where
  circuit : Circuit (PolynomialWorkspace (Fin N) W)
  initial : QState (PolynomialWorkspace (Fin N) W)
  decode : W → Option (Fin N)

noncomputable def SearchProgram.successProb {N : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (P : SearchProgram N W) (g : Fin N → Bool) (S : Finset (Fin N)) : ℝ :=
  MeasureProb (Run (TensorGate (BitOracleOn g) (1 : Matrix W W ℂ)) P.circuit P.initial)
    {z | ∃ j, z.2 = j ∧ ∃ i, P.decode j = some i ∧ i ∈ S}

def markedCount {N : ℕ} (g : Fin N → Bool) : ℕ :=
  (Finset.univ.filter (fun i => g i = true)).card

def SearchProgram.queryCount {N : ℕ} {W : Type} (P : SearchProgram N W) : ℕ :=
  QueryCount P.circuit

structure SearchClass (N : ℕ) (W : Type) where
  programs : List (SearchProgram N W)
  nonempty : programs ≠ []

def SearchClass.realizedCountSet {N : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : SearchClass N W) (inst : SearchInstance N) (threshold : ℝ) : Finset ℕ :=
  let filtered : List (SearchProgram N W) :=
    C.programs.filter (fun (P : SearchProgram N W) =>
      decide (threshold ≤ P.successProb (fun i => decide (i ∈ inst.marked)) inst.marked))
  (filtered.map (fun (P : SearchProgram N W) => QueryCount P.circuit)).toFinset

noncomputable def SearchClass.minSearchQueries {N : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : SearchClass N W) (inst : SearchInstance N) (threshold : ℝ)
    (h : ∃ k, k ∈ C.realizedCountSet inst threshold) : ℕ :=
  finsetMinNat (C.realizedCountSet inst threshold) h

end Qatlib.Concepts.QueryComplexity.DegreeMethod
