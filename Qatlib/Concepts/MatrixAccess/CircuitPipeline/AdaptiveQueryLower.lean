/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.MbqcFlow.FlowDecision.AdaptiveQueryLower
public import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitMixed
public import Qatlib.Concepts.AdversaryBounds.AdvDuality.VariableKrausStatistics
public import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.BlockEncoding.StateBlockEncoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.Execution.CircuitCompile
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.MatrixAccess.CircuitPipeline
open Matrix
open Qatlib.Concepts.MbqcFlow.FlowDecision.AdaptiveQueryLower

variable {n d : ℕ} {W : Type} [Fintype W] [DecidableEq W]

def refined (P : TniCircuit d) : VariableKrausCircuit d := compileInstrumentCircuit (toInstrument P)
def width (P : TniCircuit d) : ℕ := variableKrausWidth (refined P)+1

instance width_nonzero (P : TniCircuit d) : NeZero (width P) := ⟨by unfold width; omega⟩

/-- The refined Kraus circuit fits within the chosen workspace width. -/
theorem fits (P : TniCircuit d) : variableKrausFits (width P) (refined P) :=
  variableKraus_fits_of_width_le _ _ (Nat.le_add_right _ _)

def padded (P : TniCircuit d) : KrausCircuit d (width P) := padVariableKraus (width P) (refined P)

/-- Padding a well formed trace nonincreasing circuit produces a well formed Kraus circuit. -/
theorem padded_legal (P : TniCircuit d) (hP : tniWellFormed P) :
    krausCircuitWellFormed (padded P) :=
  padVariableKraus_wellFormed _ _ (fits P)
    (compileInstrumentCircuit_wellFormed _ (toInstrument_wellFormed P hP))

/-- Refinement preserves the query budget when the state dimension is nonzero. -/
theorem refined_budget_exact [NeZero d] (P : TniCircuit d) :
    variableKrausBudget (refined P) = tniBudget P := by
  induction P with
  | halt b => rfl
  | step action P ih =>
      cases action with
      | gate G => exact ih
      | query => exact congrArg (fun a : ℕ => a+1) ih
  | instrument s K hK next ih =>
      simp only [refined, toInstrument, compileInstrumentCircuit, variableKrausBudget, tniBudget]
      have hb (a : Fin (s+1)) :
          variableKrausBudget (compileInstrumentCircuit
            (Fin.cases (.halt false) (fun i => toInstrument (next i)) a)) =
              Fin.cases 0 (fun i => tniBudget (next i)) a :=
        Fin.cases rfl (fun i => ih i) a
      simp only [hb]
      let f : Fin (s+1) → ℕ := Fin.cases 0 (fun i => tniBudget (next i))
      change Finset.univ.sup (fun k => f (instrumentFineEquiv d (s+1) k).1) = Finset.univ.sup f
      apply le_antisymm
      · apply Finset.sup_le
        intro k _
        exact Finset.le_sup (f := f) (Finset.mem_univ _)
      · apply Finset.sup_le
        intro a _
        have h := Finset.le_sup
          (f := fun k => f (instrumentFineEquiv d (s+1) k).1)
          (Finset.mem_univ ((instrumentFineEquiv d (s+1)).symm (a, (0,0))))
        simpa only [Equiv.apply_symm_apply] using h

/-- Padding preserves the original query budget when the state dimension is nonzero. -/
theorem padded_budget_exact [NeZero d] (P : TniCircuit d) :
    krausCircuitBudget (padded P) = tniBudget P := by
  rw [padded, padVariableKraus_budget _ _ (fits P)]
  exact refined_budget_exact P

def layout {s : ℕ} (e : Fin d ≃ (Fin n × Bool) × W) :
    (Fin d × Fin s) ≃ (Fin n × Bool) × (W × Fin s) :=
  (Equiv.prodCongr e (Equiv.refl (Fin s))).trans (Equiv.prodAssoc _ _ _)

omit [Fintype W] in

/-- Extending and relabeling the bit oracle gives the bit oracle on the enlarged workspace. -/
theorem oracle_extend {s : ℕ} (e : Fin d ≃ (Fin n × Bool) × W) (f : Fin n → Bool) :
    relabelGate (layout (s := s) e)
      (TensorGate (relabelGate e.symm (workspaceBitOracle (W := W) f)) (1 : Operator s)) =
      workspaceBitOracle (W := W × Fin s) f := by
  ext x y
  change workspaceBitOracle (W := W) f (e (e.symm (x.1,x.2.1)))
      (e (e.symm (y.1,y.2.1))) * (1 : Operator s) x.2.2 y.2.2 = _
  simp only [Equiv.apply_symm_apply, workspaceBitOracle, TensorGate, Matrix.kronecker_apply,
    Matrix.one_apply]
  rcases x with ⟨a,w,r⟩
  rcases y with ⟨b,v,t⟩
  by_cases hw : w = v
  · subst v
    by_cases hr : r = t <;> simp [hr]
  · simp [hw]

def observed (e : Fin d ≃ (Fin n × Bool) × W) (P : TniCircuit d) (hP : tniWellFormed P) :
    ObservedCircuit ((Fin n × Bool) × (W × Fin (width P))) :=
  relabelObserved (layout e) (compileKrausCircuit (0 : Fin (width P)) (padded P) (padded_legal P hP))

/-- The observed circuit compiled from a well formed trace nonincreasing circuit is well formed. -/
theorem observed_legal (e : Fin d ≃ (Fin n × Bool) × W) (P : TniCircuit d) (hP : tniWellFormed P) :
    observedWellFormed (observed e P hP) :=
  relabelObserved_wellFormed _ _ (compileKrausCircuit_wellFormed _ _ _)

/-- The observed query depth equals the padded Kraus circuit budget. -/
theorem observed_budget (e : Fin d ≃ (Fin n × Bool) × W) (P : TniCircuit d) (hP : tniWellFormed P) :
    observedQueryDepth (observed e P hP) = krausCircuitBudget (padded P) := by
  rw [observedQueryDepth_eq_budget, observed, relabelObserved_budget, compileKrausCircuit_budget]

def nativeObserved (P : TniCircuit d) (hP : tniWellFormed P) :
    ObservedCircuit (Fin (d * width P)) :=
  relabelObserved finProdFinEquiv
    (compileKrausCircuit (0 : Fin (width P)) (padded P) (padded_legal P hP))

def originalRecord (P : TniCircuit d) (record : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  restoreTniRecord P (restoreInstrumentRecord (toInstrument P) (restoreVariableKrausRecord (refined P) record))

/-- The native observed simulation preserves event mass after translating its records to the
original records. -/
theorem native_event (O : Operator d) (P : TniCircuit d) (hP : tniWellFormed P)
    (rho : Operator d) (E : Bool → List (ℕ × ℕ) → Bool) :
    mixedObservedEventMass (relabelGate finProdFinEquiv (TensorGate O (1 : Operator (width P))))
      (nativeObserved P hP)
      (relabelGate finProdFinEquiv (TensorGate rho (outerProduct (Ket (0 : Fin (width P))))))
      (fun b rec => E b (originalRecord P rec)) = tniEventMass O P rho E := by
  calc
    _ = krausCircuitEventMass O (padded P) rho (fun b rec => E b (originalRecord P rec)) :=
      kraus_compiled_event finProdFinEquiv (0 : Fin (width P)) O (padded P) (padded_legal P hP) rho _
    _ = variableKrausEventMass O (refined P) rho
        (fun b rec => E b (restoreTniRecord P (restoreInstrumentRecord (toInstrument P) rec))) :=
      by
        simpa only [padded, originalRecord] using
          variableKraus_padding_event O (refined P) (width P) (fits P) rho
            (fun b rec => E b (restoreTniRecord P (restoreInstrumentRecord (toInstrument P) rec)))
    _ = instrumentCircuitEventMass O (toInstrument P) rho
        (fun b rec => E b (restoreTniRecord P rec)) :=
      instrumentCircuit_compile_event O (toInstrument P) rho (fun b rec => E b (restoreTniRecord P rec))
    _ = _ := toInstrument_event O P rho E

/-- The native observed simulation preserves the expected number of queries. -/
theorem native_expected (O : Operator d) (P : TniCircuit d) (hP : tniWellFormed P)
    (rho : Operator d) :
    mixedExpectedQueries (relabelGate finProdFinEquiv (TensorGate O (1 : Operator (width P))))
      (nativeObserved P hP)
      (relabelGate finProdFinEquiv (TensorGate rho (outerProduct (Ket (0 : Fin (width P)))))) =
      tniExpectedQueries O P rho := by
  calc
    _ = krausCircuitExpectedQueries O (padded P) rho :=
      kraus_compiled_expected finProdFinEquiv (0 : Fin (width P)) O (padded P) (padded_legal P hP) rho
    _ = variableKrausExpectedQueries O (refined P) rho :=
      variableKraus_padding_expected O (refined P) (width P) (fits P) rho
    _ = instrumentCircuitExpectedQueries O (toInstrument P) rho :=
      instrumentCircuit_compile_expected O (toInstrument P) rho
    _ = _ := toInstrument_expected O P rho

/-- A well formed trace nonincreasing circuit admits a unitary simulation with the same query
budget and amplitudes encoding its observed traces. -/
theorem exists_unitary_tni_trace_simulation_with_same_queries [Nonempty W] (e : Fin d ≃ (Fin n × Bool) × W)
    (P : TniCircuit d) (hP : tniWellFormed P) (hn : 0 < n) :
    ∃ (R : ℕ) (C : Circuit ((Fin n × Bool) × ((W × Fin (width P)) × Fin (R+1) × Bool))),
      IsUnitaryCircuit C ∧ QueryCount C = tniBudget P ∧
      ∀ (f : Fin n → Bool) (psi : QState ((Fin n × Bool) × (W × Fin (width P)))),
        let ts := observedTraces (workspaceBitOracle f) (observed e P hP) psi
        ts.length ≤ R+1 ∧ ∀ x,
          Run (workspaceBitOracle f) C (deferredObservedInput (R := R) psi) x =
            (ts.getD x.2.2.1.val (emptyObservedTrace _)).state (x.1,x.2.1) / Real.sqrt 2 := by
  have hd : d ≠ 0 := by
    intro hz
    have h := (e.symm ((⟨0,hn⟩,false), Classical.choice (inferInstance : Nonempty W))).isLt
    omega
  let : NeZero d := ⟨hd⟩
  obtain ⟨R,C,hC,hq,_,hr⟩ := observed_query_same_cost_full_branch_purification
    n (W × Fin (width P)) (observed e P hP) hn (observed_legal e P hP)
  exact ⟨R,C,hC,(hq.trans (observed_budget e P hP) |>.trans (padded_budget_exact P)),hr⟩
end Qatlib.Concepts.MatrixAccess.CircuitPipeline
