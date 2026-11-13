/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.FreshSignalWordBridge

/-!
# Coherent fresh-register oracle words

The `synchronizeWords` construction combines families of adjoint oracle words with a common
instruction shape into a single selected circuit. The resulting `coherentFreshLCUWord` encodes
weighted ordered products and padded Taylor sums, with explicit query and gate counts. These
results support the contour-based algorithms of [WangEtAl2026].

## Main statements

* `synchronizeWords_evaluate`: identifies synchronized evaluation with branchwise selection.
* `coherent_fresh_padded_lcu_counted`: constructs an exact Taylor LCU encoding of scale two
  using `K` queries.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SharedAncilla.AncillaProduct
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.CoherentSim.TaylorEncoding

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator

/-- Records whether an adjoint instruction is a gate, a forward query, or a backward query. -/
def oracleStepShape {H : Type} : AdjointStep H → Option Bool
  | .gate _ => none
  | .forward => some true
  | .backward => some false

/-- Maps an adjoint circuit to its sequence of gate and query tags, discarding the gate
matrices. -/
def oracleWordShape {H : Type} (cs : List (AdjointStep H)) : List (Option Bool) :=
  cs.map oracleStepShape

/-- Returns the leading gate matrix of a word, or the identity when its head is not a gate. -/
def wordHeadGate {H : Type} [DecidableEq H] : List (AdjointStep H) → Matrix H H ℂ
  | .gate V :: _ => V
  | _ => 1

/-- Uses the head gate of `ds` when `c` is a gate and otherwise retains the query direction of
`c`. -/
def alignedHead {H : Type} [DecidableEq H] (c : AdjointStep H)
    (ds : List (AdjointStep H)) : AdjointStep H :=
  match c with
  | .gate _ => .gate (wordHeadGate ds)
  | .forward => .forward
  | .backward => .backward

/-- Forms a selected head gate across the label register, or retains the query direction of the
template instruction. -/
def synchronizedHead {L H : Type} [DecidableEq L] [DecidableEq H]
    (c : AdjointStep H) (ds : L → List (AdjointStep H)) : AdjointStep (L × H) :=
  match c with
  | .gate _ => .gate (select (fun l => wordHeadGate (ds l)))
  | .forward => .forward
  | .backward => .backward

/-- Synchronizes a label-indexed family of words according to a template, selecting their gates
and sharing the template's query instructions. -/
def synchronizeWords {L H : Type} [DecidableEq L] [DecidableEq H] :
    List (AdjointStep H) → (L → List (AdjointStep H)) → List (AdjointStep (L × H))
  | [], _ => []
  | c :: cs, ds => synchronizedHead c ds :: synchronizeWords cs (fun l => (ds l).tail)

/-- Taking the tail of a word commutes with extracting its instruction shape. -/
private theorem oracleWordShape_tail {H : Type} (ds : List (AdjointStep H)) :
    oracleWordShape ds.tail = (oracleWordShape ds).tail := by
  cases ds <;> rfl

/-- A word with empty instruction shape is empty. -/
private theorem oracleWordShape_nil {H : Type} (ds : List (AdjointStep H))
    (h : oracleWordShape ds = []) : ds = [] := by
  exact List.map_eq_nil_iff.mp h

section Synchronize
variable {L H : Type} [Fintype L] [DecidableEq L] [Fintype H] [DecidableEq H]

omit [Fintype L] [DecidableEq L] in

/-- For words with matching instruction shape, evaluation factors into the aligned head matrix
followed by evaluation of the tail. -/
private theorem evaluate_alignedHead (U : Matrix H H ℂ) (c : AdjointStep H)
    (cs ds : List (AdjointStep H)) (h : oracleWordShape ds = oracleWordShape (c :: cs)) :
    evaluate U ds = instructionMatrix U (alignedHead c ds) * evaluate U ds.tail := by
  cases ds with
  | nil => simp [oracleWordShape] at h
  | cons d ds =>
    cases c <;> cases d <;>
      simp_all [oracleWordShape, oracleStepShape, alignedHead, wordHeadGate, evaluate]

omit [Fintype L] [Fintype H] in

/-- The matrix of a synchronized head is the selected family of aligned head matrices. -/
private theorem instructionMatrix_synchronizedHead (U : Matrix H H ℂ)
    (c : AdjointStep H) (ds : L → List (AdjointStep H)) :
    instructionMatrix (parallelOracle (J := L) U) (synchronizedHead c ds) =
      select (fun l => instructionMatrix U (alignedHead c (ds l))) := by
  cases c <;> simp [synchronizedHead, alignedHead, instructionMatrix,
    parallelOracle, parallel_select_adjoint]

/-- Synchronizing words of the same instruction shape evaluates to the selected family of their
evaluations. -/
theorem synchronizeWords_evaluate (U : Matrix H H ℂ) (cs : List (AdjointStep H))
    (ds : L → List (AdjointStep H))
    (hshape : ∀ l, oracleWordShape (ds l) = oracleWordShape cs) :
    evaluate (parallelOracle (J := L) U) (synchronizeWords cs ds) =
      select (fun l => evaluate U (ds l)) := by
  induction cs generalizing ds with
  | nil =>
    have hd : ∀ l, ds l = [] := fun l => oracleWordShape_nil _ (hshape l)
    simp [synchronizeWords, hd, evaluate, parallel_select_one]
  | cons c cs ih =>
    have ht : ∀ l, oracleWordShape (ds l).tail = oracleWordShape cs := by
      intro l
      rw [oracleWordShape_tail, hshape l]
      rfl
    rw [synchronizeWords, evaluate, instructionMatrix_synchronizedHead, ih _ ht,
      parallel_select_mul]
    congr 1
    funext l
    exact (evaluate_alignedHead U c cs (ds l) (hshape l)).symm

omit [Fintype L] [Fintype H] in

/-- Synchronization preserves the template's query count and gate count. -/
theorem synchronizeWords_cost (cs : List (AdjointStep H))
    (ds : L → List (AdjointStep H)) :
    adjointQueryCount (synchronizeWords cs ds) = adjointQueryCount cs ∧
    adjointGateCount (synchronizeWords cs ds) = adjointGateCount cs := by
  induction cs generalizing ds with
  | nil => exact ⟨rfl, rfl⟩
  | cons c cs ih =>
    cases c <;> simp [synchronizeWords, synchronizedHead, adjointQueryCount,
      adjointGateCount, (ih (fun l => (ds l).tail)).1, (ih (fun l => (ds l).tail)).2]

omit [Fintype L] [DecidableEq L] in

/-- The tail of a well-formed adjoint circuit is well formed. -/
private theorem wellFormed_tail (cs : List (AdjointStep H))
    (hcs : WellFormedAdjointCircuit cs) : WellFormedAdjointCircuit cs.tail := by
  cases cs with
  | nil => exact hcs
  | cons c cs => exact ((Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.cons_iff c cs).mp hcs).2

omit [Fintype L] [DecidableEq L] in

/-- The leading gate, with identity as the default, is unitary for a well-formed word. -/
private theorem wordHeadGate_unitary (cs : List (AdjointStep H))
    (hcs : WellFormedAdjointCircuit cs) : wordHeadGate cs ∈ Matrix.unitaryGroup H ℂ := by
  cases cs with
  | nil => exact (Matrix.unitaryGroup H ℂ).one_mem
  | cons c cs =>
    cases c with
    | gate V => exact (Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff V cs).mp hcs |>.1
    | forward => exact (Matrix.unitaryGroup H ℂ).one_mem
    | backward => exact (Matrix.unitaryGroup H ℂ).one_mem

/-- Synchronizing a family of well-formed words produces a well-formed adjoint circuit. -/
theorem synchronizeWords_wellFormed (cs : List (AdjointStep H))
    (ds : L → List (AdjointStep H)) (hds : ∀ l, WellFormedAdjointCircuit (ds l)) :
    WellFormedAdjointCircuit (synchronizeWords cs ds) := by
  induction cs generalizing ds with
  | nil => exact Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil
  | cons c cs ih =>
    have ht := ih (fun l => (ds l).tail) (fun l => wellFormed_tail _ (hds l))
    cases c <;> simp only [synchronizeWords, synchronizedHead,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.backward_cons_iff]
    · exact ⟨select_unitary _ (fun l => wordHeadGate_unitary _ (hds l)), ht⟩
    · exact ht
    · exact ht

end Synchronize

/-- The instruction shape of concatenated words is the concatenation of their instruction
shapes. -/
private theorem oracleWordShape_append {H : Type} (cs ds : List (AdjointStep H)) :
    oracleWordShape (cs ++ ds) = oracleWordShape cs ++ oracleWordShape ds :=
  List.map_append

/-- Reindexing an adjoint word preserves its instruction shape. -/
private theorem oracleWordShape_reindex {H K : Type} (e : K ≃ H)
    (cs : List (AdjointStep H)) :
    oracleWordShape (reindexAdjointWord e cs) = oracleWordShape cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> simp [oracleWordShape, reindexAdjointWord, reindexAdjointStep,
      oracleStepShape] at ih ⊢ <;> exact ih

/-- Adding a spectator register preserves the instruction shape of an adjoint word. -/
private theorem oracleWordShape_spectator {H K : Type} [DecidableEq K]
    (cs : List (AdjointStep H)) :
    oracleWordShape (spectatorLiftWord K cs) = oracleWordShape cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> simp [oracleWordShape, spectatorLiftWord, spectatorLiftStep,
      oracleStepShape] at ih ⊢ <;> exact ih

section Fresh
variable {A J I L : Type} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
  [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

omit [Fintype A] [Fintype J] [Fintype I] [Fintype L] [DecidableEq L] in

/-- Fresh-query words of the same length have the same instruction shape, independently of their
branch choices. -/
theorem freshQueryWord_shape (j₀ : J) (n : ℕ) (cs ds : Fin n → Bool × J) :
    oracleWordShape (freshQueryWord (A := A) (I := I) j₀ n cs) =
      oracleWordShape (freshQueryWord (A := A) (I := I) j₀ n ds) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [freshQueryWord, oracleWordShape_append, freshTailWord,
      oracleWordShape_reindex, oracleWordShape_spectator,
      ih (fun k => cs k.succ) (fun k => ds k.succ)]
    rfl

/-- Synchronizes the fresh-query words specified by a label-indexed family of choices. -/
def coherentFreshWord (j₀ : J) (n : ℕ) (choices : L → Fin n → Bool × J) :
    List (AdjointStep (L × FreshQueryWorkspace A J I n)) :=
  synchronizeWords (freshQueryWord j₀ n (fun _ => (false, j₀)))
    (fun l => freshQueryWord j₀ n (choices l))

/-- The coherent fresh word evaluates to the selected family of fresh-query word evaluations. -/
theorem coherentFreshWord_evaluate (j₀ : J) (n : ℕ)
    (choices : L → Fin n → Bool × J) (U : J → Matrix (A × I) (A × I) ℂ) :
    evaluate (parallelOracle (J := L) (freshPrimitiveQuery n U))
      (coherentFreshWord j₀ n choices) =
      select (fun l => evaluate (freshPrimitiveQuery n U) (freshQueryWord j₀ n (choices l))) :=
  synchronizeWords_evaluate _ _ _ (fun l => freshQueryWord_shape (A := A) (I := I) j₀ n (choices l) _)

omit [Fintype A] [Fintype J] [Fintype I] [Fintype L] in

/-- A coherent fresh word of length `n` uses exactly `n` queries and `2 * n` gates. -/
theorem coherentFreshWord_cost (j₀ : J) (n : ℕ) (choices : L → Fin n → Bool × J) :
    adjointQueryCount (coherentFreshWord (A := A) (I := I) j₀ n choices) = n ∧
    adjointGateCount (coherentFreshWord (A := A) (I := I) j₀ n choices) = 2 * n := by
  simpa only [coherentFreshWord, (synchronizeWords_cost _ _).1,
    (synchronizeWords_cost _ _).2] using!
    freshQueryWord_cost (A := A) (I := I) j₀ n (fun _ => (false, j₀))

/-- Every coherent fresh word is a well-formed adjoint circuit. -/
theorem coherentFreshWord_wellFormed (j₀ : J) (n : ℕ)
    (choices : L → Fin n → Bool × J) :
    WellFormedAdjointCircuit (coherentFreshWord (A := A) (I := I) j₀ n choices) :=
  synchronizeWords_wellFormed _ _ (fun l => freshQueryWord_wellFormed j₀ n (choices l))

/-- Adds coefficient preparation and phase gates to a coherent fresh word to form an LCU
circuit. -/
def coherentFreshLCUWord (j₀ : J) (l₀ : L) (n : ℕ)
    (choices : L → Fin n → Bool × J) (c : L → ℂ) :
    List (AdjointStep (L × FreshQueryWorkspace A J I n)) :=
  [.gate (prepareRegister (I := FreshQueryWorkspace A J I n) (coefficientPrepare c l₀))ᴴ,
   .gate (select (phaseAbsorbed c
      (fun _ => (1 : Matrix (FreshQueryWorkspace A J I n) (FreshQueryWorkspace A J I n) ℂ))))] ++
    coherentFreshWord j₀ n choices ++
  [.gate (prepareRegister (I := FreshQueryWorkspace A J I n) (coefficientPrepare c l₀))]

/-- The coherent fresh LCU word evaluates to the coefficient LCU unitary of the branch
evaluations. -/
theorem coherentFreshLCUWord_evaluate (j₀ : J) (l₀ : L) (n : ℕ)
    (choices : L → Fin n → Bool × J) (c : L → ℂ)
    (U : J → Matrix (A × I) (A × I) ℂ) :
    evaluate (parallelOracle (J := L) (freshPrimitiveQuery n U))
      (coherentFreshLCUWord j₀ l₀ n choices c) =
      coefficientLCUUnitary c
        (fun l => evaluate (freshPrimitiveQuery n U) (freshQueryWord j₀ n (choices l))) l₀ := by
  have hp : select (phaseAbsorbed c
      (fun _ => (1 : Matrix (FreshQueryWorkspace A J I n) (FreshQueryWorkspace A J I n) ℂ))) *
      select (fun l => evaluate (freshPrimitiveQuery n U) (freshQueryWord j₀ n (choices l))) =
    select (phaseAbsorbed c
      (fun l => evaluate (freshPrimitiveQuery n U) (freshQueryWord j₀ n (choices l)))) := by
    rw [parallel_select_mul]
    congr 1
    funext l
    simp [phaseAbsorbed]
  simp only [coherentFreshLCUWord, evaluate_append, evaluate, instructionMatrix,
    Matrix.mul_one, coherentFreshWord_evaluate]
  unfold coefficientLCUUnitary
  simp only [Matrix.mul_assoc] at hp ⊢
  rw [← Matrix.mul_assoc (select _) (select _) (prepareRegister _), hp]

omit [Fintype A] [Fintype J] [Fintype I] in

/-- The coherent fresh LCU word uses exactly `n` queries and `2 * n + 3` gates. -/
theorem coherentFreshLCUWord_cost (j₀ : J) (l₀ : L) (n : ℕ)
    (choices : L → Fin n → Bool × J) (c : L → ℂ) :
    adjointQueryCount (coherentFreshLCUWord (A := A) (I := I) j₀ l₀ n choices c) = n ∧
    adjointGateCount (coherentFreshLCUWord (A := A) (I := I) j₀ l₀ n choices c) = 2 * n + 3 := by
  obtain ⟨hq, hg⟩ := coherentFreshWord_cost (A := A) (I := I) j₀ n choices
  simp [coherentFreshLCUWord, adjointQueryCount_append, adjointGateCount_append,
    adjointQueryCount, adjointGateCount, hq, hg]

/-- Positive coefficient mass makes the coherent fresh LCU word well formed. -/
theorem coherentFreshLCUWord_wellFormed (j₀ : J) (l₀ : L) (n : ℕ)
    (choices : L → Fin n → Bool × J) (c : L → ℂ) (hc : 0 < coefficientMass c) :
    WellFormedAdjointCircuit (coherentFreshLCUWord (A := A) (I := I) j₀ l₀ n choices c) := by
  have hp := prepareRegister_unitary (I := FreshQueryWorkspace A J I n)
    (coefficientPrepare_unitary c l₀ hc)
  have hd := select_unitary _ (phaseAbsorbed_unitary c
    (fun _ => (1 : Matrix (FreshQueryWorkspace A J I n) (FreshQueryWorkspace A J I n) ℂ))
    (fun _ => (Matrix.unitaryGroup _ ℂ).one_mem))
  apply Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append
  · apply Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append
    · simp only [Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
        Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
      exact ⟨adjoint_unitary hp, hd⟩
    · exact coherentFreshWord_wellFormed j₀ n choices
  · simpa using! hp

/-- Exact projected unitary encodings yield an exact encoding of the weighted ordered block
products, normalized by the coefficient mass. -/
theorem coherentFreshLCUWord_blockEncoding (j₀ : J) (l₀ : L) (a₀ : A) (n : ℕ)
    (choices : L → Fin n → Bool × J) (c : L → ℂ) (B : J → Matrix I I ℂ)
    (U : J → Matrix (A × I) (A × I) ℂ)
    (hc : 0 < coefficientMass c)
    (henc : ∀ j, ProjectedUnitaryEncoding (B j) (U j) (encodingFiber a₀) (encodingFiber a₀)) :
    BlockEncoding
      (∑ l, c l • orderedBlockProduct n (fun k => if (choices l k).1 then B (choices l k).2 else 1))
      (evaluate (parallelOracle (J := L) (freshPrimitiveQuery n U))
        (coherentFreshLCUWord j₀ l₀ n choices c))
      (tagFrame l₀ (freshWordFrame j₀ a₀ n)) (tagFrame l₀ (freshWordFrame j₀ a₀ n))
      (coefficientMass c) 0 := by
  rw [coherentFreshLCUWord_evaluate]
  have hs : scaledLCUCoefficients c (fun _ : L => (1 : ℝ)) = c := by
    funext l
    simp [scaledLCUCoefficients]
  have h := scaled_approximate_lcu_encoding
    (J := L) (H := FreshQueryWorkspace A J I n) (O := I) (I := I) l₀
    (fun l => orderedBlockProduct n (fun k => if (choices l k).1 then B (choices l k).2 else 1))
    (fun l => evaluate (freshPrimitiveQuery n U) (freshQueryWord j₀ n (choices l)))
    (freshWordFrame j₀ a₀ n) (freshWordFrame j₀ a₀ n) c (fun _ => 1) (fun _ => 0)
    (fun l => (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding (freshQueryWord_projectedEncoding j₀ a₀ n (choices l) B U henc)))
    (by rw [hs]; exact hc)
  rw [hs] at h
  simpa only [mul_one, mul_zero, Finset.sum_const_zero, coefficientMass] using! h

/-- Combines well-formedness, primitive-oracle unitarity, and exact LCU block encoding with the
counts `n` queries and `2 * n + 3` gates [WangEtAl2026]. -/
theorem coherent_fresh_lcu_counted (j₀ : J) (l₀ : L) (a₀ : A) (n : ℕ)
    (choices : L → Fin n → Bool × J) (c : L → ℂ) (B : J → Matrix I I ℂ)
    (U : J → Matrix (A × I) (A × I) ℂ) (hc : 0 < coefficientMass c)
    (henc : ∀ j, ProjectedUnitaryEncoding (B j) (U j) (encodingFiber a₀) (encodingFiber a₀)) :
    WellFormedAdjointCircuit (coherentFreshLCUWord (A := A) (I := I) j₀ l₀ n choices c) ∧
    parallelOracle (J := L) (freshPrimitiveQuery n U) ∈
      Matrix.unitaryGroup (L × FreshQueryWorkspace A J I n) ℂ ∧
    BlockEncoding
      (∑ l, c l • orderedBlockProduct n (fun k => if (choices l k).1 then B (choices l k).2 else 1))
      (evaluate (parallelOracle (J := L) (freshPrimitiveQuery n U))
        (coherentFreshLCUWord j₀ l₀ n choices c))
      (tagFrame l₀ (freshWordFrame j₀ a₀ n)) (tagFrame l₀ (freshWordFrame j₀ a₀ n))
      (coefficientMass c) 0 ∧
    adjointQueryCount (coherentFreshLCUWord (A := A) (I := I) j₀ l₀ n choices c) = n ∧
    adjointGateCount (coherentFreshLCUWord (A := A) (I := I) j₀ l₀ n choices c) = 2 * n + 3 :=
  ⟨coherentFreshLCUWord_wellFormed j₀ l₀ n choices c hc,
    select_unitary _ (fun _ => freshPrimitiveQuery_unitary n U (fun j => (henc j).unitary)),
    coherentFreshLCUWord_blockEncoding j₀ l₀ a₀ n choices c B U hc henc,
    coherentFreshLCUWord_cost j₀ l₀ n choices c⟩

end Fresh

section Routed
variable {A J I : Type} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
  [Fintype I] [DecidableEq I]

private instance routedFreshWorkspaceDecEq (K : ℕ) :
    DecidableEq (FreshQueryWorkspace A J I K) :=
  @instDecidableEqProd (FreshSignals A K) (Bool × (J × (A × I)))
    (freshSignalsDecidableEq A K) inferInstance

private instance routedFreshLabelWorkspaceDecEq (K : ℕ) :
    DecidableEq (TaylorWordLabel J K × FreshQueryWorkspace A J I K) :=
  @instDecidableEqProd (TaylorWordLabel J K) (FreshQueryWorkspace A J I K)
    inferInstance (routedFreshWorkspaceDecEq K)

/-- Routes a Taylor label to its activity flag and oracle index, using an inactive default for
padding labels. -/
def routedFreshChoiceAt (j₀ : J) (K : ℕ) (w : TaylorWordLabel J K) (j : Fin K) : Bool × J :=
  match w with
  | .inl w => (taylorActive w j, taylorWordAt j₀ w j)
  | .inr _ => (false, j₀)

/-- Lists routed fresh-register choices in descending position order for the first `n` Taylor
positions. -/
def routedFreshChoices (j₀ : J) (K : ℕ) : (n : ℕ) → n ≤ K →
    TaylorWordLabel J K → Fin n → Bool × J
  | 0, _, _ => fun j => Fin.elim0 j
  | n + 1, hn, w => Fin.cons
      (routedFreshChoiceAt j₀ K w ⟨n, Nat.lt_of_succ_le hn⟩)
      (routedFreshChoices j₀ K n (Nat.le_of_succ_le hn) w)

omit [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J] [Fintype I] in

/-- The matrix selected by a routed fresh choice equals the corresponding Taylor branch step. -/
private theorem routedFreshChoiceAt_step (j₀ : J) (K : ℕ)
    (w : TaylorWordLabel J K) (j : Fin K) (B : J → Matrix I I ℂ) :
    (if (routedFreshChoiceAt j₀ K w j).1 then B (routedFreshChoiceAt j₀ K w j).2 else 1) =
      taylorBranchStep B j w := by
  cases w with
  | inl w =>
    by_cases hj : j.val < w.1.val <;>
      simp [routedFreshChoiceAt, taylorActive, taylorWordAt, taylorBranchStep, hj]
  | inr b => simp [routedFreshChoiceAt, taylorBranchStep]

omit [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J] in

/-- The ordered product of routed fresh choices equals the corresponding Taylor branch word. -/
theorem orderedBlockProduct_routedFreshChoices (j₀ : J) (K n : ℕ) (hn : n ≤ K)
    (w : TaylorWordLabel J K) (B : J → Matrix I I ℂ) :
    orderedBlockProduct n (fun j => if (routedFreshChoices j₀ K n hn w j).1
      then B (routedFreshChoices j₀ K n hn w j).2 else 1) = taylorBranchWord B K n hn w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [orderedBlockProduct, routedFreshChoices, Fin.cons_zero, Fin.cons_succ,
      routedFreshChoiceAt_step, ih, taylorBranchWord]

/-- Taylor coefficients of mass at most two yield an exact block encoding of scale two, using
`K` queries and `2 * K + 3` gates [WangEtAl2026]. -/
theorem coherent_fresh_padded_lcu_counted (j₀ : J) (a₀ : A) (K : ℕ)
    (a : (Σ l : Fin (K + 1), Fin l.val → J) → ℂ) (B : J → Matrix I I ℂ)
    (U : J → Matrix (A × I) (A × I) ℂ) (ha : coefficientMass a ≤ 2)
    (henc : ∀ j, ProjectedUnitaryEncoding (B j) (U j) (encodingFiber a₀) (encodingFiber a₀)) :
    WellFormedAdjointCircuit
      (coherentFreshLCUWord (A := A) (I := I) j₀ (taylorEmptyLabel J K) K
        (routedFreshChoices j₀ K K le_rfl) (routedPaddedCoefficients K a)) ∧
    parallelOracle (J := TaylorWordLabel J K) (freshPrimitiveQuery K U) ∈
      Matrix.unitaryGroup (TaylorWordLabel J K × FreshQueryWorkspace A J I K) ℂ ∧
    BlockEncoding
      (∑ w : (Σ l : Fin (K + 1), Fin l.val → J), a w • taylorBranchWord B K K le_rfl (.inl w))
      (evaluate (parallelOracle (J := TaylorWordLabel J K) (freshPrimitiveQuery K U))
        (coherentFreshLCUWord j₀ (taylorEmptyLabel J K) K
          (routedFreshChoices j₀ K K le_rfl) (routedPaddedCoefficients K a)))
      (tagFrame (taylorEmptyLabel J K) (freshWordFrame j₀ a₀ K))
      (tagFrame (taylorEmptyLabel J K) (freshWordFrame j₀ a₀ K)) 2 0 ∧
    adjointQueryCount
      (coherentFreshLCUWord (A := A) (I := I) j₀ (taylorEmptyLabel J K) K
        (routedFreshChoices j₀ K K le_rfl) (routedPaddedCoefficients K a)) = K ∧
    adjointGateCount
      (coherentFreshLCUWord (A := A) (I := I) j₀ (taylorEmptyLabel J K) K
        (routedFreshChoices j₀ K K le_rfl) (routedPaddedCoefficients K a)) = 2 * K + 3 := by
  have hm := routedPaddedCoefficients_mass K a ha
  have hc : 0 < coefficientMass (routedPaddedCoefficients K a) := by rw [hm]; norm_num
  have h := coherent_fresh_lcu_counted j₀ (taylorEmptyLabel J K) a₀ K
    (routedFreshChoices j₀ K K le_rfl) (routedPaddedCoefficients K a) B U hc henc
  simpa only [orderedBlockProduct_routedFreshChoices, hm, routedPaddedCoefficients_operator] using!
      h

end Routed
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
