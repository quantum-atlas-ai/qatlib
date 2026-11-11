/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.CleanTwoOracleWord

/-!
# Flattening Prepared Oracle Predicates

`PreparedPredicateLabels` and `preparedPredicateWorkspaceEquiv` combine the branch, sample,
spectator, and control registers of a prepared two-oracle circuit into one label register. The
effective mask `preparedPredicateMask` requires both the branch predicate and the original
control bit.

`compiledPreparedPredicateWord` then implements the flattened masked circuit using controlled
parallel access to the two original oracles. The construction preserves both query counts and
block-encoding accuracy, with two additional fixed gates per oracle query, for the CBMD
implementations of [WangEtAl2026].

## Main statements

* `preparedPredicateSource_reindex` identifies the nested oracle source with a single masked
  oracle.
* `flattenPreparedPredicateWord_evaluate` and `flattenPreparedPredicateWord_cost` preserve
  semantics and all cost counts under reindexing.
* `compiledPreparedPredicateWord_cost` gives the fixed-gate overhead, and
  `compiledPreparedPredicateWord_blockEncoding` transports the encoding to a clean tagged frame.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
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
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix

/-- The combined label type `(K × J) × (R × Bool)` for branch, sample, spectator, and control
registers. -/
abbrev PreparedPredicateLabels (K J R : Type) := (K × J) × (R × Bool)

/-- Reassociates the combined predicate label and data register into the nested workspace `(K ×
J) × (R × (Bool × W))`. -/
def preparedPredicateWorkspaceEquiv (K J R W : Type) :
    PreparedPredicateLabels K J R × W ≃ (K × J) × (R × (Bool × W)) where
  toFun := fun ⟨⟨⟨k,j⟩,r,b⟩,w⟩ => ((k,j),r,b,w)
  invFun := fun ⟨⟨k,j⟩,r,b,w⟩ => (((k,j),r,b),w)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The effective oracle mask requiring both the branch predicate `p` and the Boolean control
bit in the combined label. -/
def preparedPredicateMask {K J R : Type} (p : K → Bool)
    (label : PreparedPredicateLabels K J R) : Bool := p label.1.1 && label.2.2

section Source
variable {K J R W : Type} [DecidableEq K] [DecidableEq J] [DecidableEq R] [DecidableEq W]

/-- The nested prepared oracle source that masks by `p`, acts in parallel over `J` and `R`, and
controls `O` by the Boolean register. -/
def preparedPredicateSource (p : K → Bool) (O : Matrix W W ℂ) :
    Matrix ((K × J) × (R × (Bool × W))) ((K × J) × (R × (Bool × W))) ℂ :=
  (maskedOracle p (parallelOracle (J := J) (parallelOracle (J := R) (controlOracle O)))).submatrix
    (Equiv.prodAssoc K J (R × (Bool × W))) (Equiv.prodAssoc K J (R × (Bool × W)))

/-- Reindexing `preparedPredicateSource` by `preparedPredicateWorkspaceEquiv` gives the single
masked oracle with mask `preparedPredicateMask p`. -/
theorem preparedPredicateSource_reindex (p : K → Bool) (O : Matrix W W ℂ) :
    (preparedPredicateSource (J := J) (R := R) p O).submatrix
      (preparedPredicateWorkspaceEquiv K J R W) (preparedPredicateWorkspaceEquiv K J R W) =
    maskedOracle (preparedPredicateMask (J := J) (R := R) p) O := by
  ext ⟨⟨⟨k,j⟩,r,b⟩,i⟩ ⟨⟨⟨k',j'⟩,r',b'⟩,l⟩
  by_cases hk : k = k' <;> by_cases hj : j = j' <;>
    by_cases hr : r = r' <;> by_cases hb : b = b' <;>
    simp [preparedPredicateSource, preparedPredicateWorkspaceEquiv, preparedPredicateMask,
      maskedOracle, select, parallelOracle, controlOracle, hk, hj, hr, hb]
  all_goals cases hp : p k <;> cases b <;> simp_all [Matrix.one_apply]
end Source

section Words
variable {K J R W : Type} [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]

/-- Reindexes a prepared circuit from the nested predicate workspace to the combined-label
workspace. -/
def flattenPreparedPredicateWord (cs : List (PreparedStep ((K × J) × (R × (Bool × W))))) :
    List (PreparedStep (PreparedPredicateLabels K J R × W)) :=
  reindexPreparedWord (preparedPredicateWorkspaceEquiv K J R W) cs

/-- Evaluation of the flattened word with the two effective masked oracles equals the reindexed
evaluation of the original nested-source circuit. -/
theorem flattenPreparedPredicateWord_evaluate (p : K → Bool) (O1 O2 : Matrix W W ℂ)
    (cs : List (PreparedStep ((K × J) × (R × (Bool × W))))) :
    evaluatePrepared (maskedOracle (preparedPredicateMask (J := J) (R := R) p) O1)
      (maskedOracle (preparedPredicateMask (J := J) (R := R) p) O2)
      (flattenPreparedPredicateWord cs) =
    (evaluatePrepared (preparedPredicateSource (J := J) (R := R) p O1)
      (preparedPredicateSource (J := J) (R := R) p O2) cs).submatrix
      (preparedPredicateWorkspaceEquiv K J R W) (preparedPredicateWorkspaceEquiv K J R W) := by
  rw [← preparedPredicateSource_reindex p O1, ← preparedPredicateSource_reindex p O2]
  exact reindexPreparedWord_evaluate _ _ _ _

omit [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W] in

/-- Flattening the predicate workspace preserves the data-query, input-query, and fixed-gate
counts. -/
theorem flattenPreparedPredicateWord_cost
    (cs : List (PreparedStep ((K × J) × (R × (Bool × W))))) :
    preparedDataQueries (flattenPreparedPredicateWord cs) = preparedDataQueries cs ∧
    preparedInputQueries (flattenPreparedPredicateWord cs) = preparedInputQueries cs ∧
    preparedFixedGates (flattenPreparedPredicateWord cs) = preparedFixedGates cs :=
  reindexPreparedWord_cost _ _

/-- Flattening the predicate workspace preserves validity of a prepared circuit. -/
theorem flattenPreparedPredicateWord_valid
    {cs : List (PreparedStep ((K × J) × (R × (Bool × W))))}
    (hcs : PreparedCircuitValid cs) : PreparedCircuitValid (flattenPreparedPredicateWord cs) :=
  reindexPreparedWord_valid _ hcs

/-- Flattens a prepared predicate circuit and compiles its two masked oracles into controlled
parallel oracle access with a clean Boolean register. -/
def compiledPreparedPredicateWord (p : K → Bool)
    (cs : List (PreparedStep ((K × J) × (R × (Bool × W))))) :
    List (PreparedStep (Bool × (PreparedPredicateLabels K J R × W))) :=
  cleanTwoOracleWord (preparedPredicateMask p) (flattenPreparedPredicateWord cs)

/-- The compiled word evaluates to a Boolean selection of flattened circuits whose effective
masks are XORed with the outer control bit. -/
theorem compiledPreparedPredicateWord_evaluate (p : K → Bool) (O1 O2 : Matrix W W ℂ)
    (cs : List (PreparedStep ((K × J) × (R × (Bool × W))))) :
    evaluatePrepared
      (controlOracle (parallelOracle (J := PreparedPredicateLabels K J R) O1))
      (controlOracle (parallelOracle (J := PreparedPredicateLabels K J R) O2))
      (compiledPreparedPredicateWord p cs) =
    select (fun b : Bool => evaluatePrepared
      (maskedOracle (fun j => xor b (preparedPredicateMask p j)) O1)
      (maskedOracle (fun j => xor b (preparedPredicateMask p j)) O2)
      (flattenPreparedPredicateWord cs)) :=
  cleanTwoOracleWord_evaluate _ _ _ _

omit [Fintype K] [Fintype J] [Fintype R] [Fintype W] in

/-- Compilation preserves both oracle-query counts and adds two fixed gates for each data or
input query. -/
theorem compiledPreparedPredicateWord_cost (p : K → Bool)
    (cs : List (PreparedStep ((K × J) × (R × (Bool × W))))) :
    preparedDataQueries (compiledPreparedPredicateWord p cs) = preparedDataQueries cs ∧
    preparedInputQueries (compiledPreparedPredicateWord p cs) = preparedInputQueries cs ∧
    preparedFixedGates (compiledPreparedPredicateWord p cs) =
      preparedFixedGates cs + 2 * (preparedDataQueries cs + preparedInputQueries cs) := by
  obtain ⟨h1,h2,hg⟩ := cleanTwoOracleWord_cost (preparedPredicateMask p)
    (flattenPreparedPredicateWord cs)
  have hf := flattenPreparedPredicateWord_cost cs
  exact ⟨h1.trans hf.1, h2.trans hf.2.1, by simpa only [hf.1, hf.2.1, hf.2.2] using! hg⟩

/-- Compiling a prepared predicate word preserves validity of the prepared circuit. -/
theorem compiledPreparedPredicateWord_valid (p : K → Bool)
    {cs : List (PreparedStep ((K × J) × (R × (Bool × W))))}
    (hcs : PreparedCircuitValid cs) : PreparedCircuitValid (compiledPreparedPredicateWord p cs) :=
  cleanTwoOracleWord_valid _ (flattenPreparedPredicateWord_valid hcs)

/-- For unitary source oracles and a valid prepared circuit, compilation preserves its block
encoding with the same normalization and error on the false-tagged reindexed frame. -/
theorem compiledPreparedPredicateWord_blockEncoding {I : Type} [Fintype I] [DecidableEq I]
    (p : K → Bool) (O1 O2 : Matrix W W ℂ)
    (hO1 : O1 ∈ Matrix.unitaryGroup W ℂ) (hO2 : O2 ∈ Matrix.unitaryGroup W ℂ)
    (cs : List (PreparedStep ((K × J) × (R × (Bool × W))))) (hcs : PreparedCircuitValid cs)
    (A : Matrix I I ℂ) (F : Matrix ((K × J) × (R × (Bool × W))) I ℂ) (α ε : ℝ)
    (henc : BlockEncoding A (evaluatePrepared (preparedPredicateSource (J := J) (R := R) p O1)
      (preparedPredicateSource (J := J) (R := R) p O2) cs) F F α ε) :
    BlockEncoding A
      (evaluatePrepared
        (controlOracle (parallelOracle (J := PreparedPredicateLabels K J R) O1))
        (controlOracle (parallelOracle (J := PreparedPredicateLabels K J R) O2))
        (compiledPreparedPredicateWord p cs))
      (tagFrame false (reindexFrame (preparedPredicateWorkspaceEquiv K J R W) F))
      (tagFrame false (reindexFrame (preparedPredicateWorkspaceEquiv K J R W) F)) α ε := by
  have he := reindexWorkspace_blockEncoding (preparedPredicateWorkspaceEquiv K J R W)
    A _ F α ε henc
  rw [← flattenPreparedPredicateWord_evaluate] at he
  exact cleanTwoOracleWord_blockEncoding (preparedPredicateMask p) O1 O2 hO1 hO2
    (flattenPreparedPredicateWord cs) (flattenPreparedPredicateWord_valid hcs)
    A (reindexFrame (preparedPredicateWorkspaceEquiv K J R W) F) α ε he
end Words
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
