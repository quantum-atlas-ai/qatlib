/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.FrameTransport
import Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointWord

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath

/-!
# Source Word Transport

The existing source circuit uses only unitary known gates. This checks individual matrices, rather than deriving legality from the product alone.
-/
open Qatlib.Concepts.CoherentSim.CoherentOAA

open Qatlib Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
open scoped BigOperators Classical ComplexOrder
set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
/-- The existing source circuit uses only unitary known gates. This checks
individual matrices, rather than deriving legality from the product alone. -/
def SourceWordValid {D : ℕ} (cs : List (AdjointStep (Fin D))) : Prop :=
  ∀ V,Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep.gate V∈cs → V∈Matrix.unitaryGroup (Fin D) ℂ

/-- Source lists use operator-product order; output lists use chronological
order. Compilation reverses the list and keeps forward/adjoint query tags. -/
def sourceWord {D : ℕ} : (cs : List (AdjointStep (Fin D))) → SourceWordValid cs → List (OutputGate D)
  | [], _ => []
  | .gate V::cs, hc => sourceWord cs (fun W hW => hc W (List.mem_cons_of_mem _ hW))++
      [.known V (hc V (by simp))]
  | .forward::cs, hc => sourceWord cs (fun W hW => hc W (List.mem_cons_of_mem _ hW))++[.query true]
  | .backward::cs, hc => sourceWord cs (fun W hW => hc W (List.mem_cons_of_mem _ hW))++[.query false]

/-- The finite protocol identity or bound `wordMatrix_append_source` holds under exactly the displayed hypotheses. -/
private theorem wordMatrix_append_source {D : ℕ} (O : Bool → Operator D) (gs hs : List (OutputGate D)) :
    wordMatrix O (gs++hs)=wordMatrix O hs*wordMatrix O gs := by
  induction gs with
  | nil => simp [wordMatrix]
  | cons g gs ih => simp [wordMatrix,ih,Matrix.mul_assoc]

/-- The finite protocol identity or bound `wordQueries_append_source` holds under exactly the displayed hypotheses. -/
private theorem wordQueries_append_source {D : ℕ} (gs hs : List (OutputGate D)) :
    wordQueries (gs++hs)=wordQueries gs+wordQueries hs := by
  induction gs with
  | nil => simp [wordQueries]
  | cons g gs ih => cases g <;> simp [wordQueries,ih,Nat.add_assoc,Nat.add_comm 1]

/-- The actual source word satisfies `sourceWord_matrix` with the stated validity and inverse-oracle hypotheses. -/
theorem sourceWord_matrix {D : ℕ} (O : Bool → Operator D)
    (hinv : O false=(O true).conjTranspose) (cs : List (AdjointStep (Fin D))) (hc : SourceWordValid cs) :
    wordMatrix O (sourceWord cs hc)=Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (O true) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> simp [sourceWord,wordMatrix_append_source,wordMatrix,gateMatrix,
      Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate,instructionMatrix,ih,hinv]

/-- The actual source word satisfies `sourceWord_queries` with the stated validity and inverse-oracle hypotheses. -/
theorem sourceWord_queries {D : ℕ} (cs : List (AdjointStep (Fin D))) (hc : SourceWordValid cs) :
    wordQueries (sourceWord cs hc)=adjointQueryCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> simp [sourceWord,wordQueries_append_source,wordQueries,adjointQueryCount,ih]

/-- The actual source word satisfies `sourceWord_length` with the stated validity and inverse-oracle hypotheses. -/
theorem sourceWord_length {D : ℕ} (cs : List (AdjointStep (Fin D))) (hc : SourceWordValid cs) :
    (sourceWord cs hc).length=cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [sourceWord,ih]

/-- The actual source word satisfies `sourceWordValid_adjoint` with the stated validity and inverse-oracle hypotheses. -/
theorem sourceWordValid_adjoint {D : ℕ} (cs : List (AdjointStep (Fin D)))
    (hc : SourceWordValid cs) : SourceWordValid (adjointCircuit cs) := by
  induction cs with
  | nil => intro V hV; simp [adjointCircuit] at hV
  | cons c cs ih =>
    have ht : SourceWordValid cs := fun V hV => hc V (List.mem_cons_of_mem c hV)
    intro V hV
    rw [adjointCircuit] at hV
    rcases List.mem_append.mp hV with hV | hV
    · exact ih ht V hV
    · have he := List.mem_singleton.mp hV
      cases c with
      | gate U =>
        have hEq : V=U.conjTranspose := Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep.gate.inj he
        rw [hEq]
        exact adjoint_unitary (hc U (by simp))
      | forward => cases he
      | backward => cases he

/-- The supplied inverse is the actual Frozen adjoint circuit, with gate
adjoints and swapped oracle directions, not a reversal of a compiled list. -/
theorem sourceWord_adjoint_matrix {D : ℕ} (O : Bool → Operator D)
    (hinv : O false=(O true).conjTranspose) (cs : List (AdjointStep (Fin D))) (hc : SourceWordValid cs) :
    wordMatrix O (sourceWord (adjointCircuit cs) (sourceWordValid_adjoint cs hc))=
      (wordMatrix O (sourceWord cs hc)).conjTranspose := by
  rw [sourceWord_matrix O hinv,sourceWord_matrix O hinv,evaluate_adjointCircuit]

/-- The actual source word satisfies `sourceWord_adjoint_queries` with the stated validity and inverse-oracle hypotheses. -/
theorem sourceWord_adjoint_queries {D : ℕ} (cs : List (AdjointStep (Fin D))) (hc : SourceWordValid cs) :
    wordQueries (sourceWord (adjointCircuit cs) (sourceWordValid_adjoint cs hc))=adjointQueryCount cs := by
  rw [sourceWord_queries,adjointQueryCount_adjointCircuit]

/-- Invalid failed output code is replaced by a valid empty word, keeping
its constructor record. Validation uses known source matrices only. -/
def safeSourceWord {D : ℕ} (cs : List (AdjointStep (Fin D))) : List (OutputGate D) :=
  if hc : SourceWordValid cs then sourceWord cs hc else []

/-- The finite protocol identity or bound `safeSourceWord_matrix` holds under exactly the displayed hypotheses. -/
theorem safeSourceWord_matrix {D : ℕ} (O : Bool → Operator D)
    (hinv : O false=(O true).conjTranspose) (cs : List (AdjointStep (Fin D))) (hc : SourceWordValid cs) :
    wordMatrix O (safeSourceWord cs)=Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (O true) cs := by
  unfold safeSourceWord
  rw [dite_eq_left hc,sourceWord_matrix O hinv]

/-- The finite protocol identity or bound `safeSourceWord_queries_le` holds under exactly the displayed hypotheses. -/
theorem safeSourceWord_queries_le {D : ℕ} (cs : List (AdjointStep (Fin D))) :
    wordQueries (safeSourceWord cs) ≤ adjointQueryCount cs := by
  unfold safeSourceWord
  split_ifs with hc
  · rw [sourceWord_queries]
  · exact Nat.zero_le _


end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol

/-- The actual source word satisfies `coordinate_source_adjoint` with the stated validity and inverse-oracle hypotheses. -/
theorem coordinate_source_adjoint {D : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (φ : I → Fin D) (hφ : Function.Injective φ) (L R : Matrix (Fin D) I ℂ)
    (O : Bool → Operator D) (hinv : O false=(O true).conjTranspose)
    (cs : List (AdjointStep (Fin D))) (hc : SourceWordValid cs) :
    wordMatrix O (coordinateWord φ hφ R L (sourceWord (adjointCircuit cs) (sourceWordValid_adjoint cs hc)))=
      (wordMatrix O (coordinateWord φ hφ L R (sourceWord cs hc))).conjTranspose ∧
    wordQueries (coordinateWord φ hφ R L (sourceWord (adjointCircuit cs) (sourceWordValid_adjoint cs hc)))=
      adjointQueryCount cs := by
  constructor
  · exact coordinateWord_adjoint_matrix φ hφ L R O _ _ (sourceWord_adjoint_matrix O hinv cs hc)
  · rw [coordinateWord_queries]
    exact sourceWord_adjoint_queries cs hc

/-- Only a successful source description must be legal and encode the
specified target. Bad source code and bad frames remain as full records. -/
def sourceFramedPromise {D R : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (cs : Path P → List (AdjointStep (Fin D)))
    (L Rf : Path P → Matrix (Fin D) I ℂ) (T : Matrix I I ℂ) (τ : ℝ) (r0 : Fin D) : Prop :=
  ∃ G : Finset (Path P),
    2/3 ≤ (∑ p∈G,(preparedLaw (fun mode => unitaryChannel (O mode) (hO mode)) S r0 P).prob p) ∧
    ∀ p∈G,SourceWordValid (cs p) ∧ BlockEncoding T (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (O true) (cs p)) (L p) (Rf p) 1 (τ/100)

/-- The actual source word satisfies `sourceFramedPromise_transport` with the stated validity and inverse-oracle hypotheses. -/
theorem sourceFramedPromise_transport {D R : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ)
    (hinv : O false=(O true).conjTranspose) (S : ℝ → Fin R)
    (P : Program D R) (cs : Path P → List (AdjointStep (Fin D)))
    (L Rf : Path P → Matrix (Fin D) I ℂ) (T : Matrix I I ℂ) (τ : ℝ) (r0 : Fin D)
    (hc : sourceFramedPromise O hO S P cs L Rf T τ r0) :
    framedPromise O hO S P (fun p => safeSourceWord (cs p)) L Rf T τ r0 := by
  rcases hc with ⟨G,hG,hgood⟩
  refine ⟨G,hG,?_⟩
  intro p hp
  rw [safeSourceWord_matrix O hinv (cs p) (hgood p hp).1]
  exact (hgood p hp).2


end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor
