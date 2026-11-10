/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.Theorem41ClosedGapConsumer
import Qatlib.Concepts.QsvtCore.LinearSystems.ExplicitNoisyQSVTSolver
import Qatlib.Concepts.QsvtCore.PhaseExistence.PairCompletionDuality
import Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary8ComplexPhaseExistenceGily
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.WalshMoment.Forrelation

set_option autoImplicit false

namespace Qatlib.Concepts.QsvtCore.LinearSystems
namespace StageBQLSQSVT

open Qatlib Polynomial Matrix

set_option linter.unusedSectionVars false

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

noncomputable def closedSectorCoefficientReal (δ x : ℝ) : ℝ :=
  if 0 < x then (if δ ≤ x then 1 else 0) else (if x < 0 then 0 else 1)

noncomputable def closedSectorCoefficient (δ x : ℝ) : ℂ :=
  (closedSectorCoefficientReal δ x : ℂ)

noncomputable def strictSectorCoefficient (δ x : ℝ) : ℝ :=
  (1 : ℝ) - thresholdIndicator 0 x + thresholdIndicator δ x

noncomputable def closedRightSector (A : Matrix O I ℂ) (δ : ℝ) : Matrix I I ℂ :=
  basisColumns (rightSingularBasis A) *
    diagonal (fun i : Fin (Fintype.card I) =>
      closedSectorCoefficient δ (matrixSingularValues A i)) *
    (basisColumns (rightSingularBasis A))ᴴ

noncomputable def closedLeftSector (A : Matrix O I ℂ) (δ : ℝ) : Matrix O O ℂ :=
  basisColumns (leftSingularBasis A) *
    diagonal (fun j : Fin (Fintype.card O) =>
      closedSectorCoefficient δ (matrixSingularValues A j)) *
    (basisColumns (leftSingularBasis A))ᴴ

noncomputable def strictRightSector (A : Matrix O I ℂ) (δ : ℝ) : Matrix I I ℂ :=
  1 - (rightThresholdProjection A 0 - rightThresholdProjection A δ)

noncomputable def strictLeftSector (A : Matrix O I ℂ) (δ : ℝ) : Matrix O O ℂ :=
  1 - (leftThresholdProjection A 0 - leftThresholdProjection A δ)

inductive QlsStratum where

  | negative

  | kernel

  | midBand

  | threshold

  | above
  deriving DecidableEq, Repr

noncomputable def qlsStratum (δ σ : ℝ) : QlsStratum :=
  if σ < 0 then .negative
  else if 0 < σ then (if σ < δ then .midBand else if δ < σ then .above else .threshold)
  else .kernel

noncomputable def qlsWindowResidual (δ : ℝ) (Pw : Polynomial ℝ) (σ : ℝ) : ℝ :=
  if 0 < σ then |Pw.eval σ - (δ/2)/σ|
  else if σ < 0 then |Pw.eval σ - (δ/2)/σ|
  else |Pw.eval 0|

structure QlsSectorReadout where

  stratum : QlsStratum

  coefficient : ℂ

  residual : ℝ

noncomputable def qlsSectorReadout (δ : ℝ) (Pw : Polynomial ℝ) (σ : ℝ) : QlsSectorReadout :=
  { stratum := qlsStratum δ σ
    coefficient := closedSectorCoefficient δ σ
    residual := qlsWindowResidual δ Pw σ }

noncomputable def qlsSectorReadouts (δ : ℝ) (Pw : Polynomial ℝ) (σs : List ℝ) :
    List QlsSectorReadout :=
  σs.map (qlsSectorReadout δ Pw)

def qlsMaxResidual : List QlsSectorReadout → ℝ
  | [] => 0
  | r :: rs => max r.residual (qlsMaxResidual rs)

noncomputable def qlsNormVec {H : Type} [Fintype H] [DecidableEq H] (ψ : H → ℂ) : ℝ :=
  ‖toEuclidean_fromVec ψ‖

def qlsSourceLedger (Φ : List ℝ) : ℕ × ℕ × ℕ × ℕ :=
  cppCounts (cppCompile (sourceRealFamily Φ))

structure QlsThresholdReport where

  readouts : List QlsSectorReadout

  ledger : ℕ × ℕ × ℕ × ℕ

  wordLength : ℕ

noncomputable def qlsThresholdReport (δ : ℝ) (Pw : Polynomial ℝ) (σs : List ℝ) (Φ : List ℝ) :
    QlsThresholdReport :=
  { readouts := qlsSectorReadouts δ Pw σs
    ledger := qlsSourceLedger Φ
    wordLength := Φ.length }

inductive QlsCor8Parity where

  | odd

  | even
  deriving DecidableEq, Repr

def qlsCor8ParityOf (n : ℕ) : QlsCor8Parity :=
  if n % 2 = 1 then .odd else .even

structure QlsCor8Conditions (P : Polynomial ℂ) : Prop where

  parity : Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity P.natDegree P

  inner : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
    Complex.normSq (P.eval (Complex.ofReal x)) ≤ 1

  outer : ∀ x : ℝ, x ∉ Set.Ioo (-1 : ℝ) 1 →
    1 ≤ Complex.normSq (P.eval (Complex.ofReal x))

  imaginary : P.natDegree % 2 = 0 → ∀ y : ℝ,
    1 ≤ Complex.normSq (P.eval (Complex.ofReal y * Complex.I))

structure QlsCor8Report where

  wordLength : ℕ

  parity : QlsCor8Parity

  ledger : ℕ × ℕ × ℕ × ℕ

  budget : ℕ

  withinBudget : Bool
  deriving Repr

def qlsCor8Report (Φ : List ℝ) (budget : ℕ) : QlsCor8Report :=
  { wordLength := Φ.length
    parity := qlsCor8ParityOf Φ.length
    ledger := qlsSourceLedger Φ
    budget := budget
    withinBudget := decide (Φ.length ≤ budget) }

structure QlsExecutionLedger where

  wordLength : ℕ

  dataCalls : ℕ

  pAccesses : ℕ

  qAccesses : ℕ

  phaseMacros : ℕ

  peakWorkspace : ℕ

  bitTime : ℕ
  deriving Repr

def qlsExecutionLedger (Φ : List ℝ) (workspaceDim : ℕ) : QlsExecutionLedger :=
  let c := cppCounts (cppCompile (sourceRealFamily Φ))
  { wordLength := Φ.length
    dataCalls := c.1
    pAccesses := c.2.1
    qAccesses := c.2.2.1
    phaseMacros := c.2.2.2
    peakWorkspace := 2*workspaceDim
    bitTime := c.2.1 + c.2.2.1 }

end StageBQLSQSVT
end Qatlib.Concepts.QsvtCore.LinearSystems
