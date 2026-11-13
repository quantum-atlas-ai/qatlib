/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.Theorem41ClosedGapConsumer
import Qatlib.Concepts.QsvtCore.LinearSystems.ExplicitNoisyQSVTSolver
import Qatlib.Concepts.QsvtCore.PhaseExistence.PairCompletionDuality
import Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary8ComplexPhaseExistenceGily

/-!
# Sector readouts and execution ledgers for QSVT

This module defines closed and strict singular value sectors, scalar strata, and residual
readouts for polynomial linear system responses. The closed coefficients retain zero and
positive values at least the threshold, so threshold and kernel behavior can be recorded
explicitly.

The report structures combine these readouts with compilation counts, parity, and budget data.
`QlsCor8Conditions` packages polynomial completion conditions, while `qlsExecutionLedger`
records word length, oracle and projector accesses, workspace, and bit time. The mathematical
background is developed in [GilyenSuLowWiebe2019].

## Main statements

* `closedRightSector`: the right singular sector defined by closed coefficients.
* `QlsCor8Conditions`: the parity and magnitude conditions on a complex response.
* `qlsExecutionLedger`: execution counts derived from a source phase family.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

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

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

/-- The real coefficient equal to one at zero and at positive values at least `δ`, and zero at
all other real values. -/
noncomputable def closedSectorCoefficientReal (δ x : ℝ) : ℝ :=
  if 0 < x then (if δ ≤ x then 1 else 0) else (if x < 0 then 0 else 1)

/-- The complex cast of the real closed sector coefficient. -/
noncomputable def closedSectorCoefficient (δ x : ℝ) : ℂ :=
  (closedSectorCoefficientReal δ x : ℂ)

/-- The strict sector coefficient `1 - thresholdIndicator 0 x + thresholdIndicator δ x`. -/
noncomputable def strictSectorCoefficient (δ x : ℝ) : ℝ :=
  (1 : ℝ) - thresholdIndicator 0 x + thresholdIndicator δ x

/-- The right singular basis conjugate of the diagonal closed sector coefficients. -/
noncomputable def closedRightSector (A : Matrix O I ℂ) (δ : ℝ) : Matrix I I ℂ :=
  basisColumns (rightSingularBasis A) *
    diagonal (fun i : Fin (Fintype.card I) =>
      closedSectorCoefficient δ (matrixSingularValues A i)) *
    (basisColumns (rightSingularBasis A))ᴴ

/-- The left singular basis conjugate of the diagonal closed sector coefficients. -/
noncomputable def closedLeftSector (A : Matrix O I ℂ) (δ : ℝ) : Matrix O O ℂ :=
  basisColumns (leftSingularBasis A) *
    diagonal (fun j : Fin (Fintype.card O) =>
      closedSectorCoefficient δ (matrixSingularValues A j)) *
    (basisColumns (leftSingularBasis A))ᴴ

/-- The identity minus the difference of the right threshold projections at zero and at `δ`. -/
noncomputable def strictRightSector (A : Matrix O I ℂ) (δ : ℝ) : Matrix I I ℂ :=
  1 - (rightThresholdProjection A 0 - rightThresholdProjection A δ)

/-- The identity minus the difference of the left threshold projections at zero and at `δ`. -/
noncomputable def strictLeftSector (A : Matrix O I ℂ) (δ : ℝ) : Matrix O O ℂ :=
  1 - (leftThresholdProjection A 0 - leftThresholdProjection A δ)

/-- The five scalar strata: negative, kernel, middle band, threshold, and above threshold. -/
inductive QlsStratum where

  | negative

  | kernel

  | midBand

  | threshold

  | above
  deriving DecidableEq, Repr

/-- The stratum of a scalar value, separating negative and zero values before comparing positive
values with `δ`. -/
noncomputable def qlsStratum (δ σ : ℝ) : QlsStratum :=
  if σ < 0 then .negative
  else if 0 < σ then (if σ < δ then .midBand else if δ < σ then .above else .threshold)
  else .kernel

/-- The absolute error from `(δ / 2) / σ` for nonzero `σ`, with residual `|Pw.eval 0|` at zero. -/
noncomputable def qlsWindowResidual (δ : ℝ) (Pw : Polynomial ℝ) (σ : ℝ) : ℝ :=
  if 0 < σ then |Pw.eval σ - (δ/2)/σ|
  else if σ < 0 then |Pw.eval σ - (δ/2)/σ|
  else |Pw.eval 0|

/-- A scalar sector report containing its stratum, complex coefficient, and real residual. -/
structure QlsSectorReadout where

  stratum : QlsStratum

  coefficient : ℂ

  residual : ℝ

/-- The sector readout combining the stratum, closed coefficient, and window residual of one
scalar value. -/
noncomputable def qlsSectorReadout (δ : ℝ) (Pw : Polynomial ℝ) (σ : ℝ) : QlsSectorReadout :=
  { stratum := qlsStratum δ σ
    coefficient := closedSectorCoefficient δ σ
    residual := qlsWindowResidual δ Pw σ }

/-- The list of sector readouts obtained by mapping `qlsSectorReadout` over the supplied scalar
values. -/
noncomputable def qlsSectorReadouts (δ : ℝ) (Pw : Polynomial ℝ) (σs : List ℝ) :
    List QlsSectorReadout :=
  σs.map (qlsSectorReadout δ Pw)

/-- The maximum residual in a list of readouts, with zero included as the initial value. -/
def qlsMaxResidual : List QlsSectorReadout → ℝ
  | [] => 0
  | r :: rs => max r.residual (qlsMaxResidual rs)

/-- The Euclidean norm of a complex coordinate vector. -/
noncomputable def qlsNormVec {H : Type} [Fintype H] [DecidableEq H] (ψ : H → ℂ) : ℝ :=
  ‖toEuclidean_fromVec ψ‖

/-- The four compilation counts of the source real phase family associated to `Φ`. -/
def qlsSourceLedger (Φ : List ℝ) : ℕ × ℕ × ℕ × ℕ :=
  cppCounts (cppCompile (sourceRealFamily Φ))

/-- A threshold report containing scalar readouts, the four compilation counts, and the phase
word length. -/
structure QlsThresholdReport where

  readouts : List QlsSectorReadout

  ledger : ℕ × ℕ × ℕ × ℕ

  wordLength : ℕ

/-- The threshold report formed from the supplied polynomial, scalar values, threshold, and
phase list. -/
noncomputable def qlsThresholdReport (δ : ℝ) (Pw : Polynomial ℝ) (σs : List ℝ) (Φ : List ℝ) :
    QlsThresholdReport :=
  { readouts := qlsSectorReadouts δ Pw σs
    ledger := qlsSourceLedger Φ
    wordLength := Φ.length }

/-- The two parity labels odd and even for completion reports. -/
inductive QlsCor8Parity where

  | odd

  | even
  deriving DecidableEq, Repr

/-- The parity label determined by whether the natural number `n` has remainder one modulo two. -/
def qlsCor8ParityOf (n : ℕ) : QlsCor8Parity :=
  if n % 2 = 1 then .odd else .even

/-- The response parity condition at the natural degree, norm squared at most one on `[-1, 1]`,
and norm squared at least one outside `(-1, 1)`. For even natural degree it also requires
norm squared at least one on the imaginary axis. -/
structure QlsCor8Conditions (P : Polynomial ℂ) : Prop where

  parity : Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity P.natDegree P

  inner : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
    Complex.normSq (P.eval (Complex.ofReal x)) ≤ 1

  outer : ∀ x : ℝ, x ∉ Set.Ioo (-1 : ℝ) 1 →
    1 ≤ Complex.normSq (P.eval (Complex.ofReal x))

  imaginary : P.natDegree % 2 = 0 → ∀ y : ℝ,
    1 ≤ Complex.normSq (P.eval (Complex.ofReal y * Complex.I))

/-- A report containing word length, parity, compilation counts, a budget, and a Boolean budget
comparison. -/
structure QlsCor8Report where

  wordLength : ℕ

  parity : QlsCor8Parity

  ledger : ℕ × ℕ × ℕ × ℕ

  budget : ℕ

  withinBudget : Bool
  deriving Repr

/-- The completion report computed from a phase list and word length budget. -/
def qlsCor8Report (Φ : List ℝ) (budget : ℕ) : QlsCor8Report :=
  { wordLength := Φ.length
    parity := qlsCor8ParityOf Φ.length
    ledger := qlsSourceLedger Φ
    budget := budget
    withinBudget := decide (Φ.length ≤ budget) }

/-- Execution data containing word length, data calls, two projector access counts, phase
macros, peak workspace, and bit time. -/
structure QlsExecutionLedger where

  wordLength : ℕ

  dataCalls : ℕ

  pAccesses : ℕ

  qAccesses : ℕ

  phaseMacros : ℕ

  peakWorkspace : ℕ

  bitTime : ℕ
  deriving Repr

/-- The execution ledger derived from the compiled source real phase family, with peak workspace
twice the supplied dimension and bit time the sum of projector accesses. -/
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
