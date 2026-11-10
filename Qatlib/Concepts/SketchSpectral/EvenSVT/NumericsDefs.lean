/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.SketchBuild.CompactImportanceSketch
import Qatlib.Concepts.SketchArith.TransposeAccess.CompactSketchConsumers
import Qatlib.Concepts.SketchSpectral.SketchAnalysis.SketchOperatorConcentration
import Qatlib.Concepts.RandCompile.ChannelBudget.SingularValues
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Qatlib.Concepts.SketchSpectral.MatrixFunctions.HermitianRankLogStability
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.PositivePolarFactor
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.SketchSpectral.MatrixFunctions

open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false
set_option warningAsError false

namespace Qatlib.Concepts.SketchSpectral.EvenSVT
namespace ConstructionStageB
namespace StageBSQNUMERICS

open Matrix
open Qatlib
open scoped Classical BigOperators Matrix.Norms.Frobenius Matrix.Norms.L2Operator

noncomputable section

def sourceOperator {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ) : Matrix C C ℂ :=
  Aᴴ * A

def sourceEnergy {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ) : ℝ :=
  sketchSquared A

def rankLogFactor (r : ℕ) : ℝ := 1 + Real.log (1 + (r : ℝ))

structure SqOversampling where

  row : ℝ

  col : ℝ

  row_ge_one : 1 ≤ row

  col_ge_one : 1 ≤ col

  col_le_two_row : col ≤ 2 * row

def rowTailScale (φ : ℝ) (δ : ℝ) (r : ℕ) (E : ℝ) : ℝ :=
  Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 3)) / (r : ℝ)) * E

def colTailScale (φ : ℝ) (δ : ℝ) (c : ℕ) (E : ℝ) : ℝ :=
  Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 3)) / (c : ℝ)) * (2 * E)

def requiredRowSamples (L ε φ δ E : ℝ) (rank : ℕ) : ℝ :=
  32 * φ ^ 2 * Real.log (2 / (δ / 3)) * (L * rankLogFactor rank) ^ 2 * E ^ 2 / ε ^ 2

def requiredColSamples (M Lbar ε φ δ E : ℝ) (rank : ℕ) : ℝ :=
  128 * φ ^ 2 * Real.log (2 / (δ / 3)) * (M * Lbar * rankLogFactor rank) ^ 2 * E ^ 2 / ε ^ 2

def rowBudgetMul (L ε φ δ E : ℝ) (rank r : ℕ) : Prop :=
  32 * φ ^ 2 * Real.log (2 / (δ / 3)) * (L * rankLogFactor rank) ^ 2 * E ^ 2
    ≤ ε ^ 2 * (r : ℝ)

def colBudgetMul (M Lbar ε φ δ E : ℝ) (rank c : ℕ) : Prop :=
  128 * φ ^ 2 * Real.log (2 / (δ / 3)) * (M * Lbar * rankLogFactor rank) ^ 2 * E ^ 2
    ≤ ε ^ 2 * (c : ℝ)

structure SqAccessLedger where

  pointReads : ℕ

  samplerReads : ℕ

  probReads : ℕ

  fieldOps : ℕ
  deriving DecidableEq, Repr

def sqTwoStageLedger (r c : ℕ) : SqAccessLedger where
  pointReads := 2 * r * c
  samplerReads := r + c
  probReads := r + c
  fieldOps := 2 * r * c

def SqAccessLedger.runtime (l : SqAccessLedger) : ℕ :=
  l.pointReads + l.samplerReads + l.probReads + l.fieldOps

def frameWeight {C R : Type} [Fintype C] [Fintype R] (Cc : Matrix C R ℂ) (i : C) : ℝ :=
  ∑ j, Complex.normSq (Cc i j)

def frameScale {C R : Type} [Fintype C] [Fintype R] (Cc : Matrix C R ℂ) (i : C) : ℝ :=
  (Real.sqrt (frameWeight Cc i))⁻¹

def frameUnit {C R : Type} [Fintype C] [Fintype R] (Cc : Matrix C R ℂ) (i : C) : R → ℂ :=
  fun j => if frameWeight Cc i = 0 then 0 else Cc i j * (frameScale Cc i : ℂ)

def frameProjection {R : Type} [Fintype R] (u : R → ℂ) : Matrix R R ℂ :=
  fun k l => star (u k) * u l

def frameOperator {C R : Type} [Fintype C] [Fintype R] (Cc : Matrix C R ℂ) : Matrix R R ℂ :=
  fun k l => ∑ i : C, (frameWeight Cc i : ℂ) * (frameProjection (frameUnit Cc i)) k l

def numericalEigenvalue {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (v : EuclideanSpace ℂ I) : ℝ :=
  (inner ℂ v (H.toEuclideanLin v)).re

def numericalRayleigh {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (v : EuclideanSpace ℂ I) : ℝ :=
  (inner ℂ v (H.toEuclideanLin v)).re / (‖v‖ ^ 2)

def numericalSpectrum {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian) : Fin (Fintype.card I) → ℝ :=
  orderedHermitianValues hH

def pow2 (p : ℕ) : ℝ := (2 : ℝ) ^ p

def fixedRound (p : ℕ) (x : ℝ) : ℝ := ((Int.floor (x * pow2 p) : ℤ) : ℝ) / pow2 p

def fixedBitWidth (m p : ℕ) : ℕ := m + p

structure SqWord (p : ℕ) where

  mantissa : ℤ
  deriving DecidableEq, Repr

def SqWord.value {p : ℕ} (w : SqWord p) : ℝ := (w.mantissa : ℝ) / 2 ^ p

def SqWord.add {p : ℕ} (a b : SqWord p) : SqWord p := ⟨a.mantissa + b.mantissa⟩

def SqWord.mul {p : ℕ} (a b : SqWord p) : SqWord (2 * p) := ⟨a.mantissa * b.mantissa⟩

def SqWord.rescaleTo {p t : ℕ} (a : SqWord p) (_h : p ≤ t) : SqWord t :=
  ⟨a.mantissa * 2 ^ (t - p)⟩

def intBitWidth (z : ℤ) : ℕ := Nat.log2 z.natAbs + 1

def SqWord.addBitCost {p : ℕ} (a b : SqWord p) : ℕ :=
  intBitWidth a.mantissa + intBitWidth b.mantissa + 1

def SqWord.mulBitCost {p : ℕ} (a b : SqWord p) : ℕ :=
  intBitWidth a.mantissa * intBitWidth b.mantissa

structure SqBitLedger where

  reads : ℕ

  multiplies : ℕ

  cacheBuilds : ℕ

  rowScales : ℕ

  rowAdds : ℕ

  repeats : ℕ
  deriving DecidableEq, Repr

def sketchArithmeticLedger (n r c q : ℕ) : SqBitLedger where
  reads := q * n * r
  multiplies := q * 2 * n * r
  cacheBuilds := q * r
  rowScales := q * c
  rowAdds := q * c
  repeats := q

def SqBitLedger.ramOps (l : SqBitLedger) : ℕ :=
  l.reads + l.multiplies + l.cacheBuilds + l.rowScales + l.rowAdds

def SqBitLedger.bitTime (l : SqBitLedger) (w : ℕ) : ℕ :=
  l.reads * w + l.multiplies * w * w + l.cacheBuilds * w + l.rowScales * w + l.rowAdds * w

def SqBitLedger.workspaceWords (l : SqBitLedger) : ℕ := l.cacheBuilds

end

end StageBSQNUMERICS
