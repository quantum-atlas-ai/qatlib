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

/-!
# Numerical definitions and ledgers for even SVT

This module defines source Gram data, rank logarithm factors, concentration scales, and sample
budgets for two-stage sketches. It also introduces normalized row frames, spectral observables,
fixed-point words, and explicit access and bit-cost ledgers for the numerical analysis of
sampling-based matrix arithmetic in [ChiaEtAl2022].

## Main statements

* `requiredRowSamples`: The real-valued row-sample requirement, including the squared Lipschitz,
  rank-logarithm, energy, and inverse-error factors.
* `frameOperator`: The sum of normalized row outer products weighted by the corresponding
  squared row norms.
* `SqWord`: A fixed-point word consisting of an integer mantissa at precision `p`.
* `sketchArithmeticLedger`: The repeated sketch arithmetic ledger with explicit counts
  determined by `n`, `r`, `c`, and `q`.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

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

/-- The source Gram matrix `Aᴴ * A`. -/
def sourceOperator {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ) : Matrix C C ℂ :=
  Aᴴ * A

/-- The source matrix's squared Frobenius energy. -/
def sourceEnergy {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ) : ℝ :=
  sketchSquared A

/-- The rank-dependent factor `1 + log (1 + r)`. -/
def rankLogFactor (r : ℕ) : ℝ := 1 + Real.log (1 + (r : ℝ))

/-- Row and column oversampling factors at least one, with the column factor at most twice the
row factor. -/
structure SqOversampling where

  row : ℝ

  col : ℝ

  row_ge_one : 1 ≤ row

  col_ge_one : 1 ≤ col

  col_le_two_row : col ≤ 2 * row

/-- The row Gram tail scale `√(8 * φ² * log (2 / (δ / 3)) / r) * E`. -/
def rowTailScale (φ : ℝ) (δ : ℝ) (r : ℕ) (E : ℝ) : ℝ :=
  Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 3)) / (r : ℝ)) * E

/-- The column Gram tail scale `√(8 * φ² * log (2 / (δ / 3)) / c) * (2 * E)`. -/
def colTailScale (φ : ℝ) (δ : ℝ) (c : ℕ) (E : ℝ) : ℝ :=
  Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 3)) / (c : ℝ)) * (2 * E)

/-- The real-valued row-sample requirement, including the squared Lipschitz, rank-logarithm,
energy, and inverse-error factors. -/
def requiredRowSamples (L ε φ δ E : ℝ) (rank : ℕ) : ℝ :=
  32 * φ ^ 2 * Real.log (2 / (δ / 3)) * (L * rankLogFactor rank) ^ 2 * E ^ 2 / ε ^ 2

/-- The real-valued column-sample requirement, including the squared norm, Lipschitz,
rank-logarithm, energy, and inverse-error factors. -/
def requiredColSamples (M Lbar ε φ δ E : ℝ) (rank : ℕ) : ℝ :=
  128 * φ ^ 2 * Real.log (2 / (δ / 3)) * (M * Lbar * rankLogFactor rank) ^ 2 * E ^ 2 / ε ^ 2

/-- The denominator-cleared inequality expressing the row-sample budget. -/
def rowBudgetMul (L ε φ δ E : ℝ) (rank r : ℕ) : Prop :=
  32 * φ ^ 2 * Real.log (2 / (δ / 3)) * (L * rankLogFactor rank) ^ 2 * E ^ 2
    ≤ ε ^ 2 * (r : ℝ)

/-- The denominator-cleared inequality expressing the column-sample budget. -/
def colBudgetMul (M Lbar ε φ δ E : ℝ) (rank c : ℕ) : Prop :=
  128 * φ ^ 2 * Real.log (2 / (δ / 3)) * (M * Lbar * rankLogFactor rank) ^ 2 * E ^ 2
    ≤ ε ^ 2 * (c : ℝ)

/-- A ledger of point reads, sampler reads, probability reads, and field operations. -/
structure SqAccessLedger where

  pointReads : ℕ

  samplerReads : ℕ

  probReads : ℕ

  fieldOps : ℕ
  deriving DecidableEq, Repr

/-- The two-stage ledger with `2 * r * c` point reads and field operations and `r + c` sampler
and probability reads. -/
def sqTwoStageLedger (r c : ℕ) : SqAccessLedger where
  pointReads := 2 * r * c
  samplerReads := r + c
  probReads := r + c
  fieldOps := 2 * r * c

/-- The sum of all four access-ledger counters. -/
def SqAccessLedger.runtime (l : SqAccessLedger) : ℕ :=
  l.pointReads + l.samplerReads + l.probReads + l.fieldOps

/-- The squared Euclidean norm of row `i` of the frame matrix. -/
def frameWeight {C R : Type} [Fintype C] [Fintype R] (Cc : Matrix C R ℂ) (i : C) : ℝ :=
  ∑ j, Complex.normSq (Cc i j)

/-- The reciprocal square root of the frame row's weight. -/
def frameScale {C R : Type} [Fintype C] [Fintype R] (Cc : Matrix C R ℂ) (i : C) : ℝ :=
  (Real.sqrt (frameWeight Cc i))⁻¹

/-- The frame row normalized by its weight, with the zero vector used when the row weight is
zero. -/
def frameUnit {C R : Type} [Fintype C] [Fintype R] (Cc : Matrix C R ℂ) (i : C) : R → ℂ :=
  fun j => if frameWeight Cc i = 0 then 0 else Cc i j * (frameScale Cc i : ℂ)

/-- The conjugate outer-product matrix with entries `star (u k) * u l`. -/
def frameProjection {R : Type} [Fintype R] (u : R → ℂ) : Matrix R R ℂ :=
  fun k l => star (u k) * u l

/-- The sum of normalized row outer products weighted by the corresponding squared row norms. -/
def frameOperator {C R : Type} [Fintype C] [Fintype R] (Cc : Matrix C R ℂ) : Matrix R R ℂ :=
  fun k l => ∑ i : C, (frameWeight Cc i : ℂ) * (frameProjection (frameUnit Cc i)) k l

/-- The real quadratic form `Re ⟨v, H v⟩`, without normalization of `v`. -/
def numericalEigenvalue {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (v : EuclideanSpace ℂ I) : ℝ :=
  (inner ℂ v (H.toEuclideanLin v)).re

/-- The real quadratic form divided by the squared norm of `v`. -/
def numericalRayleigh {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (v : EuclideanSpace ℂ I) : ℝ :=
  (inner ℂ v (H.toEuclideanLin v)).re / (‖v‖ ^ 2)

/-- The ordered real eigenvalues of a Hermitian matrix. -/
def numericalSpectrum {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian) : Fin (Fintype.card I) → ℝ :=
  orderedHermitianValues hH

/-- The real power `2^p` used as the fixed-point scale. -/
def pow2 (p : ℕ) : ℝ := (2 : ℝ) ^ p

/-- Rounds `x` downward to the grid of multiples of `2^(-p)` using an integer floor. -/
def fixedRound (p : ℕ) (x : ℝ) : ℝ := ((Int.floor (x * pow2 p) : ℤ) : ℝ) / pow2 p

/-- The sum of the magnitude-width parameter `m` and precision parameter `p`. -/
def fixedBitWidth (m p : ℕ) : ℕ := m + p

/-- A fixed-point word consisting of an integer mantissa at precision `p`. -/
structure SqWord (p : ℕ) where

  mantissa : ℤ
  deriving DecidableEq, Repr

/-- The real value of a fixed-point word, given by its mantissa divided by `2^p`. -/
def SqWord.value {p : ℕ} (w : SqWord p) : ℝ := (w.mantissa : ℝ) / 2 ^ p

/-- Adds fixed-point words by adding their integer mantissas. -/
def SqWord.add {p : ℕ} (a b : SqWord p) : SqWord p := ⟨a.mantissa + b.mantissa⟩

/-- Multiplies fixed-point words by multiplying mantissas and doubling the precision. -/
def SqWord.mul {p : ℕ} (a b : SqWord p) : SqWord (2 * p) := ⟨a.mantissa * b.mantissa⟩

/-- Rescales a fixed-point word to precision `t ≥ p` by multiplying its mantissa by `2^(t - p)`. -/
def SqWord.rescaleTo {p t : ℕ} (a : SqWord p) (_h : p ≤ t) : SqWord t :=
  ⟨a.mantissa * 2 ^ (t - p)⟩

/-- The bit-width measure `Nat.log2 z.natAbs + 1` for an integer. -/
def intBitWidth (z : ℤ) : ℕ := Nat.log2 z.natAbs + 1

/-- The addition bit-cost measure given by the two mantissa widths plus one. -/
def SqWord.addBitCost {p : ℕ} (a b : SqWord p) : ℕ :=
  intBitWidth a.mantissa + intBitWidth b.mantissa + 1

/-- The multiplication bit-cost measure given by the product of the two mantissa widths. -/
def SqWord.mulBitCost {p : ℕ} (a b : SqWord p) : ℕ :=
  intBitWidth a.mantissa * intBitWidth b.mantissa

/-- A ledger of reads, multiplications, cache builds, row scalings, row additions, and
repetitions. -/
structure SqBitLedger where

  reads : ℕ

  multiplies : ℕ

  cacheBuilds : ℕ

  rowScales : ℕ

  rowAdds : ℕ

  repeats : ℕ
  deriving DecidableEq, Repr

/-- The repeated sketch arithmetic ledger with explicit counts determined by `n`, `r`, `c`, and
`q`. -/
def sketchArithmeticLedger (n r c q : ℕ) : SqBitLedger where
  reads := q * n * r
  multiplies := q * 2 * n * r
  cacheBuilds := q * r
  rowScales := q * c
  rowAdds := q * c
  repeats := q

/-- The sum of read, multiplication, cache-build, row-scaling, and row-addition counts. -/
def SqBitLedger.ramOps (l : SqBitLedger) : ℕ :=
  l.reads + l.multiplies + l.cacheBuilds + l.rowScales + l.rowAdds

/-- The ledger's bit-time estimate, charging reads and linear operations by word width and
multiplications by its square. -/
def SqBitLedger.bitTime (l : SqBitLedger) (w : ℕ) : ℕ :=
  l.reads * w + l.multiplies * w * w + l.cacheBuilds * w + l.rowScales * w + l.rowAdds * w

/-- The workspace-word count defined as the number of cache builds. -/
def SqBitLedger.workspaceWords (l : SqBitLedger) : ℕ := l.cacheBuilds

end

end StageBSQNUMERICS
