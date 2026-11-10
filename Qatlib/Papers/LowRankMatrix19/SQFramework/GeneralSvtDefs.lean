/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.SketchAnalysis.SketchArithmetic
import Qatlib.Papers.LowRankMatrix19.SQFramework.SqClosureEstimationDefs
import Qatlib.Concepts.SketchSpectral.EvenSVT.EvenSVTDecompositionNormBoundsSamp
import Qatlib.Papers.LowRankMatrix19.SDPTrace.Lemma627Samp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Call
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.SketchSpectral.EvenSVT

set_option autoImplicit false
set_option warningAsError false

namespace Qatlib.Papers.LowRankMatrix19.SQFramework
namespace ConstructionStageB
namespace StageBSQGENERALSVT

open Matrix
open Qatlib
open scoped Classical BigOperators Matrix.Norms.Frobenius Matrix.Norms.L2Operator

noncomputable section

inductive QvParity where

  | even

  | odd
  deriving DecidableEq, Repr

def qvQuotientEven (p : ℝ → ℝ) (x : ℝ) : ℝ := p (Real.sqrt x)

def qvQuotientOdd (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else p (Real.sqrt x) / Real.sqrt x

def qvTransformEven {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (p : ℝ → ℝ) : Matrix I I ℂ :=
  hermitianFunction (Aᴴ * A) (Matrix.isHermitian_conjTranspose_mul_self A)
    (fun x => (qvQuotientEven p x : ℂ))

def qvTransformOdd {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (p : ℝ → ℝ) : Matrix I I ℂ :=
  A * hermitianFunction (Aᴴ * A) (Matrix.isHermitian_conjTranspose_mul_self A)
    (fun x => (qvQuotientOdd p x : ℂ))

structure QvEvenSmoothness (d : ℕ) where

  supQ : ℝ

  supQ' : ℝ

  supQbar : ℝ

  supQbar' : ℝ

  supQ_le_one : supQ ≤ 1

  supQ'_le : supQ' ≤ (d : ℝ) ^ 2

  supQbar_le : supQbar ≤ (d : ℝ) ^ 2

  supQbar'_le : supQbar' ≤ (d : ℝ) ^ 4

structure QvOddSmoothness (d : ℕ) where

  supQ : ℝ

  supQ' : ℝ

  supQbar : ℝ

  supQbar' : ℝ

  supQ_le : supQ ≤ (d : ℝ)

  supQ'_le : supQ' ≤ (d : ℝ) ^ 3

  supQbar_le : supQbar ≤ (d : ℝ) ^ 3

  supQbar'_le : supQbar' ≤ (d : ℝ) ^ 5

def qvEvenRuntime (d : ℕ) (normA normPv eps delta logMN : ℝ) : ℝ :=
  (d : ℝ) ^ 16 * normA ^ 10 * (eps * normPv)⁻¹ ^ 6 * (Real.log delta⁻¹) ^ 3
    + ((d : ℝ) ^ 12 * normA ^ 8 + (d : ℝ) ^ 6 * normA ^ 2) * (eps * normPv)⁻¹ ^ 4
      * (Real.log delta⁻¹) ^ 2 * logMN

def qvEvenSamples (d : ℕ) (normA normPv eps delta logMN : ℝ) : ℝ :=
  (d : ℝ) ^ 12 * normA ^ 4 * (eps ^ 4 * normPv ^ 6)⁻¹ * logMN
    * (Real.log delta⁻¹) ^ 3

def qvOddRuntime (d : ℕ) (normA normPv eps delta logMN : ℝ) : ℝ :=
  (d : ℝ) ^ 22 * normA ^ 16 * (eps * normPv)⁻¹ ^ 6
    + ((d : ℝ) ^ 16 * normA ^ 12 + (d : ℝ) ^ 10 * normA ^ 4 * delta⁻¹)
      * (eps * normPv)⁻¹ ^ 4 * logMN

def qvOddSamples (d : ℕ) (normPv eps delta logMN : ℝ) : ℝ :=
  (d : ℝ) ^ 8 * (eps ^ 2 * delta * normPv ^ 4)⁻¹ * logMN

def qvQuantumPerSample (d : ℕ) (normPv : ℝ) (polylog : ℝ) : ℝ :=
  (d : ℝ) * normPv⁻¹ * polylog

def qvPolylog (logMN delta : ℝ) : ℝ := logMN + Real.log delta⁻¹

def qvQuantumTotal (d : ℕ) (normPv eps : ℝ) (polylog : ℝ) : ℝ :=
  (d : ℝ) * normPv⁻¹ * eps⁻¹ * polylog

def qvQuantumTotalOdd (d : ℕ) (normPv eps delta logMN : ℝ) : ℝ :=
  (d : ℝ) * normPv⁻¹ * eps⁻¹ * logMN * delta⁻¹

def qvEvenScale (d : ℕ) (normA normPv eps delta logMN : ℝ) : ℝ :=
  max 1 (d : ℝ) * max 1 normA * max 1 ((eps * normPv)⁻¹)
    * max 1 (Real.log delta⁻¹) * max 1 logMN

def qvOddScale (d : ℕ) (normA normPv eps delta logMN : ℝ) : ℝ :=
  max 1 (d : ℝ) * max 1 normA * max 1 ((eps * normPv)⁻¹)
    * max 1 (delta⁻¹) * max 1 logMN

def qvEvenSampleScale (d : ℕ) (normA normPv eps delta logMN : ℝ) : ℝ :=
  max 1 (d : ℝ) * max 1 normA * max 1 ((eps ^ 4 * normPv ^ 6)⁻¹)
    * max 1 (Real.log delta⁻¹) * max 1 logMN

def qvOddSampleScale (d : ℕ) (normPv eps delta logMN : ℝ) : ℝ :=
  max 1 (d : ℝ) * max 1 ((eps ^ 2 * delta * normPv ^ 4)⁻¹)
    * max 1 (delta⁻¹) * max 1 logMN

def thresholdSvt (sigma eta lam : ℝ) : ℝ :=
  if sigma * (1 + eta) ≤ lam then lam
  else if lam < sigma * (1 - eta) then 0
  else (sigma * (1 + eta)) * (lam - sigma * (1 - eta))
    / (sigma * (1 + eta) - sigma * (1 - eta))

def thresholdInv (sigma eta lam : ℝ) : ℝ :=
  if sigma ≤ lam then 1 / lam
  else if lam < sigma * (1 - eta) then 0
  else (1 / sigma) * (lam - sigma * (1 - eta)) / (sigma - sigma * (1 - eta))

def thresholdRatio (sigma eta x : ℝ) : ℝ :=
  if x = 0 then 0 else thresholdSvt sigma eta (Real.sqrt x) / Real.sqrt x

def thresholdSvtOperator {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (sigma eta : ℝ) : Matrix I I ℂ :=
  A * hermitianFunction (Aᴴ * A) (Matrix.isHermitian_conjTranspose_mul_self A)
    (fun x => (thresholdRatio sigma eta x : ℂ))

def thresholdInvOperator {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (sigma eta : ℝ) : Matrix I I ℂ :=
  hermitianFunction (Aᴴ * A) (Matrix.isHermitian_conjTranspose_mul_self A)
    (fun x => (thresholdInv sigma eta x : ℂ))

def cor67K (normAF sigma : ℝ) : ℝ := normAF ^ 2 / sigma ^ 2

def cor67Kappa (normA sigma : ℝ) : ℝ := normA ^ 2 / sigma ^ 2

def cor67Runtime (K kappa rowRatio eps eta delta : ℝ) : ℝ :=
  K ^ 3 * kappa ^ 5 / (eta ^ 6 * eps ^ 6) * (Real.log delta⁻¹) ^ 3
    + K ^ 2 * kappa * rowRatio / (eta ^ 2 * eps ^ 2) * (Real.log delta⁻¹) ^ 2

def cor67RowBudget (K eps delta : ℝ) : ℝ := K / eps ^ 2 * Real.log delta⁻¹

def cor67Phi (normX normAF normAhatRow : ℝ) : ℝ :=
  normX ^ 2 * normAF ^ 2 / normAhatRow ^ 2

def cor67QuantumRuntime (normAF sigma : ℝ) : ℝ := normAF / sigma

def cor67PriorRuntime (normAF sigma eps delta : ℝ) : ℝ :=
  normAF ^ 24 / (sigma ^ 24 * eps ^ 12) * (Real.log delta⁻¹) ^ 3

def cor610TensorNorms (normMF normW : ℝ) : ℝ := normMF ^ 2 * normW ^ 2

def cor610Runtime (normMF normW eps delta : ℝ) : ℝ :=
  normMF ^ 4 * normW ^ 4 / eps ^ 2 * Real.log delta⁻¹

def cor610QuantumRuntime (normMF normW eps : ℝ) : ℝ := normMF ^ 2 * normW ^ 2 / eps

def cor612K (traceX lambdaK : ℝ) : ℝ := traceX / lambdaK

def cor612Kappa (normX lambdaK : ℝ) : ℝ := normX ^ 2 / lambdaK

def cor612Runtime (normXF normX lambdaK eta eps deltaK : ℝ) : ℝ :=
  normXF ^ 6 / (lambdaK ^ 2 * normX ^ 2) / (eta ^ 6 * eps ^ 6)
    * (Real.log deltaK⁻¹) ^ 3

def cor612Samples (normXF normX lambdaI eta eps delta : ℝ) : ℝ :=
  normXF ^ 4 / (lambdaI * normX ^ 2) / (eta ^ 2 * eps ^ 2) * (Real.log delta⁻¹) ^ 2

def cor612SpectralFilter (lambdaHat gap : ℝ) (x : ℝ) : ℝ :=
  if |x - lambdaHat| ≤ gap / 8 then 1
  else if gap / 4 ≤ |x - lambdaHat| then 0
  else (gap / 4 - |x - lambdaHat|) / (gap / 4 - gap / 8)

def cor612PriorRuntime (normXF normX lambdaK eta eps deltaK : ℝ) : ℝ :=
  normXF ^ 36 / (normX ^ 12 * lambdaK ^ 12) / (eta ^ 6 * eps ^ 12)
    * (Real.log deltaK⁻¹) ^ 3

def cor615Runtime (phi K kappa eps eta delta : ℝ) : ℝ :=
  phi ^ 6 * K ^ 3 * kappa ^ 11 / (eta ^ 6 * eps ^ 6) * (Real.log delta⁻¹) ^ 3

def cor615Samples (phi K kappa eps eta delta normXStar normXHat : ℝ) : ℝ :=
  phi ^ 4 * K ^ 2 * kappa ^ 5 / (eta ^ 2 * eps ^ 2) * (normXStar ^ 2 / normXHat ^ 2)
    * (Real.log delta⁻¹) ^ 2

def cor615WorstRuntime (phi K kappa eps eta delta : ℝ) : ℝ :=
  phi ^ 6 * K ^ 3 * kappa ^ 8 / (eta ^ 6 * eps ^ 6) * (Real.log delta⁻¹) ^ 3

def cor615WorstSamples (phi K kappa eps eta delta : ℝ) : ℝ :=
  phi ^ 4 * K ^ 2 * kappa ^ 4 / (eta ^ 2 * eps ^ 2) * (Real.log delta⁻¹) ^ 2

def cor615QuantumRuntime (normAF sigma : ℝ) : ℝ := normAF / sigma

def cor617Runtime (lam eps eta delta : ℝ) : ℝ :=
  lam ^ (-28 : ℤ) / (eta ^ 6 * eps ^ 6) * (Real.log delta⁻¹) ^ 3

def cor617Samples (lam eps eta delta logM : ℝ) : ℝ :=
  lam ^ (-14 : ℤ) / (eta ^ 2 * eps ^ 4) * (Real.log delta⁻¹) ^ 2 * logM

def cor617Phi (eps normXF normKF : ℝ) : ℝ := (1 + eps) ^ 2 * normXF ^ 4 / normKF ^ 2

def cor617MNorm (normF traceF : ℝ) : ℝ := normF ^ 2 / traceF ^ 2

def cor617PhiPrime (normM : ℝ) : ℝ := 1 / normM ^ 2

def cor618Runtime (normXF normX gamma eps delta : ℝ) : ℝ :=
  normXF ^ 6 * normX ^ 16 * gamma ^ 11 / eps ^ 6 * (Real.log delta⁻¹) ^ 3

def cor618Samples (normXF normX gamma m normAlphaHat eps delta : ℝ) : ℝ :=
  normXF ^ 4 * normX ^ 6 * gamma ^ 5 * (gamma ^ 2 * m / normAlphaHat ^ 2) / eps ^ 4
    * (Real.log delta⁻¹) ^ 2

def cor618DimensionFreeGamma (normXF : ℝ) : ℝ := 1 / normXF ^ 2

def cor620Runtime (normHF normH sigma eps delta : ℝ) : ℝ :=
  normHF ^ 6 * normH ^ 16 / (sigma ^ 16 * eps ^ 6) * (Real.log delta⁻¹) ^ 3

def cor620Samples (normHF normH sigma eps delta : ℝ) : ℝ :=
  normHF ^ 4 * normH ^ 8 / (sigma ^ 8 * eps ^ 4) * (Real.log delta⁻¹) ^ 3

def cor620NaturalRuntime (normHF normH sigma eps delta : ℝ) : ℝ :=
  normHF ^ 6 * normH ^ 10 / (sigma ^ 16 * eps ^ 6) * (Real.log delta⁻¹) ^ 3

def cor621Runtime (normH normHF eps delta : ℝ) : ℝ :=
  normH ^ 16 * normHF ^ 6 / eps ^ 6 * (Real.log delta⁻¹) ^ 3

def cor621Samples (normH normHF eps delta : ℝ) : ℝ :=
  normH ^ 8 * normHF ^ 4 / eps ^ 4 * (Real.log delta⁻¹) ^ 3

def fCos (x : ℝ) : ℝ := Real.cos (Real.sqrt x)

def fSinc (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sin (Real.sqrt x) / Real.sqrt x

def fCosDeriv (x : ℝ) : ℝ :=
  if x = 0 then 0 else -Real.sin (Real.sqrt x) / (2 * Real.sqrt x)

def fSincDeriv (x : ℝ) : ℝ :=
  if x = 0 then 0 else Real.cos (Real.sqrt x) / (2 * x)

def cor625Runtime (F m n eps delta sqA qA : ℝ) : ℝ :=
  (F ^ 18 / eps ^ 40 * (Real.log delta⁻¹) ^ 2 * (Real.log n) ^ 20 * sqA
    + F ^ 22 / eps ^ 46 * (Real.log n) ^ 23
    + m * F ^ 8 / eps ^ 18 * (Real.log n) ^ 8 * qA
    + m * F ^ 14 / eps ^ 28 * (Real.log n) ^ 13) * (Real.log delta⁻¹) ^ 3

def cor625UnitSqRuntime (F m n eps delta : ℝ) : ℝ :=
  (F ^ 22 / eps ^ 46 * (Real.log n) ^ 23
    + m * F ^ 14 / eps ^ 28 * (Real.log n) ^ 13) * (Real.log delta⁻¹) ^ 3

def cor625Rounds (n eps : ℝ) : ℝ := 16 * Real.log n / eps ^ 2

def cor625Step (eps : ℝ) : ℝ := eps / 4

def cor625PriorRuntime (m r eps n : ℝ) : ℝ :=
  m * r ^ 57 / eps ^ 92 * (Real.log n) ^ 37

def cor625RankRuntime (m r eps n : ℝ) : ℝ :=
  r ^ 11 / eps ^ 46 * (Real.log n) ^ 23 + m * r ^ 7 / eps ^ 28 * (Real.log n) ^ 13

def cor625QuantumRuntime (F m eps : ℝ) : ℝ :=
  F ^ 7 / eps ^ (15 / 2) + Real.sqrt m * F ^ 2 / eps ^ 4

def lemma626Runtime (F m n theta delta sqA qA : ℝ) : ℝ :=
  (F ^ 18 / theta ^ 38 * (Real.log n) ^ 19 * sqA
    + F ^ 22 / theta ^ 44 * (Real.log n) ^ 22
    + m * F ^ 8 / theta ^ 16 * (Real.log n) ^ 7 * qA
    + m * F ^ 14 / theta ^ 26 * (Real.log n) ^ 12) * (Real.log delta⁻¹) ^ 3
    + (Real.log n / theta ^ 2) * n

def lemma626Samples (F n theta delta sqA : ℝ) : ℝ :=
  F ^ 18 / theta ^ 38 * (Real.log n) ^ 19 * sqA * (Real.log delta⁻¹) ^ 3

def lemma626Precision (theta : ℝ) : ℝ := theta / 3

def fSqrt (sigma x : ℝ) : ℝ :=
  if x < sigma ^ 2 / 2 then 0
  else if x < sigma ^ 2 then 2 * x / sigma - sigma
  else Real.sqrt x

def fInv (sigma x : ℝ) : ℝ :=
  if x < sigma ^ 2 / 2 then 0
  else if x < sigma ^ 2 then 2 * x / sigma ^ 4 - 1 / sigma ^ 2
  else 1 / x

def cor631Runtime (normBF normB normWF normW eps sigma delta : ℝ) : ℝ :=
  (normBF ^ 6 * normB ^ 4 / (eps ^ 6 * sigma ^ 10)
    + normWF ^ 6 * normW ^ 10 / (eps ^ 6 * sigma ^ 16)) * (Real.log delta⁻¹) ^ 3

def cor631Samples (normBF eps sigma delta : ℝ) : ℝ :=
  normBF ^ 4 / (eps ^ 2 * sigma ^ 4) * (Real.log delta⁻¹) ^ 2

def cor631RowBudget (normBF eps sigma delta : ℝ) : ℝ :=
  normBF ^ 2 / (eps ^ 2 * sigma ^ 2) * Real.log delta⁻¹

def cor631ColumnError (eps normB sigma : ℝ) : ℝ := eps * normB ^ 2 / sigma ^ 2

def polyDominatedBy (cost perSample : ℝ) (k : ℕ) (C : ℝ) : Prop :=
  cost ≤ C * perSample ^ k

end

end StageBSQGENERALSVT
