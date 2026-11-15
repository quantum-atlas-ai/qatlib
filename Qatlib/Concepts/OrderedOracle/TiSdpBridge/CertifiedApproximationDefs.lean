/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.ApproximationAlgorithms
public import Mathlib.RingTheory.Polynomial.Chebyshev

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

set_option autoImplicit false

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge

open Matrix Polynomial

open scoped Classical BigOperators Matrix.Norms.L2Operator

abbrev RatComplex := ℚ × ℚ

def ratNormSq (z : RatComplex) : ℚ := z.1 ^ 2 + z.2 ^ 2

def natBinaryLength (n : ℕ) : ℕ := n.log2 + 1

def ratBitLength (q : ℚ) : ℕ :=
  1 + natBinaryLength q.num.natAbs + natBinaryLength q.den

def ratComplexBitLength (z : RatComplex) : ℕ := ratBitLength z.1 + ratBitLength z.2

structure RationalMatrix (O I : ℕ) where

  entries : Fin O → Fin I → RatComplex

def rationalMatrixBitLength {O I : ℕ} (A : RationalMatrix O I) : ℕ :=
  ∑ o, ∑ i, ratComplexBitLength (A.entries o i)

def RatComplex.toComplex (z : RatComplex) : ℂ :=
  ((z.1 : ℝ) : ℂ) + ((z.2 : ℝ) : ℂ) * Complex.I

def ratMatrixLift {O I : ℕ} (A : Matrix (Fin O) (Fin I) ℚ) : Matrix (Fin O) (Fin I) ℂ :=
  A.map fun q => ((q : ℝ) : ℂ)

noncomputable def cheb (n : ℕ) : Polynomial ℝ := Polynomial.Chebyshev.T ℝ (n : ℤ)

noncomputable def chebNodeN (N j : ℕ) : ℝ := Real.cos ((2 * j + 1) * Real.pi / (2 * N))

structure ChebParams where

  nodes : ℕ

  interpDegree : ℕ

  degree_eq : interpDegree + 1 = nodes

  nodes_pos : 0 < nodes

def chebParams (N : ℕ) (hN : 0 < N) : ChebParams :=
  { nodes := N, interpDegree := N - 1, degree_eq := by omega, nodes_pos := hN }

def chebGridExcept (N j : ℕ) : Finset ℕ := (Finset.range N).filter fun k => k ≠ j

noncomputable def chebLagrangeNum (N j : ℕ) : Polynomial ℝ :=
  ∏ k ∈ chebGridExcept N j, (Polynomial.X - Polynomial.C (chebNodeN N k))

noncomputable def chebLagrangeDen (N j : ℕ) : ℝ :=
  ∏ k ∈ chebGridExcept N j, (chebNodeN N j - chebNodeN N k)

noncomputable def chebInterpolantPoly (N : ℕ) (f : ℝ → ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range N,
    Polynomial.C (f (chebNodeN N j) / chebLagrangeDen N j) * chebLagrangeNum N j

noncomputable def ratRayleighQuotient {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ)
    (v : Fin D → ℚ) : ℚ :=
  (∑ i, ∑ j, v i * A i j * v j) / (∑ i, v i ^ 2)

noncomputable def ratResidualSq {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ)
    (v : Fin D → ℚ) (ρ : ℚ) : ℚ :=
  ∑ i, (∑ j, A i j * v j - ρ * v i) ^ 2

noncomputable def ratNormalizedResidualSq {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ)
    (v : Fin D → ℚ) (ρ : ℚ) : ℚ :=
  ratResidualSq A v ρ / (∑ i, v i ^ 2)

noncomputable def ratVectorSq {D : ℕ} (v : Fin D → ℚ) : ℚ := ∑ i, v i ^ 2

structure SpectralRun (D : ℕ) where

  quotient : ℚ

  residualSq : ℚ

  bitTime : ℕ

  bitSpace : ℕ

noncomputable def spectralRun {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ) (v : Fin D → ℚ)
    (inputBits : ℕ) : SpectralRun D where
  quotient := ratRayleighQuotient A v
  residualSq := ratNormalizedResidualSq A v (ratRayleighQuotient A v)
  bitTime := (D + 1) ^ 3 * (inputBits + 1)
  bitSpace := (D + 1) ^ 2 * (inputBits + 1)

noncomputable def spectralMultiplicity {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (j : Fin (Fintype.card I)) : ℕ :=
  (Finset.univ.filter fun i : Fin (Fintype.card I) =>
    orderedHermitianValues hA i = orderedHermitianValues hA j).card

structure SpectralLedger (D : ℕ) where

  dim : ℕ

  inputBits : ℕ

  precisionBits : ℕ

  gapBits : ℕ

  bitTime : ℕ

  bitSpace : ℕ

noncomputable def spectralLedger (D : ℕ) (inputBits precisionBits gapBits : ℕ) :
    SpectralLedger D where
  dim := D
  inputBits := inputBits
  precisionBits := precisionBits
  gapBits := gapBits
  bitTime := (D + 1) ^ 3 * (inputBits + precisionBits + gapBits + 1)
  bitSpace := (D + 1) ^ 2 * (inputBits + precisionBits + 1)

noncomputable def ratGramMatrix {O I : ℕ} (A : Matrix (Fin O) (Fin I) ℚ) :
    Matrix (Fin I) (Fin I) ℚ :=
  A.transpose * A

inductive CertifiedSpectralVerdict where

  | certified (quotient halfWidth : ℝ)

  | stopped (residual : ℝ)

structure CertifiedSpectralRun where

  verdict : CertifiedSpectralVerdict

  bitTime : ℕ

  bitSpace : ℕ

inductive CertifiedSingularVerdict where

  | certified (sqLower sqUpper lower upper : ℝ)

  | stopped (residual : ℝ)

structure ChebNodeReads (N : ℕ) where

  values : Fin N → ℝ

structure FuncEvalRun (I : Type) where

  approx : Matrix I I ℂ

  nodeReads : ℕ

  coefficientBits : ℕ

  spaceBits : ℕ

  errorBound : ℝ

noncomputable def chebFuncEval {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (fr : ℝ → ℝ) (N : ℕ) (inputBits : ℕ) (εq : ℚ)
    (ε : ℝ) : FuncEvalRun I :=
  let p := chebInterpolantPoly N fr
  { approx := aeval A (p.map Complex.ofRealHom)
    nodeReads := N
    coefficientBits := (N + 1) * (inputBits + 1) + ratBitLength εq
    spaceBits := (N + 1) * (inputBits + 1)
    errorBound := ε }

structure FuncEvalCost where

  nodeReads : ℕ

  coefficientBits : ℕ

  spaceBits : ℕ

def funcEvalCost (N : ℕ) (inputBits : ℕ) (ε : ℚ) : FuncEvalCost where
  nodeReads := N
  coefficientBits := (N + 1) * (inputBits + 1) + ratBitLength ε
  spaceBits := (N + 1) * (inputBits + 1)

structure TriBlock where

  a : ℚ

  b : ℚ

  c : RatComplex

  ab_ne : a ≠ b

noncomputable def TriBlock.toMatrix (T : TriBlock) : Matrix (Fin 2) (Fin 2) ℂ :=
  let e00 : ℂ := ((T.a : ℝ) : ℂ)
  let e01 : ℂ := T.c.toComplex
  let e11 : ℂ := ((T.b : ℝ) : ℂ)
  fun i j => if i.val = 0 then (if j.val = 0 then e00 else e01)
    else (if j.val = 1 then e11 else 0)

noncomputable def triBlockSpecProjA (T : TriBlock) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i.val = 0 then
      (if j.val = 0 then 1 else T.c.toComplex / (((T.a - T.b : ℚ) : ℝ) : ℂ))
    else 0

noncomputable def triBlockSpecProjB (T : TriBlock) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i.val = 0 then
      (if j.val = 0 then 0 else -(T.c.toComplex / (((T.a - T.b : ℚ) : ℝ) : ℂ)))
    else (if j.val = 1 then 1 else 0)

noncomputable def triBlockCondition (T : TriBlock) : ℝ :=
  spectralFrobenius (triBlockSpecProjA T) + spectralFrobenius (triBlockSpecProjB T)

noncomputable def triBlockConditionClosed (T : TriBlock) : ℝ :=
  2 * Real.sqrt (1 + (T.c.1 ^ 2 + T.c.2 ^ 2) / ((T.a - T.b) ^ 2))

noncomputable def zeroPadRows {O I D : ℕ} (A : Matrix (Fin O) (Fin I) ℚ) :
    Matrix (Fin D) (Fin I) ℚ :=
  fun i j => if h : i.val < O then A ⟨i.val, h⟩ j else 0

noncomputable def zeroPadCols {O I J : ℕ} (A : Matrix (Fin O) (Fin I) ℚ) :
    Matrix (Fin O) (Fin J) ℚ :=
  fun i j => if h : j.val < I then A i ⟨j.val, h⟩ else 0

noncomputable def ratProjector {D : ℕ} (v : EuclideanSpace ℝ (Fin D)) :
    Matrix (Fin D) (Fin D) ℝ :=
  fun i j => v i * v j / (∑ k, v k ^ 2)

structure SpectralProjectionRun (D : ℕ) where

  projector : Matrix (Fin D) (Fin D) ℝ

  quotient : ℝ

  errorBound : ℝ

  bitTime : ℕ

  bitSpace : ℕ

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
