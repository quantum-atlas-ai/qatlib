/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.EntanglementEntropy
import Qatlib.Concepts.QuantumEntropy.EntropyCalculus
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ThreeBasis

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs

open Qatlib
open scoped BigOperators ComplexOrder

variable {D E n : ℕ}

noncomputable def schmidtSpectrum (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) : Fin D → ℝ :=
  (Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ)).M.H.eigenvalues

noncomputable def schmidtEntropy (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) : ℝ :=
  ∑ j, Real.negMulLog (schmidtSpectrum ψ hψ j)

noncomputable def reducedHermitian (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    HermitianMat (Fin D) ℂ :=
  (Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ)).M

noncomputable def schmidtUnitary (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    Matrix.unitaryGroup (Fin D) ℂ :=
  (reducedHermitian ψ hψ).H.eigenvectorUnitary

noncomputable def schmidtRotated (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    QState (Fin D × Fin E) :=
  ApplyGate (TensorGate ((schmidtUnitary ψ hψ).val.conjTranspose) (1 : Operator E)) ψ

structure DiagonalInstrument (D n : ℕ) where

  entry : Fin n → Fin D → ℝ

  hcomplete : ∀ j, (∑ i, entry i j ^ 2) = 1

def DiagonalInstrument.op (I : DiagonalInstrument D n) (i : Fin n) : Operator D :=
  Matrix.diagonal (fun j => (I.entry i j : ℂ))

noncomputable def schmidtKraus (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (I : DiagonalInstrument D n) (i : Fin n) : Operator D :=
  (schmidtUnitary ψ hψ).val * I.op i * (schmidtUnitary ψ hψ).val.conjTranspose

noncomputable def branchMass (I : DiagonalInstrument D n) (spec : Fin D → ℝ) (i : Fin n) : ℝ :=
  ∑ j, I.entry i j ^ 2 * spec j

noncomputable def branchWeight (I : DiagonalInstrument D n) (spec : Fin D → ℝ) (i : Fin n) :
    Fin D → ℝ :=
  fun j => I.entry i j ^ 2 * spec j

noncomputable def branchSpectrum (I : DiagonalInstrument D n) (spec : Fin D → ℝ) (i : Fin n) :
    Fin D → ℝ :=
  fun j => I.entry i j ^ 2 * spec j / branchMass I spec i

noncomputable def schmidtBranch (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (I : DiagonalInstrument D n) (i : Fin n) : QState (Fin D × Fin E) :=
  ApplyGate (TensorGate (I.op i) (1 : Operator E)) (schmidtRotated ψ hψ)

noncomputable def schmidtBranchScaled (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (I : DiagonalInstrument D n) (i : Fin n) (m : ℝ) : QState (Fin D × Fin E) :=
  ApplyGate (TensorGate (((Real.sqrt m)⁻¹ : ℂ) • (I.op i)) (1 : Operator E)) (schmidtRotated ψ hψ)

noncomputable def rotationVector (c s : ℝ) (k l : Fin D) (dir : Fin 2) (j : Fin D) : ℂ :=
  if dir.val = 0 then
    if j = k then (c : ℂ) else if j = l then (s : ℂ) else 0
  else
    if j = k then (-(s : ℂ)) else if j = l then (c : ℂ) else 0

noncomputable def rotationWeight (c s : ℝ) (k l : Fin D) (dir : Fin 2) (j : Fin D) : ℝ :=
  if dir.val = 0 then
    if j = k then c ^ 2 else if j = l then s ^ 2 else 0
  else
    if j = k then s ^ 2 else if j = l then c ^ 2 else 0

noncomputable def rotationProjector (c s : ℝ) (k l : Fin D) (dir : Fin 2) : Operator D :=
  outerProduct (fun j => rotationVector c s k l dir j)

noncomputable def rotationBranchState (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (c s : ℝ) (k l : Fin D) (dir : Fin 2) : QState (Fin D × Fin E) :=
  ApplyGate (TensorGate (rotationProjector c s k l dir) (1 : Operator E)) (schmidtRotated ψ hψ)

noncomputable def rotationBranchMass (spec : Fin D → ℝ) (c s : ℝ) (k l : Fin D) (dir : Fin 2) : ℝ :=
  ∑ j, rotationWeight c s k l dir j * spec j

noncomputable def rotationBranchSecond (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (c s : ℝ) (k l : Fin D) (dir : Fin 2) : QState (Fin E) :=
  fun a => ∑ j, (starRingEnd ℂ) (rotationVector c s k l dir j) * (schmidtRotated ψ hψ) (j, a)

noncomputable def tTransformSpectrum (spec : Fin D → ℝ) (θ : ℝ) (k l : Fin D) (j : Fin D) : ℝ :=
  spec j + (1 - θ) * ((if j = k then spec l - spec k else 0)
    + (if j = l then spec k - spec l else 0))

noncomputable def tTransformFilter (spec : Fin D → ℝ) (p θ : ℝ) (k l : Fin D) (j : Fin D) : ℝ :=
  p * tTransformSpectrum spec θ k l j / spec j

def tTransformInstrument (D : ℕ) (spec : Fin D → ℝ) (p θ : ℝ) (k l : Fin D)
    (hfilter : ∀ j, tTransformFilter spec p θ k l j ≤ 1)
    (hfilter0 : ∀ j, 0 ≤ tTransformFilter spec p θ k l j) : DiagonalInstrument D 2 where
  entry := fun i j =>
    if i.val = 0 then Real.sqrt (tTransformFilter spec p θ k l j)
    else Real.sqrt (1 - tTransformFilter spec p θ k l j)
  hcomplete := by
    intro j
    have hsq : (Real.sqrt (tTransformFilter spec p θ k l j)) ^ 2
        + (Real.sqrt (1 - tTransformFilter spec p θ k l j)) ^ 2 = 1 := by
      have h0 : 0 ≤ tTransformFilter spec p θ k l j := hfilter0 j
      have h1 : tTransformFilter spec p θ k l j ≤ 1 := hfilter j
      rw [Real.sq_sqrt h0, Real.sq_sqrt (by linarith)]
      ring
    show (∑ i : Fin 2, (if i.val = 0 then Real.sqrt (tTransformFilter spec p θ k l j)
        else Real.sqrt (1 - tTransformFilter spec p θ k l j)) ^ 2) = 1
    rw [Fin.sum_univ_two]
    simp only [show (0 : Fin 2).val = 0 from rfl, show ¬((1 : Fin 2).val = 0) by simp]
    exact hsq

noncomputable def outcomeCostBits (n : ℕ) : ℕ :=
  Nat.ceil (Real.log ((n : ℝ)) / Real.log 2)

structure LoccRoundLedger (D E n : ℕ) where

  outcomes : ℕ

  outcomeBits : ℕ

  peakQubits : ℕ

  bitTime : ℕ

noncomputable def diagonalRoundLedger (D E n : ℕ) : LoccRoundLedger D E n where
  outcomes := n
  outcomeBits := outcomeCostBits n
  peakQubits := D
  bitTime := D * E

structure LoccExecution (D E n : ℕ) where

  outcome : Fin n

  mass : ℝ

  entropy : ℝ

  ledger : LoccRoundLedger D E n

end Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs
