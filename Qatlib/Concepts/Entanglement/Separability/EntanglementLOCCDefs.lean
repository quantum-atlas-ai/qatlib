/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.EntanglementEntropy
import Qatlib.Concepts.QuantumEntropy.EntropyCalculus

/-!
# Schmidt-basis instruments and LOCC bookkeeping

`schmidtSpectrum` and `schmidtEntropy` define the reduced-state spectrum and entropy of a
normalized bipartite pure state, while `DiagonalInstrument` describes diagonal local instruments
in its Schmidt basis. It supplies branch weights and spectra, two-coordinate rotation operators,
filters for spectral T-transforms, and records for outcome and resource bookkeeping. These
constructions support the pure-state transformation framework discussed in [Nielsen1999] and the
quantum information background in [Wilde2017].

## Main statements

* `schmidtSpectrum` and `schmidtEntropy` extract the reduced-state eigenvalues and their
  entropy.
* `DiagonalInstrument`, `schmidtKraus`, and `schmidtBranch` describe diagonal local measurement
  branches.
* `rotationVector` and `tTransformInstrument` define two-coordinate constructions and a complete
  two-outcome filter.
* `LoccRoundLedger` and `LoccExecution` record costs and individual outcomes.

## References

* [Nielsen, 1999][Nielsen1999]
* [Wilde, 2017][Wilde2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ThreeBasis

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs

open Qatlib
open scoped BigOperators ComplexOrder

variable {D E n : ℕ}

/-- The eigenvalues of the first reduced density state of a normalized bipartite pure state,
representing its squared Schmidt coefficients. -/
noncomputable def schmidtSpectrum (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) : Fin D → ℝ :=
  (Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ)).M.H.eigenvalues

/-- The entropy of the reduced-state spectrum, computed as the sum of negative eigenvalue times
its natural logarithm. -/
noncomputable def schmidtEntropy (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) : ℝ :=
  ∑ j, Real.negMulLog (schmidtSpectrum ψ hψ j)

/-- The first reduced density state of a normalized bipartite pure state, viewed as a Hermitian
matrix. -/
noncomputable def reducedHermitian (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    HermitianMat (Fin D) ℂ :=
  (Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ)).M

/-- A unitary eigenvector matrix for the first reduced density state, chosen by its Hermitian
spectral decomposition. -/
noncomputable def schmidtUnitary (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    Matrix.unitaryGroup (Fin D) ℂ :=
  (reducedHermitian ψ hψ).H.eigenvectorUnitary

/-- The bipartite state after applying the adjoint reduced-state eigenvector unitary to the
first subsystem. -/
noncomputable def schmidtRotated (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    QState (Fin D × Fin E) :=
  ApplyGate (TensorGate ((schmidtUnitary ψ hψ).val.conjTranspose) (1 : Operator E)) ψ

/-- A finite family of real diagonal coefficients whose squared entries sum to one at every
basis index, encoding a complete diagonal local instrument. -/
structure DiagonalInstrument (D n : ℕ) where

  entry : Fin n → Fin D → ℝ

  hcomplete : ∀ j, (∑ i, entry i j ^ 2) = 1

/-- The complex diagonal operator formed from the real coefficients of one instrument outcome. -/
def DiagonalInstrument.op (I : DiagonalInstrument D n) (i : Fin n) : Operator D :=
  Matrix.diagonal (fun j => (I.entry i j : ℂ))

/-- The diagonal outcome operator conjugated by the reduced-state eigenvector unitary,
expressing it in the original first-subsystem basis. -/
noncomputable def schmidtKraus (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (I : DiagonalInstrument D n) (i : Fin n) : Operator D :=
  (schmidtUnitary ψ hψ).val * I.op i * (schmidtUnitary ψ hψ).val.conjTranspose

/-- The sum of the input spectral entries weighted by the squared diagonal coefficients of one
outcome. -/
noncomputable def branchMass (I : DiagonalInstrument D n) (spec : Fin D → ℝ) (i : Fin n) : ℝ :=
  ∑ j, I.entry i j ^ 2 * spec j

/-- The unnormalized spectral weights obtained by multiplying each input entry by the squared
diagonal coefficient of the selected outcome. -/
noncomputable def branchWeight (I : DiagonalInstrument D n) (spec : Fin D → ℝ) (i : Fin n) :
    Fin D → ℝ :=
  fun j => I.entry i j ^ 2 * spec j

/-- The outcome spectral weights divided by their total branch mass, using real division also
when the mass is zero. -/
noncomputable def branchSpectrum (I : DiagonalInstrument D n) (spec : Fin D → ℝ) (i : Fin n) :
    Fin D → ℝ :=
  fun j => I.entry i j ^ 2 * spec j / branchMass I spec i

/-- The unnormalized bipartite branch obtained by applying a diagonal outcome operator to the
first subsystem of the Schmidt-rotated state. -/
noncomputable def schmidtBranch (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (I : DiagonalInstrument D n) (i : Fin n) : QState (Fin D × Fin E) :=
  ApplyGate (TensorGate (I.op i) (1 : Operator E)) (schmidtRotated ψ hψ)

/-- The Schmidt-basis branch with its local outcome operator scaled by the reciprocal square
root of the supplied real parameter. -/
noncomputable def schmidtBranchScaled (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (I : DiagonalInstrument D n) (i : Fin n) (m : ℝ) : QState (Fin D × Fin E) :=
  ApplyGate (TensorGate (((Real.sqrt m)⁻¹ : ℂ) • (I.op i)) (1 : Operator E)) (schmidtRotated ψ hψ)

/-- The coordinate formula for either rotation vector on the selected indices, using
coefficients `c`, `s`, and `-s`. -/
noncomputable def rotationVector (c s : ℝ) (k l : Fin D) (dir : Fin 2) (j : Fin D) : ℂ :=
  if dir.val = 0 then
    if j = k then (c : ℂ) else if j = l then (s : ℂ) else 0
  else
    if j = k then (-(s : ℂ)) else if j = l then (c : ℂ) else 0

/-- The coordinate weights `c ^ 2` and `s ^ 2` for the chosen rotation direction and selected
indices. -/
noncomputable def rotationWeight (c s : ℝ) (k l : Fin D) (dir : Fin 2) (j : Fin D) : ℝ :=
  if dir.val = 0 then
    if j = k then c ^ 2 else if j = l then s ^ 2 else 0
  else
    if j = k then s ^ 2 else if j = l then c ^ 2 else 0

/-- The outer-product operator of the chosen rotation vector. No normalization or orthogonality
hypotheses are required by this definition. -/
noncomputable def rotationProjector (c s : ℝ) (k l : Fin D) (dir : Fin 2) : Operator D :=
  outerProduct (fun j => rotationVector c s k l dir j)

/-- The unnormalized branch obtained by applying the rotation-vector outer-product operator to
the first subsystem of the Schmidt-rotated state. -/
noncomputable def rotationBranchState (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (c s : ℝ) (k l : Fin D) (dir : Fin 2) : QState (Fin D × Fin E) :=
  ApplyGate (TensorGate (rotationProjector c s k l dir) (1 : Operator E)) (schmidtRotated ψ hψ)

/-- The sum of the input spectral entries weighted by the coordinate weights of the selected
rotation direction. -/
noncomputable def rotationBranchMass (spec : Fin D → ℝ) (c s : ℝ) (k l : Fin D) (dir : Fin 2) : ℝ :=
  ∑ j, rotationWeight c s k l dir j * spec j

/-- The second-subsystem vector obtained by contracting the Schmidt-rotated state against the
conjugate of the selected rotation vector. -/
noncomputable def rotationBranchSecond (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (c s : ℝ) (k l : Fin D) (dir : Fin 2) : QState (Fin E) :=
  fun a => ∑ j, (starRingEnd ℂ) (rotationVector c s k l dir j) * (schmidtRotated ψ hψ) (j, a)

/-- The coordinate formula that mixes the selected spectral entries with parameter `θ` while
retaining all other entries. -/
noncomputable def tTransformSpectrum (spec : Fin D → ℝ) (θ : ℝ) (k l : Fin D) (j : Fin D) : ℝ :=
  spec j + (1 - θ) * ((if j = k then spec l - spec k else 0)
    + (if j = l then spec k - spec l else 0))

/-- The filter ratio `p * tTransformSpectrum spec θ k l j / spec j`. -/
noncomputable def tTransformFilter (spec : Fin D → ℝ) (p θ : ℝ) (k l : Fin D) (j : Fin D) : ℝ :=
  p * tTransformSpectrum spec θ k l j / spec j

/-- A complete two-outcome diagonal instrument with entries given by square roots of the filter
and its complement, assuming every filter value lies between zero and one. -/
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

/-- The natural-number ceiling of `Real.log (n : ℝ) / Real.log 2`, used for outcome-bit
bookkeeping. -/
noncomputable def outcomeCostBits (n : ℕ) : ℕ :=
  Nat.ceil (Real.log ((n : ℝ)) / Real.log 2)

/-- A record of outcome count, outcome bits, peak-qubit count, and bit-time bookkeeping for a
local measurement round. -/
structure LoccRoundLedger (D E n : ℕ) where

  outcomes : ℕ

  outcomeBits : ℕ

  peakQubits : ℕ

  bitTime : ℕ

/-- The diagonal-round ledger assigning `n` outcomes, `outcomeCostBits n` outcome bits, `D` to
`peakQubits`, and `D * E` to `bitTime`. -/
noncomputable def diagonalRoundLedger (D E n : ℕ) : LoccRoundLedger D E n where
  outcomes := n
  outcomeBits := outcomeCostBits n
  peakQubits := D
  bitTime := D * E

/-- A record of one outcome index, its mass and entropy, and the associated local-round ledger. -/
structure LoccExecution (D E n : ℕ) where

  outcome : Fin n

  mass : ℝ

  entropy : ℝ

  ledger : LoccRoundLedger D E n

end Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs
