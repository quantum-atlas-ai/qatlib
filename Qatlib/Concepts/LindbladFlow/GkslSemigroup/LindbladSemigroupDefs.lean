/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroup
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupDirichlet
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupKmsMixing
import Qatlib.Concepts.GibbsMetropolis.RationalBath.DiagonalMetropolisKernel
import Qatlib.Concepts.QuantumGibbs.FormAlgebra.ParentBridge
import Qatlib.Foundations.PureStateMath.Qubit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Concepts.LindbladFlow.GkslSemigroup
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Foundations.DirichletForm.KmsDirichlet

set_option autoImplicit false

namespace Qatlib.Concepts.LindbladFlow.GkslSemigroup

open Matrix Qatlib

open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal Classical

noncomputable section

variable {D : ℕ}

noncomputable def initialStateFactor (ρ σ : Operator D) : ℝ :=
  kmsNorm ρ (kmsDensityRatio ρ (σ - ρ))

noncomputable def referenceWeight (ρ : Operator D) : ℝ :=
  ‖(CFC.sqrt ρ)⁻¹‖

noncomputable def initialEntropy (σ ρ : Operator D) : ℝ :=
  relativeEntropy σ ρ

def EntropyContractionLaw (G : GKSL D) (ρ : Operator D) (η : ℝ) : Prop :=
  0 < η ∧ η ≤ 1 ∧
    ∀ (h : ℝ) (σ : Operator D), 0 < h → h ≤ 1 → IsDensityOperator σ →
      relativeEntropy (lindbladSemigroup G h σ) ρ ≤ (1 - η * h) * relativeEntropy σ ρ

def EntropyStepLaw (G : GKSL D) (ρ : Operator D) (η : ℝ) : Prop :=
  0 < η ∧ η ≤ 1 ∧
    ∀ σ : Operator D, IsDensityOperator σ →
      relativeEntropy (lindbladSemigroup G 1 σ) ρ ≤ (1 - η) * relativeEntropy σ ρ

def RetainedEntropyLaw (G : GKSL D) (ρ : Operator D) (η : ℝ) : Prop :=
  0 < η ∧ η ≤ 1 ∧
    ∀ (h : ℝ) (σ : Operator D), 0 < h → h ≤ 1 → IsDensityOperator σ →
      (1 - η * h) * relativeEntropy σ ρ ≤ relativeEntropy (lindbladSemigroup G h σ) ρ

structure MixingEntropyData (D : ℕ) where

  gen : GKSL D

  ref : Operator D

  refDensity : IsDensityOperator ref

  refFull : ref.PosDef

  gapRate : ℝ

  gapPos : 0 < gapRate

  selfAdj : KmsSelfAdjoint ref (gkslHeisenbergMap gen)

  gapHyp : KmsGapAtLeast ref (gkslHeisenbergMap gen) gapRate

  entropyRate : ℝ

  entropyLaw : EntropyContractionLaw gen ref entropyRate

structure MixingEntropyInterface (D : ℕ) where

  gen : GKSL D

  ref : Operator D

  gapRate : ℝ

  entropyRate : ℝ

  mixingInitialState : ∀ (σ : Operator D), IsDensityOperator σ → ∀ t : ℝ, 0 ≤ t →
    traceDistance (lindbladSemigroup gen t σ) ref ≤
      Real.exp (-gapRate * t) * initialStateFactor ref σ / 2

  mixingNormalization : ∀ (σ : Operator D), IsDensityOperator σ → ∀ t : ℝ, 0 ≤ t →
    traceDistance (lindbladSemigroup gen t σ) ref ≤
      Real.exp (-gapRate * t) * referenceWeight ref / 2

  mixingCombined : ∀ (σ : Operator D), IsDensityOperator σ → ∀ t : ℝ, 0 ≤ t →
    traceDistance (lindbladSemigroup gen t σ) ref ≤
      Real.exp (-gapRate * t) * min (initialStateFactor ref σ) (referenceWeight ref) / 2

  mixingTimeBound : ∀ (η : ℝ), 0 < η → η ≤ 1 →
    mixingTime gen ref η ≠ ⊤ ∧ (mixingTime gen ref η).toReal ≤
      Real.log ((referenceWeight ref + 1) / η) / gapRate

  entropyContraction : ∀ (σ : Operator D), IsDensityOperator σ → ∀ t : ℝ, 0 ≤ t →
    relativeEntropy (lindbladSemigroup gen t σ) ref ≤
      Real.exp (-entropyRate * t) * relativeEntropy σ ref

  entropyUnitStep : ∀ (σ : Operator D), IsDensityOperator σ → ∀ t : ℝ, 1 ≤ t →
    relativeEntropy (lindbladSemigroup gen t σ) ref ≤
      Real.exp entropyRate * Real.exp (-entropyRate * t) * relativeEntropy σ ref

  entropyMonotone : ∀ (σ : Operator D), IsDensityOperator σ → ∀ t : ℝ, 0 ≤ t →
    relativeEntropy (lindbladSemigroup gen t σ) ref ≤ relativeEntropy σ ref

def ckRankOne (i j : Fin D) : Operator D :=
  Matrix.of fun r c => if r = j ∧ c = i then 1 else 0

noncomputable def ckAcceptJump (E : Fin D → ℝ) (β : ℝ) (i j : Fin D) : Operator D :=
  if i = j then 0 else ((Real.sqrt (thermalAcceptance E β i j) : ℂ)) • ckRankOne i j

def ckHamiltonian (E : Fin D → ℝ) : Operator D :=
  Matrix.diagonal fun i => (E i : ℂ)

noncomputable def ckJumps (E : Fin D → ℝ) (β : ℝ) : Fin (D * D) → Operator D :=
  fun k => ckAcceptJump E β (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

noncomputable def ckGenerator (E : Fin D → ℝ) (β : ℝ) : GKSL D where
  ham := ckHamiltonian E
  hamHermitian := by
    unfold ckHamiltonian
    rw [isHermitian_diagonal_iff]
    intro i
    exact Complex.conj_ofReal (E i)
  jumps := ckJumps E β

noncomputable def ckEnergyClass (E : Fin D → ℝ) (i : Fin D) : Operator D :=
  Matrix.diagonal fun k => if E k = E i then 1 else 0

def ckStepReadouts (nStar : ℕ) : ℕ := 2 + nStar

def ckRunReadouts (m nStar : ℕ) : ℕ := m * ckStepReadouts nStar

noncomputable def ckDissipatorTerm (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ)
    (i j : Fin D) : Operator D :=
  ((thermalAcceptance E β i j : ℂ) * (p i : ℂ)) • (ckRankOne j j - ckRankOne i i)

noncomputable def ckJumpDissipator (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ)
    (k : Fin (D * D)) : Operator D :=
  (ckJumps E β k) * Matrix.diagonal (fun t => (p t : ℂ)) * (ckJumps E β k)ᴴ
    - (1 / 2 : ℂ) • ((ckJumps E β k)ᴴ * (ckJumps E β k)
        * Matrix.diagonal (fun t => (p t : ℂ))
      + Matrix.diagonal (fun t => (p t : ℂ)) * (ckJumps E β k)ᴴ * (ckJumps E β k))

noncomputable def ckRejectMass (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (i : Fin D) : ℝ :=
  thermalKernel D E β i i

noncomputable def ckAcceptInflow (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ)
    (j : Fin D) : ℝ :=
  ∑ i ∈ (Finset.univ : Finset (Fin D)).erase j,
    thermalAcceptance E β i j / (D : ℝ) * p i

noncomputable def ckRejectPart (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ)
    (j : Fin D) : ℝ :=
  ckRejectMass D E β j * p j

noncomputable def ckRecoveryTerm (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ)
    (j : Fin D) (n : ℕ) : ℝ :=
  (ckRejectMass D E β j) ^ n * p j

noncomputable def ckRecoveryTail (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ)
    (j : Fin D) (N : ℕ) : ℝ :=
  ∑' n : ℕ, ckRecoveryTerm D E β p j (N + n)

noncomputable def ckOneStepInflow (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ)
    (j : Fin D) : ℝ :=
  ckAcceptInflow D E β p j + ckRejectPart D E β p j

noncomputable def ckOneStepOperator (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ)
    : Operator D :=
  Matrix.diagonal fun j => ((ckOneStepInflow D E β p j : ℝ) : ℂ)

noncomputable def ckRecoveryTailTotal (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ)
    (N : ℕ) : ℝ :=
  ∑ j : Fin D, ckRecoveryTail D E β p j N

structure CkGeneratorInterface (D : ℕ) where

  energy : Fin D → ℝ

  temp : ℝ

  gibbsFixed : ∀ (hD : 0 < D),
    lindbladApply (ckGenerator energy temp) (diagonalGibbsDensity D hD energy temp) = 0

  gibbsSemigroup : ∀ (hD : 0 < D) (t : ℝ), 0 ≤ t →
    lindbladSemigroup (ckGenerator energy temp) t (diagonalGibbsDensity D hD energy temp)
      = diagonalGibbsDensity D hD energy temp

  jumpFilter : ∀ (i j : Fin D),
    ckEnergyClass energy j * ckAcceptJump energy temp i j = ckAcceptJump energy temp i j ∧
      ckAcceptJump energy temp i j * ckEnergyClass energy i = ckAcceptJump energy temp i j

  detailedBalance : ∀ (hD : 0 < D) (i j : Fin D),
    thermalAcceptance energy temp i j * (diagonalGibbsDist D hD energy temp).prob i
      = thermalAcceptance energy temp j i * (diagonalGibbsDist D hD energy temp).prob j

  windowError : ∀ (hD : 0 < D) (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (n : ℕ),
    ‖((gkslEulerMap (ckGenerator energy temp) h)^[n])
        (diagonalGibbsDensity D hD energy temp) - diagonalGibbsDensity D hD energy temp‖
      ≤ (n : ℝ) * (‖gkslDrift (ckGenerator energy temp)‖ ^ 2
        + (2 * ‖(ckGenerator energy temp).ham‖
          + 2 * ∑ j, ‖(ckGenerator energy temp).jumps j‖ ^ 2) ^ 2
          * Real.exp (2 * ‖(ckGenerator energy temp).ham‖
            + 2 * ∑ j, ‖(ckGenerator energy temp).jumps j‖ ^ 2)) * h ^ 2
        * Real.exp ((2 * ‖(ckGenerator energy temp).ham‖
          + 2 * ∑ j, ‖(ckGenerator energy temp).jumps j‖ ^ 2
          + ‖gkslDrift (ckGenerator energy temp)‖ ^ 2) * ((n : ℝ) * h))
        * ‖diagonalGibbsDensity D hD energy temp‖

  acceptTransport : ∀ (hD : 0 < D) (i j : Fin D), i ≠ j →
    D * thermalKernel D energy temp i j = thermalAcceptance energy temp i j

  rejectTransport : ∀ (hD : 0 < D) (i : Fin D),
    D * (1 - thermalKernel D energy temp i i)
      = ∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i, thermalAcceptance energy temp i j'

  oneStepAssembly : ∀ (hD : 0 < D) (p : Fin D → ℝ),
    ∑ j : Fin D, ckOneStepInflow D energy temp p j = ∑ i : Fin D, p i

  oneStepGibbs : ∀ (hD : 0 < D) (j : Fin D),
    ∑ i : Fin D, (diagonalGibbsDist D hD energy temp).prob i
        * thermalKernel D energy temp i j
      = (diagonalGibbsDist D hD energy temp).prob j

  recoveryWindow : ∀ (hD : 1 < D) (p : Fin D → ℝ) (N : ℕ) (j : Fin D),
    ckRecoveryTail D energy temp p j N
      = (ckRejectMass D energy temp j) ^ N * p j / (1 - ckRejectMass D energy temp j)

  realizedCost : ∀ (m nStar : ℕ), 4 * D ≤ nStar → 0 < m →
    m * (D * 2 * 2) < ckRunReadouts m nStar

noncomputable def ckConsumerKernel (D : ℕ) (E : Fin D → ℝ) (β : ℝ) : Fin D → Fin D → ℝ :=
  thermalKernel D E β

end

end Qatlib.Concepts.LindbladFlow.GkslSemigroup
