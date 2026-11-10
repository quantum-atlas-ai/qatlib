/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.DegenerateEnergyInstrument
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroup
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCoreDefs
import Mathlib.Data.Int.Interval
open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.LindbladFlow.GkslSemigroup
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
namespace StageAQUANTUMGIBBS

open Matrix Qatlib
open scoped Classical BigOperators ComplexOrder

structure PhaseGrid where

  levels : ℕ

  levelsPos : 0 < levels

noncomputable def phaseIndexReal (G : PhaseGrid) (t E : ℝ) : ℝ :=
  -(t * E * (G.levels : ℝ)) / (2 * Real.pi)

noncomputable def phaseIndex (G : PhaseGrid) (t E : ℝ) : ℤ :=
  ⌊phaseIndexReal G t E + 1 / 2⌋

noncomputable def energyLabel (G : PhaseGrid) (t E : ℝ) : Fin G.levels :=
  ⟨(phaseIndex G t E % (G.levels : ℤ)).toNat, by
    have h0 : 0 ≤ phaseIndex G t E % (G.levels : ℤ) :=
      Int.emod_nonneg _ (by exact_mod_cast Nat.ne_of_gt G.levelsPos)
    have h1 : phaseIndex G t E % (G.levels : ℤ) < (G.levels : ℤ) :=
      Int.emod_lt_of_pos _ (by exact_mod_cast G.levelsPos)
    have h2 : (phaseIndex G t E % (G.levels : ℤ)).toNat < G.levels := by
      have := (Int.toNat_lt (n := G.levels) (z := phaseIndex G t E % (G.levels : ℤ)) h0).2 h1
      simpa using this
    omega⟩

theorem phaseIndex_round_error (G : PhaseGrid) (t E : ℝ) :
    |(phaseIndex G t E : ℝ) - phaseIndexReal G t E| ≤ 1 / 2 := by
  have hfloor : (phaseIndex G t E : ℝ) ≤ phaseIndexReal G t E + 1 / 2 := by
    have h := Int.floor_le (phaseIndexReal G t E + 1 / 2)
    simpa [phaseIndex] using h
  have hfloor' : phaseIndexReal G t E - 1 / 2 < (phaseIndex G t E : ℝ) := by
    have h := Int.lt_floor_add_one (phaseIndexReal G t E + 1 / 2)
    have h' : phaseIndexReal G t E + 1 / 2 < (⌊phaseIndexReal G t E + 1 / 2⌋ : ℤ) + 1 := by
      simpa [Int.cast_add, Int.cast_one] using h
    have h'' : phaseIndexReal G t E + 1 / 2 < (phaseIndex G t E : ℝ) + 1 := by
      simpa [phaseIndex, Int.cast_add, Int.cast_one] using h'
    linarith
  rw [abs_le]
  constructor
  · linarith
  · linarith

structure EnergyOracle (D : ℕ) where

  ham : Operator D

  hamHermitian : ham.IsHermitian

  time : ℝ

  timePos : 0 < time

  evolution : Operator D

  evolutionUnitary : evolution ∈ Matrix.unitaryGroup (Fin D) ℂ

  evolutionPhase : ∀ (E : ℝ) (v : QState (Fin D)),
    ham *ᵥ v = (E : ℂ) • v →
      evolution *ᵥ v = Complex.exp (-(time * E) * Complex.I) • v

abbrev QpeSpace (G : PhaseGrid) (D : ℕ) : Type := Fin G.levels × Fin D

noncomputable def registerProjector (G : PhaseGrid) (j : Fin G.levels) :
    Operator G.levels :=
  Matrix.diagonal (fun a => if a = j then (1 : ℂ) else 0)

noncomputable def qpeCircuit {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) :
    Matrix (QpeSpace G D) (QpeSpace G D) ℂ :=
  TensorGate (QFTMatrix G.levels)ᴴ (1 : Operator D) * ControlledPowers O.evolution G.levels

noncomputable def qpeKraus {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) :
    Fin G.levels → Matrix (QpeSpace G D) (QpeSpace G D) ℂ :=
  fun j => TensorGate (registerProjector G j) (1 : Operator D) * qpeCircuit O G

noncomputable def energyEigenvector {D : ℕ} (O : EnergyOracle D) (i : Fin D) :
    QState (Fin D) :=
  ⇑ (O.hamHermitian.eigenvectorBasis i)

noncomputable def energyLevel {D : ℕ} (O : EnergyOracle D) (i : Fin D) : ℝ :=
  O.hamHermitian.eigenvalues i

theorem energyEigenvector_spec {D : ℕ} (O : EnergyOracle D) (i : Fin D) :
    O.ham *ᵥ energyEigenvector O i = (energyLevel O i : ℂ) • energyEigenvector O i := by
  simpa [energyEigenvector, energyLevel] using O.hamHermitian.mulVec_eigenvectorBasis i

noncomputable def energyProjector {D : ℕ} (O : EnergyOracle D) (E : ℝ) : Operator D :=
  ∑ i : Fin D, if energyLevel O i = E then
      Matrix.of fun a b =>
        if a = b then
          (energyEigenvector O i a) * (starRingEnd ℂ) (energyEigenvector O i b)
        else 0
    else 0

noncomputable def energyLabelMap {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) :
    Fin D → Fin G.levels :=
  fun i => energyLabel G O.time (energyLevel O i)

noncomputable def metropolisAcceptWeight (β E E' : ℝ) : ℝ :=
  if E' ≤ E then 1 else Real.exp (-(β * (E' - E)))

theorem metropolisAcceptWeight_mem (β E E' : ℝ) (hβ : 0 ≤ β) :
    0 ≤ metropolisAcceptWeight β E E' ∧ metropolisAcceptWeight β E E' ≤ 1 := by
  unfold metropolisAcceptWeight
  by_cases h : E' ≤ E
  · rw [if_pos h]
    constructor <;> linarith
  · rw [if_neg h]
    have hE : E < E' := lt_of_not_ge h
    constructor
    · positivity
    · have hmul : 0 ≤ β * (E' - E) := mul_nonneg hβ (by linarith)
      have hexp := Real.exp_le_exp.mpr (show -(β * (E' - E)) ≤ 0 by linarith)
      simpa [Real.exp_zero] using hexp

theorem metropolisAcceptWeight_one (β E E' : ℝ) (h : E' ≤ E) :
    metropolisAcceptWeight β E E' = 1 := by
  unfold metropolisAcceptWeight
  rw [if_pos h]

theorem metropolisAcceptWeight_exp (β E E' : ℝ) (h : E < E') :
    metropolisAcceptWeight β E E' = Real.exp (-(β * (E' - E))) := by
  unfold metropolisAcceptWeight
  rw [if_neg (not_le_of_gt h)]

structure DoeblinData (M : ℕ) where

  nu : Fin M → ℝ

  nuSum : (∑ j, nu j) = 1

  nuNonneg : ∀ j, 0 ≤ nu j

  epsilon : ℝ

  epsilonPos : 0 < epsilon

noncomputable def gibbsState {D : ℕ} (O : EnergyOracle D) (β : ℝ) : Operator D :=
  Qatlib.Concepts.LindbladFlow.GkslSemigroup.gibbsDensity O.ham β

noncomputable def gibbsWeight (β E : ℝ) : ℝ :=
  Real.exp (-(β * E))

structure QpeCostLedger where

  levels : ℕ

  controlledPowers : ℕ

  inverseQftGates : ℕ

  controlledSystemQubits : ℕ

noncomputable def qpeCostLedger {D : ℕ} (_O : EnergyOracle D) (G : PhaseGrid) :
    QpeCostLedger :=
  { levels := G.levels
    controlledPowers := G.levels
    inverseQftGates := G.levels
    controlledSystemQubits := D }

noncomputable def labelChain (M : ℕ) (accept : Fin M → ℝ) (propose : Fin M → Fin M → ℝ) :
    Fin M → Fin M → ℝ :=
  fun j k => accept k * propose k j

structure ChainMinorization (M : ℕ) (T : Fin M → Fin M → ℝ) where

  nu : Fin M → ℝ

  nuSum : (∑ k, nu k) = 1

  nuNonneg : ∀ k, 0 ≤ nu k

  epsilon : ℝ

  epsilonPos : 0 < epsilon

  epsilonLtOne : epsilon < 1

  minorize : ∀ j k, epsilon * nu k ≤ T j k

noncomputable def lindbladGenerator {D : ℕ} (O : EnergyOracle D) :
    Qatlib.Concepts.LindbladFlow.GkslSemigroup.GKSL D :=
  { ham := O.ham, hamHermitian := O.hamHermitian, jumps := fun _ => 0 }

structure ProposalOracle (D : ℕ) where

  unitary : Operator D

  unitary_mem : unitary ∈ Matrix.unitaryGroup (Fin D) ℂ

  inverse : Operator D

  inverse_mem : inverse ∈ Matrix.unitaryGroup (Fin D) ℂ

  inverse_mul : inverse * unitary = 1

  inverse_mul' : unitary * inverse = 1

structure LabelProjectors (D M : ℕ) where

  proj : Fin M → Operator D

  hermitian : ∀ j, (proj j)ᴴ = proj j

  idempotent : ∀ j, proj j * proj j = proj j

  orthogonality : ∀ j k, j ≠ k → proj j * proj k = 0

  total : (∑ j, proj j) = 1

structure AcceptWeights (M : ℕ) where

  weight : Fin M → ℝ

  nonneg : ∀ j, 0 ≤ weight j

  le_one : ∀ j, weight j ≤ 1

noncomputable def acceptScale (w : ℝ) : ℂ := (Real.sqrt w : ℂ)

theorem acceptScale_sq {w : ℝ} (hw : 0 ≤ w) :
    acceptScale w * acceptScale w = (w : ℂ) := by
  have h : (Real.sqrt w : ℝ) * (Real.sqrt w : ℝ) = w := Real.mul_self_sqrt hw
  unfold acceptScale
  rw [← Complex.ofReal_mul, h]

theorem acceptScale_star (w : ℝ) : star (acceptScale w) = acceptScale w := by
  simp [acceptScale, Complex.conj_ofReal]

theorem acceptScale_sq_sub {w : ℝ} (hw : w ≤ 1) :
    acceptScale (1 - w) * acceptScale (1 - w) = 1 - (w : ℂ) := by
  rw [acceptScale_sq (by linarith)]
  exact Complex.ofReal_sub 1 w

noncomputable def metropolisAcceptKraus {D M : ℕ} (P : LabelProjectors D M)
    (Q : ProposalOracle D) (α : AcceptWeights M) (j : Fin M) : Operator D :=
  acceptScale (α.weight j) • (P.proj j * Q.unitary)

noncomputable def metropolisRejectKraus {D M : ℕ} (P : LabelProjectors D M)
    (Q : ProposalOracle D) (α : AcceptWeights M) (j : Fin M) : Operator D :=
  acceptScale (1 - α.weight j) • (Q.inverse * P.proj j * Q.unitary)

noncomputable def metropolisJointKraus {D M : ℕ} (P : LabelProjectors D M)
    (Q : ProposalOracle D) (α : AcceptWeights M) : Fin M × Fin 2 → Operator D :=
  fun jb =>
    if jb.2.val = 0 then metropolisAcceptKraus P Q α jb.1
    else metropolisRejectKraus P Q α jb.1

noncomputable def proposalFidelity {D M : ℕ} (P : LabelProjectors D M)
    (Q : ProposalOracle D) (ρ : Operator D) (j : Fin M) : ℝ :=
  (Matrix.trace (P.proj j * (Q.unitary * ρ * Q.unitaryᴴ))).re

structure MetropolisStepLedger where

  energyControlledPowers : ℕ

  energyInverseQftGates : ℕ

  proposalApplications : ℕ

  rewindApplications : ℕ

  controlledSystemQubits : ℕ

  classicalReadoutBits : ℕ

end StageAQUANTUMGIBBS
end Qatlib.Concepts.MbqcFlow.FlowDecision
