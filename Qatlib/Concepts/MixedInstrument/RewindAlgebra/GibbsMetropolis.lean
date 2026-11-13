/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.GibbsMetropolisDefs
import Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalanceFixedPointQuan
import Qatlib.Concepts.GibbsMetropolis.EnergyReadout
import Qatlib.Concepts.GibbsMetropolis.RationalBath.RationalHeatBathChannel
import Qatlib.Concepts.GibbsMetropolis.RationalBath.ApproximateRationalGibbs
import Qatlib.Concepts.QuantumGibbs.RejectionRewind.RejectionBudgetQuan
import Qatlib.Concepts.MixedInstrument.RewindAlgebra.RejectionFailureBoundQuan

/-!
# Quantum Metropolis contracts and finite examples

This module studies explicit contracts for quantum Metropolis sampling [TemmeEtAl2011]. It
proves rational and dyadic Gibbs approximation estimates, a two projector rejection formula and
asymptotic lower bound, and conditional Gibbs stationarity. It also constructs finite
counterexamples to `clause41Body`, `clause42Body`, `clause44Body`, and `clause45Body` under
their stated hypotheses.

## Main statements

* `clause28_block3_dyadicWindow`: For positive inverse temperature and scaled energies in `[0,
  1]`, the dyadic rational heat bath approximates the diagonal Gibbs density with the stated sum
  of energy shift and integer weight errors.
* `rejectFailProb_twoProjector`: For `0 ≤ d ≤ 1`, the two projector rejection failure
  probability after `n` rounds equals `d * (1 - d) * (d ^ 2 + (1 - d) ^ 2) ^ n`.
* `duplicate_detailed_balance_impossible`: No complex linear realization of the duplicate
  example Temme map satisfies quantum detailed balance with its Gibbs state.
* `clause42_contract_false`: The universal detailed balance contract `clause42Body` is false.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

open Qatlib.Concepts.RiskEstimation.PopulationGap

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.CoherentSim.CleanQPEBands
open Qatlib.Concepts.GibbsMetropolis.EnergyReadout
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.MixedInstrument.RewindAlgebra

open Qatlib.Concepts.MixedInstrument.RewindAlgebra Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.MixedInstrument.RewindAlgebra
open Qatlib.Concepts.QuantumGibbs.DetailedBalance
open Qatlib.Concepts.QuantumGibbs.RejectionRewind
open Matrix
open scoped BigOperators Classical

section ContractBodies
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib

/-- The contract combining unknown Hamiltonian branch maps, normalized joint probabilities,
eigenbasis independence, dyadic acceptance, energy readout estimates, and a clean phase
estimation implementation. -/
def clause41Body : Prop :=
  ∀ (D : ℕ) (A : Operator D), A.IsHermitian →
    ∀ (t : ℝ) (M : ℕ) (hM : 2 ≤ M) (ht : t ≠ 0),
      ∀ (β : ℝ), 0 ≤ β →
        ∀ (k : ℕ), 0 < k →
          ∀ (old : Fin M),

            (∃ B : (Fin M × Bool) → (Operator D →ₗ[ℂ] Operator (D * 2)),
                (∀ p : Fin M × Bool, ∀ ρ : Operator D,
                  B p ρ = unknownHBranch A t M β k old p.1 p.2 ρ) ∧
                (∀ p, CompletelyPositive (B p)) ∧
                (∀ ρ : Operator D,
                  Matrix.trace (∑ p, B p ρ) = Matrix.trace ρ)) ∧

            (∀ ρ : Operator D, IsDensityOperator ρ →
                (∀ p : Fin M × Bool,
                  0 ≤ unknownHJointProb A t M β k old p.1 p.2 ρ ∧
                    unknownHJointProb A t M β k old p.1 p.2 ρ ≤ 1) ∧
                ∑ p : Fin M × Bool, unknownHJointProb A t M β k old p.1 p.2 ρ = 1) ∧

            (∀ (ψ : Fin D → QState (Fin D)) (eig : Fin D → ℝ),
                (∀ i, A *ᵥ ψ i = (eig i : ℂ) • ψ i) →
                (∀ i j, Qatlib.Foundations.PureStateMath.Inner (ψ i) (ψ j) = if i = j then 1 else 0) →
                (∀ x : QState (Fin D), ∑ i, Qatlib.Foundations.PureStateMath.Inner (ψ i) x • ψ i = x) →
                ∀ (ψ' : Fin D → QState (Fin D)) (eig' : Fin D → ℝ),
                  (∀ i, A *ᵥ ψ' i = (eig' i : ℂ) • ψ' i) →
                  (∀ i j, Qatlib.Foundations.PureStateMath.Inner (ψ' i) (ψ' j) = if i = j then 1 else 0) →
                  (∀ x : QState (Fin D), ∑ i, Qatlib.Foundations.PureStateMath.Inner (ψ' i) x • ψ' i = x) →
                  ∀ (ρ : Operator D) (z : Fin M),
                    unknownHEigenProb A t M ψ eig ρ z
                      = unknownHEigenProb A t M ψ' eig' ρ z ∧
                    (Matrix.trace (qpePovmElement A t M z * ρ)).re
                      = unknownHEigenProb A t M ψ eig ρ z) ∧

            (∀ z : Fin M,
                0 ≤ fairBitAcceptMass k (labelAcceptance t M β old z) ∧
                  fairBitAcceptMass k (labelAcceptance t M β old z)
                    ≤ labelAcceptance t M β old z ∧
                  labelAcceptance t M β old z
                    - fairBitAcceptMass k (labelAcceptance t M β old z)
                    ≤ (1 / 2 : ℝ) ^ k ∧
                  ∃ j : ℕ,
                    fairBitAcceptMass k (labelAcceptance t M β old z)
                      = (j : ℝ) / (2 : ℝ) ^ k) ∧

            ((∀ (e : ℝ) (z : Fin M),
                phaseDistance (phaseOfEnergy t e) ((z.val : ℝ) / (M : ℝ)) ≤ 1 / (M : ℝ) →
                |e - labelEnergy t M z| ≤ 2 * Real.pi / |t| / (M : ℝ)) ∧
              (∀ (δ ea ea' eb eb' : ℝ), 0 ≤ δ → |ea - ea'| ≤ δ → |eb - eb'| ≤ δ →
                |min 1 (Real.exp (-β * (eb - ea)))
                  - min 1 (Real.exp (-β * (eb' - ea')))| ≤ 2 * β * δ)) ∧

            (∀ (H : Type) [Fintype H] [DecidableEq H] (ksim : ℕ)
                (U : Matrix H H ℂ) (F : Matrix H (Fin D) ℂ),
              ProjectedUnitaryEncoding A U F F →
                ∃ (V : Operator D) (eig : Fin D → ℝ),
                  V ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
                  A = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ ∧
                  ∃ (n : ℕ) (cs : List (AdjointStep (Bool × (Bool × H)))),
                    WellFormedAdjointCircuit cs ∧
                    let word := cleanQPEWord M (scaleEightAmplifyWord (hamiltonianFrame F) cs)
                    WellFormedAdjointCircuit word ∧
                      adjointQueryCount word = qpeWindowQueries M n ∧
                      adjointGateCount word = qpeWindowGates M n ∧
                      ∀ i : Fin D,
                        8 / Real.pi ^ 2 - (1 / 2 : ℝ) ^ ksim ≤
                          cleanQPEEventMass M
                            (evaluate
                                (TensorGate (1 : Operator M) (controlOracle (signalEnergyOracle U)))
                                word *ᵥ cleanQPEInput M (by omega)
                                  (signalEnergyFrame F *ᵥ (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i)))
                            (Finset.univ.filter (fun z : Fin M =>
                              phaseDistance (-t * eig i / (2 * Real.pi))
                                ((z.val : ℝ) / (M : ℝ)) ≤ 1 / (M : ℝ))))

end ContractBodies

section ContractBodies
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib

/-- The contract combining variational gap mixing, a rejection budget, phase estimation circuit
counts, and run ledger identities with strictly positive step queries. -/
def clause44Body : Prop :=

  (∀ (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D)),
      (∀ i j : Fin D, Qatlib.Foundations.PureStateMath.Inner (ψ i) (ψ j) = if i = j then 1 else 0) →
      (∀ x : QState (Fin D), ∑ i, Qatlib.Foundations.PureStateMath.Inner (ψ i) x • ψ i = x) →
      ∀ ens : ProposalEnsemble D,
        proposalEnsembleLegal ens →
        proposalSymmetric ens →
        ∀ β : ℝ, 0 ≤ β →
          ∀ Δ : ℝ, 0 < Δ →
            IsTransitionMatrix (temmeStepMatrix E ψ ens β) →
            IsReversible (temmeStepMatrix E ψ ens β) (diagonalGibbsDist D hD E β).prob →
            variationalGapPremise (temmeStepMatrix E ψ ens β)
              (diagonalGibbsDist D hD E β).prob Δ →
            ∀ (i : Fin D) (m : ℕ),
              tvDistance (kernelPower (temmeStepMatrix E ψ ens β) m i)
                (diagonalGibbsDist D hD E β).prob
                ≤ (1 / 2) *
                    Real.sqrt ((1 - (diagonalGibbsDist D hD E β).prob i) /
                      (diagonalGibbsDist D hD E β).prob i) * (1 - Δ) ^ m) ∧

  RejectionBudget ∧

  (∀ (H : Type) [Fintype H] [DecidableEq H] (D M : ℕ) (_hM : 2 ≤ M)
      (A : Operator D) (U : Matrix H H ℂ) (F : Matrix H (Fin D) ℂ) (_t : ℝ),
    A.IsHermitian → ProjectedUnitaryEncoding A U F F →
      ∃ (n : ℕ) (cs : List (AdjointStep (Bool × (Bool × H)))),
        WellFormedAdjointCircuit cs ∧
        adjointQueryCount (cleanQPEWord M (scaleEightAmplifyWord (hamiltonianFrame F) cs))
          = qpeWindowQueries M n ∧
        adjointGateCount (cleanQPEWord M (scaleEightAmplifyWord (hamiltonianFrame F) cs))
          = qpeWindowGates M n) ∧

  (∀ (D M k n nStar m : ℕ),
      (metropolisRunLedger m D M k n nStar).prepQueries = qpeWindowQueries M n ∧
      (metropolisRunLedger m D M k n nStar).stepQueries
        = m * ((2 + nStar) * qpeWindowQueries M n) ∧
      (metropolisRunLedger m D M k n nStar).stepGates
        = m * ((2 + nStar) * qpeWindowGates M n) ∧
      (metropolisRunLedger m D M k n nStar).stepBits
        = m * (k + 1 + Nat.clog 2 M * (nStar + 1)) ∧
      (metropolisRunLedger m D M k n nStar).spaceQubits
        = D + 2 * Nat.clog 2 M + 1 + k ∧
      0 < (metropolisRunLedger m D M k n nStar).stepQueries)

end ContractBodies

section ContractBodies

/-- The contract combining rational Gibbs approximation, a variational gap mixing estimate, a
sharp rejection budget, and an asymptotically matching two projector lower bound. -/
def clause45Body : Prop :=

  (∀ (N : ℕ) (hN : 0 < N) (E : Fin N → ℝ) (β : ℝ), 0 < β →
      ∀ ε : ℝ, 0 < ε →
        ∃ (K : ℕ) (E' : Fin N → ℚ),
          ∀ hW : 0 < weightTotal (boltzmannIntegerWeights K E'),
            Matrix.traceNorm
              (rationalHeatBathDensity (boltzmannIntegerWeights K E') hW
                - diagonalGibbsDensity N hN E β) ≤ ε) ∧

  (∀ (N K : ℕ) (E : Fin N → ℚ), 0 < N → (∀ i, 0 ≤ E i ∧ E i ≤ 1) →
      ∃ hW : 0 < weightTotal (boltzmannIntegerWeights K E),
        IsDensityOperator (rationalEnergyGibbsDensity E) ∧
        Matrix.traceNorm
          (rationalHeatBathDensity (boltzmannIntegerWeights K E) hW
            - rationalEnergyGibbsDensity E) ≤ 4 * (1 / 2 : ℝ) ^ K) ∧
  (∀ (N k K : ℕ) (hN : 0 < N) (E : Fin N → ℝ) (β : ℝ), 0 < β →
      (∀ i, 0 ≤ β * E i ∧ β * E i ≤ 1) →
      ∃ hW : 0 < weightTotal
          (boltzmannIntegerWeights K (fun i => dyadicRat k (β * E i))),
        Matrix.traceNorm
          (rationalHeatBathDensity
            (boltzmannIntegerWeights K (fun i => dyadicRat k (β * E i))) hW
            - diagonalGibbsDensity N hN E β)
          ≤ gibbsL1ShiftBound N 1 ((1 / 2 : ℝ) ^ k) 1 + 4 * (1 / 2 : ℝ) ^ K) ∧

  (∀ (I : Type) [Fintype I] [DecidableEq I] (P : I → I → ℝ) (π : I → ℝ) (Δ : ℝ),
      (∀ x, 0 ≤ π x) → (∑ x, π x = 1) →
      IsTransitionMatrix P → IsReversible P π →
      0 < Δ → variationalGapPremise P π Δ →
        ∀ (x : I) (m : ℕ),
          tvDistance (kernelPower P m x) π
            ≤ (1 / 2) * Real.sqrt ((1 - π x) / π x) * (1 - Δ) ^ m) ∧

  (∀ pfail : ℕ → ℝ,
      (∀ n, 0 ≤ pfail n ∧ pfail n ≤ sharpTailBound n) →
      ∀ (m n : ℕ) (c : ℝ), 0 ≤ c → c < 1 → 0 < m →
        ((n : ℝ) + 1) * (2 * Real.exp 1 * (1 - c)) ≥ (m : ℝ) →
        (1 - pfail n) ^ m ≥ c) ∧

  (∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ d : ℝ, 0 < d ∧ d < 1 ∧
          1 / (2 * Real.exp 1) - ε
            ≤ (n : ℝ) * rejectFailProb twoProjectorP (twoProjectorQ d) twoProjectorPsi n)

end ContractBodies

section ContractBodies

/-- The universal contract asserting that every legal symmetric proposal ensemble in an
orthonormal energy basis has a completely positive trace preserving realization satisfying
quantum detailed balance. -/
def clause42Body : Prop :=
  ∀ (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D)),
    (∀ i j : Fin D, Qatlib.Foundations.PureStateMath.Inner (ψ i) (ψ j) = if i = j then 1 else 0) →
    (∀ x : QState (Fin D), ∑ i, Qatlib.Foundations.PureStateMath.Inner (ψ i) x • ψ i = x) →
    ∀ ens : ProposalEnsemble D,
      proposalEnsembleLegal ens →
      proposalSymmetric ens →
      ∀ β : ℝ, 0 ≤ β →
        ∃ T : Operator D →ₗ[ℂ] Operator D,
          (∀ ρ : Operator D, T ρ = temmeMapFun E ψ ens β ρ) ∧
          CompletelyPositive T ∧
          TracePreserving T ∧
          QuantumDetailedBalance T (temmeGibbsState D hD E β ψ)

/-- The contract combining detailed balance stationarity, conditional irreducibility and fixed
point uniqueness, and a strictly contractive two dimensional instance. -/
def clause43Body : Prop :=

  QuantumDetailedBalanceFixedPoint ∧
  (∀ (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D)),
      (∀ i j : Fin D, Qatlib.Foundations.PureStateMath.Inner (ψ i) (ψ j) = if i = j then 1 else 0) →
      (∀ x : QState (Fin D), ∑ i, Qatlib.Foundations.PureStateMath.Inner (ψ i) x • ψ i = x) →
      ∀ ens : ProposalEnsemble D,
        proposalEnsembleLegal ens →
        proposalSymmetric ens →
        ∀ β : ℝ, 0 ≤ β →
          ∀ T : Operator D →ₗ[ℂ] Operator D,
            (∀ ρ : Operator D, T ρ = temmeMapFun E ψ ens β ρ) →
            CompletelyPositive T →
            TracePreserving T →
            QuantumDetailedBalance T (temmeGibbsState D hD E β ψ) →

              T (temmeGibbsState D hD E β ψ) = temmeGibbsState D hD E β ψ ∧

              (proposalPositive ens →
                denseGenerated ens →
                  (∀ (φ χ : QState (Fin D)), Qatlib.Foundations.PureStateMath.Inner φ φ = 1 → Qatlib.Foundations.PureStateMath.Inner χ χ = 1 →
                    ∃ m : ℕ,
                      0 < (Qatlib.Foundations.PureStateMath.Inner χ ((T^[m]) (ketbra φ φ) *ᵥ χ)).re) ∧
                  (∀ ρ : Operator D, IsDensityOperator ρ → T ρ = ρ →
                    ρ = temmeGibbsState D hD E β ψ))) ∧

  (∃ T : Operator 2 →ₗ[ℂ] Operator 2,
    (∀ ρ : Operator 2, T ρ = temmeMapFun instanceEnergy instanceBasis instanceEnsemble 1 ρ) ∧
    T (temmeGibbsState 2 (by decide) instanceEnergy 1 instanceBasis)
      = temmeGibbsState 2 (by decide) instanceEnergy 1 instanceBasis ∧
    instanceEta < 1 ∧
    ∀ X Y : Operator 2, IsDensityOperator X → IsDensityOperator Y →
      SchattenOne (T X - T Y) ≤ instanceEta * SchattenOne (X - Y))

end ContractBodies

section Clause41Counterexample
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib

/-- The universal unknown Hamiltonian contract `clause41Body` is false. -/
theorem clause41_contract_false : ¬ clause41Body := by
  intro h
  have hA : ((0 : Operator 1)).IsHermitian := by
    show (0 : Operator 1)ᴴ = 0
    simp
  have hconj := h 1 0 hA 1 3 (by norm_num) (by norm_num) 0 (by norm_num) 1
    (by norm_num) (0 : Fin 3)
  have hphase := hconj.2.2.2.2.1.1
  have he1 : phaseOfEnergy 1 (2 * Real.pi) = (-1 : ℝ) := by
    unfold phaseOfEnergy
    have hp : (2 * Real.pi : ℝ) ≠ 0 := by
      have := Real.pi_pos
      positivity
    field_simp
  have he2 : labelEnergy 1 3 (0 : Fin 3) = (0 : ℝ) := by
    simp [labelEnergy]
  have hzval : (((0 : Fin 3).val : ℝ) / (3 : ℝ)) = 0 := by norm_num
  have hfloor : (⌊(-1 : ℝ) - 0 + 1 / 2⌋ : ℤ) = -1 := by
    have hq : (-1 : ℝ) - 0 + 1 / 2 = -1 / 2 := by ring
    rw [hq]
    exact Int.floor_eq_iff.mpr (by norm_num)
  have hpd : phaseDistance (-1 : ℝ) 0 = 0 := by
    unfold phaseDistance
    rw [hfloor]
    simp
  have hprem : phaseDistance (phaseOfEnergy 1 (2 * Real.pi)) (((0 : Fin 3).val : ℝ) / (3 : ℝ))
      ≤ 1 / (3 : ℝ) := by
    rw [he1, hzval]
    rw [hpd]
    norm_num
  have hcon := hphase (2 * Real.pi) 0 hprem
  rw [he2] at hcon
  simp only [sub_zero] at hcon
  have hpos : (0 : ℝ) < 2 * Real.pi := by
    have := Real.pi_pos
    positivity
  rw [abs_of_pos hpos, abs_one] at hcon
  norm_num at hcon
  have hpp : (0 : ℝ) < Real.pi := Real.pi_pos
  linarith

end Clause41Counterexample

section Clause44Counterexample

/-- The combined mixing and cost contract `clause44Body` is false. -/
theorem clause44_contract_false : ¬ clause44Body := by
  intro h
  have hled := h.2.2.2
  have hpos := (hled 1 1 0 0 0 0).2.2.2.2.2
  simp [metropolisRunLedger, qpeWindowQueries] at hpos

end Clause44Counterexample

section Clause45Counterexample

/-- The combined approximation, mixing, and rejection contract `clause45Body` is false. -/
theorem clause45_contract_false : ¬ clause45Body := by
  intro h
  have hmix := h.2.2.2.1
  let P : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 1 else 0
  let π : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1
  have hPnonneg : ∀ x y : Fin 2, 0 ≤ P x y := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp [P]
    · simp [P, hxy]
  have hProw : ∀ x : Fin 2, ∑ y, P x y = 1 := by
    intro x
    rw [Fin.sum_univ_two]
    fin_cases x <;> simp [P]
  have hpin : ∀ x : Fin 2, 0 ≤ π x := by
    intro x
    fin_cases x <;> simp [π]
  have hpsum : (∑ x : Fin 2, π x) = 1 := by
    rw [Fin.sum_univ_two]
    simp [π]
  have hrev : IsReversible P π := by
    intro x y
    fin_cases x <;> fin_cases y <;> simp [P, π]
  have hgap : variationalGapPremise P π 1 := by
    intro f hf
    have hrow1 : ∀ x : Fin 2, ∑ y : Fin 2, P x y * f y = f x := by
      intro x
      rw [Fin.sum_univ_two]
      fin_cases x <;> simp [P]
    have hf1 : f (1 : Fin 2) = 0 := by
      have hsum := hf
      rw [Fin.sum_univ_two] at hsum
      simp [π] at hsum
      exact hsum
    have hcong : ∀ x : Fin 2, π x * (∑ y, P x y * f y) ^ 2 = π x * (f x) ^ 2 := by
      intro x
      rw [hrow1]
    have hzero : (∑ x : Fin 2, π x * (f x) ^ 2) = 0 := by
      rw [Fin.sum_univ_two]
      simp [π, hf1]
    have hL : (∑ x : Fin 2, π x * (∑ y, P x y * f y) ^ 2) = 0 := by
      rw [Finset.sum_congr rfl fun x _ => hcong x]
      exact hzero
    rw [hL, hzero]
    norm_num
  have hbound := hmix (Fin 2) P π (1:ℝ) hpin hpsum ⟨hPnonneg, hProw⟩ hrev (by norm_num)
    hgap (0 : Fin 2) 0
  have hker : kernelPower P 0 (0 : Fin 2) = (fun y => if (0 : Fin 2) = y then 1 else 0) := by
    funext y
    simp [kernelPower]
  have htv : tvDistance (kernelPower P 0 (0 : Fin 2)) π = 1 := by
    rw [hker]
    unfold tvDistance
    rw [Fin.sum_univ_two]
    simp [π]
  have hrhs : (1 / 2) * Real.sqrt ((1 - π (0 : Fin 2)) / π (0 : Fin 2)) * (1 - (1:ℝ)) ^ 0
      = 0 := by
    simp [π]
  rw [htv, hrhs] at hbound
  norm_num at hbound

end Clause45Counterexample

section Clause45BlockB

/-- For rational energies in `[0, 1]` on a nonempty finite space, positive integer Boltzmann
weights give a heat bath density within trace norm `4 * (1 / 2) ^ K` of the rational energy
Gibbs density. -/
theorem clause28_block2_rationalWindow :
    ∀ (N K : ℕ) (E : Fin N → ℚ), 0 < N → (∀ i, 0 ≤ E i ∧ E i ≤ 1) →
      ∃ hW : 0 < weightTotal (boltzmannIntegerWeights K E),
        IsDensityOperator (rationalEnergyGibbsDensity E) ∧
        Matrix.traceNorm
          (rationalHeatBathDensity (boltzmannIntegerWeights K E) hW
            - rationalEnergyGibbsDensity E) ≤ 4 * (1 / 2 : ℝ) ^ K := by
  intro N K E hN hE
  have hpos : 0 < weightTotal (boltzmannIntegerWeights K E) :=
    (rational_boltzmann_exact_integer_normalization N K E hN hE).1
  exact ⟨hpos, rational_energy_gibbs_target_and_trace_accuracy N K E hpos hN hE⟩

end Clause45BlockB

section Clause45BlockE

/-- The stated sharp tail bound and budget inequality ensure that `m` independent success
factors have product at least `c`. -/
theorem clause28_block4_sharpBudget :
    ∀ pfail : ℕ → ℝ,
      (∀ n, 0 ≤ pfail n ∧ pfail n ≤ sharpTailBound n) →
      ∀ (m n : ℕ) (c : ℝ), 0 ≤ c → c < 1 → 0 < m →
        ((n : ℝ) + 1) * (2 * Real.exp 1 * (1 - c)) ≥ (m : ℝ) →
        (1 - pfail n) ^ m ≥ c := by
  intro pfail hpf m n c hc0 hc1 hm h
  have hpn : pfail n ≤ sharpTailBound n := (hpf n).2
  have hp0 : 0 ≤ pfail n := (hpf n).1
  have hsharp : sharpTailBound n = 1 / (2 * Real.exp 1 * ((n : ℝ) + 1)) := rfl
  rw [hsharp] at hpn
  have hd : 0 < (2 : ℝ) * Real.exp 1 * ((n : ℝ) + 1) := by
    have := Real.exp_pos 1
    positivity
  have hD1 : (1 : ℝ) ≤ 2 * Real.exp 1 * ((n : ℝ) + 1) := by
    have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (2 : ℝ) ≤ 2 * Real.exp 1 := by nlinarith
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.le_add_left 1 n
      exact_mod_cast this
    nlinarith
  have hp1 : pfail n ≤ 1 := by
    apply le_trans hpn
    rw [div_le_iff₀ hd]
    linarith
  have hmle : (m : ℝ) ≤ 2 * Real.exp 1 * ((n : ℝ) + 1) * (1 - c) := by
    have hrearr : ((n : ℝ) + 1) * (2 * Real.exp 1 * (1 - c))
        = 2 * Real.exp 1 * ((n : ℝ) + 1) * (1 - c) := by ring
    linarith
  have hmle' : (m : ℝ) / (2 * Real.exp 1 * ((n : ℝ) + 1)) ≤ 1 - c := by
    apply (div_le_iff₀ hd).2
    linarith
  have hmp : (m : ℝ) * pfail n ≤ 1 - c := by
    have hmul : (m : ℝ) * pfail n
        ≤ (m : ℝ) * (1 / (2 * Real.exp 1 * ((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hpn (Nat.cast_nonneg m)
    have hdiv : (m : ℝ) * (1 / (2 * Real.exp 1 * ((n : ℝ) + 1)))
        = (m : ℝ) / (2 * Real.exp 1 * ((n : ℝ) + 1)) := by ring
    linarith
  have hbern : 1 - (m : ℝ) * pfail n ≤ (1 - pfail n) ^ m := by
    have hbm := one_add_mul_le_pow (a := -pfail n) (show (-2 : ℝ) ≤ -pfail n by linarith) m
    have h1 : (1 : ℝ) + (m : ℝ) * -pfail n = 1 - (m : ℝ) * pfail n := by ring
    have h2 : (1 : ℝ) + -pfail n = 1 - pfail n := by ring
    rw [h2] at hbm
    rw [h1] at hbm
    exact hbm
  linarith

end Clause45BlockE

section DyadicRounding

/-- The real value of `dyadicRat k x` is the natural floor of `2 ^ k * x`, divided by `2 ^ k`. -/
theorem dyadicRat_num (k : ℕ) (x : ℝ) :
    ((dyadicRat k x : ℚ) : ℝ) = (Nat.floor ((2 : ℝ) ^ k * x) : ℝ) / (2 : ℝ) ^ k := by
  unfold dyadicRat
  push_cast
  ring_nf

/-- The dyadic rational formed using the natural floor is nonnegative for every real input. -/
theorem dyadicRat_nonneg {k : ℕ} (x : ℝ) : 0 ≤ dyadicRat k x := by
  unfold dyadicRat
  apply div_nonneg
  · exact_mod_cast Nat.zero_le _
  · exact_mod_cast (pow_pos (by norm_num : 0 < (2:ℕ)) k).le

/-- The real coercion of `dyadicRat k x` is nonnegative. -/
theorem dyadicRat_nonneg_real (k : ℕ) (x : ℝ) : 0 ≤ ((dyadicRat k x : ℚ) : ℝ) := by
  exact_mod_cast dyadicRat_nonneg x

/-- For nonnegative `x`, its dyadic rational approximation has real value at most `x`. -/
theorem dyadicRat_le_self {k : ℕ} {x : ℝ} (hx : 0 ≤ x) : ((dyadicRat k x : ℚ) : ℝ) ≤ x := by
  rw [dyadicRat_num]
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hfl : (Nat.floor ((2 : ℝ) ^ k * x) : ℝ) ≤ (2 : ℝ) ^ k * x := by
    exact Nat.floor_le (mul_nonneg (le_of_lt h2k) hx)
  apply (div_le_iff₀ h2k).2
  nlinarith

/-- For nonnegative `x`, the downward dyadic rounding error is at most `(1 / 2) ^ k`. -/
theorem dyadicRat_sub_le {k : ℕ} {x : ℝ} (_hx : 0 ≤ x) :
    x - ((dyadicRat k x : ℚ) : ℝ) ≤ (1 / 2 : ℝ) ^ k := by
  rw [dyadicRat_num]
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hlt : ((2 : ℝ) ^ k * x) < (Nat.floor ((2 : ℝ) ^ k * x) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have h1 : ((1 : ℝ) / 2) ^ k = 1 / (2 : ℝ) ^ k := by
    rw [div_pow, one_pow]
  rw [h1]
  have hkey : (2 : ℝ) ^ k * x - (Nat.floor ((2 : ℝ) ^ k * x) : ℝ) ≤ 1 := by linarith
  calc x - (Nat.floor ((2 : ℝ) ^ k * x) : ℝ) / (2 : ℝ) ^ k
      = (x * (2 : ℝ) ^ k - (Nat.floor ((2 : ℝ) ^ k * x) : ℝ)) / (2 : ℝ) ^ k := by
        field_simp [h2k.ne']
    _ ≤ 1 / (2 : ℝ) ^ k := by
        apply (div_le_div_iff₀ h2k h2k).2
        nlinarith

/-- Dyadic rounding of a real number in `[0, 1]` is at most one. -/
theorem dyadicRat_le_one {k : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (dyadicRat k x : ℚ) ≤ 1 := by
  have h : ((dyadicRat k x : ℚ) : ℝ) ≤ 1 := le_trans (dyadicRat_le_self hx0) hx1
  have h1 : ((dyadicRat k x : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by
    simpa using! h
  exact Rat.cast_le.mp h1

/-- Dyadic rounding preserves membership in the interval `[0, 1]`. -/
theorem dyadicRat_mem {k : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ dyadicRat k x ∧ dyadicRat k x ≤ 1 :=
  ⟨dyadicRat_nonneg x, dyadicRat_le_one hx0 hx1⟩

end DyadicRounding

section GibbsL1

/-- For entries in `[0, 1]` on a nonempty finite space, dyadic rounding changes the normalized
exponential weights by at most `4 * exp 1 * (1 / 2) ^ k` in L1 distance. -/
theorem normalized_exp_l1_rounding {N : ℕ} (hN : 0 < N) (u : Fin N → ℝ)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) (k : ℕ) :
    (∑ i, |Real.exp (-u i) / ∑ j, Real.exp (-u j)
        - Real.exp (-((dyadicRat k (u i) : ℚ) : ℝ)) /
          ∑ j, Real.exp (-((dyadicRat k (u j) : ℚ) : ℝ))|)
      ≤ 4 * Real.exp 1 * (1 / 2 : ℝ) ^ k := by
  set v : Fin N → ℝ := fun i => ((dyadicRat k (u i) : ℚ) : ℝ)
  have hvle : ∀ i, v i ≤ u i := fun i => dyadicRat_le_self (hu i).1
  have hvsub : ∀ i, u i - v i ≤ (1 / 2 : ℝ) ^ k := fun i => dyadicRat_sub_le (hu i).1
  have hvnn : ∀ i, 0 ≤ v i := fun i => dyadicRat_nonneg_real k (u i)
  have ha : ∀ i, 1 ≤ Real.exp (1 - u i) := by
    intro i
    exact Real.one_le_exp (by linarith [hu i])
  have hab : ∀ i, Real.exp (1 - u i) ≤ Real.exp (1 - v i) := by
    intro i
    exact Real.exp_le_exp_of_le (by linarith [hvle i])
  have hbd : ∀ i, Real.exp (1 - v i) - Real.exp (1 - u i)
      ≤ 2 * Real.exp 1 * (1 / 2 : ℝ) ^ k := by
    intro i
    have hfac : Real.exp (1 - v i) = Real.exp (1 - u i) * Real.exp (u i - v i) := by
      rw [← Real.exp_add]
      ring_nf
    have hx0 : 0 ≤ u i - v i := by linarith [hvle i]
    have hx1 : |u i - v i| ≤ 1 := by
      have := hvsub i
      have h21 : ((1 / 2 : ℝ) ^ k) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      rw [abs_of_nonneg hx0]
      linarith
    have hge1 : 0 ≤ Real.exp (u i - v i) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp hx0)
    have habs := Real.abs_exp_sub_one_le hx1
    have hbd' : Real.exp (u i - v i) - 1 ≤ 2 * (u i - v i) := by
      have hle := le_trans (le_abs_self _) habs
      rw [abs_of_nonneg hx0] at hle
      linarith
    have h1u : Real.exp (1 - u i) ≤ Real.exp 1 :=
      Real.exp_le_exp_of_le (by linarith [hu i])
    calc Real.exp (1 - v i) - Real.exp (1 - u i)
        = Real.exp (1 - u i) * (Real.exp (u i - v i) - 1) := by
          rw [hfac]; ring
      _ ≤ Real.exp 1 * (Real.exp (u i - v i) - 1) :=
        mul_le_mul_of_nonneg_right h1u hge1
      _ ≤ Real.exp 1 * (2 * (u i - v i)) :=
        mul_le_mul_of_nonneg_left hbd' (le_of_lt (Real.exp_pos 1))
      _ ≤ Real.exp 1 * (2 * (1 / 2 : ℝ) ^ k) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos 1))
        linarith [hvsub i]
      _ = 2 * Real.exp 1 * (1 / 2 : ℝ) ^ k := by ring
  have h1 := normalized_positive_weights_l1 hN
    (fun i => Real.exp (1 - u i)) (fun i => Real.exp (1 - v i))
    (2 * Real.exp 1 * (1 / 2 : ℝ) ^ k) ha hab hbd
  have huu : ∀ i, Real.exp (1 - u i) = Real.exp 1 * Real.exp (-u i) := by
    intro i
    rw [← Real.exp_add]
    ring_nf
  have hvv : ∀ i, Real.exp (1 - v i) = Real.exp 1 * Real.exp (-v i) := by
    intro i
    rw [← Real.exp_add]
    ring_nf
  have hsumu : (∑ j, Real.exp (1 - u j)) = Real.exp 1 * (∑ j, Real.exp (-u j)) := by
    simp_rw [huu]
    rw [Finset.mul_sum]
  have hsumv : (∑ j, Real.exp (1 - v j)) = Real.exp 1 * (∑ j, Real.exp (-v j)) := by
    simp_rw [hvv]
    rw [Finset.mul_sum]
  have hratioU : ∀ i, Real.exp (1 - u i) / ∑ j, Real.exp (1 - u j)
      = Real.exp (-u i) / ∑ j, Real.exp (-u j) := by
    intro i
    rw [huu i, hsumu]
    exact mul_div_mul_left _ _ (Real.exp_pos 1).ne'
  have hratioV : ∀ i, Real.exp (1 - v i) / ∑ j, Real.exp (1 - v j)
      = Real.exp (-v i) / ∑ j, Real.exp (-v j) := by
    intro i
    rw [hvv i, hsumv]
    exact mul_div_mul_left _ _ (Real.exp_pos 1).ne'
  simp_rw [hratioU, hratioV] at h1
  have h4 : (2 : ℝ) * (2 * Real.exp 1 * (1 / 2 : ℝ) ^ k)
      = 4 * Real.exp 1 * (1 / 2 : ℝ) ^ k := by ring
  linarith

end GibbsL1

section Clause45BlockC

/-- For positive inverse temperature and scaled energies in `[0, 1]`, the dyadic rational heat
bath approximates the diagonal Gibbs density with the stated sum of energy shift and integer
weight errors. -/
theorem clause28_block3_dyadicWindow :
    ∀ (N k K : ℕ) (hN : 0 < N) (E : Fin N → ℝ) (β : ℝ), 0 < β →
      (∀ i, 0 ≤ β * E i ∧ β * E i ≤ 1) →
      ∃ hW : 0 < weightTotal
          (boltzmannIntegerWeights K (fun i => dyadicRat k (β * E i))),
        Matrix.traceNorm
          (rationalHeatBathDensity
            (boltzmannIntegerWeights K (fun i => dyadicRat k (β * E i))) hW
            - diagonalGibbsDensity N hN E β)
          ≤ gibbsL1ShiftBound N 1 ((1 / 2 : ℝ) ^ k) 1 + 4 * (1 / 2 : ℝ) ^ K := by
  intro N k K hN E β hβ hu
  set u : Fin N → ℝ := fun i => β * E i
  set E' : Fin N → ℚ := fun i => dyadicRat k (u i)
  have hE' : ∀ i, 0 ≤ E' i ∧ E' i ≤ 1 := fun i => dyadicRat_mem (hu i).1 (hu i).2
  obtain ⟨hW, _hden, hacc⟩ := clause28_block2_rationalWindow N K E' hN hE'
  refine ⟨hW, ?_⟩
  have hL1sum : (∑ i, |Real.exp (-(E' i : ℝ)) / ∑ j, Real.exp (-(E' j : ℝ))
        - Real.exp (-u i) / ∑ j, Real.exp (-u j)|)
      ≤ 4 * Real.exp 1 * (1 / 2 : ℝ) ^ k := by
    have h := normalized_exp_l1_rounding hN u hu k
    have hswap : ∀ i,
        |Real.exp (-(E' i : ℝ)) / ∑ j, Real.exp (-(E' j : ℝ))
          - Real.exp (-u i) / ∑ j, Real.exp (-u j)|
        = |Real.exp (-u i) / ∑ j, Real.exp (-u j)
          - Real.exp (-(E' i : ℝ)) / ∑ j, Real.exp (-(E' j : ℝ))| := by
      intro i
      exact abs_sub_comm _ _
    simp_rw [hswap]
    exact h
  have he1 : rationalEnergyGibbsDensity E' = Matrix.diagonal
      (fun i => Complex.ofReal (Real.exp (-(E' i : ℝ)) / ∑ j, Real.exp (-(E' j : ℝ)))) := rfl
  have hpart : diagonalGibbsPartition N E β = ∑ j, Real.exp (-(β * E j)) := by
    unfold diagonalGibbsPartition
    simp only [neg_mul]
  have he2 : diagonalGibbsDensity N hN E β = Matrix.diagonal
      (fun i => Complex.ofReal (Real.exp (-(β * E i)) / ∑ j, Real.exp (-(β * E j)))) := by
    unfold diagonalGibbsDensity
    congr 1
    funext i
    rw [diagonalGibbsDist_prob N hN E β i, hpart]
    simp only [neg_mul]
  have htn : Matrix.traceNorm (rationalEnergyGibbsDensity E' - diagonalGibbsDensity N hN E β)
      ≤ 4 * Real.exp 1 * (1 / 2 : ℝ) ^ k := by
    rw [he1, he2, Matrix.diagonal_sub]
    simpa only [Pi.sub_apply, ← Complex.ofReal_sub, real_diagonal_traceNorm] using! hL1sum
  have hcmp : (4 : ℝ) * Real.exp 1 * (1 / 2 : ℝ) ^ k
      ≤ gibbsL1ShiftBound N 1 ((1 / 2 : ℝ) ^ k) 1 := by
    have he1' : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1:ℝ)
      linarith
    have he2' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2:ℝ) = 1 + 1 by ring, Real.exp_add]
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hN
    have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1
    have hprod : (2 : ℝ) ≤ (N : ℝ) ^ 2 * Real.exp 1 :=
      calc (2:ℝ) = 1 * 2 := (one_mul 2).symm
        _ ≤ (N:ℝ) ^ 2 * Real.exp 1 :=
          mul_le_mul hN2 he1' (by norm_num) (by positivity : (0:ℝ) ≤ (N:ℝ)^2)
    have h2e : (0 : ℝ) ≤ 2 * Real.exp 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hprod h2e
    have h4 : (2 * Real.exp 1) * 2 = 4 * Real.exp 1 := by ring
    have h5 : (2 * Real.exp 1) * ((N : ℝ) ^ 2 * Real.exp 1)
        = 2 * (N : ℝ) ^ 2 * (Real.exp 1 * Real.exp 1) := by ring
    rw [h4, h5] at hmul
    have hδ : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
    have hmul' := mul_le_mul_of_nonneg_right hmul hδ
    unfold gibbsL1ShiftBound
    have harg : (2 * 1 * 1 : ℝ) = 2 := by ring
    rw [harg, he2']
    have hL : (4 * Real.exp 1) * ((1 / 2 : ℝ) ^ k)
        = 4 * Real.exp 1 * (1 / 2 : ℝ) ^ k := by ring
    have hR : (2 * (N : ℝ) ^ 2 * (Real.exp 1 * Real.exp 1)) * ((1 / 2 : ℝ) ^ k)
        = 2 * (N : ℝ) ^ 2 * 1 * ((1 / 2 : ℝ) ^ k) * (Real.exp 1 * Real.exp 1) := by ring
    rw [← hL, ← hR]
    exact hmul'
  have hst : Matrix.traceNorm
      (rationalEnergyGibbsDensity E' - diagonalGibbsDensity N hN E β)
      ≤ gibbsL1ShiftBound N 1 ((1 / 2 : ℝ) ^ k) 1 := le_trans htn hcmp
  have hsum := Matrix.traceNorm_add_le
    (rationalHeatBathDensity (boltzmannIntegerWeights K E') hW - rationalEnergyGibbsDensity E')
    (rationalEnergyGibbsDensity E' - diagonalGibbsDensity N hN E β)
  have hdecomp :
      (rationalHeatBathDensity (boltzmannIntegerWeights K E') hW - rationalEnergyGibbsDensity E')
        + (rationalEnergyGibbsDensity E' - diagonalGibbsDensity N hN E β)
      = rationalHeatBathDensity (boltzmannIntegerWeights K E') hW
          - diagonalGibbsDensity N hN E β := by
    abel
  rw [← hdecomp]
  exact le_trans hsum ((add_le_add hacc hst).trans_eq (add_comm _ _))

end Clause45BlockC

section TwoProjectorFormula
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib

/-- The two dimensional vector with coordinates `sqrt d` and `sqrt (1 - d)`. -/
noncomputable def twoProjectorVec (d : ℝ) : QState (Fin 2) :=
  fun i => if i = 0 then Complex.ofReal (Real.sqrt d)
    else Complex.ofReal (Real.sqrt (1 - d))

/-- The matrix `twoProjectorQ d` is the outer product of `twoProjectorVec d` with itself. -/
theorem twoProjectorQ_eq (d : ℝ) :
    twoProjectorQ d = outerProduct (twoProjectorVec d) := by
  unfold twoProjectorQ outerProduct twoProjectorVec
  rfl

/-- The matrix `twoProjectorP` is the projector onto the zeroth computational basis vector. -/
theorem twoProjectorP_eq :
    twoProjectorP = outerProduct (Qatlib.Foundations.PureStateMath.Ket 0 : QState (Fin 2)) := by
  unfold twoProjectorP outerProduct ketbra
  rfl

/-- The vector `twoProjectorVec d` is normalized when `0 ≤ d ≤ 1`. -/
theorem twoProjectorVec_normalized (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    Normalized (twoProjectorVec d) := by
  have h1d : (0 : ℝ) ≤ 1 - d := by linarith
  unfold Normalized
  show (∑ i, ‖twoProjectorVec d i‖ ^ 2) = 1
  rw [Fin.sum_univ_two]
  unfold twoProjectorVec
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg d),
    abs_of_nonneg (Real.sqrt_nonneg (1 - d)), Real.sq_sqrt hd0, Real.sq_sqrt h1d]

/-- The matrix `twoProjectorQ d` is an orthogonal projector when `0 ≤ d ≤ 1`. -/
theorem twoProjectorQ_isOrthogonal (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    IsOrthogonalProjector (twoProjectorQ d) := by
  rw [twoProjectorQ_eq]
  exact isOrthogonalProjector_outerProduct (twoProjectorVec_normalized d hd0 hd1)

/-- The one column frame embedding the zeroth basis direction into the two dimensional space. -/
noncomputable def twoProjectorFrame : Matrix (Fin 2) (Fin 1) ℂ :=
  fun i _ => if i = (0 : Fin 2) then 1 else 0

/-- The one column frame `twoProjectorFrame` is an isometry. -/
theorem twoProjectorFrame_isometry : IsIsometry twoProjectorFrame := by
  show twoProjectorFrameᴴ * twoProjectorFrame = 1
  ext i j
  fin_cases i; fin_cases j
  simp [twoProjectorFrame, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The range projector of `twoProjectorFrame` equals `twoProjectorP`. -/
theorem twoProjectorFrame_span :
    twoProjectorFrame * twoProjectorFrameᴴ = twoProjectorP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoProjectorFrame, Matrix.mul_apply, Matrix.conjTranspose_apply,
      twoProjectorP, ketbra, Qatlib.Foundations.PureStateMath.Ket]

/-- For nonnegative `d`, compression of `twoProjectorQ d` to `twoProjectorFrame` is the one
dimensional diagonal matrix with entry `d`. -/
theorem twoProjectorFrame_braKet (d : ℝ) (hd0 : 0 ≤ d) :
    twoProjectorFrameᴴ * twoProjectorQ d * twoProjectorFrame
      = Matrix.diagonal (fun _ => (d : ℂ)) := by
  ext i j
  fin_cases i; fin_cases j
  simp [twoProjectorFrame, twoProjectorQ, ketbra,
    Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hd0]

/-- The projector `twoProjectorP` fixes the state `twoProjectorPsi`. -/
theorem twoProjectorP_fix : twoProjectorP *ᵥ (twoProjectorPsi : QState (Fin 2))
    = twoProjectorPsi := by
  have hket : twoProjectorP *ᵥ (Qatlib.Foundations.PureStateMath.Ket 0 : QState (Fin 2))
      = Qatlib.Foundations.PureStateMath.Inner (Qatlib.Foundations.PureStateMath.Ket 0 : QState (Fin 2)) (Qatlib.Foundations.PureStateMath.Ket 0 : QState (Fin 2)) • (Qatlib.Foundations.PureStateMath.Ket 0 : QState (Fin 2)) := by
    have h :=
        outerProduct_mulVec (Qatlib.Foundations.PureStateMath.Ket 0 : QState (Fin 2))
        (Qatlib.Foundations.PureStateMath.Ket 0 : QState (Fin 2))
    rw [← twoProjectorP_eq] at h
    exact h
  have heq :
      (twoProjectorPsi : QState (Fin 2)) =
      (Qatlib.Foundations.PureStateMath.Ket 0 : QState (Fin 2)) := rfl
  rw [heq, hket, inner_ket_ket, if_pos rfl, one_smul]

/-- For `0 ≤ d ≤ 1`, the two projector rejection failure probability after `n` rounds equals `d
* (1 - d) * (d ^ 2 + (1 - d) ^ 2) ^ n`. -/
theorem rejectFailProb_twoProjector (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (n : ℕ) :
    rejectFailProb twoProjectorP (twoProjectorQ d) twoProjectorPsi n
      = d * (1 - d) * (d ^ 2 + (1 - d) ^ 2) ^ n := by
  have hQ := twoProjectorQ_isOrthogonal d hd0 hd1
  have hA := twoProjectorFrame_isometry
  have hAP := twoProjectorFrame_span
  have ht := twoProjectorFrame_braKet d hd0
  have hψ := twoProjectorP_fix
  rw [rejection_failure_spectral_formula twoProjectorP (twoProjectorQ d) hQ
    twoProjectorFrame (fun _ => d) hA hAP ht twoProjectorPsi hψ n]
  rw [Fin.sum_univ_one]
  have hvec : twoProjectorFrameᴴ *ᵥ (twoProjectorPsi : QState (Fin 2)) = fun _ => 1 := by
    funext i
    fin_cases i
    simp [twoProjectorFrame, twoProjectorPsi, Qatlib.Foundations.PureStateMath.Ket, Matrix.mulVec, dotProduct,
      Matrix.conjTranspose_apply]
  rw [hvec]
  all_goals (simp only [norm_one, one_pow, mul_one])

end TwoProjectorFormula

section Clause45BlockF

/-- For natural `n ≥ 2`, the quantity `(1 - 1 / n) ^ n` is at least `exp (-1) * (1 - 1 / n)`. -/
theorem one_sub_pow_lower {n : ℕ} (hn : 2 ≤ n) :
    Real.exp (-1) * (1 - 1 / (n : ℝ)) ≤ (1 - 1 / (n : ℝ)) ^ n := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (le_trans (by norm_num : (1:ℕ) ≤ 2) hn)
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (show (0:ℕ) < n from lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1n : (1 : ℝ) / n ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hn0 (by norm_num : (0:ℝ) < 2)]
    nlinarith
  have hx : (0 : ℝ) < 1 - 1 / (n : ℝ) := by linarith
  have hnm1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1:ℝ) < n := by
      exact_mod_cast (show (1:ℕ) < n from lt_of_lt_of_le (by norm_num : 1 < 2) hn)
    linarith
  have hinv : (1 : ℝ) - ((1 - 1 / (n : ℝ))⁻¹) = -1 / ((n : ℝ) - 1) := by
    have hne : (n : ℝ) - 1 ≠ 0 := ne_of_gt hnm1
    field_simp
    ring
  have hlog := Real.one_sub_inv_le_log_of_pos hx
  rw [hinv] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hnm1)
  have hleft : ((n : ℝ) - 1) * (-1 / ((n : ℝ) - 1)) = -1 := by field_simp
  rw [hleft] at hmul
  have hlogpow : Real.log ((1 - 1 / (n : ℝ)) ^ ((n : ℕ) - 1))
      = ((n : ℝ) - 1) * Real.log (1 - 1 / (n : ℝ)) := by
    rw [Real.log_pow, Nat.cast_sub (le_trans (by norm_num : (1:ℕ) ≤ 2) hn), Nat.cast_one]
  have hexp := Real.exp_le_exp.mpr hmul
  rw [← hlogpow] at hexp
  have hpos : (0 : ℝ) < (1 - 1 / (n : ℝ)) ^ ((n : ℕ) - 1) :=
    pow_pos hx _
  rw [Real.exp_log hpos] at hexp
  have hpow : (1 - 1 / (n : ℝ)) ^ n
      = (1 - 1 / (n : ℝ)) ^ ((n : ℕ) - 1) * (1 - 1 / (n : ℝ)) := by
    conv_lhs =>
      rw [← pow_sub_mul_pow _ (le_trans (by norm_num : (1:ℕ) ≤ 2) hn), pow_one]
  rw [hpow]
  exact mul_le_mul_of_nonneg_right hexp (le_of_lt hx)

/-- For every positive `ε`, all sufficiently large `n` have a parameter `0 < d < 1` with scaled
rejection failure `n * rejectFailProb` at least `1 / (2 * exp 1) - ε`. -/
theorem clause28_block5_twoProjectorSharp :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ d : ℝ, 0 < d ∧ d < 1 ∧
          1 / (2 * Real.exp 1) - ε
            ≤ (n : ℝ) * rejectFailProb twoProjectorP (twoProjectorQ d) twoProjectorPsi n := by
  intro ε hε
  refine ⟨Nat.ceil (1 / (2 * Real.exp 1 * ε)) + 2, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := by
    have h0 : (Nat.ceil (1 / (2 * Real.exp 1 * ε)) : ℕ) + 2 ≤ n := hn
    omega
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn2)
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hbase : (0 : ℝ) ≤ 1 - 2 / (n : ℝ) := by
    have h1n : (2 : ℝ) / n ≤ 1 := by
      rw [div_le_iff₀ hn0]
      nlinarith
    linarith
  set d : ℝ := (1 - Real.sqrt (1 - 2 / (n : ℝ))) / 2
  have hd0 : 0 < d := by
    have hlt : Real.sqrt (1 - 2 / (n : ℝ)) < 1 := by
      have hlt' : 1 - 2 / (n : ℝ) < 1 := by
        have : (0 : ℝ) < 2 / n := div_pos (by norm_num) hn0
        linarith
      have hlt2 := Real.sqrt_lt_sqrt (by linarith : (0:ℝ) ≤ 1 - 2 / (n : ℝ)) hlt'
      rw [Real.sqrt_one] at hlt2
      exact hlt2
    have : (0:ℝ) < 1 - Real.sqrt (1 - 2 / (n : ℝ)) := by linarith
    unfold d
    positivity
  have hd1 : d < 1 := by
    have hnn : (0:ℝ) ≤ Real.sqrt (1 - 2 / (n : ℝ)) := Real.sqrt_nonneg _
    unfold d
    linarith
  have hdd : d * (1 - d) = 1 / (2 * (n : ℝ)) := by
    have hs : Real.sqrt (1 - 2 / (n : ℝ)) ^ 2 = 1 - 2 / (n : ℝ) :=
      Real.sq_sqrt hbase
    have hcalc : d * (1 - d)
        = (1 - Real.sqrt (1 - 2 / (n : ℝ)) ^ 2) / 4 := by
      unfold d
      ring
    rw [hcalc, hs]
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
    field_simp [hne]; ring
  have hr : d ^ 2 + (1 - d) ^ 2 = 1 - 1 / (n : ℝ) := by
    have hsq : d ^ 2 + (1 - d) ^ 2 = 1 - 2 * d * (1 - d) := by ring
    rw [hsq]
    have h2 : (2 : ℝ) * d * (1 - d) = 2 * (d * (1 - d)) := by ring
    rw [h2, hdd]
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
    field_simp [hne]
  refine ⟨d, hd0, hd1, ?_⟩
  have hform := rejectFailProb_twoProjector d (le_of_lt hd0) (le_of_lt hd1) n
  rw [hform, hdd, hr]
  have hnn : (n : ℝ) * (1 / (2 * (n : ℝ)) * (1 - 1 / (n : ℝ)) ^ n)
      = (1 / 2) * (1 - 1 / (n : ℝ)) ^ n := by
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
    field_simp [hne]
  rw [hnn]
  have hlow := one_sub_pow_lower hn2
  have h1 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h2 : (1 / 2) * Real.exp (-1) * (1 - 1 / (n : ℝ)) ≤ (1 / 2) * ((1 - 1 / (n : ℝ)) ^ n) := by
    nlinarith
  have hgap : (1 : ℝ) / (2 * Real.exp 1 * (n : ℝ)) ≤ ε := by
    have hceil : (1 : ℝ) / (2 * Real.exp 1 * ε) ≤
        (Nat.ceil (1 / (2 * Real.exp 1 * ε)) : ℕ) := Nat.le_ceil _
    have hnnn : (1 / (2 * Real.exp 1 * ε) : ℝ) ≤ (n : ℝ) := by
      have : ((Nat.ceil (1 / (2 * Real.exp 1 * ε)) : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_add_right _ 2) hn)
      linarith
    have hpos : (0 : ℝ) < 2 * Real.exp 1 * ε := by
      have := Real.exp_pos 1
      positivity
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.exp 1 * (n : ℝ))]
    calc (1 : ℝ)
        = (1 / (2 * Real.exp 1 * ε)) * (2 * Real.exp 1 * ε) :=
          (div_mul_cancel₀ _ (ne_of_gt hpos)).symm
      _ ≤ (n : ℝ) * (2 * Real.exp 1 * ε) :=
          mul_le_mul_of_nonneg_right hnnn (le_of_lt hpos)
      _ = ε * (2 * Real.exp 1 * (n : ℝ)) := by ring
  have hsplit : (1 / 2) * Real.exp (-1) * (1 - 1 / (n : ℝ))
      = 1 / (2 * Real.exp 1) - 1 / (2 * Real.exp 1 * (n : ℝ)) := by
    rw [Real.exp_neg]
    field_simp
  rw [hsplit] at h2
  linarith

end Clause45BlockF

section Clause43Blocks

open scoped ComplexOrder

/-- The trace of `ketbra u v` equals the inner product of `v` with `u`. -/
private theorem clause26_trace_ketbra {D : ℕ} (u v : QState (Fin D)) :
    Matrix.trace (ketbra u v) = Qatlib.Foundations.PureStateMath.Inner v u := by
  simp only [Matrix.trace, Matrix.diag_apply, ketbra, Matrix.of_apply, Qatlib.Foundations.PureStateMath.Inner, dotProduct,
    Pi.star_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Real scalar multiplication of an operator agrees with multiplication by the corresponding
complex scalar. -/
private theorem clause26_real_smul {D : ℕ} (r : ℝ) (A : Operator D) : r • A = (r : ℂ) • A := by
  ext i j
  simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  rfl

/-- The rank one operator `ketbra u u` is positive semidefinite. -/
private theorem clause26_ketbra_psd {D : ℕ} (u : QState (Fin D)) :
    (ketbra u u).PosSemidef := by
  have he : ketbra u u = outerProduct u := by
    ext i j
    simp [ketbra, outerProduct]
  rw [he]
  exact outerProduct_posSemidef u

/-- Nonnegative weights summing to one in an orthonormal basis define a density operator through
`gibbsBasis`. -/
theorem gibbsBasis_isDensity {D : ℕ} (ψ : Fin D → QState (Fin D)) (p : Fin D → ℝ)
    (horth : ∀ i j : Fin D, Qatlib.Foundations.PureStateMath.Inner (ψ i) (ψ j) = if i = j then 1 else 0)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    IsDensityOperator (gibbsBasis ψ p) := by
  have he : gibbsBasis ψ p = ∑ i, (p i : ℂ) • ketbra (ψ i) (ψ i) := by
    unfold gibbsBasis
    apply Finset.sum_congr rfl
    intro i _
    exact clause26_real_smul (p i) (ketbra (ψ i) (ψ i))
  have hpsd : (gibbsBasis ψ p).PosSemidef := by
    rw [he]
    apply Matrix.posSemidef_sum
    intro i _
    exact (clause26_ketbra_psd (ψ i)).smul (by exact_mod_cast hp i)
  have htr : Matrix.trace (gibbsBasis ψ p) = 1 := by
    rw [he, Matrix.trace_sum]
    have h1 : ∀ i : Fin D,
        Matrix.trace ((p i : ℂ) • ketbra (ψ i) (ψ i)) = (p i : ℂ) := by
      intro i
      rw [Matrix.trace_smul, clause26_trace_ketbra, horth, if_pos rfl, smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Complex.ofReal_sum, hsum,
      Complex.ofReal_one]
  exact ⟨hpsd, htr⟩

/-- The Temme Gibbs state built from an orthonormal energy basis in positive dimension is a
density operator. -/
theorem temmeGibbsState_isDensity {D : ℕ} (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (ψ : Fin D → QState (Fin D))
    (horth : ∀ i j : Fin D, Qatlib.Foundations.PureStateMath.Inner (ψ i) (ψ j) = if i = j then 1 else 0) :
    IsDensityOperator (temmeGibbsState D hD E β ψ) :=
  gibbsBasis_isDensity ψ (diagonalGibbsDist D hD E β).prob horth
    (fun i => (diagonalGibbsDist D hD E β).nonneg i)
    (diagonalGibbsDist D hD E β).sum_one

/-- Quantum detailed balance gives the fixed point property specified by
`QuantumDetailedBalanceFixedPoint`. -/
theorem clause26_anchor_fixedPoint : QuantumDetailedBalanceFixedPoint :=
  quantumDetailedBalanceFixedPoint

/-- A completely positive trace preserving realization of the Temme map fixes its Gibbs state
whenever it satisfies the stated quantum detailed balance hypothesis. -/
theorem clause26_block2_stationarity :
    ∀ (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D)),
      (∀ i j : Fin D, Qatlib.Foundations.PureStateMath.Inner (ψ i) (ψ j) = if i = j then 1 else 0) →
      (∀ x : QState (Fin D), ∑ i, Qatlib.Foundations.PureStateMath.Inner (ψ i) x • ψ i = x) →
      ∀ ens : ProposalEnsemble D,
        proposalEnsembleLegal ens →
        proposalSymmetric ens →
        ∀ β : ℝ, 0 ≤ β →
          ∀ T : Operator D →ₗ[ℂ] Operator D,
            (∀ ρ : Operator D, T ρ = temmeMapFun E ψ ens β ρ) →
            CompletelyPositive T →
            TracePreserving T →
            QuantumDetailedBalance T (temmeGibbsState D hD E β ψ) →
            T (temmeGibbsState D hD E β ψ) = temmeGibbsState D hD E β ψ := by
  intro D hD E ψ horth _hcomplete ens _hlegal _hsym β _hβ T _hfun hcp htp hdb
  exact quantumDetailedBalanceFixedPoint D ⟨T, hcp, htp⟩ (temmeGibbsState D hD E β ψ)
    (temmeGibbsState_isDensity hD E β ψ horth) hdb

/-- The contraction parameter `instanceEta` equals `(1 - exp (-1)) / 2`. -/
theorem instanceEta_eq : instanceEta = (1 - Real.exp (-1)) / 2 := by
  unfold instanceEta
  ring

/-- The instance contraction parameter is strictly positive. -/
theorem instanceEta_pos : 0 < instanceEta := by
  rw [instanceEta_eq]
  have he : Real.exp (-1) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have h : (0:ℝ) < 1 - Real.exp (-1) := by linarith
  exact div_pos h two_pos

/-- The instance contraction parameter is strictly less than one. -/
theorem instanceEta_lt_one : instanceEta < 1 := by
  have he : 0 < Real.exp (-1) := Real.exp_pos (-1)
  have h : (0:ℝ) < (1 + Real.exp (-1)) / 2 := by positivity
  unfold instanceEta
  linarith

end Clause43Blocks

/-- Left and right multiplication by fixed operators distributes over addition of the middle
operator. -/
theorem mul_mul_add {D : ℕ} (A B : Operator D) :
    ∀ ρ σ : Operator D, A * (ρ + σ) * B = A * ρ * B + A * σ * B := by
  intro ρ σ
  rw [Matrix.mul_add, Matrix.add_mul]

/-- A complex scalar multiplying the middle operator can be pulled outside a matrix sandwich. -/
theorem mul_mul_smul {D : ℕ} (A B : Operator D) :
    ∀ (c : ℂ) (ρ : Operator D), A * (c • ρ) * B = c • (A * ρ * B) := by
  intro c ρ
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- A scalar multiple of a matrix sandwich distributes over addition of the middle operator. -/
theorem smul_mul_mul_add {D : ℕ} (A B : Operator D) (c : ℂ) :
    ∀ ρ σ : Operator D, c • (A * (ρ + σ) * B) = c • (A * ρ * B) + c • (A * σ * B) := by
  intro ρ σ
  rw [mul_mul_add, smul_add]

/-- Nested complex scalars in a matrix sandwich combine into their product. -/
theorem smul_mul_mul_smul {D : ℕ} (A B : Operator D) (c d : ℂ) :
    ∀ ρ : Operator D, c • (A * (d • ρ) * B) = (c * d) • (A * ρ * B) := by
  intro ρ
  rw [mul_mul_smul, smul_smul]

/-- The Temme acceptance map preserves addition of input operators. -/
theorem temmeAcceptMap_add {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (ens : ProposalEnsemble D) (β : ℝ) :
    ∀ ρ σ : Operator D,
      temmeAcceptMap E ψ ens β (ρ + σ) =
        temmeAcceptMap E ψ ens β ρ + temmeAcceptMap E ψ ens β σ := by
  intro ρ σ
  unfold temmeAcceptMap
  simp only [Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]

/-- The Temme acceptance map preserves complex scalar multiplication. -/
theorem temmeAcceptMap_smul {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (ens : ProposalEnsemble D) (β : ℝ) :
    ∀ (c : ℂ) (ρ : Operator D),
      temmeAcceptMap E ψ ens β (c • ρ) = c • temmeAcceptMap E ψ ens β ρ := by
  intro c ρ
  unfold temmeAcceptMap
  simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  apply Matrix.ext
  intro i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun x_1 _ => ?_
  refine Finset.sum_congr rfl fun x_2 _ => ?_
  ring

/-- Each fixed rejection history map `temmeBnMap` preserves addition of input operators. -/
theorem temmeBnMap_add {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (C : Operator D) (β : ℝ) (n : ℕ) (s : Fin n → Bool) :
    ∀ ρ σ : Operator D,
      temmeBnMap E ψ C β n s (ρ + σ) =
        temmeBnMap E ψ C β n s ρ + temmeBnMap E ψ C β n s σ := by
  intro ρ σ
  unfold temmeBnMap
  simp only [Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]

/-- Each fixed rejection history map `temmeBnMap` preserves complex scalar multiplication. -/
theorem temmeBnMap_smul {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (C : Operator D) (β : ℝ) (n : ℕ) (s : Fin n → Bool) :
    ∀ (c : ℂ) (ρ : Operator D),
      temmeBnMap E ψ C β n s (c • ρ) = c • temmeBnMap E ψ C β n s ρ := by
  intro c ρ
  unfold temmeBnMap
  simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  apply Matrix.ext
  intro i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun x_1 _ => ?_
  refine Finset.sum_congr rfl fun x_2 _ => ?_
  ring

section Clause43Instance

open scoped ComplexOrder

/-- The energy of the zeroth level in the two dimensional instance is zero. -/
private theorem instanceEnergy_of_zero : instanceEnergy 0 = 0 := by
  simp [instanceEnergy]

/-- The energy of the first level in the two dimensional instance is one. -/
private theorem instanceEnergy_of_one : instanceEnergy 1 = 1 := by
  simp [instanceEnergy]

/-- The two dimensional instance assigns distinct energies to distinct indices. -/
private theorem instanceEnergy_inj : Function.Injective instanceEnergy := by
  intro a b h
  fin_cases a <;> fin_cases b
  · rfl
  · simp [instanceEnergy] at h
  · simp [instanceEnergy] at h
  · rfl

/-- A computational basis ket has coordinate one at its own index and zero elsewhere. -/
private theorem ket_eq_ite {D : ℕ} (i a : Fin D) :
    Qatlib.Foundations.PureStateMath.Ket i a = if i = a then (1 : ℂ) else 0 := by
  by_cases h : i = a <;> simp [Qatlib.Foundations.PureStateMath.Ket, h, eq_comm]

/-- The outer operator between two computational basis kets is the corresponding matrix unit. -/
private theorem ketbra_ket_eq_single {D : ℕ} (i j : Fin D) :
    ketbra (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket j) = Matrix.single i j 1 := by
  ext a b
  have hstar : star (Qatlib.Foundations.PureStateMath.Ket j b) = Qatlib.Foundations.PureStateMath.Ket j b := by
    rw [ket_eq_ite]
    by_cases h : j = b <;> simp [h]
  simp only [ketbra, Matrix.of_apply, Matrix.single, ket_eq_ite]
  by_cases ha : i = a <;> by_cases hb : j = b <;> simp [ha, hb]

/-- Each energy projector of the two dimensional instance is its diagonal matrix unit. -/
private theorem energyPi_instance (i : Fin 2) :
    energyPi instanceEnergy instanceBasis i = Matrix.single i i 1 := by
  have hfil : (Finset.univ.filter (fun j : Fin 2 => instanceEnergy j = instanceEnergy i))
      = ({i} : Finset (Fin 2)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact instanceEnergy_inj h
    · intro h
      rw [h]
  unfold energyPi instanceBasis
  rw [hfil, Finset.sum_singleton, ketbra_ket_eq_single]

/-- Every index in the two dimensional instance represents its own energy level. -/
private theorem isEnergyRep_instance (i : Fin 2) : isEnergyRep instanceEnergy i := by
  intro hex
  obtain ⟨j, hj, hlt⟩ := hex
  apply instanceEnergy_inj at hj
  subst hj
  omega

/-- The thermal acceptance from level zero to itself at inverse temperature one is one. -/
private theorem thermalAcceptance_instance_00 :
    thermalAcceptance instanceEnergy 1 0 0 = 1 := by
  simp [thermalAcceptance, instanceEnergy]

/-- The thermal acceptance from level zero to level one at inverse temperature one is `exp
(-1)`. -/
private theorem thermalAcceptance_instance_01 :
    thermalAcceptance instanceEnergy 1 0 1 = Real.exp (-1) := by
  have h : (Real.exp (-(1:ℝ) * (instanceEnergy 1 - instanceEnergy 0)) : ℝ)
      = Real.exp (-1) := by
    simp [instanceEnergy]
  have hlt : Real.exp (-1:ℝ) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  unfold thermalAcceptance
  rw [h]
  exact min_eq_right hlt.le

/-- The thermal acceptance from level one to level zero at inverse temperature one is one. -/
private theorem thermalAcceptance_instance_10 :
    thermalAcceptance instanceEnergy 1 1 0 = 1 := by
  have h : (Real.exp (-(1:ℝ) * (instanceEnergy 0 - instanceEnergy 1)) : ℝ)
      = Real.exp 1 := by
    simp [instanceEnergy]
  have hlt : (1:ℝ) ≤ Real.exp 1 := by
    nlinarith [Real.add_one_le_exp 1]
  unfold thermalAcceptance
  rw [h]
  exact min_eq_left hlt

/-- The thermal acceptance from level one to itself at inverse temperature one is one. -/
private theorem thermalAcceptance_instance_11 :
    thermalAcceptance instanceEnergy 1 1 1 = 1 := by
  simp [thermalAcceptance, instanceEnergy]

/-- The product of two real inverse square roots of two equals one half. -/
private theorem real_inv_sqrt_two_mul :
    (Real.sqrt 2 : ℝ)⁻¹ * (Real.sqrt 2 : ℝ)⁻¹ = 1 / 2 := by
  rw [← pow_two, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The product of two complex inverses of the real square root of two equals one half. -/
private theorem coe_inv_sqrt_two_mul :
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  have h := congrArg ((↑) : ℝ → ℂ) real_inv_sqrt_two_mul
  simp only [Complex.ofReal_mul, Complex.ofReal_inv] at h
  norm_num at h
  exact h

/-- The square of the complex inverse of the real square root of two equals one half. -/
private theorem coe_inv_sqrt_two_sq :
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ 2 = 1 / 2 := by
  rw [pow_two]
  exact coe_inv_sqrt_two_mul

/-- Oppositely indexed entries of `instanceProposal` have product one half. -/
private theorem instanceProposal_mul_rev (i j : Fin 2) :
    instanceProposal j i * instanceProposal i j = (1 / 2 : ℂ) := by
  fin_cases i <;> fin_cases j <;>
    simp only [instanceProposal, Matrix.add_apply, Matrix.smul_apply] <;>
    norm_num [mul_comm, RCLike.real_smul_eq_coe_mul] <;> ring_nf
  all_goals exact coe_inv_sqrt_two_sq

/-- A sum over the singleton proposal ensemble equals its unique term. -/
private theorem sum_ens_one {α : Type*} [AddCommMonoid α] (f : Fin instanceEnsemble.count → α) :
    ∑ c, f c = f ⟨0, by simp [instanceEnsemble]⟩ := by
  rw [Finset.sum_eq_single (⟨0, by simp [instanceEnsemble]⟩ : Fin instanceEnsemble.count)]
  · intro b _ hb
    have hb0 : b = (⟨0, by simp [instanceEnsemble]⟩ : Fin instanceEnsemble.count) := by
      ext
      have hlt := b.isLt
      simp only [instanceEnsemble] at hlt ⊢
      omega
    rw [hb0] at hb
    exact absurd rfl hb
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The singleton ensemble index can be removed from the stated triple sum. -/
private theorem sum3_ens {α : Type*} [AddCommMonoid α] (g : Fin 2 → Fin 2 → α) :
    (∑ i : Fin 2, ∑ j : Fin 2, ∑ _c : Fin instanceEnsemble.count, g i j)
      = ∑ i : Fin 2, ∑ j : Fin 2, g i j := by
  simp only [sum_ens_one]

/-- Sandwiching the input with instance proposal entries and diagonal matrix units yields half
its selected diagonal entry times the output matrix unit. -/
private theorem instance_sandwich (i j : Fin 2) (ρ : Operator 2) :
    (Matrix.single j j 1 : Operator 2) * instanceProposal * Matrix.single i i 1 * ρ *
      Matrix.single i i 1 * instanceProposal * Matrix.single j j 1
      = (ρ i i / 2 : ℂ) • Matrix.single j j 1 := by
  have hA : (Matrix.single j j 1 : Operator 2) * instanceProposal * Matrix.single i i 1
      = instanceProposal j i • Matrix.single j i 1 := by
    rw [Matrix.single_mul_mul_single]
    simp
  have hB : (Matrix.single i i 1 : Operator 2) * instanceProposal * Matrix.single j j 1
      = instanceProposal i j • Matrix.single i j 1 := by
    rw [Matrix.single_mul_mul_single]
    simp
  have hgroup : (Matrix.single j j 1 : Operator 2) * instanceProposal * Matrix.single i i 1 * ρ *
      Matrix.single i i 1 * instanceProposal * Matrix.single j j 1
      = ((Matrix.single j j 1 : Operator 2) * instanceProposal * Matrix.single i i 1) * ρ *
        ((Matrix.single i i 1 : Operator 2) * instanceProposal * Matrix.single j j 1) := by
    simp only [Matrix.mul_assoc]
  rw [hgroup, hA, hB, smul_mul_assoc, smul_mul_smul, Matrix.single_mul_mul_single]
  simp only [one_mul, mul_one]
  rw [instanceProposal_mul_rev i j, smul_single, smul_single]
  simp only [smul_eq_mul, mul_one]
  congr 1
  field_simp

/-- The instance proposal matrix equals its conjugate transpose. -/
private theorem instanceProposal_hermitian :
    instanceProposal.conjTranspose = instanceProposal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.conjTranspose_apply, instanceProposal, Matrix.add_apply,
      Matrix.smul_apply] <;>
    norm_num [RCLike.real_smul_eq_coe_mul, Complex.conj_ofReal]

/-- The acceptance map of the two dimensional instance is the stated diagonal operator
determined by the two input diagonal entries and `exp (-1)`. -/
private theorem temmeAcceptMap_instance (ρ : Operator 2) :
    temmeAcceptMap instanceEnergy instanceBasis instanceEnsemble 1 ρ =
      Matrix.diagonal fun j : Fin 2 =>
        ((if j = 0 then (1 : ℂ) else (Real.exp (-1) : ℂ)) * ρ 0 0 + ρ 1 1) / 2 := by
  unfold temmeAcceptMap
  have hrep : ∀ i j : Fin 2,
      (if isEnergyRep instanceEnergy i ∧ isEnergyRep instanceEnergy j then (1 : ℝ) else 0) = 1 := by
    intro i j
    simp [isEnergyRep_instance]
  have hw : ∀ c : Fin instanceEnsemble.count, instanceEnsemble.weight c = (1 : ℝ) := fun _ => rfl
  have hg : ∀ c : Fin instanceEnsemble.count, instanceEnsemble.gate c = instanceProposal :=
      fun _ => rfl
  simp only [hrep, hw, hg, one_mul, instanceProposal_hermitian]
  have hsand : ∀ i j : Fin 2,
      (energyPi instanceEnergy instanceBasis j * instanceProposal *
          energyPi instanceEnergy instanceBasis i * ρ *
          energyPi instanceEnergy instanceBasis i * instanceProposal *
          energyPi instanceEnergy instanceBasis j)
        = (ρ i i / 2 : ℂ) • Matrix.single j j 1 := by
    intro i j
    have h := instance_sandwich i j ρ
    simp only [energyPi_instance] at h ⊢
    exact h
  simp only [hsand, smul_smul, clause26_real_smul]
  rw [sum3_ens]
  simp only [← sum_single_eq_diagonal]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcoeff : (∑ i : Fin 2,
      (((thermalAcceptance instanceEnergy 1 i j : ℝ) : ℂ) * (ρ i i / 2)))
      = ((if j = 0 then (1 : ℂ) else (Real.exp (-1) : ℂ)) * ρ 0 0 + ρ 1 1) / 2 := by
    fin_cases j
    · show (∑ i : Fin 2, (((thermalAcceptance instanceEnergy 1 i 0 : ℝ) : ℂ) * (ρ i i / 2)))
        = ((1 : ℂ) * ρ 0 0 + ρ 1 1) / 2
      rw [Fin.sum_univ_two, thermalAcceptance_instance_00, thermalAcceptance_instance_10]
      push_cast
      ring
    · show (∑ i : Fin 2, (((thermalAcceptance instanceEnergy 1 i 1 : ℝ) : ℂ) * (ρ i i / 2)))
        = (((Real.exp (-1 : ℝ)) : ℂ) * ρ 0 0 + ρ 1 1) / 2
      rw [Fin.sum_univ_two, thermalAcceptance_instance_01, thermalAcceptance_instance_11]
      push_cast
      ring
  conv_lhs => rw [← Finset.sum_smul]
  rw [hcoeff, smul_single, smul_eq_mul, mul_one]

/-- The Metropolis coin at acceptance parameter one is the two dimensional flip matrix. -/
private theorem metropolisCoin_one : MetropolisCoin 1 = !![(0 : ℂ), 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [MetropolisCoin, Real.sqrt_zero, Real.sqrt_one]

/-- The two dimensional flip matrix equals its conjugate transpose. -/
private theorem flip_lit_hermitian : (!![(0 : ℂ), 1; 1, 0])ᴴ = !![(0 : ℂ), 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

/-- The flip matrix is the sum of its two off diagonal matrix units. -/
private theorem flip_lit_eq : !![(0 : ℂ), 1; 1, 0] = Matrix.single 0 1 1 + Matrix.single 1 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single]

/-- Conjugating a diagonal matrix unit by the flip matrix exchanges the two basis indices. -/
private theorem flip_conj_single (k : Fin 2) :
    (!![(0 : ℂ), 1; 1, 0]) * Matrix.single k k 1 * (!![(0 : ℂ), 1; 1, 0])
      = Matrix.single (if k = 0 then (1 : Fin 2) else 0) (if k = 0 then (1 : Fin 2) else 0) 1 := by
  rw [flip_lit_eq]
  fin_cases k <;>
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.single_mul_single_same,
      Matrix.single_mul_single_of_ne]

/-- The instance rejection factor from level one is the diagonal matrix unit selected by the
Boolean outcome. -/
private theorem temmeR_inst_one (σ : Bool) (j : Fin 2) :
    temmeR instanceEnergy 1 σ 1 j
      = Matrix.single (if σ then (0 : Fin 2) else 1) (if σ then (0 : Fin 2) else 1) 1 := by
  have ha : thermalAcceptance instanceEnergy 1 1 j = 1 := by
    fin_cases j
    · exact thermalAcceptance_instance_10
    · exact thermalAcceptance_instance_11
  have hcoin : coinProjector σ
      = Matrix.single (if σ then (1 : Fin 2) else 0) (if σ then (1 : Fin 2) else 0) 1 := by
    unfold coinProjector
    rw [ketbra_ket_eq_single]
  unfold temmeR
  rw [ha, metropolisCoin_one, flip_lit_hermitian, hcoin, flip_conj_single]
  fin_cases σ <;> rfl

/-- The product of two ketbra operators is the inner product of their middle vectors times the
outer ketbra operator. -/
private theorem ketbra_mul_ketbra {D : ℕ} (u v w x : QState (Fin D)) :
    ketbra u v * ketbra w x = Qatlib.Foundations.PureStateMath.Inner v w • ketbra u x := by
  have hinner : Qatlib.Foundations.PureStateMath.Inner v w = ∑ k : Fin D, star (v k) * w k := by
    rw [inner_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rfl
  ext a b
  simp only [Matrix.mul_apply, Matrix.smul_apply, ketbra, Matrix.of_apply, hinner, smul_eq_mul]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- Left multiplication of a ketbra operator applies the matrix to its ket vector. -/
private theorem mul_ketbra {D : ℕ} (C : Operator D) (u v : QState (Fin D)) :
    C * ketbra u v = ketbra (C *ᵥ u) v := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, ketbra, Matrix.of_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- Right multiplication of a ketbra operator by a Hermitian matrix applies that matrix to its
bra vector. -/
private theorem ketbra_mul_herm {D : ℕ} (C : Operator D) (u v : QState (Fin D))
    (hC : C.conjTranspose = C) :
    ketbra u v * C = ketbra u (C *ᵥ v) := by
  have hconj : ∀ p q : Fin D, star (C p q) = C q p := by
    intro p q
    have h := congrFun (congrFun hC q) p
    simpa [Matrix.conjTranspose_apply] using! h
  ext a b
  have hs : star (∑ k : Fin D, C b k * v k) = ∑ k : Fin D, C k b * star (v k) := by
    rw [star_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [star_mul', hconj]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, ketbra, Matrix.of_apply]
  rw [hs, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- Left multiplication by a diagonal matrix unit extracts the corresponding overlap of the ket
vector. -/
private theorem single_ketbra {D : ℕ} (i : Fin D) (u v : QState (Fin D)) :
    Matrix.single i i 1 * ketbra u v = Qatlib.Foundations.PureStateMath.Inner (Qatlib.Foundations.PureStateMath.Ket i) u • ketbra (Qatlib.Foundations.PureStateMath.Ket i) v := by
  rw [← ketbra_ket_eq_single, ketbra_mul_ketbra]

/-- Right multiplication by a diagonal matrix unit extracts the corresponding overlap of the bra
vector. -/
private theorem ketbra_single {D : ℕ} (j : Fin D) (u v : QState (Fin D)) :
    ketbra u v * Matrix.single j j 1 = Qatlib.Foundations.PureStateMath.Inner v (Qatlib.Foundations.PureStateMath.Ket j) • ketbra u (Qatlib.Foundations.PureStateMath.Ket j) := by
  rw [← ketbra_ket_eq_single, ketbra_mul_ketbra]

/-- Sandwiching a diagonal matrix unit by a Hermitian operator gives the rank one operator of
the transformed basis ket. -/
private theorem herm_single_herm {D : ℕ} (C : Operator D) (j : Fin D)
    (hC : C.conjTranspose = C) :
    C * Matrix.single j j 1 * C = ketbra (C *ᵥ Qatlib.Foundations.PureStateMath.Ket j) (C *ᵥ Qatlib.Foundations.PureStateMath.Ket j) := by
  rw [← ketbra_ket_eq_single, mul_ketbra,
      ketbra_mul_herm C (C *ᵥ Qatlib.Foundations.PureStateMath.Ket j)
      (Qatlib.Foundations.PureStateMath.Ket j) hC]

/-- Every coefficient `temmeG` starting at level one of the instance vanishes at inverse
temperature one. -/
private theorem temmeG_instance_one (n : ℕ) (s : Fin n → Bool)
    (l r : Fin (n + 1) → Fin 2) :
    temmeG instanceEnergy 1 1 n s l r = 0 := by
  have hR : temmeR instanceEnergy 1 (temmeCoinAt instanceEnergy 1 n s 0) 1 (r 0)
      = Matrix.single 1 1 1 := by
    have h0 : temmeCoinAt instanceEnergy 1 n s 0 = false := by
      unfold temmeCoinAt
      simp
    rw [h0, temmeR_inst_one]
    simp
  have hword : temmeGWord instanceEnergy 1 1 n s l r
      = Matrix.single 1 1 1 :: List.tail (temmeGWord instanceEnergy 1 1 n s l r) := by
    unfold temmeGWord
    rw [List.map_reverse, ← List.ofFn_eq_map, ← List.ofFn_eq_map, List.ofFn_succ,
      List.cons_append]
    simp only [Fin.val_zero]
    rw [hR]
    rfl
  unfold temmeG
  rw [hword, List.prod_cons, ← Matrix.mulVec_mulVec, Matrix.single_mulVec]
  simp

end Clause43Instance

section Clause42ProposalMultiplicity

open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

/-- At zero inverse temperature, the false rejection factor is the diagonal matrix unit at index
one. -/
theorem temmeR_zero_beta_false {D : ℕ} (E : Fin D → ℝ) (i j : Fin D) :
    temmeR E 0 false i j = Matrix.single 1 1 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [temmeR,thermalAcceptance,MetropolisCoin,coinProjector,ketbra,Qatlib.Foundations.PureStateMath.Ket,
      Matrix.mul_apply,Fin.sum_univ_two]

/-- At zero inverse temperature, every coefficient `temmeG` vanishes. -/
theorem temmeG_zero_beta {D : ℕ} (E : Fin D → ℝ) (i : Fin D) (n : ℕ)
    (s : Fin n → Bool) (l r : Fin (n+1) → Fin D) : temmeG E 0 i n s l r = 0 := by
  have hword : ∃ tail : List (Operator 2),
      temmeGWord E 0 i n s l r = temmeR E 0 false i (r 0) :: tail := by
    unfold temmeGWord
    rw [← List.ofFn_eq_map,List.ofFn_succ,List.cons_append]
    simp only [temmeCoinAt,Fin.val_zero,lt_self_iff_false,false_and,↓reduceDIte]
    exact ⟨_,rfl⟩
  obtain ⟨tail,ht⟩ := hword
  rw [temmeG,ht,List.prod_cons,← Matrix.mulVec_mulVec,temmeR_zero_beta_false,
    Matrix.single_mulVec]
  simp

/-- The total Temme rejection map is zero at zero inverse temperature. -/
theorem temme_rejection_zero_beta {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (ens : ProposalEnsemble D) (ρ : Operator D) : temmeBtotal E ψ ens 0 ρ = 0 := by
  have hb (C : Operator D) (n : ℕ) (s : Fin n → Bool) : temmeBnMap E ψ C 0 n s ρ = 0 := by
    simp [temmeBnMap,temmeG_zero_beta]
  simp [temmeBtotal,hb]

/-- The four dimensional permutation matrix cycling the first three basis vectors and fixing the
fourth. -/
def duplicateCycle : Operator 4 := !![0,0,1,0;1,0,0,0;0,1,0,0;0,0,0,1]

/-- The permutation matrix `duplicateCycle` is unitary. -/
theorem duplicateCycle_unitary : duplicateCycle ∈ Matrix.unitaryGroup _ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [duplicateCycle,Matrix.mul_apply,Fin.sum_univ_succ]

/-- The equally weighted three entry proposal ensemble containing two copies of `duplicateCycle`
and one copy of its adjoint. -/
noncomputable abbrev duplicateEnsemble : ProposalEnsemble 4 :=
  ⟨3,fun _ => 1/3,fun i => if i=2 then duplicateCycleᴴ else duplicateCycle⟩

/-- The duplicate proposal ensemble satisfies `proposalEnsembleLegal`. -/
theorem duplicateEnsemble_legal : proposalEnsembleLegal duplicateEnsemble := by
  refine ⟨fun _ => by norm_num [duplicateEnsemble],?_,?_⟩
  · norm_num [duplicateEnsemble,Fin.sum_univ_succ]
  · intro i
    by_cases hi : i=2
    · simpa [duplicateEnsemble,hi] using!
        Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary duplicateCycle_unitary
    · simpa [duplicateEnsemble,hi] using! duplicateCycle_unitary

/-- The duplicate proposal ensemble satisfies the predicate `proposalSymmetric`. -/
theorem duplicateEnsemble_symmetric : proposalSymmetric duplicateEnsemble := by
  intro j
  by_cases hj : j=2
  · refine ⟨0,rfl,?_⟩
    simp [hj]
  · refine ⟨2,rfl,?_⟩
    simp [hj]

/-- For the constant zero energy function on four indices, only index zero is an energy
representative. -/
theorem zero_energy_rep (i : Fin 4) : isEnergyRep (fun _ : Fin 4 => (0:ℝ)) i ↔ i=0 := by
  constructor
  · intro h
    by_contra hi
    apply h
    exact ⟨0,rfl,by omega⟩
  · rintro rfl ⟨j,_,hj⟩
    exact Nat.not_lt_zero _ hj

/-- Every energy projector for the constant zero energy function in the computational basis is
the identity. -/
theorem zero_energy_projector (i : Fin 4) : energyPi (fun _ : Fin 4 => (0:ℝ)) Qatlib.Foundations.PureStateMath.Ket i = 1 := by
  have hket (j a : Fin 4) : Qatlib.Foundations.PureStateMath.Ket j a = if j=a then (1:ℂ) else 0 := by
    by_cases h : j=a <;> simp [Qatlib.Foundations.PureStateMath.Ket,h,eq_comm]
  have hk (j : Fin 4) : ketbra (Qatlib.Foundations.PureStateMath.Ket j) (Qatlib.Foundations.PureStateMath.Ket j) = Matrix.single j j 1 := by
    ext a b
    simp only [ketbra,Matrix.of_apply,Matrix.single,hket]
    by_cases ha : j=a <;> by_cases hb : j=b <;> simp [ha,hb]
  simp only [energyPi,Finset.filter_true]
  simp_rw [hk]
  exact Matrix.sum_single_one

/-- For the duplicate ensemble at zero energy and inverse temperature zero, the Temme map is the
mixture of forward and reverse cycle conjugations with weights two thirds and one third. -/
theorem duplicate_temmemap (ρ : Operator 4) :
    temmeMapFun (fun _ : Fin 4 => (0:ℝ)) Qatlib.Foundations.PureStateMath.Ket duplicateEnsemble 0 ρ =
      (2/3:ℝ) • (duplicateCycle*ρ*duplicateCycleᴴ) +
        (1/3:ℝ) • (duplicateCycleᴴ*ρ*duplicateCycle) := by
  rw [temmeMapFun,temme_rejection_zero_beta,add_zero]
  simp only [temmeAcceptMap,zero_energy_rep,zero_energy_projector,thermalAcceptance,neg_zero,
    zero_mul,Real.exp_zero,min_self,Matrix.one_mul,Matrix.mul_one]
  simp [Fin.sum_univ_succ]
  module

/-- The Gibbs state of the four dimensional zero energy example is one quarter of the identity. -/
theorem duplicate_gibbs : temmeGibbsState 4 (by decide) (fun _ => 0) 0 Qatlib.Foundations.PureStateMath.Ket =
    (1/4:ℝ) • (1 : Operator 4) := by
  have hp (i : Fin 4) : (diagonalGibbsDist 4 (by decide) (fun _ => 0) 0).prob i = 1/4 := by
    norm_num [diagonalGibbsDist,diagonalGibbsPartition]
  unfold temmeGibbsState gibbsBasis
  simp_rw [hp]
  rw [← Finset.smul_sum]
  have hpi : (∑ i : Fin 4,ketbra (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket i)) = 1 := by
    simpa [energyPi] using! zero_energy_projector 0
  rw [hpi]

/-- The positive square root of the Gibbs state in the duplicate example is one half of the
identity. -/
theorem duplicate_gibbs_sqrt : densSqrt (temmeGibbsState 4 (by decide) (fun _ => 0) 0 Qatlib.Foundations.PureStateMath.Ket) =
    (1/2:ℝ) • (1 : Operator 4) := by
  rw [densSqrt,duplicate_gibbs,← Algebra.algebraMap_eq_smul_one,cfc_algebraMap,
    Algebra.algebraMap_eq_smul_one]
  congr 1
  rw [show (1/4:ℝ) = (1/2)^2 by norm_num,Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)]

/-- No complex linear realization of the duplicate example Temme map satisfies quantum detailed
balance with its Gibbs state. -/
theorem duplicate_detailed_balance_impossible (T : Operator 4 →ₗ[ℂ] Operator 4)
    (hT : ∀ ρ, T ρ = temmeMapFun (fun _ : Fin 4 => (0:ℝ)) Qatlib.Foundations.PureStateMath.Ket duplicateEnsemble 0 ρ) :
    ¬ QuantumDetailedBalance T (temmeGibbsState 4 (by decide) (fun _ => 0) 0 Qatlib.Foundations.PureStateMath.Ket) := by
  intro hdb
  have h := hdb (Matrix.single 0 0 1) (Matrix.single 1 1 1)
  rw [duplicate_gibbs_sqrt,hT,hT,duplicate_temmemap,duplicate_temmemap] at h
  simp only [Matrix.conjTranspose_single,star_one,Matrix.trace_single_mul,Matrix.trace_mul_single,
    one_smul,Matrix.conjTranspose_apply] at h
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_smul, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply] at h
  norm_num [Fin.sum_univ_succ, Matrix.single, duplicateCycle, MulOpposite.op_one] at h

/-- The universal detailed balance contract `clause42Body` is false. -/
theorem clause42_contract_false : ¬ clause42Body := by
  intro h
  have hb (x : QState (Fin 4)) : ∑ i, Qatlib.Foundations.PureStateMath.Inner (Qatlib.Foundations.PureStateMath.Ket i) x • Qatlib.Foundations.PureStateMath.Ket i = x := by
    have hi (i : Fin 4) : Qatlib.Foundations.PureStateMath.Inner (Qatlib.Foundations.PureStateMath.Ket i) x = x i := by
      simp [Qatlib.Foundations.PureStateMath.Inner, Qatlib.Foundations.PureStateMath.Ket,
          dotProduct]
    simp_rw [hi]
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, Qatlib.Foundations.PureStateMath.Ket, smul_eq_mul]
  obtain ⟨T,hT,_,_,hdb⟩ := h 4 (by decide) (fun _ => 0) Qatlib.Foundations.PureStateMath.Ket
    inner_ket_ket hb duplicateEnsemble duplicateEnsemble_legal
    duplicateEnsemble_symmetric 0 (by norm_num)
  exact duplicate_detailed_balance_impossible T hT hdb

end Clause42ProposalMultiplicity

end Qatlib.Concepts.MixedInstrument.RewindAlgebra
