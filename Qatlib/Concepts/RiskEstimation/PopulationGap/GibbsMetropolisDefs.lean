/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalanceCriterionStat
import Qatlib.Concepts.GibbsMetropolis.RationalBath.DiagonalMetropolisKernel
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.MeasuredMetropolisChannel
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.PureStateMath.Qubit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.QuantumGibbs.DetailedBalance

set_option autoImplicit false

namespace Qatlib.Concepts.RiskEstimation.PopulationGap

open Matrix Qatlib.Concepts.QuantumGibbs.DetailedBalance
open scoped BigOperators Classical Matrix.Norms.L2Operator

noncomputable def phaseOfEnergy (t e : ℝ) : ℝ := -t * e / (2 * Real.pi)

noncomputable def qpeBornMass (M : ℕ) (φ : ℝ) (z : Fin M) : ℝ :=
  ‖qpeKernel M φ z‖ ^ 2

noncomputable def labelEnergy (t : ℝ) (M : ℕ) (z : Fin M) : ℝ :=
  -(2 * Real.pi / t) * ((z.val : ℝ) / (M : ℝ))

noncomputable def labelAcceptance (t : ℝ) (M : ℕ) (β : ℝ) (i z : Fin M) : ℝ :=
  thermalAcceptance (fun w => labelEnergy t M w) β i z

noncomputable def fairBitAcceptMass (k : ℕ) (f : ℝ) : ℝ :=
  (Nat.floor ((2 : ℝ) ^ k * f)) / (2 : ℝ) ^ k

noncomputable def qpePovmElement {D : ℕ} (A : Operator D) (t : ℝ) (M : ℕ) (z : Fin M) :
    Operator D :=
  cfc (fun x : ℝ => qpeBornMass M (phaseOfEnergy t x) z) A

noncomputable def qpeKraus {D : ℕ} (A : Operator D) (t : ℝ) (M : ℕ) (z : Fin M) :
    Operator D :=
  cfc (fun x : ℝ => Real.sqrt (qpeBornMass M (phaseOfEnergy t x) z)) A

noncomputable def coinProjector (b : Bool) : Operator 2 :=
  ketbra (Ket (if b then 1 else 0)) (Ket (if b then 1 else 0))

noncomputable def unknownHBranchMass (t : ℝ) (M : ℕ) (β : ℝ) (k : ℕ)
    (old z : Fin M) (b : Bool) : ℝ :=
  if b then fairBitAcceptMass k (labelAcceptance t M β old z)
    else 1 - fairBitAcceptMass k (labelAcceptance t M β old z)

noncomputable def unknownHBranch {D : ℕ} (A : Operator D) (t : ℝ) (M : ℕ) (β : ℝ) (k : ℕ)
    (old z : Fin M) (b : Bool) (ρ : Operator D) : Operator (D * 2) :=
  (unknownHBranchMass t M β k old z b) •
    (TensorGate (qpeKraus A t M z * ρ * (qpeKraus A t M z)ᴴ) (coinProjector b)).submatrix
      (finProdFinEquiv.symm) (finProdFinEquiv.symm)

noncomputable def unknownHJointProb {D : ℕ} (A : Operator D) (t : ℝ) (M : ℕ) (β : ℝ) (k : ℕ)
    (old z : Fin M) (b : Bool) (ρ : Operator D) : ℝ :=
  unknownHBranchMass t M β k old z b * (Matrix.trace (qpePovmElement A t M z * ρ)).re

noncomputable def unknownHEigenProb {D : ℕ} (A : Operator D) (t : ℝ) (M : ℕ)
    (ψ : Fin D → QState (Fin D)) (eig : Fin D → ℝ) (ρ : Operator D) (z : Fin M) : ℝ :=
  ∑ i, (Inner (ψ i) (ρ *ᵥ ψ i)).re * qpeBornMass M (phaseOfEnergy t (eig i)) z

def isEnergyRep {D : ℕ} (E : Fin D → ℝ) (i : Fin D) : Prop :=
  ¬ ∃ j : Fin D, E j = E i ∧ j.val < i.val

noncomputable def energyPi {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D)) (i : Fin D) :
    Operator D :=
  ∑ j ∈ Finset.univ.filter (fun j => E j = E i), ketbra (ψ j) (ψ j)

structure ProposalEnsemble (D : ℕ) where
  count : ℕ
  weight : Fin count → ℝ
  gate : Fin count → Operator D

def proposalEnsembleLegal {D : ℕ} (ens : ProposalEnsemble D) : Prop :=
  (∀ j, 0 ≤ ens.weight j) ∧ (∑ j, ens.weight j = 1) ∧
    (∀ j, ens.gate j ∈ Matrix.unitaryGroup (Fin D) ℂ)

def proposalSymmetric {D : ℕ} (ens : ProposalEnsemble D) : Prop :=
  ∀ j, ∃ i, ens.weight i = ens.weight j ∧ ens.gate i = (ens.gate j)ᴴ

def proposalPositive {D : ℕ} (ens : ProposalEnsemble D) : Prop :=
  ∀ j, 0 < ens.weight j

noncomputable def temmeR {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (s : Bool) (i j : Fin D) :
    Operator 2 :=
  (MetropolisCoin (thermalAcceptance E β i j))ᴴ * coinProjector s *
    MetropolisCoin (thermalAcceptance E β i j)

def temmeCoinAt {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (n : ℕ) (s : Fin n → Bool) (m : ℕ) : Bool :=
  if h : 0 < m ∧ m ≤ n then s ⟨m - 1, by omega⟩ else false

noncomputable def temmeGWord {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (i : Fin D) (n : ℕ)
    (s : Fin n → Bool) (l r : Fin (n + 1) → Fin D) : List (Operator 2) :=
  (List.finRange (n + 1)).map
      (fun m => temmeR E β (temmeCoinAt E β n s m.val) i (r m)) ++
    (List.finRange (n + 1)).reverse.map
      (fun m => temmeR E β (temmeCoinAt E β n s m.val) i (l m))

noncomputable def temmeG {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (i : Fin D) (n : ℕ)
    (s : Fin n → Bool) (l r : Fin (n + 1) → Fin D) : ℂ :=
  ((temmeGWord E β i n s l r).prod *ᵥ Ket 0) 0

noncomputable def temmeDInner {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (C : Operator D) (i : Fin D) : (m : ℕ) → (l : Fin m → Fin D) → Operator D
  | 0, _ => energyPi E ψ i
  | 1, l => Cᴴ * energyPi E ψ (l ⟨0, by omega⟩) * C * energyPi E ψ i
  | m + 1, l =>
      Cᴴ * energyPi E ψ (l ⟨m, by omega⟩) * C * (1 - energyPi E ψ i) *
        temmeDInner E ψ C i m (fun j => l (Fin.castSucc j))

noncomputable def temmeD {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (C : Operator D) (i : Fin D) (n : ℕ) (l : Fin (n + 1) → Fin D) : Operator D :=
  energyPi E ψ i * temmeDInner E ψ C i (n + 1) l

noncomputable def temmeAcceptMap {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (ens : ProposalEnsemble D) (β : ℝ) (ρ : Operator D) : Operator D :=
  ∑ i, ∑ j, ∑ c,
    ((if isEnergyRep E i ∧ isEnergyRep E j then (1 : ℝ) else 0) *
        ens.weight c * thermalAcceptance E β i j) •
      (energyPi E ψ j * ens.gate c * energyPi E ψ i * ρ * energyPi E ψ i *
        (ens.gate c)ᴴ * energyPi E ψ j)

noncomputable def temmeBnMap {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (C : Operator D) (β : ℝ) (n : ℕ) (s : Fin n → Bool) (ρ : Operator D) : Operator D :=
  ∑ i, ∑ l, ∑ r,
    (if isEnergyRep E i ∧ (∀ j, isEnergyRep E (l j)) ∧ (∀ j, isEnergyRep E (r j))
      then temmeG E β i n s l r else 0) •
      (temmeD E ψ C i n l * ρ * (temmeD E ψ C i n r)ᴴ)

noncomputable def temmeBtotal {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (ens : ProposalEnsemble D) (β : ℝ) (ρ : Operator D) : Operator D :=
  ∑' n : ℕ, ∑ c, ∑ s : Fin n → Bool,
    (ens.weight c) • temmeBnMap E ψ (ens.gate c) β n s ρ

noncomputable def temmeMapFun {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (ens : ProposalEnsemble D) (β : ℝ) (ρ : Operator D) : Operator D :=
  temmeAcceptMap E ψ ens β ρ + temmeBtotal E ψ ens β ρ

noncomputable def temmeGibbsState (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (ψ : Fin D → QState (Fin D)) : Operator D :=
  gibbsBasis ψ (diagonalGibbsDist D hD E β).prob

noncomputable def temmeStepMatrix {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (ens : ProposalEnsemble D) (β : ℝ) : Fin D → Fin D → ℝ :=
  fun i j => (Inner (ψ j) (temmeMapFun E ψ ens β (ketbra (ψ i) (ψ i)) *ᵥ ψ j)).re

def denseGenerated {D : ℕ} (ens : ProposalEnsemble D) : Prop :=
  ∀ V : Operator D, V ∈ Matrix.unitaryGroup (Fin D) ℂ →
    ∀ ε : ℝ, 0 < ε → ∃ l : List (Fin ens.count), ‖(l.map ens.gate).prod - V‖ ≤ ε

def instanceEnergy : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1

def instanceBasis : Fin 2 → QState (Fin 2) := fun i => Ket i

noncomputable def instanceProposal : Operator 2 :=
  (Real.sqrt 2)⁻¹ • (!![(0 : ℂ), 1; 1, 0] + !![(1 : ℂ), 0; 0, -1])

noncomputable def instanceEnsemble : ProposalEnsemble 2 where
  count := 1
  weight := fun _ => 1
  gate := fun _ => instanceProposal

noncomputable def instanceEta : ℝ := 1 - (1 + Real.exp (-1)) / 2

noncomputable def tvDistance {I : Type} [Fintype I] (μ ν : I → ℝ) : ℝ :=
  (∑ x, |μ x - ν x|) / 2

noncomputable def kernelPower {I : Type} [Fintype I] (P : I → I → ℝ) :
    ℕ → I → I → ℝ
  | 0, x, y => if x = y then 1 else 0
  | m + 1, x, y => ∑ z, kernelPower P m x z * P z y

def variationalGapPremise {I : Type} [Fintype I] (P : I → I → ℝ) (π : I → ℝ) (Δ : ℝ) : Prop :=
  ∀ f : I → ℝ, (∑ x, π x * f x = 0) →
    ∑ x, π x * (∑ y, P x y * f y) ^ 2 ≤ (1 - Δ) ^ 2 * ∑ x, π x * (f x) ^ 2

def qpeWindowQueries (M n : ℕ) : ℕ := (M - 1) * 27 * (4 * n + 1)

def qpeWindowGates (M n : ℕ) : ℕ :=
  2 * (M - 1) + 2 + (M - 1) * (27 * (4 * n + 6) + 79)

structure MetropolisCostLedger where
  prepQueries : ℕ
  stepQueries : ℕ
  stepGates : ℕ
  stepBits : ℕ
  spaceQubits : ℕ

def metropolisStepLedger (D M k n nStar : ℕ) : MetropolisCostLedger where
  prepQueries := qpeWindowQueries M n
  stepQueries := (2 + nStar) * qpeWindowQueries M n
  stepGates := (2 + nStar) * qpeWindowGates M n
  stepBits := k + 1 + Nat.clog 2 M * (nStar + 1)
  spaceQubits := D + 2 * Nat.clog 2 M + 1 + k

def metropolisRunLedger (m D M k n nStar : ℕ) : MetropolisCostLedger where
  prepQueries := qpeWindowQueries M n
  stepQueries := m * ((2 + nStar) * qpeWindowQueries M n)
  stepGates := m * ((2 + nStar) * qpeWindowGates M n)
  stepBits := m * (k + 1 + Nat.clog 2 M * (nStar + 1))
  spaceQubits := D + 2 * Nat.clog 2 M + 1 + k

noncomputable def dyadicRat (k : ℕ) (x : ℝ) : ℚ :=
  ((Nat.floor ((2 : ℝ) ^ k * x) : ℤ) : ℚ) / ((2 ^ k : ℕ) : ℚ)

noncomputable def gibbsL1ShiftBound (N : ℕ) (β δ R : ℝ) : ℝ :=
  2 * (N : ℝ) ^ 2 * β * δ * Real.exp (2 * β * R)

noncomputable def sharpTailBound (n : ℕ) : ℝ :=
  1 / (2 * Real.exp 1 * ((n : ℝ) + 1))

noncomputable def twoProjectorP : Operator 2 :=
  ketbra (Ket 0) (Ket 0)

noncomputable def twoProjectorQ (d : ℝ) : Operator 2 :=
  ketbra (fun i => if i = 0 then Complex.ofReal (Real.sqrt d)
      else Complex.ofReal (Real.sqrt (1 - d)))
    (fun i => if i = 0 then Complex.ofReal (Real.sqrt d)
      else Complex.ofReal (Real.sqrt (1 - d)))

def twoProjectorPsi : QState (Fin 2) := Ket 0

end Qatlib.Concepts.RiskEstimation.PopulationGap
