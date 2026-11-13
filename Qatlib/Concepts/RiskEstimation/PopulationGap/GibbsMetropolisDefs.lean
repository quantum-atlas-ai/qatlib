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

/-!
# Quantum Metropolis branches and resource ledgers

This module defines finite phase estimation readout, energy label acceptance, and the accept and
rejection history expressions used in quantum Metropolis sampling [TemmeEtAl2011]. `temmeMapFun`
combines `temmeAcceptMap` with the infinite rejection history sum `temmeBtotal`; these
definitions alone impose no convergence or channel properties.

The module also records finite kernel iteration, a weighted contraction premise, explicit query
and gate ledgers, and two dimensional test operators.

## Main definitions

* `qpePovmElement` and `qpeKraus`: functional calculus expressions for phase readout.
* `temmeMapFun`: the combined Metropolis map expression.
* `variationalGapPremise`: contraction on weighted mean zero functions.
* `metropolisRunLedger`: resource accounting for repeated steps.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

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

/-- The phase `-t * e / (2 * π)` associated with energy `e` and evolution time `t`. -/
noncomputable def phaseOfEnergy (t e : ℝ) : ℝ := -t * e / (2 * Real.pi)

/-- The squared norm of the phase estimation kernel at output label `z`. -/
noncomputable def qpeBornMass (M : ℕ) (φ : ℝ) (z : Fin M) : ℝ :=
  ‖qpeKernel M φ z‖ ^ 2

/-- The energy value assigned to a phase estimation label by the rescaling `-(2 * π / t) * (z /
M)`. -/
noncomputable def labelEnergy (t : ℝ) (M : ℕ) (z : Fin M) : ℝ :=
  -(2 * Real.pi / t) * ((z.val : ℝ) / (M : ℝ))

/-- The thermal acceptance factor computed from the energies assigned to the old and proposed
labels. -/
noncomputable def labelAcceptance (t : ℝ) (M : ℕ) (β : ℝ) (i z : Fin M) : ℝ :=
  thermalAcceptance (fun w => labelEnergy t M w) β i z

/-- The dyadic value obtained by taking the natural floor of `2 ^ k * f` and dividing by `2 ^
k`. -/
noncomputable def fairBitAcceptMass (k : ℕ) (f : ℝ) : ℝ :=
  (Nat.floor ((2 : ℝ) ^ k * f)) / (2 : ℝ) ^ k

/-- The continuous functional calculus of the phase estimation Born mass evaluated on `A`. -/
noncomputable def qpePovmElement {D : ℕ} (A : Operator D) (t : ℝ) (M : ℕ) (z : Fin M) :
    Operator D :=
  cfc (fun x : ℝ => qpeBornMass M (phaseOfEnergy t x) z) A

/-- The continuous functional calculus of the square root of the phase estimation Born mass
evaluated on `A`. -/
noncomputable def qpeKraus {D : ℕ} (A : Operator D) (t : ℝ) (M : ℕ) (z : Fin M) :
    Operator D :=
  cfc (fun x : ℝ => Real.sqrt (qpeBornMass M (phaseOfEnergy t x) z)) A

/-- The computational basis projector indexed by the Boolean coin outcome. -/
noncomputable def coinProjector (b : Bool) : Operator 2 :=
  ketbra (Ket (if b then 1 else 0)) (Ket (if b then 1 else 0))

/-- The dyadic acceptance mass for a true outcome and its complement for a false outcome. -/
noncomputable def unknownHBranchMass (t : ℝ) (M : ℕ) (β : ℝ) (k : ℕ)
    (old z : Fin M) (b : Bool) : ℝ :=
  if b then fairBitAcceptMass k (labelAcceptance t M β old z)
    else 1 - fairBitAcceptMass k (labelAcceptance t M β old z)

/-- The unnormalized system and coin branch formed from the phase readout Kraus expression, the
coin projector, and the branch mass. -/
noncomputable def unknownHBranch {D : ℕ} (A : Operator D) (t : ℝ) (M : ℕ) (β : ℝ) (k : ℕ)
    (old z : Fin M) (b : Bool) (ρ : Operator D) : Operator (D * 2) :=
  (unknownHBranchMass t M β k old z b) •
    (TensorGate (qpeKraus A t M z * ρ * (qpeKraus A t M z)ᴴ) (coinProjector b)).submatrix
      (finProdFinEquiv.symm) (finProdFinEquiv.symm)

/-- The branch mass multiplied by the real trace of the phase readout effect against the input
operator. -/
noncomputable def unknownHJointProb {D : ℕ} (A : Operator D) (t : ℝ) (M : ℕ) (β : ℝ) (k : ℕ)
    (old z : Fin M) (b : Bool) (ρ : Operator D) : ℝ :=
  unknownHBranchMass t M β k old z b * (Matrix.trace (qpePovmElement A t M z * ρ)).re

/-- The sum of diagonal input weights in the supplied vectors, each multiplied by the phase
estimation mass of its supplied energy. -/
noncomputable def unknownHEigenProb {D : ℕ} (A : Operator D) (t : ℝ) (M : ℕ)
    (ψ : Fin D → QState (Fin D)) (eig : Fin D → ℝ) (ρ : Operator D) (z : Fin M) : ℝ :=
  ∑ i, (Inner (ψ i) (ρ *ᵥ ψ i)).re * qpeBornMass M (phaseOfEnergy t (eig i)) z

/-- States that `i` is the least index among those with energy `E i`. -/
def isEnergyRep {D : ℕ} (E : Fin D → ℝ) (i : Fin D) : Prop :=
  ¬ ∃ j : Fin D, E j = E i ∧ j.val < i.val

/-- The sum of rank one operators associated with supplied vectors having the same energy as
index `i`. -/
noncomputable def energyPi {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D)) (i : Fin D) :
    Operator D :=
  ∑ j ∈ Finset.univ.filter (fun j => E j = E i), ketbra (ψ j) (ψ j)

/-- A finite family of proposal operators with real weights. -/
structure ProposalEnsemble (D : ℕ) where
  count : ℕ
  weight : Fin count → ℝ
  gate : Fin count → Operator D

/-- Requires nonnegative proposal weights summing to one and unitary proposal operators. -/
def proposalEnsembleLegal {D : ℕ} (ens : ProposalEnsemble D) : Prop :=
  (∀ j, 0 ≤ ens.weight j) ∧ (∑ j, ens.weight j = 1) ∧
    (∀ j, ens.gate j ∈ Matrix.unitaryGroup (Fin D) ℂ)

/-- Requires every proposal to have a conjugate transpose proposal with the same weight. -/
def proposalSymmetric {D : ℕ} (ens : ProposalEnsemble D) : Prop :=
  ∀ j, ∃ i, ens.weight i = ens.weight j ∧ ens.gate i = (ens.gate j)ᴴ

/-- Requires every proposal weight to be strictly positive. -/
def proposalPositive {D : ℕ} (ens : ProposalEnsemble D) : Prop :=
  ∀ j, 0 < ens.weight j

/-- The coin outcome projector conjugated by the Metropolis coin rotation for the selected pair
of energies. -/
noncomputable def temmeR {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (s : Bool) (i j : Fin D) :
    Operator 2 :=
  (MetropolisCoin (thermalAcceptance E β i j))ᴴ * coinProjector s *
    MetropolisCoin (thermalAcceptance E β i j)

/-- Reads a one based coin history position when it lies between one and `n`, and returns false
otherwise. -/
def temmeCoinAt {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (n : ℕ) (s : Fin n → Bool) (m : ℕ) : Bool :=
  if h : 0 < m ∧ m ≤ n then s ⟨m - 1, by omega⟩ else false

/-- The list of coin operators along the right energy history followed by those along the
reversed left history. -/
noncomputable def temmeGWord {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (i : Fin D) (n : ℕ)
    (s : Fin n → Bool) (l r : Fin (n + 1) → Fin D) : List (Operator 2) :=
  (List.finRange (n + 1)).map
      (fun m => temmeR E β (temmeCoinAt E β n s m.val) i (r m)) ++
    (List.finRange (n + 1)).reverse.map
      (fun m => temmeR E β (temmeCoinAt E β n s m.val) i (l m))

/-- The zero basis matrix coefficient of the product of the coin history word. -/
noncomputable def temmeG {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (i : Fin D) (n : ℕ)
    (s : Fin n → Bool) (l r : Fin (n + 1) → Fin D) : ℂ :=
  ((temmeGWord E β i n s l r).prod *ᵥ Ket 0) 0

/-- The recursive operator product along an energy history, with complementary initial energy
projections inserted after the first step. -/
noncomputable def temmeDInner {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (C : Operator D) (i : Fin D) : (m : ℕ) → (l : Fin m → Fin D) → Operator D
  | 0, _ => energyPi E ψ i
  | 1, l => Cᴴ * energyPi E ψ (l ⟨0, by omega⟩) * C * energyPi E ψ i
  | m + 1, l =>
      Cᴴ * energyPi E ψ (l ⟨m, by omega⟩) * C * (1 - energyPi E ψ i) *
        temmeDInner E ψ C i m (fun j => l (Fin.castSucc j))

/-- The history product `temmeDInner` with a final projection onto the initial energy sector. -/
noncomputable def temmeD {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (C : Operator D) (i : Fin D) (n : ℕ) (l : Fin (n + 1) → Fin D) : Operator D :=
  energyPi E ψ i * temmeDInner E ψ C i (n + 1) l

/-- The proposal weighted accepted transition sum over representative energy sectors, using
thermal acceptance factors [TemmeEtAl2011]. -/
noncomputable def temmeAcceptMap {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (ens : ProposalEnsemble D) (β : ℝ) (ρ : Operator D) : Operator D :=
  ∑ i, ∑ j, ∑ c,
    ((if isEnergyRep E i ∧ isEnergyRep E j then (1 : ℝ) else 0) *
        ens.weight c * thermalAcceptance E β i j) •
      (energyPi E ψ j * ens.gate c * energyPi E ψ i * ρ * energyPi E ψ i *
        (ens.gate c)ᴴ * energyPi E ψ j)

/-- The rejection history expression for a fixed proposal, history length, and Boolean coin
history. -/
noncomputable def temmeBnMap {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (C : Operator D) (β : ℝ) (n : ℕ) (s : Fin n → Bool) (ρ : Operator D) : Operator D :=
  ∑ i, ∑ l, ∑ r,
    (if isEnergyRep E i ∧ (∀ j, isEnergyRep E (l j)) ∧ (∀ j, isEnergyRep E (r j))
      then temmeG E β i n s l r else 0) •
      (temmeD E ψ C i n l * ρ * (temmeD E ψ C i n r)ᴴ)

/-- The infinite sum of rejection history expressions over lengths, proposals, and Boolean
histories. -/
noncomputable def temmeBtotal {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (ens : ProposalEnsemble D) (β : ℝ) (ρ : Operator D) : Operator D :=
  ∑' n : ℕ, ∑ c, ∑ s : Fin n → Bool,
    (ens.weight c) • temmeBnMap E ψ (ens.gate c) β n s ρ

/-- The sum of the accepted transition expression and the total rejection history expression
[TemmeEtAl2011]. -/
noncomputable def temmeMapFun {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (ens : ProposalEnsemble D) (β : ℝ) (ρ : Operator D) : Operator D :=
  temmeAcceptMap E ψ ens β ρ + temmeBtotal E ψ ens β ρ

/-- The Gibbs operator formed from the supplied vectors and the normalized diagonal Gibbs
distribution. -/
noncomputable def temmeGibbsState (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (ψ : Fin D → QState (Fin D)) : Operator D :=
  gibbsBasis ψ (diagonalGibbsDist D hD E β).prob

/-- The real diagonal matrix coefficients of the Metropolis map applied to the supplied rank one
input operators. -/
noncomputable def temmeStepMatrix {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (ens : ProposalEnsemble D) (β : ℝ) : Fin D → Fin D → ℝ :=
  fun i j => (Inner (ψ j) (temmeMapFun E ψ ens β (ketbra (ψ i) (ψ i)) *ᵥ ψ j)).re

/-- Requires products of proposal operators to approximate every unitary arbitrarily well in
matrix norm. -/
def denseGenerated {D : ℕ} (ens : ProposalEnsemble D) : Prop :=
  ∀ V : Operator D, V ∈ Matrix.unitaryGroup (Fin D) ℂ →
    ∀ ε : ℝ, 0 < ε → ∃ l : List (Fin ens.count), ‖(l.map ens.gate).prod - V‖ ≤ ε

/-- The two level energy function taking values zero and one. -/
def instanceEnergy : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1

/-- The computational basis vectors for the two dimensional example. -/
def instanceBasis : Fin 2 → QState (Fin 2) := fun i => Ket i

/-- The normalized sum of Pauli X and Pauli Z used as the example proposal. -/
noncomputable def instanceProposal : Operator 2 :=
  (Real.sqrt 2)⁻¹ • (!![(0 : ℂ), 1; 1, 0] + !![(1 : ℂ), 0; 0, -1])

/-- The singleton proposal ensemble assigning weight one to `instanceProposal`. -/
noncomputable def instanceEnsemble : ProposalEnsemble 2 where
  count := 1
  weight := fun _ => 1
  gate := fun _ => instanceProposal

/-- The example parameter `1 - (1 + exp (-1)) / 2`. -/
noncomputable def instanceEta : ℝ := 1 - (1 + Real.exp (-1)) / 2

/-- Half the sum of absolute differences of two real functions on a finite type. -/
noncomputable def tvDistance {I : Type} [Fintype I] (μ ν : I → ℝ) : ℝ :=
  (∑ x, |μ x - ν x|) / 2

/-- Iterates a finite kernel by matrix multiplication, starting with the identity kernel. -/
noncomputable def kernelPower {I : Type} [Fintype I] (P : I → I → ℝ) :
    ℕ → I → I → ℝ
  | 0, x, y => if x = y then 1 else 0
  | m + 1, x, y => ∑ z, kernelPower P m x z * P z y

/-- Requires squared weighted norm contraction by `(1 - Δ) ^ 2` on functions with zero weighted
mean. -/
def variationalGapPremise {I : Type} [Fintype I] (P : I → I → ℝ) (π : I → ℝ) (Δ : ℝ) : Prop :=
  ∀ f : I → ℝ, (∑ x, π x * f x = 0) →
    ∑ x, π x * (∑ y, P x y * f y) ^ 2 ≤ (1 - Δ) ^ 2 * ∑ x, π x * (f x) ^ 2

/-- The query count expression `(M - 1) * 27 * (4 * n + 1)` for a phase estimation window. -/
def qpeWindowQueries (M n : ℕ) : ℕ := (M - 1) * 27 * (4 * n + 1)

/-- The elementary gate count expression for the specified phase estimation window. -/
def qpeWindowGates (M n : ℕ) : ℕ :=
  2 * (M - 1) + 2 + (M - 1) * (27 * (4 * n + 6) + 79)

/-- Resource counts for preparation queries, step queries, step gates, classical bits, and
workspace qubits. -/
structure MetropolisCostLedger where
  prepQueries : ℕ
  stepQueries : ℕ
  stepGates : ℕ
  stepBits : ℕ
  spaceQubits : ℕ

/-- The resource ledger for one Metropolis step with the specified phase window, precision, and
rejection cutoff. -/
def metropolisStepLedger (D M k n nStar : ℕ) : MetropolisCostLedger where
  prepQueries := qpeWindowQueries M n
  stepQueries := (2 + nStar) * qpeWindowQueries M n
  stepGates := (2 + nStar) * qpeWindowGates M n
  stepBits := k + 1 + Nat.clog 2 M * (nStar + 1)
  spaceQubits := D + 2 * Nat.clog 2 M + 1 + k

/-- The repeated step ledger, multiplying step query, gate, and bit costs by `m` while retaining
the preparation and space counts. -/
def metropolisRunLedger (m D M k n nStar : ℕ) : MetropolisCostLedger where
  prepQueries := qpeWindowQueries M n
  stepQueries := m * ((2 + nStar) * qpeWindowQueries M n)
  stepGates := m * ((2 + nStar) * qpeWindowGates M n)
  stepBits := m * (k + 1 + Nat.clog 2 M * (nStar + 1))
  spaceQubits := D + 2 * Nat.clog 2 M + 1 + k

/-- The rational value `Nat.floor (2 ^ k * x) / 2 ^ k`; the use of natural floor truncates
negative inputs to zero. -/
noncomputable def dyadicRat (k : ℕ) (x : ℝ) : ℚ :=
  ((Nat.floor ((2 : ℝ) ^ k * x) : ℤ) : ℚ) / ((2 ^ k : ℕ) : ℚ)

/-- The expression `2 * N ^ 2 * β * δ * exp (2 * β * R)` used for Gibbs distribution
perturbation estimates. -/
noncomputable def gibbsL1ShiftBound (N : ℕ) (β δ R : ℝ) : ℝ :=
  2 * (N : ℝ) ^ 2 * β * δ * Real.exp (2 * β * R)

/-- The tail bound expression `1 / (2 * exp 1 * (n + 1))`. -/
noncomputable def sharpTailBound (n : ℕ) : ℝ :=
  1 / (2 * Real.exp 1 * ((n : ℝ) + 1))

/-- The rank one projector onto the zero computational basis vector. -/
noncomputable def twoProjectorP : Operator 2 :=
  ketbra (Ket 0) (Ket 0)

/-- The rank one operator generated by the vector with components `sqrt d` and `sqrt (1 - d)`. -/
noncomputable def twoProjectorQ (d : ℝ) : Operator 2 :=
  ketbra (fun i => if i = 0 then Complex.ofReal (Real.sqrt d)
      else Complex.ofReal (Real.sqrt (1 - d)))
    (fun i => if i = 0 then Complex.ofReal (Real.sqrt d)
      else Complex.ofReal (Real.sqrt (1 - d)))

/-- The zero computational basis vector used in the two projector example. -/
def twoProjectorPsi : QState (Fin 2) := Ket 0

end Qatlib.Concepts.RiskEstimation.PopulationGap
