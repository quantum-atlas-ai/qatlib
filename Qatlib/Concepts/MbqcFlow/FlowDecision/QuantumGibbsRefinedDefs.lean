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

/-!
# Phase readout and quantum Metropolis data

Defines finite phase grids, rounded energy labels, Hamiltonian evolution oracles, and the
controlled-power readout operators `qpeCircuit` and `qpeKraus`. It also introduces Gibbs
weights, finite-kernel minorization data, proposal unitaries, projective labels, and weighted
acceptance and rejection Kraus operators.

The structures `QpeCostLedger` and `MetropolisStepLedger` record resource parameters for these
constructions. The quantum Metropolis setting is described in [TemmeEtAl2011].

## Main statements

* `phaseIndex_round_error`: the rounded phase index differs by at most one half.
* `metropolisAcceptWeight_mem`: acceptance weights lie between zero and one for nonnegative
  inverse temperature.
* `metropolisJointKraus`: the labeled acceptance and rejection operators.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

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

/-- A finite phase grid specified by a strictly positive number of levels. -/
structure PhaseGrid where

  levels : ℕ

  levelsPos : 0 < levels

/-- The real phase-grid index `-(t * E * G.levels) / (2 * pi)` associated with time `t` and
energy `E`. -/
noncomputable def phaseIndexReal (G : PhaseGrid) (t E : ℝ) : ℝ :=
  -(t * E * (G.levels : ℝ)) / (2 * Real.pi)

/-- The integer phase index obtained by taking the floor of the real phase index plus one half. -/
noncomputable def phaseIndex (G : PhaseGrid) (t E : ℝ) : ℤ :=
  ⌊phaseIndexReal G t E + 1 / 2⌋

/-- The rounded phase index reduced modulo the number of grid levels. -/
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

/-- The rounded integer phase index differs from the real phase index by at most one half. -/
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

/-- A Hermitian Hamiltonian, a positive evolution time, and a unitary whose action on every
Hamiltonian eigenvector is the corresponding exponential phase. -/
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

/-- The product of the phase-label register and the `D`-dimensional system basis. -/
abbrev QpeSpace (G : PhaseGrid) (D : ℕ) : Type := Fin G.levels × Fin D

/-- The diagonal projection onto the phase-register basis label `j`. -/
noncomputable def registerProjector (G : PhaseGrid) (j : Fin G.levels) :
    Operator G.levels :=
  Matrix.diagonal (fun a => if a = j then (1 : ℂ) else 0)

/-- The controlled powers of the evolution operator followed by the inverse Fourier transform on
the phase register. -/
noncomputable def qpeCircuit {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) :
    Matrix (QpeSpace G D) (QpeSpace G D) ℂ :=
  TensorGate (QFTMatrix G.levels)ᴴ (1 : Operator D) * ControlledPowers O.evolution G.levels

/-- The joint-space operators obtained by projecting the phase register onto each label after
`qpeCircuit`. -/
noncomputable def qpeKraus {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) :
    Fin G.levels → Matrix (QpeSpace G D) (QpeSpace G D) ℂ :=
  fun j => TensorGate (registerProjector G j) (1 : Operator D) * qpeCircuit O G

/-- The `i`th vector in the orthonormal eigenvector basis chosen for the oracle Hamiltonian. -/
noncomputable def energyEigenvector {D : ℕ} (O : EnergyOracle D) (i : Fin D) :
    QState (Fin D) :=
  ⇑ (O.hamHermitian.eigenvectorBasis i)

/-- The real Hamiltonian eigenvalue at index `i`. -/
noncomputable def energyLevel {D : ℕ} (O : EnergyOracle D) (i : Fin D) : ℝ :=
  O.hamHermitian.eigenvalues i

/-- The chosen energy eigenvector satisfies the Hamiltonian eigenvalue equation with
`energyLevel O i`. -/
theorem energyEigenvector_spec {D : ℕ} (O : EnergyOracle D) (i : Fin D) :
    O.ham *ᵥ energyEigenvector O i = (energyLevel O i : ℂ) • energyEigenvector O i := by
  simpa [energyEigenvector, energyLevel] using O.hamHermitian.mulVec_eigenvectorBasis i

/-- The sum, over eigenvectors with energy `E`, of the diagonal parts of their outer-product
matrices. -/
noncomputable def energyProjector {D : ℕ} (O : EnergyOracle D) (E : ℝ) : Operator D :=
  ∑ i : Fin D, if energyLevel O i = E then
      Matrix.of fun a b =>
        if a = b then
          (energyEigenvector O i a) * (starRingEnd ℂ) (energyEigenvector O i b)
        else 0
    else 0

/-- Assigns each Hamiltonian eigenvalue its rounded phase-grid label at the oracle's evolution
time. -/
noncomputable def energyLabelMap {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) :
    Fin D → Fin G.levels :=
  fun i => energyLabel G O.time (energyLevel O i)

/-- The Metropolis weight, equal to one for `E' ≤ E` and to `exp (-(β * (E' - E)))` otherwise. -/
noncomputable def metropolisAcceptWeight (β E E' : ℝ) : ℝ :=
  if E' ≤ E then 1 else Real.exp (-(β * (E' - E)))

/-- For nonnegative `β`, the Metropolis acceptance weight lies in the interval from zero to one. -/
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

/-- A nonincreasing energy proposal has Metropolis acceptance weight one. -/
theorem metropolisAcceptWeight_one (β E E' : ℝ) (h : E' ≤ E) :
    metropolisAcceptWeight β E E' = 1 := by
  unfold metropolisAcceptWeight
  rw [if_pos h]

/-- A strictly increasing energy proposal has acceptance weight `exp (-(β * (E' - E)))`. -/
theorem metropolisAcceptWeight_exp (β E E' : ℝ) (h : E < E') :
    metropolisAcceptWeight β E E' = Real.exp (-(β * (E' - E))) := by
  unfold metropolisAcceptWeight
  rw [if_neg (not_le_of_gt h)]

/-- A probability vector on `Fin M` together with a strictly positive minorization parameter. -/
structure DoeblinData (M : ℕ) where

  nu : Fin M → ℝ

  nuSum : (∑ j, nu j) = 1

  nuNonneg : ∀ j, 0 ≤ nu j

  epsilon : ℝ

  epsilonPos : 0 < epsilon

/-- The Gibbs-density expression for the oracle Hamiltonian at inverse temperature `β`. -/
noncomputable def gibbsState {D : ℕ} (O : EnergyOracle D) (β : ℝ) : Operator D :=
  Qatlib.Concepts.LindbladFlow.GkslSemigroup.gibbsDensity O.ham β

/-- The unnormalized Gibbs weight `exp (-(β * E))`. -/
noncomputable def gibbsWeight (β E : ℝ) : ℝ :=
  Real.exp (-(β * E))

/-- A record of phase levels, controlled-power and inverse-Fourier gate counts, and the
controlled-system size parameter. -/
structure QpeCostLedger where

  levels : ℕ

  controlledPowers : ℕ

  inverseQftGates : ℕ

  controlledSystemQubits : ℕ

/-- The phase-estimation ledger assigning the grid level count to the levels and both
operation-count fields, and `D` to the controlled-system field. -/
noncomputable def qpeCostLedger {D : ℕ} (_O : EnergyOracle D) (G : PhaseGrid) :
    QpeCostLedger :=
  { levels := G.levels
    controlledPowers := G.levels
    inverseQftGates := G.levels
    controlledSystemQubits := D }

/-- The finite kernel with entry `accept k * propose k j` at indices `j` and `k`. -/
noncomputable def labelChain (M : ℕ) (accept : Fin M → ℝ) (propose : Fin M → Fin M → ℝ) :
    Fin M → Fin M → ℝ :=
  fun j k => accept k * propose k j

/-- A probability vector and a parameter strictly between zero and one whose product gives an
entrywise lower bound on the finite kernel. -/
structure ChainMinorization (M : ℕ) (T : Fin M → Fin M → ℝ) where

  nu : Fin M → ℝ

  nuSum : (∑ k, nu k) = 1

  nuNonneg : ∀ k, 0 ≤ nu k

  epsilon : ℝ

  epsilonPos : 0 < epsilon

  epsilonLtOne : epsilon < 1

  minorize : ∀ j k, epsilon * nu k ≤ T j k

/-- The GKSL data with the oracle Hamiltonian and all jump operators equal to zero. -/
noncomputable def lindbladGenerator {D : ℕ} (O : EnergyOracle D) :
    Qatlib.Concepts.LindbladFlow.GkslSemigroup.GKSL D :=
  { ham := O.ham, hamHermitian := O.hamHermitian, jumps := fun _ => 0 }

/-- A unitary proposal operator and a unitary inverse satisfying both inverse multiplication
identities. -/
structure ProposalOracle (D : ℕ) where

  unitary : Operator D

  unitary_mem : unitary ∈ Matrix.unitaryGroup (Fin D) ℂ

  inverse : Operator D

  inverse_mem : inverse ∈ Matrix.unitaryGroup (Fin D) ℂ

  inverse_mul : inverse * unitary = 1

  inverse_mul' : unitary * inverse = 1

/-- A family of pairwise orthogonal Hermitian idempotents summing to the identity. -/
structure LabelProjectors (D M : ℕ) where

  proj : Fin M → Operator D

  hermitian : ∀ j, (proj j)ᴴ = proj j

  idempotent : ∀ j, proj j * proj j = proj j

  orthogonality : ∀ j k, j ≠ k → proj j * proj k = 0

  total : (∑ j, proj j) = 1

/-- A family of real acceptance weights between zero and one. -/
structure AcceptWeights (M : ℕ) where

  weight : Fin M → ℝ

  nonneg : ∀ j, 0 ≤ weight j

  le_one : ∀ j, weight j ≤ 1

/-- The complex embedding of the real square root of an acceptance weight. -/
noncomputable def acceptScale (w : ℝ) : ℂ := (Real.sqrt w : ℂ)

/-- For a nonnegative weight, the square of its acceptance scale equals its complex embedding. -/
theorem acceptScale_sq {w : ℝ} (hw : 0 ≤ w) :
    acceptScale w * acceptScale w = (w : ℂ) := by
  have h : (Real.sqrt w : ℝ) * (Real.sqrt w : ℝ) = w := Real.mul_self_sqrt hw
  unfold acceptScale
  rw [← Complex.ofReal_mul, h]

/-- The acceptance scale is fixed by complex conjugation. -/
theorem acceptScale_star (w : ℝ) : star (acceptScale w) = acceptScale w := by
  simp [acceptScale, Complex.conj_ofReal]

/-- For `w ≤ 1`, the square of the complementary acceptance scale equals `1 - (w : ℂ)`. -/
theorem acceptScale_sq_sub {w : ℝ} (hw : w ≤ 1) :
    acceptScale (1 - w) * acceptScale (1 - w) = 1 - (w : ℂ) := by
  rw [acceptScale_sq (by linarith)]
  exact Complex.ofReal_sub 1 w

/-- The proposal followed by label projection, scaled by the square root of the label's
acceptance weight. -/
noncomputable def metropolisAcceptKraus {D M : ℕ} (P : LabelProjectors D M)
    (Q : ProposalOracle D) (α : AcceptWeights M) (j : Fin M) : Operator D :=
  acceptScale (α.weight j) • (P.proj j * Q.unitary)

/-- The proposal, label projection, and inverse proposal, scaled by the square root of the
complementary acceptance weight. -/
noncomputable def metropolisRejectKraus {D M : ℕ} (P : LabelProjectors D M)
    (Q : ProposalOracle D) (α : AcceptWeights M) (j : Fin M) : Operator D :=
  acceptScale (1 - α.weight j) • (Q.inverse * P.proj j * Q.unitary)

/-- Selects the acceptance operator for binary label zero and the rejection operator for binary
label one. -/
noncomputable def metropolisJointKraus {D M : ℕ} (P : LabelProjectors D M)
    (Q : ProposalOracle D) (α : AcceptWeights M) : Fin M × Fin 2 → Operator D :=
  fun jb =>
    if jb.2.val = 0 then metropolisAcceptKraus P Q α jb.1
    else metropolisRejectKraus P Q α jb.1

/-- The real trace of the label projector against the state conjugated by the proposal unitary. -/
noncomputable def proposalFidelity {D M : ℕ} (P : LabelProjectors D M)
    (Q : ProposalOracle D) (ρ : Operator D) (j : Fin M) : ℝ :=
  (Matrix.trace (P.proj j * (Q.unitary * ρ * Q.unitaryᴴ))).re

/-- A record of energy-readout, proposal, rewind, controlled-system, and classical-readout
resource counts. -/
structure MetropolisStepLedger where

  energyControlledPowers : ℕ

  energyInverseQftGates : ℕ

  proposalApplications : ℕ

  rewindApplications : ℕ

  controlledSystemQubits : ℕ

  classicalReadoutBits : ℕ

end StageAQUANTUMGIBBS
end Qatlib.Concepts.MbqcFlow.FlowDecision
