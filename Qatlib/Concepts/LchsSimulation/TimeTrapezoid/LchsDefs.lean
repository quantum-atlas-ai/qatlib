/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TimeTrapezoid.Inhom2DTrapezoidSourceQuadratureLine
import Qatlib.Concepts.LchsSimulation.TrapPrepared.InhomTrapPreparedSolutionLine
import Qatlib.Concepts.LchsSimulation.InteractHybrid.InteractionPictureLchsReprLine
import Qatlib.Concepts.LchsSimulation.StaticLchs.StaticLCHSConsumers
import Qatlib.Concepts.CoherentSim.TaylorEncoding.TaylorLCUProgram
import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorSimulation

/-!
# Loaded LCHS labels and resource quantities

The joint trapezoidal LCHS family combines homogeneous labels with parameter-and-source-time
labels using `lchs2dCoeff` and `lchs2dUnitary`. `LchsLoadedNode` stores sampled source data,
while `LchsWindowLedger` and `LchsTheoremResources` record access and space quantities. The
module also defines interaction-picture branches, Taylor-word resource counts, and finite
fair-bit proposal quantities.

The mathematical background is described in [AnLiuLin2023].

## Main statements

* `lchs2dUnitary`: defines the combined homogeneous and loaded-source matrix family.
* `lchs2dWindowLedger`: records the expanded-word resource quantities.
* `lchsHamTQueryCount`: counts queries in a Taylor LCU word.

## References

* [An et al., 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.InteractHybrid
open Qatlib.Concepts.LchsSimulation.KTrapezoid
open Qatlib.Concepts.LchsSimulation.TimeTrapezoid
open Qatlib.Concepts.LchsSimulation.TrapPrepared
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.CoherentSim.FactorialTaylor
open Qatlib.Concepts.CoherentSim.TaylorEncoding

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Concepts.LchsSimulation.TimeTrapezoid

open Qatlib
open Matrix
open SignalProcessing

section Clause1LoadedSchedule

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The total number `(M + 1) + (M + 1) * (Mt + 1)` of homogeneous and source labels in the
joint trapezoidal family. -/
def lchs2dLabelCount (M Mt : ℕ) : ℕ := (M + 1) + (M + 1) * (Mt + 1)

/-- The homogeneous coefficient at a parameter trapezoid node. -/
noncomputable def lchs2dHomogeneousCoeff (K M : ℕ) (j : Fin (M + 1)) : ℂ :=
  kTrapCoeff K M j

/-- The source coefficient given by the time trapezoid weight, parameter trapezoid coefficient,
and Euclidean norm of the sampled source. -/
noncomputable def lchs2dSourceCoeff (b : ℝ → QState I) (s t : ℝ) (K M Mt : ℕ)
    (p : Fin (M + 1) × Fin (Mt + 1)) : ℂ :=
  (inhTrapWeight Mt s t p.2 : ℂ) * kTrapCoeff K M p.1 *
    (‖toEuclidean_fromVec (b (inhTrapNode Mt s t p.2))‖ : ℂ)

/-- The combined coefficient family whose initial labels are homogeneous coefficients and
remaining labels encode parameter-and-source-time pairs. -/
noncomputable def lchs2dCoeff (b : ℝ → QState I) (s t : ℝ) (K M Mt : ℕ)
    (x : Fin (lchs2dLabelCount M Mt)) : ℂ :=
  if hx : (x : ℕ) < M + 1 then
    kTrapCoeff K M ⟨x.val, hx⟩
  else
    have hcnt : lchs2dLabelCount M Mt = (M + 1) + (M + 1) * (Mt + 1) := rfl
    let y : Fin ((M + 1) * (Mt + 1)) := ⟨x.val - (M + 1), by omega⟩
    let p : Fin (M + 1) × Fin (Mt + 1) := finProdFinEquiv.symm y
    lchs2dSourceCoeff b s t K M Mt p

/-- The combined matrix family using full-interval ordered Hamiltonian evolution on homogeneous
labels and source-time propagation composed with `P l * Bᴴ` on source labels. -/
noncomputable def lchs2dUnitary (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K M Mt : ℕ)
    (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ)
    (x : Fin (lchs2dLabelCount M Mt)) : Matrix I I ℂ :=
  if hx : (x : ℕ) < M + 1 then
    orderedEvolution
      (fun u => Complex.I • (H u + (kTrapNode K M ⟨x.val, hx⟩) • L u)) s t
  else
    have hcnt : lchs2dLabelCount M Mt = (M + 1) + (M + 1) * (Mt + 1) := rfl
    let y : Fin ((M + 1) * (Mt + 1)) := ⟨x.val - (M + 1), by omega⟩
    let p : Fin (M + 1) × Fin (Mt + 1) := finProdFinEquiv.symm y
    inh2dTrapSourceKUnitary L H s t K M Mt p.1 p.2 * (P p.2 * Bᴴ)

/-- The sum of the norms of the parameter trapezoid coefficients. -/
noncomputable def lchs2dKMass (K M : ℕ) : ℝ :=
  ∑ j : Fin (M + 1), ‖kTrapCoeff K M j‖

/-- The time-trapezoid-weighted sum of Euclidean norms of the sampled source vectors. -/
noncomputable def lchs2dSourceMass (b : ℝ → QState I) (s t : ℝ) (Mt : ℕ) : ℝ :=
  ∑ l : Fin (Mt + 1), inhTrapWeight Mt s t l *
    ‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖

/-- A sampled source node recording its natural index, real position, and source vector. -/
structure LchsLoadedNode (I : Type) where

  index : ℕ

  position : ℝ

  source : QState I

/-- The loaded source node with index `l`, position at its trapezoid time node, and source value
at that position. -/
noncomputable def lchsLoadedNode (b : ℝ → QState I) (s t : ℝ) (Mt : ℕ)
    (l : Fin (Mt + 1)) : LchsLoadedNode I :=
  { index := l.val
    position := inhTrapNode Mt s t l
    source := b (inhTrapNode Mt s t l) }

/-- The quantity `(M + 1) * (Mt + 1)` assigned to source preparation accesses in one selection. -/
def lchs2dSelectPrepareCount (M Mt : ℕ) : ℕ := (M + 1) * (Mt + 1)

/-- The number `Mt + 1` of source-time states in the trapezoidal family. -/
def lchs2dSourceStateCount (Mt : ℕ) : ℕ := Mt + 1

/-- The quantity `(M + 1) * (Mt + 1)` assigned to input-adjoint accesses in one selection. -/
def lchs2dSelectInputAdjointCount (M Mt : ℕ) : ℕ := (M + 1) * (Mt + 1)

/-- The number `(M + 1) * (Mt + 1)` of joint parameter-and-source-time labels. -/
def lchs2dSourceLabelCount (M Mt : ℕ) : ℕ := (M + 1) * (Mt + 1)

/-- A record of forward and backward input, selection, and coefficient accesses, marking
queries, source resources, and word length. -/
structure LchsWindowLedger where
  inputForward : ℕ
  inputBackward : ℕ
  selectForward : ℕ
  selectBackward : ℕ
  coefficientForward : ℕ
  coefficientBackward : ℕ
  markQueries : ℕ
  sourcePrepare : ℕ
  sourceInputAdjoint : ℕ
  sourceStates : ℕ
  wordLength : ℕ

/-- The resource record for `m` expanded amplification iterations, including source preparation
and input-adjoint counts for each forward selection and word length `10 * m + 4`. -/
noncomputable def lchs2dWindowLedger (M Mt m : ℕ) : LchsWindowLedger :=
  { inputForward := m + 1
    inputBackward := m
    selectForward := m + 1
    selectBackward := m
    coefficientForward := 2 * m + 1
    coefficientBackward := 2 * m + 1
    markQueries := m
    sourcePrepare := (m + 1) * lchs2dSelectPrepareCount M Mt
    sourceInputAdjoint := (m + 1) * lchs2dSelectInputAdjointCount M Mt
    sourceStates := lchs2dSourceStateCount Mt
    wordLength := 10 * m + 4 }

end Clause1LoadedSchedule

section Clause4Resources

/-- The fixed-gate quantity obtained by subtracting `k` marking queries from the expanded word
length `10 * k + 4`. -/
def lchsFixedGateCount (k : ℕ) : ℕ := 10 * k + 4 - k

/-- The register-bit quantity `Nat.log2 n + 1`. -/
def lchsRegisterBits (n : ℕ) : ℕ := Nat.log2 n + 1

/-- The quantum-space quantity `N * dataStates` for a label register paired with data states. -/
def lchsQuantumSpace (N : ℕ) (dataStates : ℕ) : ℕ := N * dataStates

/-- The sum of register-bit quantities for the label count, iteration window, and source-time
count. -/
def lchsClassicalBits (N m Mt : ℕ) : ℕ :=
  lchsRegisterBits N + lchsRegisterBits m + lchsRegisterBits (Mt + 1)

/-- A record of label count, iteration window, fixed gates, oracle queries, classical bits, and
quantum-space quantity. -/
structure LchsTheoremResources where

  labels : ℕ

  window : ℕ

  fixedGates : ℕ

  oracleQueries : ℕ

  classicalBits : ℕ

  quantumSpace : ℕ

/-- The theorem resource record assembled from label count `N`, window parameter `m`, source
subdivision count `Mt`, and data-state count. -/
noncomputable def lchsTheoremResources (N m Mt dataStates : ℕ) : LchsTheoremResources :=
  { labels := N
    window := m
    fixedGates := lchsFixedGateCount m
    oracleQueries := m
    classicalBits := lchsClassicalBits N m Mt
    quantumSpace := lchsQuantumSpace N dataStates }

end Clause4Resources

section Clause3CapAndSampling

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The interaction-picture branch formed by the constant `k • L` evolution followed by the
ordered interaction-generator evolution. -/
noncomputable def capBranchUnitary (L : Matrix I I ℂ) (H : ℝ → Matrix I I ℂ)
    (k t : ℝ) : Matrix I I ℂ :=
  HamiltonianEvolution (k • L) t *
    orderedEvolution (fun u => Complex.I • interactionGenerator (k • L) H u) 0 t

/-- The three-factor interaction-picture expression obtained by appending the inverse constant
`k • L` evolution to `capBranchUnitary`. -/
noncomputable def capPrintedThreeFactor (L : Matrix I I ℂ) (H : ℝ → Matrix I I ℂ)
    (k t : ℝ) : Matrix I I ℂ :=
  HamiltonianEvolution (k • L) t *
    orderedEvolution (fun u => Complex.I • interactionGenerator (k • L) H u) 0 t *
    HamiltonianEvolution (k • L) (-t)

/-- The loaded matrix family using `capBranchUnitary` on homogeneous labels and propagated
source-preparation matrices on source labels. -/
noncomputable def capLoadedUnitary (L : Matrix I I ℂ) (H : ℝ → Matrix I I ℂ)
    (s t : ℝ) (K M Mt : ℕ) (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ)
    (x : Fin (lchs2dLabelCount M Mt)) : Matrix I I ℂ :=
  if hx : (x : ℕ) < M + 1 then
    capBranchUnitary L H (kTrapNode K M ⟨x.val, hx⟩) t
  else
    have hcnt : lchs2dLabelCount M Mt = (M + 1) + (M + 1) * (Mt + 1) := rfl
    let y : Fin ((M + 1) * (Mt + 1)) := ⟨x.val - (M + 1), by omega⟩
    let p : Fin (M + 1) × Fin (Mt + 1) := finProdFinEquiv.symm y
    inh2dTrapSourceKUnitary (fun _ => L) H s t K M Mt p.1 p.2 * (P p.2 * Bᴴ)

/-- The per-sample query quantity `2 * (m - 1)`, with subtraction taken in the natural numbers. -/
def lchsHybridSampleMaxQueries (m : ℕ) : ℕ := 2 * (m - 1)

/-- The total query quantity `2 * (m - 1) * n` for `n` samples. -/
def lchsHybridTotalQueries (m n : ℕ) : ℕ := 2 * (m - 1) * n

/-- The constant fast-forward application count of one. -/
def capFastForwardApplications : ℕ := 1

/-- The first theorem resource record using `N` labels, window parameter `m`, and no source-time
subdivision parameter. -/
noncomputable def lchsTh1Resources (N m : ℕ) (dataStates : ℕ) : LchsTheoremResources :=
  { labels := N
    window := m
    fixedGates := lchsFixedGateCount m
    oracleQueries := m
    classicalBits := lchsClassicalBits N m 0
    quantumSpace := lchsQuantumSpace N dataStates }

/-- The second theorem resource record using the joint homogeneous-and-source label count. -/
noncomputable def lchsTh2Resources (M Mt m : ℕ) (dataStates : ℕ) : LchsTheoremResources :=
  lchsTheoremResources (lchs2dLabelCount M Mt) m Mt dataStates

/-- The third theorem resource record using joint labels and adding one fast-forward application
to the fixed-gate quantity. -/
noncomputable def lchsTh3Resources (M Mt m : ℕ) (dataStates : ℕ) : LchsTheoremResources :=
  { labels := lchs2dLabelCount M Mt
    window := m
    fixedGates := lchsFixedGateCount m + capFastForwardApplications
    oracleQueries := m
    classicalBits := lchsClassicalBits (lchs2dLabelCount M Mt) m Mt
    quantumSpace := lchsQuantumSpace (lchs2dLabelCount M Mt) dataStates }

end Clause3CapAndSampling

section Clause2HamT

/-- The adjoint-query count of the Taylor LCU word for the supplied coefficients, label, time,
and Taylor order. -/
noncomputable def lchsHamTQueryCount {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (h : J → ℝ) (j₀ : J) (τ : ℝ) (K : ℕ) : ℕ :=
  adjointQueryCount (taylorLCUWord (I := I) h j₀ τ K)

/-- The fixed-gate count of the Taylor LCU word for the supplied coefficients, label, time, and
Taylor order. -/
noncomputable def lchsHamTGateCount {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (h : J → ℝ) (j₀ : J) (τ : ℝ) (K : ℕ) : ℕ :=
  adjointGateCount (taylorLCUWord (I := I) h j₀ τ K)

/-- The native Hamiltonian-simulation Taylor order `factorialTaylorCutoff m`. -/
def lchsHamTNativeOrder (m : ℕ) : ℕ := factorialTaylorCutoff m

/-- The Taylor-word label count given by the sum of `Fintype.card J ^ l` for `l ≤ K`, plus two. -/
noncomputable def taylorWordLabelCount (J : Type) [Fintype J] (K : ℕ) : ℕ :=
  (∑ l : Fin (K + 1), (Fintype.card J) ^ l.val) + 2

/-- The register-bit quantity assigned to the Taylor-word label count. -/
def taylorAncillaBits (J : Type) [Fintype J] (K : ℕ) : ℕ :=
  lchsRegisterBits (taylorWordLabelCount J K)

/-- The phase-gate quantity defined to equal the Taylor-word label count. -/
noncomputable def taylorPhaseGateCount (J : Type) [Fintype J] (K : ℕ) : ℕ :=
  taylorWordLabelCount J K

/-- The label-access quantity `N` for a selection over `N` labels. -/
def lchsSelectLabelAccesses (N : ℕ) : ℕ := N

/-- The label-access quantity `(2 * m + 1) * N` for an amplification window parameter `m`. -/
def lchsWindowLabelAccesses (N m : ℕ) : ℕ := (2 * m + 1) * N

/-- The finite type `Fin (2 ^ m)` representing the possible values of an `m`-bit sample. -/
abbrev FairBitSample (m : ℕ) : Type := Fin (2 ^ m)

/-- The natural Taylor-order proposal obtained from the value of a finite bit sample. -/
def hamTOrderProposal (m : ℕ) (x : FairBitSample m) : ℕ := x.val

/-- The fraction of the `2 ^ m` finite samples accepted by the Boolean predicate. -/
noncomputable def hamTAcceptProb (m : ℕ) (accept : FairBitSample m → Bool) : ℝ :=
  ((Finset.univ : Finset (FairBitSample m)).filter (fun x => accept x = true)).card / (2 ^ m : ℝ)

/-- The count `(2 ^ m - a) ^ r` of length-`r` sequences drawn from a rejection set of size `2 ^
m - a`. -/
def hamTFailSeqCount (m r a : ℕ) : ℕ := (2 ^ m - a) ^ r

end Clause2HamT

end Qatlib.Concepts.LchsSimulation.TimeTrapezoid
