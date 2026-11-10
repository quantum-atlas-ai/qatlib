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

def lchs2dLabelCount (M Mt : ℕ) : ℕ := (M + 1) + (M + 1) * (Mt + 1)

noncomputable def lchs2dHomogeneousCoeff (K M : ℕ) (j : Fin (M + 1)) : ℂ :=
  kTrapCoeff K M j

noncomputable def lchs2dSourceCoeff (b : ℝ → QState I) (s t : ℝ) (K M Mt : ℕ)
    (p : Fin (M + 1) × Fin (Mt + 1)) : ℂ :=
  (inhTrapWeight Mt s t p.2 : ℂ) * kTrapCoeff K M p.1 *
    (‖toEuclidean_fromVec (b (inhTrapNode Mt s t p.2))‖ : ℂ)

noncomputable def lchs2dCoeff (b : ℝ → QState I) (s t : ℝ) (K M Mt : ℕ)
    (x : Fin (lchs2dLabelCount M Mt)) : ℂ :=
  if hx : (x : ℕ) < M + 1 then
    kTrapCoeff K M ⟨x.val, hx⟩
  else
    have hcnt : lchs2dLabelCount M Mt = (M + 1) + (M + 1) * (Mt + 1) := rfl
    let y : Fin ((M + 1) * (Mt + 1)) := ⟨x.val - (M + 1), by omega⟩
    let p : Fin (M + 1) × Fin (Mt + 1) := finProdFinEquiv.symm y
    lchs2dSourceCoeff b s t K M Mt p

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

noncomputable def lchs2dKMass (K M : ℕ) : ℝ :=
  ∑ j : Fin (M + 1), ‖kTrapCoeff K M j‖

noncomputable def lchs2dSourceMass (b : ℝ → QState I) (s t : ℝ) (Mt : ℕ) : ℝ :=
  ∑ l : Fin (Mt + 1), inhTrapWeight Mt s t l *
    ‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖

structure LchsLoadedNode (I : Type) where

  index : ℕ

  position : ℝ

  source : QState I

noncomputable def lchsLoadedNode (b : ℝ → QState I) (s t : ℝ) (Mt : ℕ)
    (l : Fin (Mt + 1)) : LchsLoadedNode I :=
  { index := l.val
    position := inhTrapNode Mt s t l
    source := b (inhTrapNode Mt s t l) }

def lchs2dSelectPrepareCount (M Mt : ℕ) : ℕ := (M + 1) * (Mt + 1)

def lchs2dSourceStateCount (Mt : ℕ) : ℕ := Mt + 1

def lchs2dSelectInputAdjointCount (M Mt : ℕ) : ℕ := (M + 1) * (Mt + 1)

def lchs2dSourceLabelCount (M Mt : ℕ) : ℕ := (M + 1) * (Mt + 1)

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

def lchsFixedGateCount (k : ℕ) : ℕ := 10 * k + 4 - k

def lchsRegisterBits (n : ℕ) : ℕ := Nat.log2 n + 1

def lchsQuantumSpace (N : ℕ) (dataStates : ℕ) : ℕ := N * dataStates

def lchsClassicalBits (N m Mt : ℕ) : ℕ :=
  lchsRegisterBits N + lchsRegisterBits m + lchsRegisterBits (Mt + 1)

structure LchsTheoremResources where

  labels : ℕ

  window : ℕ

  fixedGates : ℕ

  oracleQueries : ℕ

  classicalBits : ℕ

  quantumSpace : ℕ

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

noncomputable def capBranchUnitary (L : Matrix I I ℂ) (H : ℝ → Matrix I I ℂ)
    (k t : ℝ) : Matrix I I ℂ :=
  HamiltonianEvolution (k • L) t *
    orderedEvolution (fun u => Complex.I • interactionGenerator (k • L) H u) 0 t

noncomputable def capPrintedThreeFactor (L : Matrix I I ℂ) (H : ℝ → Matrix I I ℂ)
    (k t : ℝ) : Matrix I I ℂ :=
  HamiltonianEvolution (k • L) t *
    orderedEvolution (fun u => Complex.I • interactionGenerator (k • L) H u) 0 t *
    HamiltonianEvolution (k • L) (-t)

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

def lchsHybridSampleMaxQueries (m : ℕ) : ℕ := 2 * (m - 1)

def lchsHybridTotalQueries (m n : ℕ) : ℕ := 2 * (m - 1) * n

def capFastForwardApplications : ℕ := 1

noncomputable def lchsTh1Resources (N m : ℕ) (dataStates : ℕ) : LchsTheoremResources :=
  { labels := N
    window := m
    fixedGates := lchsFixedGateCount m
    oracleQueries := m
    classicalBits := lchsClassicalBits N m 0
    quantumSpace := lchsQuantumSpace N dataStates }

noncomputable def lchsTh2Resources (M Mt m : ℕ) (dataStates : ℕ) : LchsTheoremResources :=
  lchsTheoremResources (lchs2dLabelCount M Mt) m Mt dataStates

noncomputable def lchsTh3Resources (M Mt m : ℕ) (dataStates : ℕ) : LchsTheoremResources :=
  { labels := lchs2dLabelCount M Mt
    window := m
    fixedGates := lchsFixedGateCount m + capFastForwardApplications
    oracleQueries := m
    classicalBits := lchsClassicalBits (lchs2dLabelCount M Mt) m Mt
    quantumSpace := lchsQuantumSpace (lchs2dLabelCount M Mt) dataStates }

end Clause3CapAndSampling

section Clause2HamT

noncomputable def lchsHamTQueryCount {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (h : J → ℝ) (j₀ : J) (τ : ℝ) (K : ℕ) : ℕ :=
  adjointQueryCount (taylorLCUWord (I := I) h j₀ τ K)

noncomputable def lchsHamTGateCount {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (h : J → ℝ) (j₀ : J) (τ : ℝ) (K : ℕ) : ℕ :=
  adjointGateCount (taylorLCUWord (I := I) h j₀ τ K)

def lchsHamTNativeOrder (m : ℕ) : ℕ := factorialTaylorCutoff m

noncomputable def taylorWordLabelCount (J : Type) [Fintype J] (K : ℕ) : ℕ :=
  (∑ l : Fin (K + 1), (Fintype.card J) ^ l.val) + 2

def taylorAncillaBits (J : Type) [Fintype J] (K : ℕ) : ℕ :=
  lchsRegisterBits (taylorWordLabelCount J K)

noncomputable def taylorPhaseGateCount (J : Type) [Fintype J] (K : ℕ) : ℕ :=
  taylorWordLabelCount J K

def lchsSelectLabelAccesses (N : ℕ) : ℕ := N

def lchsWindowLabelAccesses (N m : ℕ) : ℕ := (2 * m + 1) * N

abbrev FairBitSample (m : ℕ) : Type := Fin (2 ^ m)

def hamTOrderProposal (m : ℕ) (x : FairBitSample m) : ℕ := x.val

noncomputable def hamTAcceptProb (m : ℕ) (accept : FairBitSample m → Bool) : ℝ :=
  ((Finset.univ : Finset (FairBitSample m)).filter (fun x => accept x = true)).card / (2 ^ m : ℝ)

def hamTFailSeqCount (m r a : ℕ) : ℕ := (2 ^ m - a) ^ r

end Clause2HamT

end Qatlib.Concepts.LchsSimulation.TimeTrapezoid
