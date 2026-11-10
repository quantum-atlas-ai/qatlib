/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.WorkspaceCP.WorkspaceWord
import Qatlib.Papers.QCounting98.MainResults.ActualCounting.GridCapacity
import Mathlib.Logic.Equiv.Fin.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QCounting98.MainResults.ActualCounting
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.PureStateMath.BornBridge (relabelGate relabelState normalized_relabelState)
open Qatlib.Concepts.Execution.WorkspaceCP

def countingDataLabels (N : ℕ) : (Fin N × Bool) ≃ Fin (N*2) :=
  (Equiv.prodCongr (Equiv.refl (Fin N)) boolEquivFin2).trans finProdFinEquiv

def countingFlatLabels (N M : ℕ) : ((Fin N × Bool) × Fin M) ≃ Fin ((N*2)*M) :=
  (Equiv.prodCongr (countingDataLabels N) (Equiv.refl (Fin M))).trans finProdFinEquiv

theorem countingFlat_oracle (N M : ℕ) (F : Fin N → Bool) :
    relabelGate (countingFlatLabels N M) (workspaceBitOracle F) =
      forwardWorkspaceOracle M (relabelGate (countingDataLabels N) (BitOracleOn F)) := by
  rfl

def countingBinaryData (n : ℕ) : Fin (2^n*2) ≃ Reg (n+1) :=
  (countingDataLabels (2^n)).symm.trans
    ((Equiv.prodCongr (bitVecEquiv n).symm (Equiv.refl Bool)).trans (regSuccEquiv n).symm)

def countingRegisterLabels (n : ℕ) : Fin ((2^n*2)*2^(n+9)) ≃ Reg ((n+1)+(n+9)) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodCongr (countingBinaryData n) (bitVecEquiv (n+9)).symm).trans
      (Fin.appendEquiv (α := Bool) (n+1) (n+9)))

def registerCountingWord (n M : ℕ) (hM : M ≤ 2^(n+9))
    (C : Circuit ((Fin (2^n) × Bool) × Fin M)) : Circuit (Reg ((n+1)+(n+9))) :=
  relabelCircuit (countingRegisterLabels n)
    (workspaceWord hM (relabelCircuit (countingFlatLabels (2^n) M) C))

def registerCountingInput (n M : ℕ) (hM : M ≤ 2^(n+9))
    (psi : QState ((Fin (2^n) × Bool) × Fin M)) : QState (Reg ((n+1)+(n+9))) :=
  relabelState (countingRegisterLabels n)
    (workspaceEmbedding hM *ᵥ relabelState (countingFlatLabels (2^n) M) psi)

def registerCountingOracle (n : ℕ) (F : Fin (2^n) → Bool) :
    Matrix (Reg ((n+1)+(n+9))) (Reg ((n+1)+(n+9))) ℂ :=
  relabelGate (countingRegisterLabels n)
    (forwardWorkspaceOracle (2^(n+9)) (relabelGate (countingDataLabels (2^n)) (BitOracleOn F)))

def registerCountingEvent (n M : ℕ) (hM : M ≤ 2^(n+9))
    (S : Finset ((Fin (2^n) × Bool) × Fin M)) : Finset (Reg ((n+1)+(n+9))) :=
  (((S.map (countingFlatLabels (2^n) M).toEmbedding).map (workspaceBasis hM)).map
    (countingRegisterLabels n).toEmbedding)

theorem registerCounting_run (n M : ℕ) (hM : M ≤ 2^(n+9)) (F : Fin (2^n) → Bool)
    (C : Circuit ((Fin (2^n) × Bool) × Fin M)) (psi : QState ((Fin (2^n) × Bool) × Fin M)) :
    Run (registerCountingOracle n F) (registerCountingWord n M hM C) (registerCountingInput n M hM psi) =
      registerCountingInput n M hM (Run (workspaceBitOracle F) C psi) := by
  unfold registerCountingOracle registerCountingWord registerCountingInput
  rw [(run_relabelCircuit_readout _ _ _ _ ∅).1,workspaceWord_run,← countingFlat_oracle,
    (run_relabelCircuit_readout _ _ _ _ ∅).1]

theorem registerCounting_readout (n M : ℕ) (hM : M ≤ 2^(n+9)) (F : Fin (2^n) → Bool)
    (C : Circuit ((Fin (2^n) × Bool) × Fin M)) (psi : QState ((Fin (2^n) × Bool) × Fin M))
    (S : Finset ((Fin (2^n) × Bool) × Fin M)) :
    MeasureProb (Run (registerCountingOracle n F) (registerCountingWord n M hM C)
      (registerCountingInput n M hM psi)) (registerCountingEvent n M hM S) =
      MeasureProb (Run (workspaceBitOracle F) C psi) S := by
  unfold registerCountingOracle registerCountingWord registerCountingInput registerCountingEvent
  rw [(run_relabelCircuit_readout _ _ _ _ _).2,workspaceWord_readout,← countingFlat_oracle,
    (run_relabelCircuit_readout _ _ _ _ _).2]

theorem registerCounting_queries (n M : ℕ) (hM : M ≤ 2^(n+9))
    (C : Circuit ((Fin (2^n) × Bool) × Fin M)) :
    QueryCount (registerCountingWord n M hM C) = QueryCount C := by
  unfold registerCountingWord
  rw [(relabelCircuit_legality_resources _ _).2.1,workspaceWord_queries,
    (relabelCircuit_legality_resources _ _).2.1]

theorem registerCounting_gates (n M : ℕ) (hM : M ≤ 2^(n+9))
    (C : Circuit ((Fin (2^n) × Bool) × Fin M)) :
    GateCount (registerCountingWord n M hM C) = GateCount C := by
  unfold registerCountingWord
  rw [(relabelCircuit_legality_resources _ _).2.2.1,workspaceWord_gates,
    (relabelCircuit_legality_resources _ _).2.2.1]

theorem registerCounting_unitary (n M : ℕ) (hM : M ≤ 2^(n+9))
    (C : Circuit ((Fin (2^n) × Bool) × Fin M)) (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (registerCountingWord n M hM C) := by
  apply (relabelCircuit_legality_resources _ _).1.mpr
  apply workspaceWord_unitary
  exact (relabelCircuit_legality_resources _ _).1.mpr hC

theorem registerCounting_normalized (n M : ℕ) (hM : M ≤ 2^(n+9))
    (psi : QState ((Fin (2^n) × Bool) × Fin M)) (hpsi : Normalized psi) :
    Normalized (registerCountingInput n M hM psi) :=
  normalized_relabelState _ (workspaceEmbedding_normalized _ _ (normalized_relabelState _ hpsi))

theorem registerCounting_wire_count (n : ℕ) : (n+1)+(n+9) = 2*n+10 := by omega

theorem registerCounting_trial (n M : ℕ) (hM : 2 ≤ M) (hcap : M ≤ 2^(n+9))
    (A : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) (j : Fin (2^n))
    (hA : A ∈ Matrix.unitaryGroup (Fin (2^n)) ℂ) :
    IsUnitaryCircuit (registerCountingWord n M hcap (standardPaddedAEWord M A j)) ∧
    Normalized (registerCountingInput n M hcap (standardInput M hM j)) ∧
    QueryCount (registerCountingWord n M hcap (standardPaddedAEWord M A j)) = M := by
  refine ⟨registerCounting_unitary _ _ _ _ (standardPaddedAE_unitary M hM A j hA),
    registerCounting_normalized _ _ _ _ (standardInput_normalized M hM j),?_⟩
  rw [registerCounting_queries]
  exact (standardPaddedAE_resources M (by omega) A j).1

theorem registerCounting_trial_label (n M : ℕ) (hM : 2 ≤ M) (hcap : M ≤ 2^(n+9))
    (A : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) (j : Fin (2^n))
    (hA : A ∈ Matrix.unitaryGroup (Fin (2^n)) ℂ) (F : Fin (2^n) → Bool) (z : Fin M) :
    MeasureProb (Run (registerCountingOracle n F)
      (registerCountingWord n M hcap (standardPaddedAEWord M A j))
      (registerCountingInput n M hcap (standardInput M hM j)))
      (registerCountingEvent n M hcap (Finset.univ.filter (fun p => p.2 = z))) =
      (aeLaw M A j (sourceMarked F) hA hM).prob z := by
  rw [registerCounting_readout]
  exact standardPaddedAE_label M hM A j hA F z

end Qatlib.Papers.QCounting98.MainResults.ActualCounting
