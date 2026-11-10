/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.Lchs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.LchsSimulation.TimeTrapezoid

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib MeasureTheory Set Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

def lchs32JointScheduleSize (M Mt : ℕ) : ℕ := (M + 1) * (Mt + 1)

def lchs32SourcePreparationCount (M Mt : ℕ) : ℕ := lchs2dSelectPrepareCount M Mt

def lchs33HamTOrder (m : ℕ) : ℕ := lchsHamTNativeOrder m

def lchs33AncillaBits (J : Type) [Fintype J] (K : ℕ) : ℕ := taylorAncillaBits J K

def lchs33PhaseGateCount (J : Type) [Fintype J] (K : ℕ) : ℕ := taylorPhaseGateCount J K

def lchs34HybridSampleQueries (m n : ℕ) : ℕ := lchsHybridTotalQueries m n

def lchs34FastForwardApplications : ℕ := capFastForwardApplications

def lchs35FixedGateCount (k : ℕ) : ℕ := lchsFixedGateCount k

def lchs35RegisterBits (n : ℕ) : ℕ := lchsRegisterBits n

def lchs35QuantumSpace (N dataStates : ℕ) : ℕ := lchsQuantumSpace N dataStates

noncomputable def lchs35ResourceLedger (N m Mt dataStates : ℕ) : LchsTheoremResources :=
  lchsTheoremResources N m Mt dataStates

def lchs32LabelSourcePrepare : ℕ := 1

def lchs32LabelSourceAdjoint : ℕ := 1

def lchs32LabelSuccessRounds (m : ℕ) : ℕ := m

def lchs32SourceNodeReuse (M : ℕ) : ℕ := M + 1

structure LchsHybridSampleLedger where

  sourcePreparations : ℕ

  fastForward : ℕ

  queries : ℕ

  shots : ℕ

def lchs34HybridSampleLedger (m Mt : ℕ) : LchsHybridSampleLedger :=
  { sourcePreparations := lchs2dSourceStateCount Mt
    fastForward := capFastForwardApplications
    queries := lchsHybridSampleMaxQueries m
    shots := 1 }

def lchs34HybridTotalLedger (m Mt n : ℕ) : LchsHybridSampleLedger :=
  { sourcePreparations := lchs2dSourceStateCount Mt
    fastForward := n * capFastForwardApplications
    queries := lchsHybridTotalQueries m n
    shots := n }

end Qatlib.Concepts.RandCompile.ChannelBudget
