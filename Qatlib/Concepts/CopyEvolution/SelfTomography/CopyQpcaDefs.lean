/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.Qpca
import Qatlib.Concepts.CopyEvolution.SelfTomography.GramFirstRegisterDensityStat
import Qatlib.Concepts.CopyEvolution.SelfTomography.GramSpectralReadoutSubgoalQuan
import Qatlib.Concepts.CopyEvolution.SelfTomography.GramStatePreparationSubgoalStat
import Qatlib.Concepts.RandCompile.ChannelBudget.CopyEvolution
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CopyEvolution.SelfTomography

namespace Qatlib.Concepts.CopyEvolution.SelfTomography

open Matrix
open Qatlib
open scoped ComplexOrder BigOperators Classical Matrix.Norms.L2Operator

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable def piDyadicWord (w : ℕ) (k : Fin (2 ^ w)) : ℝ := (k.val : ℝ) / 2 ^ w

noncomputable def piDyadicGrid (w : ℕ) : Fin (2 ^ w) → ℝ := piDyadicWord w

noncomputable def gramEntry {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℂ) (i j : Fin d) : ℂ :=
  ∑ k, starRingEnd ℂ (A k i) * (A k j)

noncomputable def gramOperator {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℂ) : Operator d :=
  Aᴴ * A

noncomputable def gramColumnNormSq {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℂ) (k : Fin m) : ℂ :=
  ∑ i, starRingEnd ℂ (A k i) * (A k i)

structure QpcaRunLedger where

  freshCopies : ℕ

  gates : ℕ

  discards : ℕ

  queries : ℕ

noncomputable def freshStepLedger (D : ℕ) (angles : List ℝ) : QpcaRunLedger where
  freshCopies := (freshCopyResourceCounts D angles).1
  gates := (freshCopyResourceCounts D angles).2.1
  discards := (freshCopyResourceCounts D angles).2.2.1
  queries := (freshCopyResourceCounts D angles).2.2.2

noncomputable def qpePathLedger (D M n : ℕ) : QpcaRunLedger where
  freshCopies := (copyQPEResources D M n).1
  gates := (copyQPEResources D M n).2.1
  discards := (copyQPEResources D M n).2.2.1
  queries := (copyQPEResources D M n).2.2.2

noncomputable def twoSpeciesPathLedger (M n : ℕ) : QpcaRunLedger where
  freshCopies := (twoSpeciesQPEResources M n).1
  gates := (twoSpeciesQPEResources M n).2.1
  discards := (twoSpeciesQPEResources M n).2.2.1
  queries := (twoSpeciesQPEResources M n).2.2.2

def QpcaRunLedger.price (L : QpcaRunLedger) : ℕ := L.freshCopies + L.gates

end Qatlib.Concepts.CopyEvolution.SelfTomography
