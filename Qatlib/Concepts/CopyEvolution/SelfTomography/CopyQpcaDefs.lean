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

/-!
# Gram operators and QPCA resource ledgers

This module defines dyadic phase words, Gram-matrix entry formulas, and the operator
`gramOperator A = Aᴴ * A`. `QpcaRunLedger` records fresh copies, gates, discards, and queries
for fresh-copy steps and one- or two-species QPE paths.

The mathematical background is described in [LloydMohseniRebentrost2014].

## Main statements

* `piDyadicWord` and `piDyadicGrid`: dyadic phase labels.
* `gramOperator`: the conjugate-transpose Gram operator.
* `QpcaRunLedger.price`: fresh-copy count plus gate count.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

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

/-- The dyadic phase value `k.val / 2 ^ w` represented by a `w`-bit label. -/
noncomputable def piDyadicWord (w : ℕ) (k : Fin (2 ^ w)) : ℝ := (k.val : ℝ) / 2 ^ w

/-- The grid mapping each `w`-bit label to its dyadic phase value. -/
noncomputable def piDyadicGrid (w : ℕ) : Fin (2 ^ w) → ℝ := piDyadicWord w

/-- The conjugate inner product of columns `i` and `j` of `A`. -/
noncomputable def gramEntry {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℂ) (i j : Fin d) : ℂ :=
  ∑ k, starRingEnd ℂ (A k i) * (A k j)

/-- The Gram operator `Aᴴ * A` on the column index space of `A`. -/
noncomputable def gramOperator {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℂ) : Operator d :=
  Aᴴ * A

/-- The sum of conjugate products of entries in row `k` of `A`. -/
noncomputable def gramColumnNormSq {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℂ) (k : Fin m) : ℂ :=
  ∑ i, starRingEnd ℂ (A k i) * (A k i)

/-- A resource ledger containing fresh-copy, gate, discard, and query counts. -/
structure QpcaRunLedger where

  freshCopies : ℕ

  gates : ℕ

  discards : ℕ

  queries : ℕ

/-- The QPCA ledger obtained from the resource counts of a fresh-copy angle sequence. -/
noncomputable def freshStepLedger (D : ℕ) (angles : List ℝ) : QpcaRunLedger where
  freshCopies := (freshCopyResourceCounts D angles).1
  gates := (freshCopyResourceCounts D angles).2.1
  discards := (freshCopyResourceCounts D angles).2.2.1
  queries := (freshCopyResourceCounts D angles).2.2.2

/-- The QPCA ledger obtained from the copy-QPE resource counts for dimensions `D`, `M` and
repetition count `n`. -/
noncomputable def qpePathLedger (D M n : ℕ) : QpcaRunLedger where
  freshCopies := (copyQPEResources D M n).1
  gates := (copyQPEResources D M n).2.1
  discards := (copyQPEResources D M n).2.2.1
  queries := (copyQPEResources D M n).2.2.2

/-- The QPCA ledger obtained from the two-species QPE resource counts. -/
noncomputable def twoSpeciesPathLedger (M n : ℕ) : QpcaRunLedger where
  freshCopies := (twoSpeciesQPEResources M n).1
  gates := (twoSpeciesQPEResources M n).2.1
  discards := (twoSpeciesQPEResources M n).2.2.1
  queries := (twoSpeciesQPEResources M n).2.2.2

/-- The sum of the fresh-copy and gate counts in a QPCA resource ledger. -/
def QpcaRunLedger.price (L : QpcaRunLedger) : ℕ := L.freshCopies + L.gates

end Qatlib.Concepts.CopyEvolution.SelfTomography
