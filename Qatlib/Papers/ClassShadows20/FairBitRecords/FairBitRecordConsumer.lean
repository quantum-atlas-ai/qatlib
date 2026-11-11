/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# ClassShadows20 · FairBitRecords · finite fair-bit consumer

This development layer exposes the finite fair-bit record law used by a
Pauli trial.  The law is deliberately concrete: a two-bit tape has four
uniform labels, and a signed one-bit readout has the exact variance expected
from a fair record.  It provides a small typed consumer for later shadow
sampling work without claiming the paper's global confidence theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ClassShadows20.FairBitRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open scoped BigOperators Classical

/-- A finite two-bit tape has four equiprobable trial labels. -/
noncomputable def twoBitFairLaw : FinDist (Fin 4) where
  prob _ := (1 / 4 : ℝ)
  nonneg _ := by norm_num
  sum_one := by norm_num [Fin.sum_univ_succ]

/-- The finite fair-bit tape carries unit total mass. -/
theorem twoBitFairLaw_sum_one : (∑ x : Fin 4, twoBitFairLaw.prob x) = 1 :=
  twoBitFairLaw.sum_one

/-- A signed one-bit readout of the fair tape has unit variance. -/
theorem twoBitFairLaw_signed_variance :
    twoBitFairLaw.variance (fun x : Fin 4 => if x.val < 2 then 1 else -1) = 1 := by
  norm_num [FinDist.variance, FinDist.expect, twoBitFairLaw, Fin.sum_univ_succ]

/-! The same signed readout has the exact finite empirical-mean second moment
for two independent fair-bit records. -/

/-- The signed readout is the first bit of the two-bit fair tape, encoded as ±1. -/
def twoBitSignedReadout : Fin 4 → ℝ := fun x => if x.val < 2 then 1 else -1

/-- Two independent fair records reduce the empirical-mean variance by `1 / 2`. -/
theorem twoBitFairLaw_signed_sample_mean_variance :
    ∑ ω : Fin 2 → Fin 4,
      twoBitFairLaw.probOf ω *
        (FinDist.avg twoBitSignedReadout ω - twoBitFairLaw.expect twoBitSignedReadout) ^ 2 =
      (1 : ℝ) / 2 := by
  rw [expect_avg_sub_sq twoBitFairLaw twoBitSignedReadout (by norm_num)]
  rw [show twoBitFairLaw.variance twoBitSignedReadout = 1 by
    exact twoBitFairLaw_signed_variance]
  norm_num

end Qatlib.Papers.ClassShadows20.FairBitRecords
