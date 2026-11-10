/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyLearn26.MainResults.Models.InterfaceModels
import Qatlib.Papers.NoisyLearn26.MainResults.OracleSeparation
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyLearn26.MainResults.EncodedSSP

open Qatlib.Papers.NoisyLearn26.MainResults
open Qatlib.Papers.NoisyLearn26.MainResults.OracleSeparation

def encodedShufflingOracle {n : ℕ} (f : Reg n → Reg n) (d : ℕ) :
    EncodedShufflingOracle n d where
  width := n * (d + 2)
  eval := fun x => x
  isShuffling := True
  shadow := { width := n * (d + 2), eval := fun x => x }

def BPPQNC {O : Oracle} (d : ℕ) (A : RelAlgorithm O) : Prop :=
  IsPolynomial A.queries ∧ A.depth = fun _ => d

theorem o2h_encoded_oracle (q : ℕ) (p Ptrue Pshadow : ℝ)
    (hp : 0 ≤ p) (hO2H : |Ptrue - Pshadow| ^ 2 ≤ 2 * (q : ℝ) * p) :
    |Ptrue - Pshadow| ≤ Real.sqrt (2 * (q : ℝ) * p) := by
  calc
    |Ptrue - Pshadow| = Real.sqrt (|Ptrue - Pshadow| ^ 2) := by
      rw [Real.sqrt_sq (abs_nonneg _)]
    _ ≤ Real.sqrt (2 * (q : ℝ) * p) := Real.sqrt_le_sqrt hO2H

end Qatlib.Papers.NoisyLearn26.MainResults.EncodedSSP
