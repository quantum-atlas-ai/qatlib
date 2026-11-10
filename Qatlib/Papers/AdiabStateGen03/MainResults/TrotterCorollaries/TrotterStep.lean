/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Qatlib.Papers.AdiabStateGen03.MainResults.TrotterCorollaries.PowerAccumulation

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.AdiabStateGen03.MainResults.TrotterCorollaries

open Qatlib.Papers.AdiabStateGen03.MainResults

def orderedProd {n M : ℕ} (f : Fin M → Op n) : Op n :=
  (List.finRange M).foldr (fun m acc => f m * acc) (1 : Op n)

def reverseProd {n M : ℕ} (f : Fin M → Op n) : Op n :=
  (List.finRange M).reverse.foldr (fun m acc => f m * acc) (1 : Op n)

def trotterStep {n M : ℕ} (Hs : Fin M → Ham n) (δ : ℝ) : Op n :=
  orderedProd (fun m => timeEvolution (Hs m) δ) * reverseProd (fun m => timeEvolution (Hs m) δ)

theorem timeEvolution_pow_nat {n : ℕ} (H : Ham n) (t : ℝ) (N : ℕ) :
    timeEvolution H t ^ N = timeEvolution H ((N : ℝ) * t) := by

  haveI : NormedAlgebra ℚ (Op n) := NormedAlgebra.restrictScalars ℚ ℂ (Op n)
  unfold timeEvolution
  rw [← NormedSpace.exp_nsmul]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ N, smul_smul]
  congr 1
  ring

end Qatlib.Papers.AdiabStateGen03.MainResults.TrotterCorollaries
