/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsRemainder
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.AdversaryBounds.AdvDuality.CoinCode
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open scoped Classical

def rareWeights (D : ℕ) (j : Fin 2) : ℕ := if j = 0 then D - 1 else 1

noncomputable def rareBitLaw (D : ℕ) (hD : 2 ≤ D) : FinDist Bool where
  prob b := if b then 1 / (D : ℝ) else 1 - 1 / (D : ℝ)
  nonneg b := by
    have hpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    have hone : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
    cases b
    · exact sub_nonneg.mpr ((div_le_one hpos).mpr hone)
    · change 0 ≤ 1 / (D : ℝ)
      positivity
  sum_one := by simp

def rareValue (D A : ℕ) (b : Bool) : ℝ := if b then (D * A : ℕ) else 0

noncomputable def pilotFailure (D A m : ℕ) (hD : 2 ≤ D)
    (pilot : (Fin m → ℝ) → ℝ) : ℝ :=
  (rareBitLaw D hD).probEvent (fun ω =>
    pilot (fun i => rareValue D A (ω i)) < (rareBitLaw D hD).variance (rareValue D A))

end Qatlib.Concepts.AdversaryBounds.AdvDuality
