/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLowerBound00.MainResults.AdversaryCore
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QLowerBound00.MainResults.Lemma1

open Qatlib.Papers.QLowerBound00.MainResults.AdversaryCore

theorem source_lemma1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ans : ι → Bool) (fx : Bool) (ψx ψy : ι → ℂ) (αx αy : ℂ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hx_norm : (∑ iw, ‖ψx iw‖ ^ 2) = 1)
    (hy_norm : (∑ iw, ‖ψy iw‖ ^ 2) = 1)
    (hwrongX : (∑ iw ∈ univ.filter (fun iw => ans iw ≠ fx), ‖ψx iw‖ ^ 2) ≤ ε)
    (hwrongY : (∑ iw ∈ univ.filter (fun iw => ans iw = fx), ‖ψy iw‖ ^ 2) ≤ ε) :
    ‖αx * αy * (∑ iw, star (ψx iw) * ψy iw)‖ ≤
      2 * Real.sqrt (ε * (1 - ε)) * ‖αx‖ * ‖αy‖ :=
  lemma1_density_entry ans fx ψx ψy αx αy ε hε0 hε hx_norm hy_norm hwrongX hwrongY

end Qatlib.Papers.QLowerBound00.MainResults.Lemma1
