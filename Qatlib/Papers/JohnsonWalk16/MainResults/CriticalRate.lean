/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.WalkReduction.CubicSpectrum.FourBlock
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.JohnsonWalk16.MainResults.CriticalRate
open Qatlib.Foundations.WalkReduction.CubicSpectrum

theorem candidate_rate_100 : gammaC 100 = 69/20000 := gammaC_100

theorem candidate_r_value {n : ℝ} (hn : n ≠ 0) :
    Er (gammaC n) n = -1-1/(2*n)+21/(2*n^2) := Er_at_critical hn

theorem candidate_native_spectrum {n : ℝ} (hn : 6 ≤ n) :
    ∃ lam : ℝ, |lam-(-1-1/(2*n))| ≤ 54/n^2 ∧
      ∃ v : Fin 4 → ℝ, Module.End.HasEigenvector (leadingFour (gammaC n) n).toLin' lam v :=
  leadingFour_nearby hn

end Qatlib.Papers.JohnsonWalk16.MainResults.CriticalRate
