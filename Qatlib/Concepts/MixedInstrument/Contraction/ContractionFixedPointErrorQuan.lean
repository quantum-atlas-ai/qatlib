/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.Contraction.ContractionFixedPointErrorStat
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates

/-!
# Fixed point error for contractive channels

This module proves `contractionFixedPointError`, bounding the distance from a channel fixed
point to an approximate fixed point by the residual divided by `1 - η`. Contraction is required
on density operators, as in the fixed point estimate of [TemmeEtAl2011].
`globalContractionDensityFixedPointImpossible` rules out the corresponding strict contraction on
all operators when a density fixed point exists.

## Main statements

* `contractionFixedPointError`: A channel contracting density operators by `η < 1` has fixed
  point error at most `ε / (1 - η)` whenever the reference density operator has residual at most
  `ε`; see [Temme et al., Eq. (44)][TemmeEtAl2011].
* `globalContractionDensityFixedPointImpossible`: A quantum channel with a density fixed point
  cannot contract the Schatten one distance between all operators by a factor strictly less than
  one.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdaptiveCP.BranchTrace

namespace Qatlib.Concepts.MixedInstrument.Contraction

/-- A channel contracting density operators by `η < 1` has fixed point error at most `ε / (1 -
η)` whenever the reference density operator has residual at most `ε`; see [Temme et al., Eq.
(44)][TemmeEtAl2011]. -/
theorem contractionFixedPointError : ContractionFixedPointError := by
  intro D T sigma rho hs hrho hfix eta _he0 he1 hcontract eps _heps herr
  have htri : SchattenOne (sigma - rho) ≤
      SchattenOne (T.map sigma - T.map rho) + SchattenOne (T.map rho - rho) := by
    have hid : sigma - rho = (T.map sigma - T.map rho) + (T.map rho - rho) := by rw [hfix]; abel
    rw [hid]
    simp only [Qatlib.Foundations.PureStateMath.BornBridge.schattenOne_eq_physlib_traceNorm]
    exact Matrix.traceNorm_add_le _ _
  have h := hcontract sigma rho hs hrho
  apply (le_div_iff₀ (sub_pos.mpr he1)).mpr
  nlinarith

/-- A quantum channel with a density fixed point cannot contract the Schatten one distance
between all operators by a factor strictly less than one. -/
theorem globalContractionDensityFixedPointImpossible (D : ℕ) (T : QuantumChannel D D)
    (sigma : Operator D) (hs : IsDensityOperator sigma) (hfix : T.map sigma = sigma)
    (eta : ℝ) (heta : eta < 1)
    (hcontract : ∀ X Y : Operator D, SchattenOne (T.map X - T.map Y) ≤ eta * SchattenOne (X - Y)) : False := by
  have hs0 : sigma ≠ 0 := by
    intro h
    have htrace := hs.2
    rw [h, Matrix.trace_zero] at htrace
    exact zero_ne_one htrace
  have hn : 0 < SchattenOne sigma := by
    rw [Qatlib.Foundations.PureStateMath.BornBridge.schattenOne_eq_physlib_traceNorm]
    exact lt_of_le_of_ne (Matrix.traceNorm_nonneg sigma)
      (fun h => hs0 ((Matrix.traceNorm_zero_iff sigma).mp h.symm))
  have h := hcontract sigma 0
  simp only [map_zero, hfix, sub_zero] at h
  nlinarith

end Qatlib.Concepts.MixedInstrument.Contraction
