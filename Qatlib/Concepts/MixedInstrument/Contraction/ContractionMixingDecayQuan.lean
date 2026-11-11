/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.Contraction.ContractionMixingDecayStat

/-!
# Geometric mixing for contractive channels

`contractionMixingDecay` proves geometric decay of Schatten one distance to a fixed density
operator. Each iteration contributes a factor `η` under a contraction hypothesis restricted to
density operators, supporting the mixing analysis of [TemmeEtAl2011].

## Main statements

* `contractionMixingDecay`: For a channel contracting density operators by `0 ≤ η < 1`, the
  Schatten one distance to a fixed density operator after `m` steps is at most `η ^ m` times the
  initial distance; see [TemmeEtAl2011].

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MixedInstrument.Contraction

/-- For a channel contracting density operators by `0 ≤ η < 1`, the Schatten one distance to a
fixed density operator after `m` steps is at most `η ^ m` times the initial distance; see
[TemmeEtAl2011]. -/
theorem contractionMixingDecay : ContractionMixingDecay := by
  intro D T sigma rho hs hrho hfix eta he0 _he1 hcontract m
  have hiter : ∀ k : ℕ, IsDensityOperator ((T.map^[k]) rho) := by
    intro k
    induction k with
    | zero => simpa using hrho
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact T.preservesDensity ih
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have h := hcontract ((T.map^[m]) rho) sigma (hiter m) hs
    rw [hfix] at h
    apply h.trans
    have hh := mul_le_mul_of_nonneg_left ih he0
    simpa only [pow_succ, mul_assoc, mul_comm eta] using hh

end Qatlib.Concepts.MixedInstrument.Contraction
