/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem16Contracts

/-!
# Bounded cardinality-promise search specification

`BHMTTh16.Theorem16` states the exact-search contract for the promise that the marked
cardinality is either zero or a known integer `t₀` with `0 < t₀ ≤ N`. It includes state
normalization, exact marked-mass conclusions, and inverse-square-root program-cost bounds as in
[BrassardEtAl2002].

## Main statements

* `BHMTTh16.Theorem16`: the bounded exact promise-search specification.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh16
/-- Specifies exact promise search for `0 < t₀ ≤ N`, with marked mass one in the nonempty
promised case, marked mass zero in the empty case, and inverse-square-root cost bounds. -/
def Theorem16 : Prop :=
  ∃ (design : ℝ → ℝ × List (Fin 6)) (c C C₂ : ℝ),
    0 < c ∧ 0 < C ∧ 0 < C₂ ∧
    ∀ (N : ℕ) (hN : 0 < N) (S : Finset (Fin N)) (t₀ : ℕ),
      0 < t₀ → t₀ ≤ N → (S.card = 0 ∨ S.card = t₀) →
      let a : ℝ := (t₀ : ℝ)/(N : ℝ)
      let d := design a
      let v := BHMTTh16.promiseRun hN S d.1 d.2
      (0 ≤ d.1 ∧ d.1 ≤ 1 ∧
        ‖v.1‖^2 + ‖v.2‖^2 = 1 ∧
        (S.card = t₀ → BHMTTh16.promiseGoodMass hN S d.1 d.2 = 1) ∧
        (S.card = 0 → BHMTTh16.promiseGoodMass hN S d.1 d.2 = 0) ∧
        c/Real.sqrt a ≤ (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls d.2 : ℝ) ∧
        (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls d.2 : ℝ) ≤ C/Real.sqrt a ∧
        ((BHMTTh16.marksCount d.2 : ℕ) + 1 : ℝ) ≤ C₂/Real.sqrt a)
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh16
