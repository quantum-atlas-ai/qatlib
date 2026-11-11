/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryBlockTransport
import Qatlib.Concepts.AmplitudeCore.AmplifyCore.Theorem4QuadraticSpeedupWithKnownAStat
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Contracts for exact promise search

This module defines the Fourier-prepared promise-search run `BHMTTh16.promiseRun` and its marked
mass `BHMTTh16.promiseGoodMass`, in the setting of [BrassardEtAl2002]. The unrestricted
specification `Theorem16Spec.expected` omits a bound on the promised cardinality; the
corresponding bounded specification is supplied separately.

## Main statements

* `BHMTTh16.promiseRun`: the exact-amplification program applied to a Fourier-prepared input.
* `Theorem16Spec.expected`: the unrestricted promise-search contract.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false

open Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification
open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh16

/-- The canonical coordinate Hilbert basis of the finite complex Euclidean space. -/
noncomputable def finEB (N : ℕ) : HilbertBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) :=
  (EuclideanSpace.basisFun (Fin N) ℂ).toHilbertBasis

/-- The Boolean predicate on integer labels obtained from membership in the finite marked set
`S`. -/
def markLabels (N : ℕ) (S : Finset (Fin N)) : ℤ → Bool :=
  fun z => decide (z ∈ (S.image fun i : Fin N => (i.val : ℤ)))

/-- The number of instructions with label five in an exact-amplification program. -/
def marksCount (prog : List (Fin 6)) : ℕ :=
  (prog.filter fun k => decide (k.val = 5)).length

/-- Runs the exact-amplification program using Fourier preparation, the coordinate marked
projection, and mixing parameter `r`. -/
noncomputable def promiseRun {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (r : ℝ) (prog : List (Fin 6)) :
    EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N) :=
  let A := Qatlib.Concepts.QueryComplexity.DegreeMethod.unitaryEuclidean
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N) (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN)
  let P := Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.goodProjection (finEB N) (fun i : Fin N => (i.val : ℤ))
    (markLabels N S)
  Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run A (finEB N ⟨0, hN⟩) P r prog

/-- The sum of the squared norms of the marked projections of the two components returned by
`promiseRun`. -/
noncomputable def promiseGoodMass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (r : ℝ) (prog : List (Fin 6)) : ℝ :=
  let P := Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.goodProjection (finEB N) (fun i : Fin N => (i.val : ℤ))
    (markLabels N S)
  let v := promiseRun hN S r prog
  ‖P v.1‖^2 + ‖P v.2‖^2

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh16

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem16Spec
/-- Specifies exact promise search with inverse-square-root cost bounds for every positive
promised cardinality, without requiring that cardinality to be at most `N`. -/
def expected : Prop :=
  ∃ (design : ℝ → ℝ × List (Fin 6)) (c C C₂ : ℝ),
    0 < c ∧ 0 < C ∧ 0 < C₂ ∧
    ∀ (N : ℕ) (hN : 0 < N) (S : Finset (Fin N)) (t₀ : ℕ),
      0 < t₀ → (S.card = 0 ∨ S.card = t₀) →
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
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem16Spec
