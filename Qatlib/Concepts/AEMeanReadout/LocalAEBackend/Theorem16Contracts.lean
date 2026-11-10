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
set_option warningAsError false

open Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification
open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh16

noncomputable def finEB (N : ℕ) : HilbertBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) :=
  (EuclideanSpace.basisFun (Fin N) ℂ).toHilbertBasis

def markLabels (N : ℕ) (S : Finset (Fin N)) : ℤ → Bool :=
  fun z => decide (z ∈ (S.image fun i : Fin N => (i.val : ℤ)))

def marksCount (prog : List (Fin 6)) : ℕ :=
  (prog.filter fun k => decide (k.val = 5)).length

noncomputable def promiseRun {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (r : ℝ) (prog : List (Fin 6)) :
    EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N) :=
  let A := Qatlib.Concepts.QueryComplexity.DegreeMethod.unitaryEuclidean
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N) (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN)
  let P := Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.goodProjection (finEB N) (fun i : Fin N => (i.val : ℤ))
    (markLabels N S)
  Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run A (finEB N ⟨0, hN⟩) P r prog

noncomputable def promiseGoodMass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (r : ℝ) (prog : List (Fin 6)) : ℝ :=
  let P := Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.goodProjection (finEB N) (fun i : Fin N => (i.val : ℤ))
    (markLabels N S)
  let v := promiseRun hN S r prog
  ‖P v.1‖^2 + ‖P v.2‖^2

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh16

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem16Spec
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
