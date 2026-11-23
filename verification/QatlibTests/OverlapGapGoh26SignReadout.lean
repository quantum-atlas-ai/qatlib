module

import Qatlib.Papers.OverlapGapGoh26.SignReadout.GaussianTransfer

/-! Consumers of the finite-size and asymptotic sign readout bounds for quartic interactions. -/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.NormRegion
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
open Qatlib.Papers.OverlapGapGoh26.MainResults
open Qatlib.Papers.OverlapGapGoh26.MainResults.ActualMF
open Qatlib.Papers.OverlapGapGoh26.MainResults.BinaryNoGo
open Qatlib.Papers.OverlapGapGoh26.SignReadout

example (x : Input 3 4) (i : Fin 4) :
    signOutput (sourceSchedule 3) 3 x i = 1 ∨ signOutput (sourceSchedule 3) 3 x i = -1 :=
  signOutput_binary (sourceSchedule 3) 3 x i

example (x : Input 3 4) : roundingDefect (sourceSchedule 1) 1 x = 1 :=
  roundingDefect_source_one (by decide) x

example (x : Input 3 4) (hx : normScale x ≤ normBound 3) :
    |energy (sourceSchedule 3) 3 x - signedEnergy (sourceSchedule 3) 3 x| ≤
      normBound 3 * 4 * roundingDefect (sourceSchedule 3) 3 x := by
  simpa using signedEnergy_sub_le (by decide : 0 < (3 : ℕ)) (by decide : 0 < (4 : ℕ))
    (sourceSchedule 3) 3 (normBound 3) x hx

example (a δ : ℝ) :
    (stdGaussian (Input 3 4)).real (nearSigned (sourceSchedule 3) 3 a) ≤
      (stdGaussian (Input 3 4)).real (nearBinary (sourceSchedule 3) 3 (a + normBound 3 * 4 * δ)) +
        2 * Real.exp (-4) +
        (stdGaussian (Input 3 4)).real {x | δ < roundingDefect (sourceSchedule 3) 3 x} := by
  simpa using nearSigned_probability_le (by decide : 0 < (3 : ℕ)) (by decide : 0 < (4 : ℕ))
    (sourceSchedule 3) 3 a δ

example {μ ν₁ ν₂ c : ℝ} (hμ : 0 < μ) (hlo : 0 < ν₁) (hgap : ν₁ < ν₂) (hhi : ν₂ < 1)
    (hc : 0 < c) (hogp : ∀ᶠ N : ℕ in atTop,
      ((gaussianTensorLaw 3 N).prod (gaussianTensorLaw 3 N)).real
        (RawNoGo.modelOgp 3 N μ ν₁ ν₂)ᶜ ≤ Real.exp (-c * (N : ℝ)))
    (hdefect : Tendsto (fun N : ℕ => (stdGaussian (Input 3 N)).real
      {x | μ / (32 * (normBound 3 * (3 + 1 : ℕ))) < roundingDefect (sourceSchedule 3) 3 x})
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (stdGaussian (Input 3 N)).real
      (nearSigned (sourceSchedule 3) 3 (μ / 32))) atTop (𝓝 0) :=
  signed_source_nogo_of_ogp_tail (by decide : Odd 3) (by decide) (by decide) hμ hlo hgap hhi hc
    hogp hdefect
