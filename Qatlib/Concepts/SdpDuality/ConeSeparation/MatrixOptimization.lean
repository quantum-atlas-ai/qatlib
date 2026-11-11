/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.MatrixOptimizationDual
import Qatlib.Concepts.MatrixWeights.ApproxGibbs
import Qatlib.Concepts.SdpDuality.ConeSeparation.SdpRunMacros

/-!
# Recorded histories and exact dual certificate sampling

A `History` records a sampler family, the Step 2 search records, selected candidates and mass
indices, and equality between each selected candidate law and the recorded sampler output law.
`History.masses` assigns rational grid masses, and `History.rounds` extends the selected round
vectors by zero beyond the recorded horizon. This keeps the averaging formulas and sampling
programs attached to the same records.

`History.certificate_eq` identifies the averaged SDP certificate with the sampler family's dual
vector. Under a positive horizon, nonnegative rational precision, and positive rational
certificate parameters, `History.actual_certificate` realizes that certificate as a positive
scale times the exact stopped sampler's output distribution. The certificate construction fits
the quantum SDP setting of [BrandaoSvore2017].

## Main statements

* `History.rounds_same_record`: each recorded round is its mass times the corresponding sampler
  law.
* `History.certificate_eq`: the SDP certificate equals the sampler family's dual vector.
* `History.actual_certificate`: exact stopped rejection sampling realizes the normalized
  certificate distribution.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Concepts.MatrixWeights.ApproxGibbs

namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open Qatlib.Concepts.SdpDuality.ConeSeparation Qatlib.Concepts.MatrixWeights.ApproxGibbs
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib
open Qatlib
open scoped Classical ENNReal
set_option warningAsError false

variable {T D m γ Nmax M L Q : ℕ}

/-- Stores a family of `T` samplers, a Step 2 search record and selected candidate and mass
index for each round, and equality of each selected candidate law with the corresponding
sampler's real output law. -/
structure History (T D m γ Nmax M L Q : ℕ) where
  samplers : Family T D m
  records : Fin T → Step2Search m γ Nmax M L Q
  candidate : Fin T → Fin γ
  massIndex : Fin T → Fin Nmax
  law_eq : ∀ t i, (records t).law (candidate t) i = samplers.realOutput t i

namespace History

/-- Assigns round `t` the rational mass `ε * ((H.massIndex t).val + 1)`. -/
def masses (H : History T D m γ Nmax M L Q) (ε : ℚ) (t : Fin T) : ℚ :=
  ε * ((H.massIndex t).val + 1)

/-- Every recorded rational mass is nonnegative when `ε` is nonnegative. -/
theorem masses_nonneg (H : History T D m γ Nmax M L Q) (ε : ℚ) (hε : 0 ≤ ε) :
    ∀ t, 0 ≤ H.masses ε t := fun t => mul_nonneg hε (by positivity)

/-- Returns the Step 2 round vector selected by the history when `t < T`, using grid step `ε`,
and returns the zero vector for all later times. -/
noncomputable def rounds (H : History T D m γ Nmax M L Q) (ε : ℚ)
    (t : ℕ) (i : Fin m) : ℝ :=
  if h : t < T then
    (H.records ⟨t,h⟩).roundVector (ε : ℝ) (H.candidate ⟨t,h⟩) (H.massIndex ⟨t,h⟩) i
  else 0

/-- For a recorded round, identifies `H.rounds ε t i` with its rational mass cast to the reals
times the real output probability of the corresponding sampler. -/
theorem rounds_same_record (H : History T D m γ Nmax M L Q) (ε : ℚ)
    (t : Fin T) (i : Fin m) :
    H.rounds ε t i = (H.masses ε t : ℝ) * H.samplers.realOutput t i := by
  simp [rounds, t.isLt, Step2Search.roundVector, Step2Search.gridMass,
    masses, H.law_eq]

/-- The averaged SDP certificate built from `H.rounds` equals the sampler family's `dualVector`
with offset `δ*α/(2*R)` and masses `H.masses ε`. -/
theorem certificate_eq (H : History T D m γ Nmax M L Q)
    (ε δ α R : ℚ) (j₀ : Fin m) (i : Fin m) :
    sdpDualCertificate m (δ : ℝ) (α : ℝ) (R : ℝ) j₀ (H.rounds ε) T i =
      dualVector H.samplers j₀ ((δ*α/(2*R) : ℚ) : ℝ)
        (fun t => (H.masses ε t : ℝ)) i := by
  have hs : (∑ t : Fin T, (H.masses ε t : ℝ) * H.samplers.realOutput t i) =
      ∑ t ∈ Finset.range T, H.rounds ε t i := by
    rw [← Fin.sum_univ_eq_sum_range (fun t => H.rounds ε t i) T]
    exact Finset.sum_congr rfl fun t _ => (H.rounds_same_record ε t i).symm
  simp only [sdpDualCertificate, dualVector, Rat.cast_div, Rat.cast_mul,
    Rat.cast_ofNat, hs]

/-- For a positive horizon, nonnegative rational `ε`, and positive rational `δ`, `α`, and `R`,
the integer selector weights have positive total and define an exact stopped output law. The
SDP sample scale is positive, each certificate coordinate equals that scale times its output
probability, and this law equals `sdpDualSampleDist`. -/
theorem actual_certificate (H : History T D m γ Nmax M L Q) (hT : 0 < T)
    (ε δ α R : ℚ) (hε : 0 ≤ ε) (hδ : 0 < δ) (hα : 0 < α) (hR : 0 < R)
    (j₀ : Fin m) :
    let a : ℚ := δ*α/(2*R)
    let μ := H.masses ε
    let w := intWeights (selectorMasses T a μ)
    ∃ (hW : 0 < weightTotal w),
      let F := H.samplers.withOffset j₀
      let p := (F.stopped w (blockWidth w) hW (blockWidth_capacity w)).map F.value
      let scale := sdpDualSampleScale m (δ : ℝ) (α : ℝ) (R : ℝ) j₀ (H.rounds ε) T
      0 < scale ∧
      (∀ i, sdpDualCertificate m (δ : ℝ) (α : ℝ) (R : ℝ) j₀ (H.rounds ε) T i =
        scale * (p i).toReal) ∧
      (∀ i, (p i).toReal =
        sdpDualSampleDist m (δ : ℝ) (α : ℝ) (R : ℝ) j₀ (H.rounds ε) T i) := by
  (try dsimp only)
  have ha : (0 : ℚ) < δ*α/(2*R) := by positivity
  have hμ := H.masses_nonneg ε hε
  let hW := (intWeights_normalization _ (selectorMasses_nonneg _ _ ha.le hμ)
    (selectorMasses_pos hT _ _ ha hμ)).1
  refine ⟨hW, ?_⟩
  have hd := dual_actual_output H.samplers j₀ hT (δ*α/(2*R)) (H.masses ε) ha hμ
  (try dsimp only at hd)
  have hscale : sdpDualSampleScale m (δ : ℝ) (α : ℝ) (R : ℝ) j₀ (H.rounds ε) T =
      dualScale T ((δ*α/(2*R) : ℚ) : ℝ) (fun t => (H.masses ε t : ℝ)) := by
    simp only [sdpDualSampleScale, H.certificate_eq]
    exact hd.2.1
  refine ⟨hscale.symm ▸ hd.1, ?_, ?_⟩
  · intro i
    rw [H.certificate_eq, hscale]
    exact hd.2.2 i
  · intro i
    dsimp only [sdpDualSampleDist]
    rw [H.certificate_eq, hscale, hd.2.2 i]
    exact (mul_div_cancel_left₀ _ hd.1.ne').symm

end History

end Qatlib.Concepts.SdpDuality.ConeSeparation
