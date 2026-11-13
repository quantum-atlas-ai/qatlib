/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.DualMixtureDensityInput
import Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimization

/-!
# Density evaluation of SDP dual mixtures

This module connects an SDP `History` to density evaluation of a finite mixture program.
`densityMasses` adds the rational offset mass to the recorded round masses, and `densityWeights`
converts these selector masses into integer grid weights. `sampleDist_same_record` identifies
the normalized certificate distribution with the corresponding mixture of the offset sampler
family's outputs.

For a positive number of rounds, nonnegative round precision, and positive rational certificate
parameters, `density_certificate_error` bounds the successful-output L1 error of the capped
density program by its rejection tail plus an explicit grid error. These sampling constructions
support the certificate viewpoint in quantum SDP algorithms [BrandaoSvore2017].

## Main statements

* `densityMasses` and `densityWeights`: rational selector masses and their integer grid
  approximation.
* `sampleDist_same_record`: the certificate distribution uses the sampler laws recorded by the
  same history.
* `density_certificate_error`: successful-output L1 error is at most the rejection tail plus
  twice `(T+1)/((n+1)*totalMass)`.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Concepts.MatrixWeights.ApproxGibbs

set_option autoImplicit false
namespace Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpDuality.ConeSeparation Qatlib.Concepts.MatrixWeights.ApproxGibbs
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib
open Qatlib
open scoped Classical ENNReal
variable {T D m γ Nmax M L Q : ℕ}

/-- Forms the `T+1` rational selector masses from the offset `δ*α/(2*R)` and the recorded round
masses `H.masses ε`. -/
def densityMasses (H : History T D m γ Nmax M L Q) (ε δ α R : ℚ) : Fin (T+1) → ℚ :=
  selectorMasses T (δ*α/(2*R)) (H.masses ε)

/-- Applies `gridWeights` at resolution parameter `n` to the history's rational `densityMasses`,
producing natural weights on `Fin (T+1)`. -/
def densityWeights (H : History T D m γ Nmax M L Q) (ε δ α R : ℚ) (n : ℕ) :
    Fin (T+1) → ℕ := gridWeights ((Qatlib.Concepts.SdpDuality.ConeSeparation.densityMasses H) ε δ α R) n

/-- For `T > 0`, `ε ≥ 0`, and positive rational `δ`, `α`, and `R`, expresses the normalized SDP
certificate distribution as the mixture of the offset family's real output laws weighted by
normalized `densityMasses`. -/
theorem sampleDist_same_record (H : History T D m γ Nmax M L Q)
    (hT : 0 < T) (ε δ α R : ℚ) (hε : 0 ≤ ε) (hδ : 0 < δ) (hα : 0 < α) (hR : 0 < R)
    (j₀ : Fin m) (i : Fin m) :
    sdpDualSampleDist m (δ : ℝ) (α : ℝ) (R : ℝ) j₀ (H.rounds ε) T i =
      ∑ u, (((Qatlib.Concepts.SdpDuality.ConeSeparation.densityMasses H) ε δ α R u : ℝ)/∑ v, ((Qatlib.Concepts.SdpDuality.ConeSeparation.densityMasses H) ε δ α R v : ℝ))*
        (H.samplers.withOffset j₀).realOutput u i := by
  have ha : (0 : ℚ) < δ*α/(2*R) := by positivity
  have hμ := H.masses_nonneg ε hε
  have hS := selectorMasses_pos hT _ _ ha hμ
  have hn := dual_mixture_normalized H.samplers j₀ hT _ _ hS
  have hs : sdpDualSampleScale m (δ : ℝ) (α : ℝ) (R : ℝ) j₀ (H.rounds ε) T =
      dualScale T ((δ*α/(2*R) : ℚ) : ℝ) (fun t => (H.masses ε t : ℝ)) := by
    simp only [sdpDualSampleScale, H.certificate_eq]
    exact dualVector_sum _ _ _ _
  rw [sdpDualSampleDist, H.certificate_eq, hs]
  exact hn.2 i

/-- For `T > 0`, `ε ≥ 0`, and positive rational `δ`, `α`, and `R`, bounds the successful-output
L1 error of the grid-weighted capped density program from `sdpDualSampleDist`. The bound is
`(rationalRejectMass w (blockWidth w)^fuel).toReal + 2*((T+1)/(n+1))/totalMass`, where `w`
is `densityWeights` and `totalMass` is the real sum of `densityMasses`. -/
theorem density_certificate_error (H : History T D m γ Nmax M L Q)
    (hT : 0 < T) (ε δ α R : ℚ) (hε : 0 ≤ ε) (hδ : 0 < δ) (hα : 0 < α) (hR : 0 < R)
    (j₀ : Fin m) (n fuel : ℕ) :
    let v := (Qatlib.Concepts.SdpDuality.ConeSeparation.densityMasses H) ε δ α R
    let w := (Qatlib.Concepts.SdpDuality.ConeSeparation.densityWeights H) ε δ α R n
    let F := H.samplers.withOffset j₀
    (∑ i, |(F.cappedProgram w (blockWidth w) fuel).evalDensity F.oracle F.state
      (fun j σ => (Matrix.trace σ).re * if j = some i then 1 else 0)-
        sdpDualSampleDist m (δ : ℝ) (α : ℝ) (R : ℝ) j₀ (H.rounds ε) T i|) ≤
      (rationalRejectMass w (blockWidth w)^fuel).toReal+
        2*((((T+1 : ℕ) : ℝ)/(n+1))/(∑ u, (v u : ℝ))) := by
  (try dsimp only)
  simp_rw [(Qatlib.Concepts.SdpDuality.ConeSeparation.sampleDist_same_record H) hT ε δ α R hε hδ hα hR j₀]
  have ha : (0 : ℚ) < δ*α/(2*R) := by positivity
  exact grid_capped_error (H.samplers.withOffset j₀) ((Qatlib.Concepts.SdpDuality.ConeSeparation.densityMasses H) ε δ α R)
    (selectorMasses_nonneg _ _ ha.le (H.masses_nonneg ε hε))
    (selectorMasses_pos hT _ _ ha (H.masses_nonneg ε hε)) n fuel

end Qatlib.Concepts.SdpDuality.ConeSeparation
