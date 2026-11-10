/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.DualMixtureDensityInput
import Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimization
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
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

def densityMasses (H : History T D m γ Nmax M L Q) (ε δ α R : ℚ) : Fin (T+1) → ℚ :=
  selectorMasses T (δ*α/(2*R)) (H.masses ε)

def densityWeights (H : History T D m γ Nmax M L Q) (ε δ α R : ℚ) (n : ℕ) :
    Fin (T+1) → ℕ := gridWeights ((Qatlib.Concepts.SdpDuality.ConeSeparation.densityMasses H) ε δ α R) n

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
