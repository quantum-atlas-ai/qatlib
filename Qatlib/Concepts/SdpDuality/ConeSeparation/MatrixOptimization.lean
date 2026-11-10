/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.MatrixOptimizationDual
import Qatlib.Concepts.MatrixWeights.ApproxGibbs
import Qatlib.Concepts.SdpDuality.ConeSeparation.SdpRunMacros
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

structure History (T D m γ Nmax M L Q : ℕ) where
  samplers : Family T D m
  records : Fin T → Step2Search m γ Nmax M L Q
  candidate : Fin T → Fin γ
  massIndex : Fin T → Fin Nmax
  law_eq : ∀ t i, (records t).law (candidate t) i = samplers.realOutput t i

namespace History

def masses (H : History T D m γ Nmax M L Q) (ε : ℚ) (t : Fin T) : ℚ :=
  ε * ((H.massIndex t).val + 1)

theorem masses_nonneg (H : History T D m γ Nmax M L Q) (ε : ℚ) (hε : 0 ≤ ε) :
    ∀ t, 0 ≤ H.masses ε t := fun t => mul_nonneg hε (by positivity)

noncomputable def rounds (H : History T D m γ Nmax M L Q) (ε : ℚ)
    (t : ℕ) (i : Fin m) : ℝ :=
  if h : t < T then
    (H.records ⟨t,h⟩).roundVector (ε : ℝ) (H.candidate ⟨t,h⟩) (H.massIndex ⟨t,h⟩) i
  else 0

theorem rounds_same_record (H : History T D m γ Nmax M L Q) (ε : ℚ)
    (t : Fin T) (i : Fin m) :
    H.rounds ε t i = (H.masses ε t : ℝ) * H.samplers.realOutput t i := by
  simp [rounds, t.isLt, Step2Search.roundVector, Step2Search.gridMass,
    masses, H.law_eq]

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
