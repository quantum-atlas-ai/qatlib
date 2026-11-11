/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressTrainedGrid
import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressTrainedMain

set_option backward.isDefEq.respectTransparency false

/-!
Original native pilot and selected-word main records: unconditional matching tail.
The original spinors and originalTraining determine this two-stage law.
The original all-direction Bell promise, energy bridge and actual checked
words internally bound main minority on the pilot good event. No free q,
pilot success probability or caller-supplied main conditional law is used.
The returned variable is the same sparseCountValueQ from these main records.
The target is ONE directed perfect matching. Public arithmetic hN/hbudget,
checked integer count and word checks remain explicit. This does not certify
all production selection, native address gates, two-color loss or full cost.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.TrainedOriginal
noncomputable section
open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open RetainedSpin FiniteAxisWord UniformMatching

/-- Abbreviation for Pilot Record in the partial address trained original model. -/
abbrev PilotRecord (C d r : ℕ) (α τ : ℚ) :=
  Fin 3 → Fin (PilotVector.pilotCountQ ((2*C)^d) α τ) → (Fin d → Fin (2^r)) × Bool

/-- Construction for endpoint Spin in the partial address trained original model. -/
def endpointSpin (C m d r : ℕ) [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m))) (axis : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (bit : Bool) : TrainedGrid.Edge C m d axis → Bool → ℂ :=
  fun e => complexSpinor a b c k ((TrainedGrid.matchingEquiv C m d r hN offset axis).symm (e,bit))

/-- Complete original `endpoint_mass` guarantee for `PartialAddressTrainedOriginal`; all source hypotheses and output obligations are retained. -/
theorem endpoint_mass (C m d r : ℕ) [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m))) (axis : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (bit : Bool) :
    ∀ e,qubitMass (endpointSpin C m d r hN offset axis a b c k bit e)=1 := by
  intro e
  exact complex_spinor_mass a b c k hz _

/-- Construction for target in the partial address trained original model. -/
def target (C m d r : ℕ) [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m))) (axis : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) : ℝ :=
  average (fun e => bellProbability (endpointSpin C m d r hN offset axis a b c k false e)
    (endpointSpin C m d r hN offset axis a b c k true e))

/-- Construction for original Law in the partial address trained original model. -/
def originalLaw (C m d r : ℕ) [NeZero C] [NeZero m] [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m))) (axis : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (α τ : ℚ)
    (words : PilotRecord C d r α τ → TrainedGrid.Box C d → List Gate) (n : ℕ) :
    FinDist (PilotRecord C d r α τ × (Fin n → GlobalRecord (TrainedGrid.Edge C m d axis))) :=
  TrainedMain.trainedLaw
    (NativePilot.originalTraining d r a b c k hz (PilotVector.pilotCountQ ((2*C)^d) α τ))
    (endpointSpin C m d r hN offset axis a b c k false)
    (endpointSpin C m d r hN offset axis a b c k true)
    (endpoint_mass C m d r hN offset axis a b c k hz false)
    (endpoint_mass C m d r hN offset axis a b c k hz true)
    (fun Ω e => words Ω e.1) n

/-- Complete original `original_law_native` guarantee for `PartialAddressTrainedOriginal`; all source hypotheses and output obligations are retained. -/
theorem original_law_native (C m d r : ℕ) [NeZero C] [NeZero m] [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m))) (axis : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (α τ : ℚ)
    (words : PilotRecord C d r α τ → TrainedGrid.Box C d → List Gate) (n : ℕ)
    (z : PilotRecord C d r α τ × (Fin n → GlobalRecord (TrainedGrid.Edge C m d axis))) :
    (originalLaw C m d r hN offset axis a b c k hz α τ words n).prob z=
      (NativePilot.originalTraining d r a b c k hz (PilotVector.pilotCountQ ((2*C)^d) α τ)).prob z.1*
        ∏ i,TrainedMain.wordNativeProb
          (endpointSpin C m d r hN offset axis a b c k false)
          (endpointSpin C m d r hN offset axis a b c k true)
          (fun e => words z.1 e.1) (z.2 i) := by
  exact TrainedMain.trained_law_native _ _ _ _ _ _ _ z

/-- Complete original `original_sparse_unbiased` guarantee for `PartialAddressTrainedOriginal`; all source hypotheses and output obligations are retained. -/
theorem original_sparse_unbiased (C m d r : ℕ) [NeZero C] [NeZero m] [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m))) (axis : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (α τ : ℚ)
    (words : PilotRecord C d r α τ → TrainedGrid.Box C d → List Gate) (n : ℕ) (hn : 2≤n) :
    (originalLaw C m d r hN offset axis a b c k hz α τ words n).expect
      (fun z => (CountMap.sparseCountValueQ z.2 : ℝ))=target C m d r hN offset axis a b c k := by
  exact TrainedMain.trained_sparse_unbiased _ _ _ _ _ _ _ hn

-- The word selection may be specialized at any fixed earlier classical history.
-- It is not assumed independent of this pilot or of compiler cache contents.
/-- Complete original `original_matching_tail` guarantee for `PartialAddressTrainedOriginal`; all source hypotheses and output obligations are retained. -/
theorem original_matching_tail (C m d r : ℕ) [NeZero C] [NeZero m]
    [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m))) (axis : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (p0 : ℝ) (hp : ∀ j : Fin d,bellMean a b c k (periodicDoubleShift d (2^r) j)≤p0)
    (α β τ ε : ℚ) (hα : 0<α) (hβ : 0<β) (hτ : 0<τ) (hτ1 : τ≤1/2)
    (hbudget : (d : ℝ)*((2*m : ℕ) : ℝ)^2*p0≤(τ : ℝ)/32)
    (words : PilotRecord C d r α τ → TrainedGrid.Box C d → List Gate)
    (hcheck : ∀ Ω box,AxisCertificate.check
      (fun h => PilotProjection.counterMeanQ box
        (fun i => NativePilot.recordEquiv (GridPatch.nativeGridEquiv C (2*m) d r hN offset) (Ω h i)))
      τ (words Ω box)=true)
    (n : ℕ) (hcount : checkedXYZCountQ (2*Fintype.card (TrainedGrid.Edge C m d axis)) τ ε β=some n) :
    (originalLaw C m d r hN offset axis a b c k hz α τ words n).expect
      (fun z => if (ε : ℝ)< |(CountMap.sparseCountValueQ z.2 : ℝ)-target C m d r hN offset axis a b c k|
        then (1 : ℝ) else 0)≤(α : ℝ)+(β : ℝ) := by
  classical
  let ge := GridPatch.nativeGridEquiv C (2*m) d r hN offset
  let fields := NativePilot.actualFields ge a b c k
  let boxed := fun Ω : PilotRecord C d r α τ =>
    fun h i => NativePilot.recordEquiv ge (Ω h i)
  let bad := fun Ω : PilotRecord C d r α τ =>
    (τ : ℝ)/16<PilotVector.averageError fields (boxed Ω)
  unfold originalLaw
  refine TrainedMain.trained_event_bound
    (NativePilot.originalTraining d r a b c k hz (PilotVector.pilotCountQ ((2*C)^d) α τ))
    (endpointSpin C m d r hN offset axis a b c k false)
    (endpointSpin C m d r hN offset axis a b c k true)
    (endpoint_mass C m d r hN offset axis a b c k hz false)
    (endpoint_mass C m d r hN offset axis a b c k hz true)
    (fun Ω e => words Ω e.1) n bad
    (fun ω : Fin n → GlobalRecord (TrainedGrid.Edge C m d axis) =>
      (ε : ℝ)< |(CountMap.sparseCountValueQ ω : ℝ)-target C m d r hN offset axis a b c k|)
    (α : ℝ) (β : ℝ) (Rat.cast_nonneg.mpr hβ.le) ?_ ?_
  · exact NativePilot.grid_pilot_tail C (2*m) d r hN offset a b c k hz α τ hα hτ
  · intro Ω hgood
    have he : PilotVector.averageError fields (boxed Ω)≤(τ : ℝ)/16 := le_of_not_gt hgood
    have hd : PilotVector.averageDefect fields≤(τ : ℝ)/32 :=
      (BoxGridEnergy.native_average_defect_promise C m d r hN offset a b c k hz p0 hp).trans hbudget
    have hm := AxisCertificate.checked_good_minority fields (boxed Ω) (words Ω) τ
      (fun box => NativePilot.actual_box_length ge a b c k hz box) hτ hτ1 (hcheck Ω) hd he
    have hq : average (fun e : TrainedGrid.Edge C m d axis => sectorMass
        (TrainedMain.rotated (endpointSpin C m d r hN offset axis a b c k false) (fun e => words Ω e.1) e)
        (TrainedMain.rotated (endpointSpin C m d r hN offset axis a b c k true) (fun e => words Ω e.1) e) true)≤(τ : ℝ) := by
      change average (fun e : TrainedGrid.Edge C m d axis => sectorMass
        (runSpin (words Ω e.1) (complexSpinor a b c k ((TrainedGrid.matchingEquiv C m d r hN offset axis).symm (e,false))))
        (runSpin (words Ω e.1) (complexSpinor a b c k ((TrainedGrid.matchingEquiv C m d r hN offset axis).symm (e,true)))) true)≤(τ : ℝ)
      rw [TrainedGrid.actual_matching_minority C m d r hN offset axis a b c k hz (words Ω)]
      exact hm.trans (by have ht : (0 : ℝ)<τ := Rat.cast_pos.mpr hτ; linarith)
    have hmain := CountMap.checked_sparse_value_confidence
      (TrainedMain.rotated (endpointSpin C m d r hN offset axis a b c k false) (fun e => words Ω e.1))
      (TrainedMain.rotated (endpointSpin C m d r hN offset axis a b c k true) (fun e => words Ω e.1))
      (TrainedMain.rotated_mass _ _ (endpoint_mass C m d r hN offset axis a b c k hz false))
      (TrainedMain.rotated_mass _ _ (endpoint_mass C m d r hN offset axis a b c k hz true))
      τ ε β n hcount hq
    simpa only [TrainedMain.mainLaw,TrainedMain.main_target,target] using hmain

#print axioms endpoint_mass
#print axioms originalLaw
#print axioms original_law_native
#print axioms original_sparse_unbiased
#print axioms original_matching_tail
end
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.TrainedOriginal
