/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceJets

/-!
# The same finite packet and its four original answers

The execution schedule is consumed by the decoder, rather than being a
separate diagnostic count. All value and derivative data come from that
one answer list. This is not yet a total bit-cost theorem.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Decode precisely one value and three first-derivative answers. -/
def firstJetPacketOfAnswerTuple (length : ℚ) (p : ℕ)
    (answers : List (Fin 3 → ℚ)) : Option RationalFirstJetPacket :=
  match answers with
  | [v,dx,dy,dz] =>
      some (fun j => nearestDyadicNumerator (v j) p,
        fun i j => nearestDyadicNumerator (length*(![dx,dy,dz] i) j) p)
  | _ => none

/-- Actual finite execution: query the four labels and decode those same answers. -/
def sourceFirstJetExecution (source : RationalJetSource) (m1 m2 : ℚ)
    (a : Fin 3 → ℚ) (b : ℕ) : Option RationalFirstJetPacket :=
  let labels := sourceFirstJetSchedule m1 m2 a b
  let length := periodLower (b+2+rescaleSourceOverhead m1 m2)
  firstJetPacketOfAnswerTuple length (b+2) (labels.map source)

/-- The operational decoder produces the same packet whose numerical accuracy
is proved in `roundedSourceFirstJet_error`. -/
theorem sourceFirstJetExecution_eq (source : RationalJetSource) (m1 m2 : ℚ)
    (a : Fin 3 → ℚ) (b : ℕ) :
    sourceFirstJetExecution source m1 m2 a b=some (roundedSourceFirstJet source m1 m2 a b) := by
  simp only [sourceFirstJetExecution,sourceFirstJetSchedule,List.ofFn_succ,List.ofFn_zero,
    List.map_cons,List.map_nil,firstJetPacketOfAnswerTuple]
  congr 1
  apply Prod.ext
  · rfl
  · funext i j
    fin_cases i <;> rfl

/-- Every actual value/first-derivative request is at a legal physical rational
point. The common lower period is used in all four directions. -/
theorem sourceFirstJetSchedule_legal (m1 m2 : ℚ) (a : Fin 3 → ℚ) (b : ℕ)
    (ha : ∀ j, (a j : ℝ) ∈ Set.Icc 0 1) :
    ∀ q ∈ sourceFirstJetSchedule m1 m2 a b,
      ∀ j, 0 ≤ (q.1.1 j : ℝ) ∧ (q.1.1 j : ℝ) ≤ physicalPeriod := by
  intro q hq
  simp [sourceFirstJetSchedule,List.ofFn_succ] at hq
  have h := rescaleSourceQuery_legal m1 m2 a (b+2) ha
  rcases hq with rfl | rfl | rfl | rfl <;> exact h

noncomputable section
open scoped ContDiff

/-- Actual successful execution, actual packet, and all-direction errors refer
to the same original source. No packet accuracy is an extra input premise. -/
theorem sourceFirstJetExecution_correct (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (source : RationalJetSource) (hs : OriginalFirstJetAccurate v source)
    (m1 m2 : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hbounds : SourceAllRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (a : Fin 3 → ℚ) (ha : ∀ j, (a j : ℝ) ∈ Set.Icc 0 1) (b : ℕ) :
    ∃ packet, sourceFirstJetExecution source m1 m2 a b=some packet ∧
      ‖firstJetPacketVector (b+2) packet.1-v (physicalPeriod • rationalSpatialPoint a)‖ ≤
        2*(2^b : ℝ)⁻¹ ∧
      ∀ i, ‖firstJetPacketVector (b+2) (packet.2 i)-
        physicalPeriod • fderiv ℝ v (physicalPeriod • rationalSpatialPoint a) (EuclideanSpace.single i 1)‖ ≤
          2*(2^b : ℝ)⁻¹ := by
  exact ⟨_,sourceFirstJetExecution_eq source m1 m2 a b,
    roundedSourceFirstJet_error v hv source hs m1 m2 hm1 hm2 hbounds a ha b⟩

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
