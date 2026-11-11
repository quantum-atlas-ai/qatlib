/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellPlanArithmetic
import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellPlanGeometry

set_option backward.isDefEq.respectTransparency false

/-!
# Retained Bell Plan Confidence

Retained Bell Plan Confidence constructions and identities for Spinor Sampling.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Matched

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]

-- These laws are the existing native observation laws, with the rounded
-- integers computed by the public schedule rather than supplied as witnesses.
/-- Complete original `bell_sparse_integer_confidence` guarantee for `RetainedBellPlanConfidence`; all source hypotheses and output obligations are retained. -/
theorem bell_sparse_integer_confidence (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (p ε δ : ℚ) (hp : 0≤p) (hp1 : p≤1/2) (hε : 0<ε)
    (hδ : 0<δ) (hδ1 : δ<1) (hmid : ¬p≤2*ε)
    (hn : bellRecordsQ (Fintype.card S) p ε δ≤Fintype.card S)
    (hmean : bellMean a b c k τ≤(p : ℝ)) :
    (freshObservationBlocks (n:=bellRecordsQ (Fintype.card S) p ε δ)
      (m:=bellRecordsQ (Fintype.card S) p ε δ) a b c k hz τ 1).expect
      (fun ω => if (ε : ℝ)< |(clippedPooledMeanQ p τ ω : ℝ)-bellMean a b c k τ|
        then 1 else 0)≤(δ : ℝ) := by
  let M := Fintype.card S
  let n := bellRecordsQ M p ε δ
  let L : ℝ := ceilLog2Q (4/δ)
  have hM : 0<M := Fintype.card_pos
  have he : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
  have hr := bell_sparse_rates M hM p ε δ hp hp1 hε hmid
  have hexp := bell_exp_log_quarter δ hδ
  have hfirst : Real.exp (-(n : ℝ)*(n : ℝ)/(32*(M : ℝ)))≤(δ : ℝ)/4 := by
    calc
      _ = Real.exp (-((n : ℝ)^2/(32*(M : ℝ)))) := by congr 1; ring
      _ ≤ Real.exp (-L) := Real.exp_le_exp.mpr (neg_le_neg hr.1)
      _ ≤ _ := hexp
  have hsecond : Real.exp (-((n : ℝ)*(n : ℝ)/(32*(M : ℝ)))*(ε : ℝ)^2/
      (4*((p : ℝ)+(ε : ℝ))))≤(δ : ℝ)/4 := by
    calc
      _ = Real.exp (-(((n : ℝ)^2/(32*(M : ℝ)))*(ε : ℝ)^2/
          (4*((p : ℝ)+(ε : ℝ))))) := by congr 1; ring
      _ ≤ Real.exp (-L) := Real.exp_le_exp.mpr (neg_le_neg hr.2)
      _ ≤ _ := hexp
  have ht := clipped_pooled_sparse_tail (n:=n) (m:=n) a b c k hz τ
    (bell_records_pos M hM p ε δ hp hε hδ hδ1) hn hn p (ε : ℝ) hmean he
  exact ht.trans (by linarith)

/-- Complete original `bell_dense_integer_confidence` guarantee for `RetainedBellPlanConfidence`; all source hypotheses and output obligations are retained. -/
theorem bell_dense_integer_confidence (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (p ε δ : ℚ) (hp : 0≤p) (hp1 : p≤1/2) (hε : 0<ε)
    (hδ : 0<δ) (hmid : ¬p≤2*ε)
    (hmean : bellMean a b c k τ≤(p : ℝ)) :
    (freshObservationBlocks (n:=Fintype.card S) (m:=Fintype.card S) a b c k hz τ
      (bellBlocksQ (Fintype.card S) p ε δ)).expect
      (fun ω => if (ε : ℝ)< |(clippedPooledMeanQ p τ ω : ℝ)-bellMean a b c k τ|
        then 1 else 0)≤(δ : ℝ) := by
  let M := Fintype.card S
  let K := bellBlocksQ M p ε δ
  let L : ℝ := ceilLog2Q (4/δ)
  have hr := bell_dense_rates M Fintype.card_pos p ε δ hp hp1 hε hmid
  have hexp := bell_exp_log_quarter δ hδ
  have hfirst : Real.exp (-(K : ℝ)*(M : ℝ)/64)≤(δ : ℝ)/4 := by
    calc
      _ = Real.exp (-((K : ℝ)*(M : ℝ)/64)) := by congr 1; ring
      _ ≤ Real.exp (-L) := Real.exp_le_exp.mpr (neg_le_neg hr.1)
      _ ≤ _ := hexp
  have hsecond : Real.exp (-((K : ℝ)*(M : ℝ)/8)*(ε : ℝ)^2/
      (4*((p : ℝ)+(ε : ℝ))))≤(δ : ℝ)/4 := by
    calc
      _ = Real.exp (-(((K : ℝ)*(M : ℝ)/8)*(ε : ℝ)^2/
          (4*((p : ℝ)+(ε : ℝ))))) := by congr 1; ring
      _ ≤ Real.exp (-L) := Real.exp_le_exp.mpr (neg_le_neg hr.2)
      _ ≤ _ := hexp
  have ht := clipped_pooled_dense_tail a b c k hz τ K p (ε : ℝ) hmean
    (Rat.cast_pos.mpr hε)
  have hδR : (0 : ℝ)<δ := Rat.cast_pos.mpr hδ
  exact ht.trans (by linarith)

/-- Construction for planned Bell Mean Q in the retained bell plan confidence model. -/
def plannedBellMeanQ (q : BellPlanQ) (τ : S → S)
    (ω : Fin q.blocks → CohortObservation q.records q.records τ) : ℚ :=
  match q.mode with
  | .identity => 0
  | .midpoint => q.meanUpper/2
  | .sparse | .pooled => clippedPooledMeanQ q.meanUpper τ ω

/-- Keep the plan as one argument while rewriting its dependent data carrier. -/
private def plannedBellFailure (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (ε : ℝ) (q : BellPlanQ) : ℝ :=
  (freshObservationBlocks (n:=q.records) (m:=q.records) a b c k hz τ q.blocks).expect
    (fun ω => if ε< |(plannedBellMeanQ q τ ω : ℝ)-bellMean a b c k τ| then 1 else 0)

-- All four branches return the same public plan's output. The sole geometric
-- premise below is discharged by the concrete periodic-grid endpoint.
/-- Complete original `bell_plan_confidence` guarantee for `RetainedBellPlanConfidence`; all source hypotheses and output obligations are retained. -/
theorem bell_plan_confidence (side : ℕ) (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (p ε δ : ℚ) (hp : 0≤p) (hp1 : p≤1/2) (hε : 0<ε)
    (hδ : 0<δ) (hδ1 : δ<1) (hmean : bellMean a b c k τ≤(p : ℝ))
    (hidentity : side≤2 → τ=Equiv.refl S) :
    let q := bellPlanQ side (Fintype.card S) p ε δ
    (freshObservationBlocks (n:=q.records) (m:=q.records) a b c k hz τ q.blocks).expect
      (fun ω => if (ε : ℝ)< |(plannedBellMeanQ q τ ω : ℝ)-bellMean a b c k τ|
        then 1 else 0)≤(δ : ℝ) := by
  have he : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
  have hd : (0 : ℝ)≤δ := le_of_lt (Rat.cast_pos.mpr hδ)
  change plannedBellFailure a b c k hz τ (ε : ℝ)
    (bellPlanQ side (Fintype.card S) p ε δ)≤(δ : ℝ)
  by_cases hside : side≤2
  · have ht : bellMean a b c k τ=0 := by
      rw [hidentity hside]
      exact bell_mean_identity a b c k
    have hplan : bellPlanQ side (Fintype.card S) p ε δ=⟨.identity,0,0,0,p,ε,δ⟩ := by
      simp [bellPlanQ,hside]
    rw [hplan]
    simpa only [plannedBellFailure,plannedBellMeanQ,ht,Rat.cast_zero,sub_self,abs_zero,
      ite_eq_right (not_lt.mpr he.le),FinDist.expect,mul_zero,Finset.sum_const_zero] using hd
  · by_cases hmid : p≤2*ε
    · have ha := bell_midpoint_accuracy p ε (bellMean a b c k τ)
        (bell_mean_nonneg a b c k hz τ) hmean hmid
      have hplan : bellPlanQ side (Fintype.card S) p ε δ=⟨.midpoint,0,0,0,p,ε,δ⟩ := by
        simp [bellPlanQ,hside,hmid]
      rw [hplan]
      simpa only [plannedBellFailure,plannedBellMeanQ,ite_eq_right (not_lt.mpr ha),FinDist.expect,
        mul_zero,Finset.sum_const_zero] using hd
    · by_cases hn : bellRecordsQ (Fintype.card S) p ε δ≤Fintype.card S
      · have hplan : bellPlanQ side (Fintype.card S) p ε δ=
            ⟨.sparse,bellRecordsQ (Fintype.card S) p ε δ,1,
              2*bellRecordsQ (Fintype.card S) p ε δ,p,ε,δ⟩ := by
          simp [bellPlanQ,hside,hmid,hn]
        rw [hplan]
        simpa only [plannedBellFailure,plannedBellMeanQ] using
          bell_sparse_integer_confidence a b c k hz τ p ε δ hp hp1 hε hδ hδ1 hmid hn hmean
      · have hplan : bellPlanQ side (Fintype.card S) p ε δ=
            ⟨.pooled,Fintype.card S,bellBlocksQ (Fintype.card S) p ε δ,
              2*Fintype.card S*bellBlocksQ (Fintype.card S) p ε δ,p,ε,δ⟩ := by
          simp [bellPlanQ,hside,hmid,hn]
        rw [hplan]
        simpa only [plannedBellFailure,plannedBellMeanQ] using
          bell_dense_integer_confidence a b c k hz τ p ε δ hp hp1 hε hδ hmid hmean

-- This is the actual physical site type and two-step periodic shift.
-- No success-probability, positive-match or caller-selected budget certificate
-- is an input to this endpoint.
/-- Complete original `periodic_bell_plan_confidence` guarantee for `RetainedBellPlanConfidence`; all source hypotheses and output obligations are retained. -/
theorem periodic_bell_plan_confidence (d N : ℕ) [NeZero N] (j : Fin d)
    (a b c k : (Fin d → Fin N) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (p ε δ : ℚ) (hp : 0≤p) (hp1 : p≤1/2) (hε : 0<ε)
    (hδ : 0<δ) (hδ1 : δ<1)
    (hmean : bellMean a b c k (periodicDoubleShift d N j)≤(p : ℝ)) :
    let q := bellPlanQ N (N^d) p ε δ
    (freshObservationBlocks (n:=q.records) (m:=q.records) a b c k hz
      (periodicDoubleShift d N j) q.blocks).expect
      (fun ω => if (ε : ℝ)< |(plannedBellMeanQ q (periodicDoubleShift d N j) ω : ℝ)-
        bellMean a b c k (periodicDoubleShift d N j)| then 1 else 0)≤(δ : ℝ) := by
  change plannedBellFailure a b c k hz (periodicDoubleShift d N j) (ε : ℝ)
    (bellPlanQ N (N^d) p ε δ)≤(δ : ℝ)
  have ht :=
    bell_plan_confidence N a b c k hz (periodicDoubleShift d N j) p ε δ hp hp1 hε hδ hδ1
      hmean (periodic_double_shift_small_side d N j)
  change plannedBellFailure a b c k hz (periodicDoubleShift d N j) (ε : ℝ)
    (bellPlanQ N (Fintype.card (Fin d → Fin N)) p ε δ)≤(δ : ℝ) at ht
  rw [periodic_grid_card] at ht
  exact ht

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_sparse_integer_confidence
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_dense_integer_confidence
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_plan_confidence
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.periodic_bell_plan_confidence
