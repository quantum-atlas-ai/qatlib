/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenVariableTimeAlgorithmStat
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenCascadeAux
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.AverageStopTailBoundVari
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Sector transport through growing-stop cascades

This module develops measurement-mass identities for the good, bad, running, and live sectors of
a growing variable-time pipeline. It proves monotonicity and comparison bounds for the original
evolution, then transports sector masses through amplification cascades used in the analysis of
[Ambainis2012].

## Main statements

* `rdvt_sector_step`: one-step mass conservation and bad-sector growth bounds.
* `rdvt_sector_bridge`: comparison of prefix live mass with final good mass.
* `rdvt_cascade_input_live`: a common scaling factor for consecutive live-sector masses.
* `rdvt_cascade_good_eq_live`: equality of final good and live mass after complete stopping.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Papers.VarTimeAmpAmp10.StopModel

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability

set_option autoImplicit false
set_option maxHeartbeats 900000
open Matrix
open scoped Classical BigOperators

variable {C : Type} [Fintype C] [DecidableEq C]

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
noncomputable section
omit [DecidableEq C] in

/-- States agreeing at every index in `S` have equal measurement mass on `S`. -/
theorem rdvt_prob_congr {ψ χ : QState (VtSpace C)} (S : Finset (VtSpace C))
    (h : ∀ p ∈ S, ψ p = χ p) : MeasureProb ψ S = MeasureProb χ S := by
  unfold MeasureProb BornProb
  exact Finset.sum_congr rfl fun p hp => by rw [h p hp]
end
noncomputable section
omit [DecidableEq C] in

/-- Every index in the bad sector has flag `vtBadFlag`. -/
theorem rdvt_bad_flag (p : VtSpace C) (hp : p ∈ badSet C) : p.1 = vtBadFlag :=
  (Finset.mem_filter.mp hp).2
end
noncomputable section
omit [DecidableEq C] in

/-- Every index in the good sector has flag `vtGoodFlag`. -/
theorem rdvt_good_flag (p : VtSpace C) (hp : p ∈ goodSet C) : p.1 = vtGoodFlag :=
  (Finset.mem_filter.mp hp).2
end
noncomputable section
omit [DecidableEq C] in

/-- Every index in the running sector has flag `vtRunningFlag`. -/
theorem rdvt_running_flag (p : VtSpace C) (hp : p ∈ runningSet C) : p.1 = vtRunningFlag :=
  (Finset.mem_filter.mp hp).2
end
noncomputable section
omit [DecidableEq C] in

/-- The good and bad sectors are disjoint. -/
theorem rdvt_good_bad_disjoint : Disjoint (goodSet C) (badSet C) :=
  Finset.disjoint_left.mpr fun p hp hq =>
    (by decide : vtGoodFlag ≠ vtBadFlag) ((rdvt_good_flag p hp).symm.trans (rdvt_bad_flag p hq))
end
noncomputable section
omit [DecidableEq C] in

/-- The good and running sectors are disjoint. -/
theorem rdvt_good_running_disjoint : Disjoint (goodSet C) (runningSet C) :=
  Finset.disjoint_left.mpr fun p hp hq =>
    (by decide : vtGoodFlag ≠ vtRunningFlag)
      ((rdvt_good_flag p hp).symm.trans (rdvt_running_flag p hq))
end
noncomputable section
omit [DecidableEq C] in

/-- The bad and running sectors are disjoint. -/
theorem rdvt_bad_running_disjoint : Disjoint (badSet C) (runningSet C) :=
  Finset.disjoint_left.mpr fun p hp hq =>
    (by decide : vtBadFlag ≠ vtRunningFlag)
      ((rdvt_bad_flag p hp).symm.trans (rdvt_running_flag p hq))
end
noncomputable section

/-- The live and bad sectors are disjoint. -/
theorem rdvt_live_bad_disjoint : Disjoint (liveSet C) (badSet C) :=
  Finset.disjoint_left.mpr fun p hp hq => (nonlive_iff_bad p).mpr (rdvt_bad_flag p hq) hp
end
noncomputable section

/-- The live and bad sectors together cover the full basis index set. -/
theorem rdvt_live_bad_union : liveSet C ∪ badSet C = Finset.univ := by
  ext p
  obtain ⟨f, x⟩ := p
  simp only [liveSet, Finset.mem_union, goodSet, badSet, runningSet, Finset.mem_filter,
    Finset.mem_univ, true_and]
  fin_cases f <;> simp [vtGoodFlag, vtRunningFlag, vtBadFlag]
end
noncomputable section

/-- For a normalized state, the live and bad sector masses sum to one. -/
theorem rdvt_live_bad_univ (ψ : QState (VtSpace C)) (hnorm : Normalized ψ) :
    MeasureProb ψ (liveSet C) + MeasureProb ψ (badSet C) = 1 := by
  rw [← measureProb_union ψ rdvt_live_bad_disjoint, rdvt_live_bad_union, measureProb_univ hnorm]
end
noncomputable section

/-- A unitary matrix preserves the total measurement mass of any state. -/
theorem rdvt_unitary_mass {U : Matrix (VtSpace C) (VtSpace C) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (VtSpace C) ℂ) (x : QState (VtSpace C)) :
    MeasureProb (ApplyGate U x) Finset.univ = MeasureProb x Finset.univ := by
  have h1 : MeasureProb (ApplyGate U x) Finset.univ = ∑ i, Complex.normSq ((ApplyGate U x) i) := by
    simp [MeasureProb, BornProb, Complex.normSq_eq_norm_sq]
  have h2 : MeasureProb x Finset.univ = ∑ i, Complex.normSq (x i) := by
    simp [MeasureProb, BornProb, Complex.normSq_eq_norm_sq]
  rw [h1, h2]
  exact sum_normSq_mulVec_of_mem_unitaryGroup hU x
end
noncomputable section

/-- The total measurement mass of a state collapsed to `S` equals its original measurement mass
on `S`. -/
theorem rdvt_collapse_mass (ψ : QState (VtSpace C)) (S : Finset (VtSpace C)) :
    MeasureProb (Collapse ψ S) Finset.univ = MeasureProb ψ S := by
  unfold MeasureProb
  simp only [bornProb_collapse]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
end
noncomputable section
omit [DecidableEq C] in

/-- Gate application distributes over addition of states. -/
theorem rdvt_apply_add (U : Matrix (VtSpace C) (VtSpace C) ℂ) (a b : QState (VtSpace C)) :
    ApplyGate U (a+b) = ApplyGate U a+ApplyGate U b := by
  simp only [ApplyGate, Matrix.mulVec_add]
end
noncomputable section

/-- For disjoint sets `S` and `T`, the sum of the two collapsed states equals collapse onto
their union. -/
theorem rdvt_collapse_union (ψ : QState (VtSpace C)) (S T : Finset (VtSpace C))
    (h : Disjoint S T) : Collapse ψ S+Collapse ψ T = Collapse ψ (S∪T) := by
  funext p
  by_cases hS : p ∈ S
  · have hT : p ∉ T := fun hh => Finset.disjoint_left.mp h hS hh
    simp [collapse_apply, hS, hT]
  · by_cases hT : p ∈ T
    · simp [collapse_apply, hS, hT]
    · simp [collapse_apply, hS, hT]
end
noncomputable section
omit [DecidableEq C] in

/-- Adding a state that vanishes on `S` does not change the other state's measurement mass on
`S`. -/
theorem rdvt_sector_add_zero_left (a b : QState (VtSpace C)) (S : Finset (VtSpace C))
    (h : ∀ p ∈ S, a p = 0) : MeasureProb (a+b) S = MeasureProb b S :=
  rdvt_prob_congr S fun p hp => by rw [Pi.add_apply, h p hp, _root_.zero_add]
end
noncomputable section
omit [DecidableEq C] in

/-- Adding a state that vanishes on `S` to the right does not change the left state's
measurement mass on `S`. -/
theorem rdvt_sector_add_zero_right (a b : QState (VtSpace C)) (S : Finset (VtSpace C))
    (h : ∀ p ∈ S, b p = 0) : MeasureProb (a+b) S = MeasureProb a S :=
  rdvt_prob_congr S fun p hp => by rw [Pi.add_apply, h p hp, _root_.add_zero]
end
noncomputable section
omit [DecidableEq C] in

/-- If at least one of two states vanishes at every index of `S`, their sum's measurement mass
on `S` is the sum of their masses. -/
theorem rdvt_sector_add (a b : QState (VtSpace C)) (S : Finset (VtSpace C))
    (h : ∀ p ∈ S, a p = 0 ∨ b p = 0) :
    MeasureProb (a+b) S = MeasureProb a S+MeasureProb b S := by
  have key : ∀ p ∈ S, ‖(a+b) p‖^2 = ‖a p‖^2+‖b p‖^2 := by
    intro p hp
    rcases h p hp with h0 | h0
    · simp [h0]
    · simp [h0]
  unfold MeasureProb BornProb
  rw [Finset.sum_congr rfl key, ← Finset.sum_add_distrib]
end
noncomputable section

/-- A growing stage fixes any state supported on its previously reached stopped set. -/
theorem rdvt_fixes_reached {history : ℕ → Finset C} {k : ℕ}
    {U : Matrix (VtSpace C) (VtSpace C) ℂ} (hU : IsGrowingVtStage history k U)
    (x : QState (VtSpace C)) (hx : ∀ p, x p ≠ 0 → p ∈ reachedStoppedSet history k) :
    ApplyGate U x = x := by
  funext q
  simp only [ApplyGate, Matrix.mulVec, dotProduct]
  have ht (p : VtSpace C) : U q p*x p = if q = p then x p else 0 := by
    by_cases h0 : x p = 0
    · simp [h0]
    · rw [hU.2 p (hx p h0) q]
      split_ifs <;> simp
  simp_rw [ht]
  simp
end
noncomputable section

/-- A growing stage preserves each coordinate indexed by its previously reached stopped set. -/
theorem rdvt_stage_row {history : ℕ → Finset C} {k : ℕ}
    {U : Matrix (VtSpace C) (VtSpace C) ℂ} (hU : IsGrowingVtStage history k U)
    (q : VtSpace C) (hq : q ∈ reachedStoppedSet history k) (x : QState (VtSpace C)) :
    ApplyGate U x q = x q := by
  have hr (p : VtSpace C) :
      U q p = if q = p then (1:ℂ) else 0 := growing_stage_reached_row hU q hq p
  simp only [ApplyGate, Matrix.mulVec, dotProduct, hr]
  simp
end
noncomputable section

/-- For a legal supported growing pipeline, one stage preserves combined live and bad mass,
increases bad mass monotonically, and bounds that increase by the decrease in running mass. -/
theorem rdvt_sector_step (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (hl : GrowingVtLegal stages history)
    (j₀ : VtSpace C) (hs : GrowingVtSupported stages history j₀) (k : ℕ)
    (hk : k < stages.length) :
    MeasureProb (vtState stages (k+1) (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)
        + MeasureProb (vtState stages (k+1) (Qatlib.Foundations.PureStateMath.Ket j₀)) (badSet C)
      = MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)
        + MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (badSet C) ∧
    MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (badSet C)
      ≤ MeasureProb (vtState stages (k+1) (Qatlib.Foundations.PureStateMath.Ket j₀)) (badSet C) ∧
    MeasureProb (vtState stages (k+1) (Qatlib.Foundations.PureStateMath.Ket j₀)) (badSet C)
        - MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (badSet C)
      ≤ MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C)
        - MeasureProb (vtState stages (k+1) (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C) := by
  have hU := hl.2.2.2 k hk
  have hkn : k ≤ stages.length := by omega
  have he : vtState stages (k+1) (Qatlib.Foundations.PureStateMath.Ket j₀)
      = ApplyGate stages[k] (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) := by
    rw [vtState, vt_prefix_step stages k hk, ← Matrix.mulVec_mulVec]
    rfl

  set φ := vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀) with hφ
  set live := Collapse φ (liveSet C) with hlive
  set old := φ-live with hold
  have holdsup : ∀ p, old p ≠ 0 → p.1 = vtBadFlag ∧ p.2 ∈ history k :=
    original_bad_support stages history j₀ hs k hkn
  have holdfix : ApplyGate stages[k] old = old :=
    growing_stage_fixes_bad history k stages[k] hU old holdsup
  have hlive0 : ∀ p ∈ badSet C, live p = 0 := fun p hp => by
    rw [hlive, collapse_apply]
    exact if_neg ((nonlive_iff_bad p).mpr (rdvt_bad_flag p hp))
  have hold0r : ∀ p ∈ runningSet C, old p = 0 := by
    intro p hp
    by_contra h
    obtain ⟨hf, _⟩ := holdsup p h
    have hbm : p ∈ badSet C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
    exact Finset.disjoint_left.mp rdvt_bad_running_disjoint hbm hp
  have hbadold : MeasureProb old (badSet C) = MeasureProb φ (badSet C) :=
    rdvt_prob_congr (badSet C) fun p hp => by
      have h0 : live p = 0 := hlive0 p hp
      simp only [hold, Pi.sub_apply, h0, sub_zero]
  have hφlive : live+old = φ := by
    funext p
    simp only [Pi.add_apply, hold, Pi.sub_apply]
    ring
  have hdecomp : vtState stages (k+1) (Qatlib.Foundations.PureStateMath.Ket j₀) = ApplyGate stages[k] live+old := by
    rw [he, ← hφlive, rdvt_apply_add, holdfix]
  have hrun' : MeasureProb (vtState stages (k+1) (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C)
      = MeasureProb (ApplyGate stages[k] live) (runningSet C) := by
    rw [hdecomp]
    exact rdvt_sector_add_zero_right _ _ _ hold0r

  have hrow0 : ∀ p ∈ badSet C, old p ≠ 0 → ApplyGate stages[k] live p = 0 := by
    intro p hp hne
    obtain ⟨hf, hm⟩ := holdsup p hne
    have hre : p ∈ reachedStoppedSet history k :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hf]; decide, hm⟩
    rw [rdvt_stage_row hU p hre live]
    exact hlive0 p hp
  have hbad' : MeasureProb (vtState stages (k+1) (Qatlib.Foundations.PureStateMath.Ket j₀)) (badSet C)
      = MeasureProb (ApplyGate stages[k] live) (badSet C)+MeasureProb φ (badSet C) := by
    rw [hdecomp]
    rw [rdvt_sector_add _ _ _ (fun p hp => by
      by_cases h0 : old p = 0
      · exact Or.inr h0
      · exact Or.inl (hrow0 p hp h0)), hbadold]
  refine ⟨?_, ?_, ?_⟩
  · rw [← measureProb_union _ rdvt_live_bad_disjoint,
      ← measureProb_union _ rdvt_live_bad_disjoint, rdvt_live_bad_union, he,
      rdvt_unitary_mass hU.1]
  · rw [hbad']
    have hnn : 0 ≤ MeasureProb (ApplyGate stages[k] live) (badSet C) :=
      Finset.sum_nonneg fun i _ => bornProb_nonneg _ i
    linarith
  · have hgsup : ∀ p, Collapse φ (goodSet C) p ≠ 0 → p ∈ reachedStoppedSet history k := by
      intro p hp
      rw [collapse_apply] at hp
      split_ifs at hp with hg
      · have hne : p.1 ≠ vtRunningFlag := by rw [rdvt_good_flag p hg]; decide
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, (hs k hkn p hp).1 hne⟩
      · exact absurd rfl hp
    have hgfix : ApplyGate stages[k] (Collapse φ (goodSet C)) = Collapse φ (goodSet C) :=
      rdvt_fixes_reached hU _ hgsup
    have hgr : Collapse φ (goodSet C)+Collapse φ (runningSet C) = live := by
      have hu := rdvt_collapse_union φ (goodSet C) (runningSet C) rdvt_good_running_disjoint
      rw [← liveSet] at hu
      exact hu
    have hUl : ApplyGate stages[k] live
        = Collapse φ (goodSet C)+ApplyGate stages[k] (Collapse φ (runningSet C)) := by
      conv_lhs => rw [← hgr]
      rw [rdvt_apply_add, hgfix]
    have hgood0b : ∀ p ∈ badSet C, Collapse φ (goodSet C) p = 0 := by
      intro p hp
      rw [collapse_apply]
      by_cases hg : p ∈ goodSet C
      · exact (Finset.disjoint_left.mp rdvt_good_bad_disjoint hg hp).elim
      · rw [if_neg hg]
    have hgood0r : ∀ p ∈ runningSet C, Collapse φ (goodSet C) p = 0 := by
      intro p hp
      rw [collapse_apply]
      by_cases hg : p ∈ goodSet C
      · exact (Finset.disjoint_left.mp rdvt_good_running_disjoint hg hp).elim
      · rw [if_neg hg]
    have hbp : MeasureProb (ApplyGate stages[k] live) (badSet C)
        = MeasureProb (ApplyGate stages[k] (Collapse φ (runningSet C))) (badSet C) := by
      rw [hUl]
      exact rdvt_sector_add_zero_left _ _ _ hgood0b
    have hrp : MeasureProb (ApplyGate stages[k] live) (runningSet C)
        = MeasureProb (ApplyGate stages[k] (Collapse φ (runningSet C))) (runningSet C) := by
      rw [hUl]
      exact rdvt_sector_add_zero_left _ _ _ hgood0r
    rw [hbad', hrun', hbp, hrp]
    have hsplit : MeasureProb (ApplyGate stages[k] (Collapse φ (runningSet C))) (badSet C)
        + MeasureProb (ApplyGate stages[k] (Collapse φ (runningSet C))) (runningSet C)
      = MeasureProb (ApplyGate stages[k] (Collapse φ (runningSet C))) (badSet C∪runningSet C) :=
      (measureProb_union _ rdvt_bad_running_disjoint).symm
    have hle : MeasureProb (ApplyGate stages[k] (Collapse φ (runningSet C)))
        (badSet C∪runningSet C)
      ≤ MeasureProb (ApplyGate stages[k] (Collapse φ (runningSet C))) (Finset.univ) :=
      measureProb_mono _ (Finset.subset_univ _)
    rw [rdvt_unitary_mass hU.1, rdvt_collapse_mass] at hle
    linarith
end
noncomputable section

/-- If a legal supported pipeline has no final running mass, each prefix live mass lies between
the final good mass and that mass plus the prefix running mass. -/
theorem rdvt_sector_bridge (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (hl : GrowingVtLegal stages history)
    (j₀ : VtSpace C) (hs : GrowingVtSupported stages history j₀)
    (hrun : MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C) = 0)
    (k : ℕ) (hk : k ≤ stages.length) :
    MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C)
      ≤ MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) ∧
    MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)
      ≤ MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C)
        +MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C) := by
  set m := stages.length with hm
  set Ψ := vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀) with hΨ
  have hnorm (i : ℕ) : Normalized (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) :=
    normalized_applyGate (growing_prefix_unitary stages history hl i) (normalized_ket j₀)
  have hsplit (i : ℕ) :
      MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)
        +MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (badSet C) = 1 :=
    rdvt_live_bad_univ _ (hnorm i)
  have hsm : MeasureProb Ψ (liveSet C) = MeasureProb Ψ (goodSet C) := by
    rw [liveSet, measureProb_union Ψ rdvt_good_running_disjoint, hrun, _root_.add_zero]
  have hbadm : MeasureProb Ψ (badSet C) = 1-MeasureProb Ψ (goodSet C) := by
    have h := hsplit m
    rw [hsm] at h
    linarith
  have hmono : ∀ d, k+d ≤ stages.length →
      MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (badSet C)
        ≤ MeasureProb (vtState stages (k+d) (Qatlib.Foundations.PureStateMath.Ket j₀)) (badSet C) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      intro hd
      rw [← Nat.add_assoc]
      exact le_trans (ih (by omega))
        (rdvt_sector_step stages history hl j₀ hs (k+d) (by omega)).2.1
  have htele : ∀ d, k+d ≤ stages.length →
      MeasureProb (vtState stages (k+d) (Qatlib.Foundations.PureStateMath.Ket j₀)) (badSet C)
        -MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (badSet C)
      ≤ MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C)
        -MeasureProb (vtState stages (k+d) (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      intro hd
      rw [← Nat.add_assoc]
      have h1 := ih (by omega)
      have h2 := (rdvt_sector_step stages history hl j₀ hs (k+d) (by omega)).2.2
      linarith
  have hd : k+(m-k) = m := by omega
  have hbadk := hmono (m-k) (by omega)
  have htel := htele (m-k) (by omega)
  rw [hd] at hbadk htel
  rw [hrun, sub_zero] at htel
  have hs := hsplit k
  constructor
  · linarith
  · linarith

end
noncomputable section
omit [DecidableEq C] in

/-- Gate application commutes with complex scalar multiplication. -/
theorem rdvt_apply_smul (U : Matrix (VtSpace C) (VtSpace C) ℂ) (a : ℂ) (ψ : QState (VtSpace C)) :
    ApplyGate U (a • ψ) = a • ApplyGate U ψ := by
  simp only [ApplyGate, Matrix.mulVec_smul]
end
noncomputable section
omit [DecidableEq C] in

/-- Gate application distributes over subtraction of states. -/
theorem rdvt_apply_sub (U : Matrix (VtSpace C) (VtSpace C) ℂ) (a b : QState (VtSpace C)) :
    ApplyGate U (a-b) = ApplyGate U a-ApplyGate U b := by
  simp only [ApplyGate, Matrix.mulVec_sub]
end
noncomputable section
omit [DecidableEq C] in

/-- Scaling a state by `a` multiplies its sector mass by `Complex.normSq a`. -/
theorem rdvt_smul_sector (a : ℂ) (ψ : QState (VtSpace C)) (S : Finset (VtSpace C)) :
    MeasureProb (a • ψ) S = Complex.normSq a*MeasureProb ψ S := by
  unfold MeasureProb BornProb
  simp only [Pi.smul_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.normSq_eq_norm_sq, norm_smul]
  ring
end
noncomputable section

/-- Collapsing a state to `S` preserves its measurement mass on `S`. -/
theorem rdvt_collapse_sector (ψ : QState (VtSpace C)) (S : Finset (VtSpace C)) :
    MeasureProb (Collapse ψ S) S = MeasureProb ψ S := by
  unfold MeasureProb
  simp only [bornProb_collapse]
  rw [Finset.sum_ite_mem]
  simp
end
noncomputable section

/-- For a legal supported pipeline starting in the running sector, the live mass of any valid
cascade prefix is a squared scalar multiple of the corresponding original prefix live mass. -/
theorem rdvt_cascade_live (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (hl : GrowingVtLegal stages history) (j₀ : VtSpace C)
    (hj : j₀.1 = vtRunningFlag) (hs : GrowingVtSupported stages history j₀)
    (sched : ℕ → ℕ) (i : ℕ) (hi : i ≤ stages.length) :
    ∃ α : ℂ,
      MeasureProb (dataVtWordState stages history j₀ (cascadeWord sched i)) (liveSet C)
        = Complex.normSq α*MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) := by
  obtain ⟨a, b, hstate, hsup, hbl⟩ :=
    ((cascadePrefixTransport_answer C stages history hl j₀ hj hs sched).1 i hi).2.2
  have hb0 : ∀ p ∈ liveSet C, b p = 0 := fun p hp => by
    have h := congrFun hbl p
    simpa [collapse_apply, hp] using! h
  refine ⟨a, ?_⟩
  rw [hstate, rdvt_sector_add_zero_right _ _ _ hb0, rdvt_smul_sector, rdvt_collapse_sector]
end
noncomputable section

/-- For a legal supported pipeline starting in the running sector, the full cascade's good mass
is a squared scalar multiple of the original final good mass. -/
theorem rdvt_cascade_good (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (hl : GrowingVtLegal stages history) (j₀ : VtSpace C)
    (hj : j₀.1 = vtRunningFlag) (hs : GrowingVtSupported stages history j₀)
    (sched : ℕ → ℕ) :
    ∃ α : ℂ,
      MeasureProb (dataVtWordState stages history j₀ (cascadeWord sched stages.length))
        (goodSet C)
        = Complex.normSq α*MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C) := by
  obtain ⟨a, hray⟩ := (cascadePrefixTransport_answer C stages history hl j₀ hj hs sched).2.2
  refine ⟨a, ?_⟩
  have hmass : MeasureProb (dataVtWordState stages history j₀ (cascadeWord sched stages.length))
      (goodSet C)
      = MeasureProb (Collapse (dataVtWordState stages history j₀
      (cascadeWord sched stages.length)) (goodSet C)) (goodSet C) :=
    (rdvt_collapse_sector _ _).symm
  rw [hmass, hray, rdvt_smul_sector, rdvt_collapse_sector]
end
noncomputable section

/-- For a legal supported pipeline starting in the running sector, appending the next forward
stage to a cascade prefix gives live mass proportional to the original next-stage live mass
by a squared scalar factor. -/
theorem rdvt_input_live (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (hl : GrowingVtLegal stages history) (j₀ : VtSpace C)
    (hj : j₀.1 = vtRunningFlag) (hs : GrowingVtSupported stages history j₀)
    (sched : ℕ → ℕ) (i : ℕ) (hi : i < stages.length) :
    ∃ α : ℂ,
      MeasureProb (dataVtWordState stages history j₀
        (cascadeWord sched i++[DataVtStep.stageF i])) (liveSet C)
        = Complex.normSq α*MeasureProb (vtState stages (i+1) (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) := by
  obtain ⟨a, b, hstate, hsup, hbl⟩ :=
    ((cascadePrefixTransport_answer C stages history hl j₀ hj hs sched).1 i (by omega)).2.2
  have hb0 : ∀ p ∈ liveSet C, b p = 0 := fun p hp => by
    have h := congrFun hbl p
    simpa [collapse_apply, hp] using! h
  have hU := hl.2.2.2 i hi
  have hprefix : ApplyGate stages[i] (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) = vtState stages (i+1) (Qatlib.Foundations.PureStateMath.Ket j₀) := by
    simp only [vtState, ApplyGate]
    rw [vt_prefix_step stages i hi, Matrix.mulVec_mulVec]
  have hfix : ApplyGate stages[i] (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)
      -Collapse (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C))
      = vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)-Collapse (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) :=
    growing_stage_fixes_bad history i stages[i] hU _
      (original_bad_support stages history j₀ hs i (by omega))
  have hlive : ApplyGate stages[i] (Collapse (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C))
      = vtState stages (i+1) (Qatlib.Foundations.PureStateMath.Ket j₀)
        -(vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)-Collapse (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)) := by
    have hc : Collapse (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)
        = vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)
          -(vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)-Collapse (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)) := by
      funext p
      rw [Pi.sub_apply, Pi.sub_apply, collapse_apply]
      by_cases hp : p ∈ liveSet C
      · simp [hp]
      · simp [hp]
    rw [hc, rdvt_apply_sub, hprefix, hfix]
    abel
  have hword : dataVtWordState stages history j₀ (cascadeWord sched i++[DataVtStep.stageF i])
      = ApplyGate stages[i] (dataVtWordState stages history j₀ (cascadeWord sched i)) := by
    simp only [dataVtWordState, dataVtWordMatrix_append, dataVtWordMatrix_singleton,
      dataVtStepMatrix, applyGate_mul]
    rw [List.getD_eq_getElem stages 1 hi]
  have hbfix : ApplyGate stages[i] b = b := growing_stage_fixes_bad history i stages[i] hU b hsup
  have hpt : ∀ q ∈ liveSet C,
      (a • (vtState stages (i+1) (Qatlib.Foundations.PureStateMath.Ket j₀)
          -(vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)-Collapse (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)))+b) q
      = (a • Collapse (vtState stages (i+1) (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)+b) q := by
    intro p hp
    have h0 : (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)-Collapse (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)) p = 0 := by
      simp only [Pi.sub_apply, collapse_apply, if_pos hp, sub_self]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, h0, sub_zero, hb0 p hp, _root_.add_zero,
      collapse_apply, if_pos hp]
  refine ⟨a, ?_⟩
  rw [hword, hstate, rdvt_apply_add, rdvt_apply_smul, hlive, hbfix, rdvt_prob_congr _ hpt,
    rdvt_sector_add_zero_right _ _ _ hb0, rdvt_smul_sector, rdvt_collapse_sector]
end
noncomputable section
omit [DecidableEq C] in

/-- A state vanishing at every index in `S` has zero measurement mass on `S`. -/
theorem rdvt_zero_sector {ψ : QState (VtSpace C)} (S : Finset (VtSpace C))
    (h : ∀ p ∈ S, ψ p = 0) : MeasureProb ψ S = 0 := by
  unfold MeasureProb BornProb
  exact Finset.sum_eq_zero fun p hp => by simp [h p hp]
end
noncomputable section

/-- A basis state with running flag has running-sector measurement mass one. -/
theorem rdvt_ket_running (j₀ : VtSpace C) (hj : j₀.1 = vtRunningFlag) :
    MeasureProb (Qatlib.Foundations.PureStateMath.Ket j₀) (runningSet C) = 1 := by
  have hmem : j₀ ∈ runningSet C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  unfold MeasureProb BornProb
  rw [Finset.sum_eq_single_of_mem j₀ hmem (fun q hq hne => by simp [Qatlib.Foundations.PureStateMath.Ket, hne])]
  simp [Qatlib.Foundations.PureStateMath.Ket]
end
noncomputable section

/-- For a legal supported pipeline starting in the running sector, one squared scalar factor
relates both a cascade prefix's live mass and, when available, its next-stage input live
mass to the corresponding original masses. -/
theorem rdvt_cascade_input_live (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (hl : GrowingVtLegal stages history)
    (j₀ : VtSpace C) (hj : j₀.1 = vtRunningFlag) (hs : GrowingVtSupported stages history j₀)
    (sched : ℕ → ℕ) (i : ℕ) (hi : i ≤ stages.length) :
    ∃ a : ℂ,
      MeasureProb (dataVtWordState stages history j₀ (cascadeWord sched i)) (liveSet C)
        = Complex.normSq a*MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) ∧
      (i < stages.length →
      MeasureProb (dataVtWordState stages history j₀
        (cascadeWord sched i++[DataVtStep.stageF i])) (liveSet C)
        = Complex.normSq a*MeasureProb (vtState stages (i+1) (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)) := by
  obtain ⟨a, b, hstate, hsup, hbl⟩ :=
    ((cascadePrefixTransport_answer C stages history hl j₀ hj hs sched).1 i hi).2.2
  have hb0 : ∀ p ∈ liveSet C, b p = 0 := by
    intro p hp
    have h := congrFun hbl p
    simpa [collapse_apply, hp] using! h
  refine ⟨a, ?_, ?_⟩
  · rw [hstate, rdvt_sector_add_zero_right _ _ _ hb0, rdvt_smul_sector, rdvt_collapse_sector]
  · intro hi2
    have hU := hl.2.2.2 i hi2
    have hprefix : ApplyGate stages[i] (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) = vtState stages (i+1) (Qatlib.Foundations.PureStateMath.Ket j₀) := by
      simp only [vtState, ApplyGate]
      rw [vt_prefix_step stages i hi2, Matrix.mulVec_mulVec]
    have hfix : ApplyGate stages[i] (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)
        -Collapse (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C))
        = vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)-Collapse (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) :=
      growing_stage_fixes_bad history i stages[i] hU _
        (original_bad_support stages history j₀ hs i (by omega))
    have hlive : ApplyGate stages[i] (Collapse (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C))
        = vtState stages (i+1) (Qatlib.Foundations.PureStateMath.Ket j₀)
          -(vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)-Collapse (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)) := by
      have hc : Collapse (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)
          = vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)
            -(vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)-Collapse (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)) := by
        funext p
        rw [Pi.sub_apply, Pi.sub_apply, collapse_apply]
        by_cases hp : p ∈ liveSet C
        · simp [hp]
        · simp [hp]
      rw [hc, rdvt_apply_sub, hprefix, hfix]
      abel
    have hword : dataVtWordState stages history j₀ (cascadeWord sched i++[DataVtStep.stageF i])
        = ApplyGate stages[i] (dataVtWordState stages history j₀ (cascadeWord sched i)) := by
      simp only [dataVtWordState, dataVtWordMatrix_append, dataVtWordMatrix_singleton,
        dataVtStepMatrix, applyGate_mul]
      rw [List.getD_eq_getElem stages 1 hi2]
    have hbfix : ApplyGate stages[i] b = b := growing_stage_fixes_bad history i stages[i] hU b hsup
    have hpt : ∀ q ∈ liveSet C,
        (a • (vtState stages (i+1) (Qatlib.Foundations.PureStateMath.Ket j₀)
            -(vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)-Collapse (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)))+b) q
        = (a • Collapse (vtState stages (i+1) (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)+b) q := by
      intro p hp
      have h0 : (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)-Collapse (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)) p = 0 := by
        simp only [Pi.sub_apply, collapse_apply, if_pos hp, sub_self]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, h0, sub_zero, hb0 p hp, _root_.add_zero,
        collapse_apply, if_pos hp]
    rw [hword, hstate, rdvt_apply_add, rdvt_apply_smul, hlive, hbfix, rdvt_prob_congr _ hpt,
      rdvt_sector_add_zero_right _ _ _ hb0, rdvt_smul_sector, rdvt_collapse_sector]
end
noncomputable section

/-- For a legal supported pipeline starting in the running sector, zero final running mass is
preserved by the full amplification cascade. -/
theorem rdvt_cascade_running_zero (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (hl : GrowingVtLegal stages history)
    (j₀ : VtSpace C) (hj : j₀.1 = vtRunningFlag) (hs : GrowingVtSupported stages history j₀)
    (sched : ℕ → ℕ)
    (hrun : MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C) = 0) :
    MeasureProb (dataVtWordState stages history j₀ (cascadeWord sched stages.length))
      (runningSet C) = 0 := by
  obtain ⟨a, b, hstate, hsup, hbl⟩ :=
    ((cascadePrefixTransport_answer C stages history hl j₀ hj hs sched).1
      stages.length le_rfl).2.2
  have hb0 : ∀ p ∈ liveSet C, b p = 0 := by
    intro p hp
    have h := congrFun hbl p
    simpa [collapse_apply, hp] using! h
  have hpsi : ∀ p ∈ runningSet C, vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀) p = 0 := by
    intro p hp
    have hunfold : ∑ q ∈ runningSet C,
        (‖vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀) q‖^2 : ℝ) = 0 := hrun
    have h := Finset.sum_eq_zero_iff_of_nonneg
      (fun q _ => pow_nonneg (norm_nonneg _) 2) |>.mp hunfold p hp
    have h2 : ‖vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀) p‖ = 0 :=
      (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp h
    exact norm_eq_zero.mp h2
  rw [hstate]
  refine rdvt_zero_sector _ fun p hp => ?_
  have hmem : p ∈ liveSet C := by
    have hflag := rdvt_running_flag p hp
    simp only [liveSet, goodSet, runningSet, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    right
    exact hflag
  rw [Pi.add_apply, Pi.smul_apply, collapse_apply, if_pos hmem, hpsi p hp, smul_zero,
    hb0 p hmem, _root_.add_zero]
end
noncomputable section

/-- For a legal supported pipeline starting in the running sector and ending with zero running
mass, the full cascade has equal good and live masses. -/
theorem rdvt_cascade_good_eq_live (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (hl : GrowingVtLegal stages history)
    (j₀ : VtSpace C) (hj : j₀.1 = vtRunningFlag) (hs : GrowingVtSupported stages history j₀)
    (sched : ℕ → ℕ)
    (hrun : MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C) = 0) :
    MeasureProb (dataVtWordState stages history j₀ (cascadeWord sched stages.length))
        (goodSet C)
      = MeasureProb (dataVtWordState stages history j₀ (cascadeWord sched stages.length))
        (liveSet C) := by
  have hz := rdvt_cascade_running_zero stages history hl j₀ hj hs sched hrun
  have hsplit : MeasureProb (dataVtWordState stages history j₀ (cascadeWord sched stages.length))
      (liveSet C)
      = MeasureProb (dataVtWordState stages history j₀ (cascadeWord sched stages.length))
      (goodSet C)
      +MeasureProb (dataVtWordState stages history j₀ (cascadeWord sched stages.length))
      (runningSet C) := by
    rw [liveSet, measureProb_union _ rdvt_good_running_disjoint]
  rw [hz, _root_.add_zero] at hsplit
  exact hsplit.symm
end
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
