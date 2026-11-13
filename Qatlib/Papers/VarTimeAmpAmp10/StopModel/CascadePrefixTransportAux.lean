/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.LiveVtProgramAux

/-!
# Transport of live cascade components

The lemmas describe how stage evolution and amplitude amplification transport a scalar multiple
of the original live component together with a bad component supported in the reached history.
Amplification stays in the span of the marked and unmarked components.

This development concerns variable-time amplitude amplification in [Ambainis2012].

## Main statements

* `growing_stage_live_transport`: stage transport with a reached bad remainder.
* `live_aa_transport`: preservation of the live/bad span during amplification.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

noncomputable section
set_option autoImplicit false
namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Matrix
open scoped Classical BigOperators
variable {C : Type} [Fintype C] [DecidableEq C]

/-- For a unitary preparation matrix, every amplitude-amplification iterate lies in the span of
the prepared state's marked and unmarked components. -/
theorem prepared_aa_orbit_span (A : Matrix (VtSpace C) (VtSpace C) ℂ) (j₀ : VtSpace C)
    (hA : A ∈ Matrix.unitaryGroup (VtSpace C) ℂ) (S : Finset (VtSpace C)) (k : ℕ) :
    ∃ c d : ℂ,
      ApplyGate ((preparedAAIterate A j₀ S)^k) (preparedAAState A j₀) =
        c • Collapse (preparedAAState A j₀) S +
        d • (preparedAAState A j₀-Collapse (preparedAAState A j₀) S) := by
  let a := MeasureProb (preparedAAState A j₀) S
  have hstep := prepared_aa_two_component_step A j₀ S hA
  induction k with
  | zero =>
    refine ⟨1, 1, ?_⟩
    simp only [pow_zero, applyGate_one, one_smul, add_sub_cancel]
  | succ k ih =>
    obtain ⟨c, d, he⟩ := ih
    refine ⟨c*((1-2*a : ℝ) : ℂ)+d*((2*(1-a) : ℝ) : ℂ),
      c*((-2*a : ℝ) : ℂ)+d*((1-2*a : ℝ) : ℂ), ?_⟩
    rw [pow_succ', applyGate_mul, he]
    simp only [ApplyGate, Matrix.mulVec_add, Matrix.mulVec_smul]
    change c • ApplyGate (preparedAAIterate A j₀ S)
        (Collapse (preparedAAState A j₀) S) +
      d • ApplyGate (preparedAAIterate A j₀ S)
        (preparedAAState A j₀-Collapse (preparedAAState A j₀) S) = _
    rw [hstep.1, hstep.2]
    module

/-- For a unitary preparation matrix, amplification with the live set stays in the span of the
prepared state's live and nonlive components. -/
theorem live_aa_orbit_span (A : Matrix (VtSpace C) (VtSpace C) ℂ) (j₀ : VtSpace C)
    (hA : A ∈ Matrix.unitaryGroup (VtSpace C) ℂ) (k : ℕ) :
    ∃ c d : ℂ,
      ApplyGate ((preparedAAIterate A j₀ (liveSet C))^k) (preparedAAState A j₀) =
        c • Collapse (preparedAAState A j₀) (liveSet C) +
        d • (preparedAAState A j₀-Collapse (preparedAAState A j₀) (liveSet C)) :=
  prepared_aa_orbit_span A j₀ hA (liveSet C) k

/-- A basis label lies outside the live set exactly when its flag is `vtBadFlag`. -/
theorem nonlive_iff_bad (p : VtSpace C) : p ∉ liveSet C ↔ p.1 = vtBadFlag := by
  obtain ⟨f, x⟩ := p
  fin_cases f <;> simp [liveSet, goodSet, runningSet, vtGoodFlag, vtRunningFlag, vtBadFlag]

/-- A growing-history stage fixes any state supported on bad labels whose payloads lie in the
current history. -/
theorem growing_stage_fixes_bad (history : ℕ → Finset C) (i : ℕ)
    (U : Matrix (VtSpace C) (VtSpace C) ℂ) (hU : IsGrowingVtStage history i U)
    (b : QState (VtSpace C))
    (hb : ∀ p, b p ≠ 0 → p.1 = vtBadFlag ∧ p.2 ∈ history i) : ApplyGate U b = b := by
  funext q
  simp only [ApplyGate, Matrix.mulVec, dotProduct]
  have ht (p : VtSpace C) : U q p*b p = if q = p then b p else 0 := by
    by_cases h0 : b p = 0
    · simp [h0]
    · obtain ⟨hf, hp⟩ := hb p h0
      have hmem : p ∈ reachedStoppedSet history i := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hf]; decide, hp⟩
      rw [hU.2 p hmem q]
      split_ifs <;> simp
  simp_rw [ht]
  simp

/-- The nonlive part of a supported original prefix state is supported on bad labels in the
current history. -/
theorem original_bad_support (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (hs : GrowingVtSupported stages history j₀)
    (i : ℕ) (hi : i ≤ stages.length) :
    ∀ p, (vtState stages i (Ket j₀)-Collapse (vtState stages i (Ket j₀)) (liveSet C)) p ≠ 0 →
      p.1 = vtBadFlag ∧ p.2 ∈ history i := by
  intro p hp
  have hl : p ∉ liveSet C := by
    intro h
    simp only [Pi.sub_apply, collapse_apply, if_pos h, sub_self, ne_eq] at hp
    exact hp trivial
  have hf := (nonlive_iff_bad p).mp hl
  have hφ : vtState stages i (Ket j₀) p ≠ 0 := by
    simpa only [Pi.sub_apply, collapse_apply, if_neg hl, sub_zero] using hp
  exact ⟨hf, (hs i hi p hφ).1 (by rw [hf]; decide)⟩

/-- A state supported only on bad flags has zero collapse onto the live set. -/
theorem collapse_bad_live_zero (b : QState (VtSpace C))
    (hb : ∀ p, b p ≠ 0 → p.1 = vtBadFlag) : Collapse b (liveSet C) = 0 := by
  funext p
  rw [collapse_apply]
  by_cases hp : p ∈ liveSet C
  · rw [if_pos hp]
    by_contra hn
    have hf := hb p hn
    exact ((nonlive_iff_bad p).mpr hf) hp
  · simp [hp]

/-- A legal stage transports a scalar multiple of the original live prefix plus a reached bad
remainder to the corresponding next-prefix form. -/
theorem growing_stage_live_transport
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) (hl : GrowingVtLegal stages history)
    (hs : GrowingVtSupported stages history j₀) (i : ℕ) (hi : i < stages.length)
    (a : ℂ) (b : QState (VtSpace C))
    (hb : ∀ p, b p ≠ 0 → p.1 = vtBadFlag ∧ p.2 ∈ history i) :
    ∃ b', ApplyGate stages[i] (a • Collapse (vtState stages i (Ket j₀)) (liveSet C)+b) =
      a • Collapse (vtState stages (i+1) (Ket j₀)) (liveSet C)+b' ∧
      (∀ p, b' p ≠ 0 → p.1 = vtBadFlag ∧ p.2 ∈ history (i+1)) := by
  let old := vtState stages i (Ket j₀)-Collapse (vtState stages i (Ket j₀)) (liveSet C)
  let next := vtState stages (i+1) (Ket j₀)-Collapse (vtState stages (i+1) (Ket j₀)) (liveSet C)
  have hold := original_bad_support stages history j₀ hs i (by omega)
  have hnext := original_bad_support stages history j₀ hs (i+1) (by omega)
  have hfixed := growing_stage_fixes_bad history i stages[i] (hl.2.2.2 i hi) old hold
  have hbfix := growing_stage_fixes_bad history i stages[i] (hl.2.2.2 i hi) b hb
  have hstate : ApplyGate stages[i] (vtState stages i (Ket j₀)) =
      vtState stages (i+1) (Ket j₀) := by
    simp only [vtState, ApplyGate]
    rw [vt_prefix_step stages i hi, Matrix.mulVec_mulVec]
  have hlive : ApplyGate stages[i] (Collapse (vtState stages i (Ket j₀)) (liveSet C)) =
      vtState stages (i+1) (Ket j₀)-old := by
    have he : Collapse (vtState stages i (Ket j₀)) (liveSet C) = vtState stages i (Ket j₀)-old := by
      dsimp [old]; module
    rw [he]
    simp only [ApplyGate, Matrix.mulVec_sub] at *
    rw [hstate, hfixed]
  refine ⟨a • next+b-a • old, ?_, ?_⟩
  · simp only [ApplyGate, Matrix.mulVec_add, Matrix.mulVec_smul]
    change a • ApplyGate stages[i] (Collapse (vtState stages i (Ket j₀)) (liveSet C))+
      ApplyGate stages[i] b = _
    rw [hlive, hbfix]
    dsimp [next]
    module
  · intro p hp
    by_contra hn
    have hno : next p = 0 := by
      by_contra h; exact hn (hnext p h)
    have hbo : b p = 0 := by
      by_contra h
      obtain ⟨hf, hm⟩ := hb p h
      exact hn ⟨hf, hl.2.1 i hm⟩
    have hoo : old p = 0 := by
      by_contra h
      obtain ⟨hf, hm⟩ := hold p h
      exact hn ⟨hf, hl.2.1 i hm⟩
    exact hp (by simp [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, hno, hbo, hoo])

/-- Amplification of a prepared state decomposed into a scalar live component and a remainder
with zero live collapse stays in their span. -/
theorem live_aa_transport (A : Matrix (VtSpace C) (VtSpace C) ℂ) (j₀ : VtSpace C)
    (hA : A ∈ Matrix.unitaryGroup (VtSpace C) ℂ) (k : ℕ)
    (φ b : QState (VtSpace C)) (a : ℂ)
    (he : preparedAAState A j₀ = a • Collapse φ (liveSet C)+b)
    (hb : Collapse b (liveSet C) = 0) :
    ∃ c d : ℂ, ApplyGate ((preparedAAIterate A j₀ (liveSet C))^k) (preparedAAState A j₀) =
      (c*a) • Collapse φ (liveSet C) +
        d • b := by
  have hcollapse : Collapse (preparedAAState A j₀) (liveSet C) = a • Collapse φ (liveSet C) := by
    rw [he]
    funext p
    have hbp := congrFun hb p
    by_cases hp : p ∈ liveSet C
    · simpa [collapse_apply, hp] using congrArg (fun z : ℂ => a*φ p+z) hbp
    · simp [collapse_apply, hp]
  have hbad : preparedAAState A j₀-Collapse (preparedAAState A j₀) (liveSet C) = b := by
    rw [hcollapse, he]; module
  obtain ⟨c, d, hout⟩ := live_aa_orbit_span A j₀ hA k
  refine ⟨c, d, ?_⟩
  rw [hout, hbad, hcollapse, smul_smul]

end Qatlib.Papers.VarTimeAmpAmp10.StopModel
