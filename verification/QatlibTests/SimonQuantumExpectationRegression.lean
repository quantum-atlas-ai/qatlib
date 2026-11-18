/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ExactSimon97.SampleStoppingQuantum
public import Mathlib.Data.ZMod.Basic
public import Qatlib.Concepts.HspRecovery.BackendAudit.CharacterTableRecoveryConsumers

@[expose] public section

/-! Nontrivial and degenerate consumers of repeated coherent sampling.
The identity oracle on two elements hides the trivial subgroup and has a
two-element annihilator. The constant oracle is rejected for that same target.
These checks do not assume a target-known record or a bounded stopping time. -/

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open scoped Classical ENNReal

namespace QatlibTests.SimonQuantumExpectationRegression

open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Papers.ExactSimon97.SampleStoppingQuantum
open Qatlib.Papers.ExactSimon97.SampleStoppingInf

local instance : MeasurableSpace (AddChar (ZMod 2) ℂ) := ⊤
local instance : DiscreteMeasurableSpace (AddChar (ZMod 2) ℂ) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (AddChar (ZMod 4) ℂ) := ⊤
local instance : DiscreteMeasurableSpace (AddChar (ZMod 4) ℂ) := ⟨fun _ => trivial⟩

/-- A concrete labeling for the two-element Fourier gate. -/
def twoFourier : ZMod 2 ≃ AddChar (ZMod 2) ℂ :=
  Fintype.equivOfCardEq AddChar.card_eq.symm

/-- The identity oracle is an injective, hence trivial-subgroup hiding oracle. -/
theorem identity_hides : HidesSubgroup (fun x : ZMod 2 => x) ⊥ := by
  intro x y
  simp only [AddSubgroup.mem_bot, sub_eq_zero]

/-- The target has positive rank: both characters annihilate the trivial subgroup. -/
theorem annihilator_card : Fintype.card (characterAnnihilator (⊥ : AddSubgroup (ZMod 2))) = 2 := by
  have h := card_characterAnnihilator (⊥ : AddSubgroup (ZMod 2))
  simpa using h

example : MeasureTheory.IsProbabilityMeasure (bornSeq (fun x : ZMod 2 => x) twoFourier) :=
  bornSeq_isProbabilityMeasure _ _ identity_hides _

example :
    (∫⁻ ω, totalQueries (R := ZMod 2) twoFourier
      (characterAnnihilator (⊥ : AddSubgroup (ZMod 2))) ω
      ∂(bornSeq (fun x : ZMod 2 => x) twoFourier)) ≤
      ENNReal.ofReal (2 * Real.logb 2 (2 : ℝ)) := by
  have h := expected_totalQueries_le (fun x : ZMod 2 => x) ⊥ identity_hides twoFourier
    (by rw [annihilator_card])
  simpa only [annihilator_card, Nat.cast_ofNat] using h

example : bornSeq (fun x : ZMod 2 => x) twoFourier
    {ω | ¬ ∃ k, recoveredPrefix ω k = (⊥ : AddSubgroup (ZMod 2))} = 0 :=
  bornSeq_recovery_null _ _ identity_hides _

-- A size-two stopping rule inspects the observed span, not the hidden subgroup.
example : (∫⁻ ω, observedQueries (R := ZMod 2) twoFourier 2 ω
    ∂(bornSeq (fun x : ZMod 2 => x) twoFourier)) ≤
      ENNReal.ofReal (2 * Real.logb 2 (2 : ℝ)) :=
  expected_observedQueries_le _ _ identity_hides _ 2 annihilator_card (by decide)

example : ¬ HidesSubgroup (fun _ : ZMod 2 => (0 : ZMod 2)) ⊥ := by
  intro h
  have hbad := (h 0 1).mp rfl
  norm_num at hbad

-- A genuinely nontrivial hidden subgroup: the parity oracle on four elements
-- hides the two-element even subgroup, and the annihilator target also has size two.
example : (∫⁻ ω, observedQueries (R := ZMod 2)
    (Fintype.equivOfCardEq AddChar.card_eq.symm : ZMod 4 ≃ AddChar (ZMod 4) ℂ) 2 ω
    ∂(bornSeq (fun x : ZMod 4 => (x.val : ZMod 2))
      (Fintype.equivOfCardEq AddChar.card_eq.symm))) ≤
      ENNReal.ofReal (2 * Real.logb 2 (2 : ℝ)) := by
  exact expected_observedQueries_le _
    Qatlib.Concepts.HspRecovery.BackendAudit.fourEvenSubgroup
    Qatlib.Concepts.HspRecovery.BackendAudit.hidesSubgroup_fourParity _ 2
    Qatlib.Concepts.HspRecovery.BackendAudit.card_fourEvenAnnihilator (by decide)

-- With no observations the running span is trivial, hence zero cost is
-- legitimate for a trivial sampling target, even on a nontrivial ambient group.
example (ω : ℕ → AddChar (ZMod 2) ℂ) :
    totalQueries (R := ZMod 2) twoFourier ⊥ ω = 0 := by
  rw [totalQueries_eq]
  apply le_antisymm ?_ zero_le
  have hspan : spanInf ω 0 = (⊥ : AddSubgroup (AddChar (ZMod 2) ℂ)) := by
    simp [spanInf]
  simpa only [Nat.cast_zero] using
    stopGenInf_le_of_spanInf (⊥ : AddSubgroup (AddChar (ZMod 2) ℂ))
      (ω := ω) (k := 0) hspan

end QatlibTests.SimonQuantumExpectationRegression
