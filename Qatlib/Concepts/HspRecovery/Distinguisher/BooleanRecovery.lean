/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.ExactRank.BooleanCharacters
import Qatlib.Concepts.HspRecovery.BackendAudit.FiniteAbelianDuality
set_option warningAsError false

open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.HspRecovery.Distinguisher

open scoped Classical

private theorem booleanDot_comm {n : ℕ} (a x : BooleanVec n) :
    booleanDot a x = booleanDot x a := by
  simp only [booleanDot]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

private theorem booleanDot_add_right {n : ℕ} (a x y : BooleanVec n) :
    booleanDot a (x + y) = booleanDot a x + booleanDot a y := by
  simp [booleanDot, mul_add, Finset.sum_add_distrib]

private theorem booleanDot_neg_right {n : ℕ} (a x : BooleanVec n) :
    booleanDot a (-x) = -booleanDot a x := by
  simp [booleanDot]

def booleanSampleSpan {n m : ℕ} (samples : Fin m → BooleanVec n) :
    AddSubgroup (BooleanVec n) :=
  AddSubgroup.closure (Set.range samples)

def booleanSampleCandidate {n m : ℕ} (samples : Fin m → BooleanVec n) :
    AddSubgroup (BooleanVec n) where
  carrier := {x | ∀ i, booleanDot (samples i) x = 0}
  zero_mem' := by
    intro i
    simp [booleanDot]
  add_mem' := by
    intro x y hx hy i
    rw [booleanDot_add_right, hx i, hy i, add_zero]
  neg_mem' := by
    intro x hx i
    rw [booleanDot_neg_right, hx i, neg_zero]

@[simp] theorem mem_booleanSampleCandidate {n m : ℕ}
    (samples : Fin m → BooleanVec n) (x : BooleanVec n) :
    x ∈ booleanSampleCandidate samples ↔ ∀ i, booleanDot (samples i) x = 0 :=
  Iff.rfl

theorem booleanSampleCandidate_eq_booleanOrthogonal_span {n m : ℕ}
    (samples : Fin m → BooleanVec n) :
    booleanSampleCandidate samples = booleanOrthogonal (booleanSampleSpan samples) := by
  ext x
  rw [mem_booleanSampleCandidate, mem_booleanOrthogonal]
  constructor
  · intro hx a
    apply AddSubgroup.closure_induction (k := Set.range samples)
      (p := fun y _ => booleanDot x y = 0)
      (x := a)
    · intro y hy
      rcases hy with ⟨i, rfl⟩
      rw [booleanDot_comm]
      exact hx i
    · simp [booleanDot]
    · intro y z hy hz hy0 hz0
      rw [booleanDot_add_right, hy0, hz0, add_zero]
    · intro y hy hy0
      rw [booleanDot_neg_right, hy0, neg_zero]
    · exact a.property
  · intro hx i
    rw [booleanDot_comm]
    exact hx ⟨samples i, AddSubgroup.subset_closure ⟨i, rfl⟩⟩

theorem booleanOrthogonal_booleanOrthogonal_eq {n : ℕ}
    (H : AddSubgroup (BooleanVec n)) :
    booleanOrthogonal (booleanOrthogonal H) = H := by
  ext x
  rw [← doubleDualEmb_mem_characterAnnihilator_characterAnnihilator_iff H x]
  change x ∈ booleanOrthogonal (booleanOrthogonal H) ↔
    AddChar.doubleDualEmb x ∈ characterAnnihilator (characterAnnihilator H)
  rw [mem_booleanOrthogonal, mem_characterAnnihilator]
  constructor
  · intro hx χ
    let a : BooleanVec n := (booleanCharacterEquiv n).symm (χ : AddChar (BooleanVec n) ℂ)
    have hχa : booleanCharacter a = (χ : AddChar (BooleanVec n) ℂ) := by
      change booleanCharacterEquiv n a = (χ : AddChar (BooleanVec n) ℂ)
      simp [a]
    have ha : a ∈ booleanOrthogonal H := by
      rw [← booleanCharacter_mem_characterAnnihilator_iff H a, hχa]
      exact χ.property
    have hdot : booleanDot x a = 0 := hx ⟨a, ha⟩
    change (χ : AddChar (BooleanVec n) ℂ) x = 1
    rw [← hχa, booleanCharacter_apply, booleanDot_comm, hdot, AddChar.map_zero_eq_one]
  · intro hx a
    have haChar : booleanCharacter a ∈ characterAnnihilator H :=
      (booleanCharacter_mem_characterAnnihilator_iff H a).2 a.property
    have heval := hx ⟨booleanCharacter a, haChar⟩
    change booleanDot x a = 0
    rw [booleanDot_comm]
    apply ZMod.injective_stdAddChar
    change booleanCharacter a x = ZMod.stdAddChar 0
    simpa [AddChar.map_zero_eq_one] using heval

theorem booleanSampleCandidate_eq_of_span_eq_orthogonal {n m : ℕ}
    (H : AddSubgroup (BooleanVec n)) (samples : Fin m → BooleanVec n)
    (hspan : booleanSampleSpan samples = booleanOrthogonal H) :
    booleanSampleCandidate samples = H := by
  rw [booleanSampleCandidate_eq_booleanOrthogonal_span, hspan,
    booleanOrthogonal_booleanOrthogonal_eq]

end Qatlib.Concepts.HspRecovery.Distinguisher
