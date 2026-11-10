/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.LocalMachineDefs
import Mathlib.Logic.Equiv.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace Qatlib.Papers.QWeakness97.MainResults

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Foundations.PureStateMath
open scoped BigOperators

variable {Q A C : Type*} [Fintype Q] [DecidableEq Q]
  [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
variable {w : ℕ}

def reindexRule (R : QtmRule Q A) (e : A ≃ C) : QtmRule Q C where
  blank := e R.blank
  start := R.start
  step q c d q' c' := R.step q (e.symm c) d q' (e.symm c')

def reindexCfg (e : A ≃ C) (c : QtmCfg Q A w) : QtmCfg Q C w :=
  (c.1, c.2.1, fun i => e (c.2.2 i))

theorem reindexCfg_injective (e : A ≃ C) :
    Function.Injective (reindexCfg (Q := Q) (A := A) (C := C) (w := w) e) := by
  intro c d h
  unfold reindexCfg at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hst, hhd, htp⟩ := h
  refine Prod.ext hst (Prod.ext hhd ?_)
  funext i
  exact e.injective (congrFun htp i)

theorem update_reindex (e : A ≃ C) (f : Fin w → A) (i : Fin w) (a : A) :
    Function.update (fun j => e (f j)) i (e a)
      = fun j => e (Function.update f i a j) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [Function.update]
  · simp [Function.update, h]

theorem stepTarget_reindex (e : A ≃ C) (c : QtmCfg Q A w) (d : QtmMove)
    (q' : Q) (a : A) :
    QtmRule.stepTarget (reindexCfg e c) d q' (e a)
      = Option.map (reindexCfg e) (QtmRule.stepTarget c d q' a) := by
  unfold QtmRule.stepTarget reindexCfg
  rcases hm : moveCell c.2.1 d with _ | j
  · simp
  · simp
    rw [update_reindex]

theorem stepTarget_reindex_eq_some (e : A ≃ C) (c c' : QtmCfg Q A w)
    (d : QtmMove) (q' : Q) (a : A) :
    QtmRule.stepTarget (reindexCfg e c) d q' (e a) = some (reindexCfg e c') ↔
      QtmRule.stepTarget c d q' a = some c' := by
  rw [stepTarget_reindex]
  constructor
  · intro h
    rcases hm : QtmRule.stepTarget c d q' a with _ | z
    · simp [hm] at h
    · have hz : reindexCfg e z = reindexCfg e c' := by
        simpa [hm] using h
      rw [reindexCfg_injective e hz]
  · intro h
    simp [h]

theorem reindex_stepAmplitude (R : QtmRule Q A) (e : A ≃ C) (w : ℕ)
    (c c' : QtmCfg Q A w) :
    (reindexRule R e).stepAmplitude w (reindexCfg e c) (reindexCfg e c')
      = R.stepAmplitude w c c' := by
  unfold QtmRule.stepAmplitude
  refine Finset.sum_congr rfl ?_
  intro d _
  refine Finset.sum_congr rfl ?_
  intro q' _
  trans ∑ a' : A,
      if QtmRule.stepTarget c d q' a' = some c' then
        R.step c.1 (c.2.2 c.2.1) d q' a'
      else 0
  · refine (Function.Bijective.sum_comp e.bijective (fun cOut : C =>
      if QtmRule.stepTarget (reindexCfg e c) d q' cOut = some (reindexCfg e c') then
        (reindexRule R e).step (reindexCfg e c).1
          ((reindexCfg e c).2.2 (reindexCfg e c).2.1) d q' cOut
      else 0)).symm.trans ?_
    refine Finset.sum_congr rfl fun a' _ => ?_
    simp only [reindexRule]
    simp only [stepTarget_reindex_eq_some]
    simp [reindexCfg]
  · refine Finset.sum_congr rfl fun a' _ => ?_
    by_cases h : QtmRule.stepTarget c d q' a' = some c'
    · rw [if_pos h]
    · rw [if_neg h]

theorem reindexRule_localWellformed (R : QtmRule Q A) (h : R.LocalWellformed)
    (e : A ≃ C) : (reindexRule R e).LocalWellformed := by
  obtain ⟨hn, hsc, hrs, hsl, hrl⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q c
    simp only [reindexRule]
    rw [← hn q (e.symm c)]
    refine Finset.sum_congr rfl fun q' _ => ?_
    exact Function.Bijective.sum_comp e.symm.bijective
      (fun a => ∑ d : QtmMove, ‖R.step q (e.symm c) d q' a‖ ^ 2)
  · intro q₁ c₁ q₂ c₂ hne
    simp only [reindexRule]
    rw [← hsc q₁ (e.symm c₁) q₂ (e.symm c₂) (by
      intro hp
      have hp' := Prod.ext_iff.mp hp
      exact hne (Prod.ext hp'.1 (e.symm.injective hp'.2)))]
    refine Finset.sum_congr rfl fun q' _ => ?_
    exact Function.Bijective.sum_comp e.symm.bijective
      (fun a => ∑ d : QtmMove,
        star (R.step q₁ (e.symm c₁) d q' a) * R.step q₂ (e.symm c₂) d q' a)
  · intro q₁ c₁ q₂ c₂ c d
    simpa only [reindexRule] using
      hrs q₁ (e.symm c₁) q₂ (e.symm c₂) (e.symm c) (e.symm d)
  · intro q₁ c₁ q₂ c₂ c d
    simpa only [reindexRule] using
      hsl q₁ (e.symm c₁) q₂ (e.symm c₂) (e.symm c) (e.symm d)
  · intro q₁ c₁ q₂ c₂ c d
    simpa only [reindexRule] using
      hrl q₁ (e.symm c₁) q₂ (e.symm c₂) (e.symm c) (e.symm d)

def reindexState (e : A ≃ C) (ψ : QState (QtmCfg Q A w)) : QState (QtmCfg Q C w) :=
  fun d => ∑ c, if reindexCfg e c = d then ψ c else 0

theorem reindexState_apply (e : A ≃ C) (ψ : QState (QtmCfg Q A w))
    (c : QtmCfg Q A w) : reindexState e ψ (reindexCfg e c) = ψ c := by
  unfold reindexState
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' _ hc'
    have hne : reindexCfg e c' ≠ reindexCfg e c := fun h =>
      hc' (reindexCfg_injective e h)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem reindexState_eq_zero (e : A ≃ C) (ψ : QState (QtmCfg Q A w))
    (d : QtmCfg Q C w) (hd : ∀ c, reindexCfg e c ≠ d) :
    reindexState e ψ d = 0 := by
  unfold reindexState
  exact Finset.sum_eq_zero fun c _ => by simp [hd c]

theorem reindex_stepAmplitude_eq_zero (R : QtmRule Q A) (e : A ≃ C) (w : ℕ)
    (c : QtmCfg Q A w) (d : QtmCfg Q C w)
    (hd : ∀ c', reindexCfg e c' ≠ d) :
    (reindexRule R e).stepAmplitude w (reindexCfg e c) d = 0 := by
  unfold QtmRule.stepAmplitude
  refine Finset.sum_eq_zero fun d' _ => ?_
  refine Finset.sum_eq_zero fun q' _ => ?_
  refine Finset.sum_eq_zero fun cOut _ => ?_
  have hstep : QtmRule.stepTarget (reindexCfg e c) d' q' cOut
      = Option.map (reindexCfg e)
          (QtmRule.stepTarget c d' q' (e.symm cOut)) := by
    conv_lhs => rw [show cOut = e (e.symm cOut) from (e.apply_symm_apply cOut).symm]
    rw [stepTarget_reindex]
  by_cases h : QtmRule.stepTarget (reindexCfg e c) d' q' cOut = some d
  · rw [if_pos h]
    have hcfg : ∃ z : QtmCfg Q A w, reindexCfg e z = d := by
      rw [hstep] at h
      cases hm : QtmRule.stepTarget c d' q' (e.symm cOut) with
      | none => simp [hm] at h
      | some z => exact ⟨z, by simpa [hm] using h⟩
    obtain ⟨z, hz⟩ := hcfg
    exact absurd hz (hd z)
  · simp [h]

theorem reindex_evolve_support (R : QtmRule Q A) (e : A ≃ C) (w : ℕ)
    (ψ : QState (QtmCfg Q C w))
    (hψ : ∀ d, (∀ c, reindexCfg e c ≠ d) → ψ d = 0)
    (d : QtmCfg Q C w) (hd : ∀ c, reindexCfg e c ≠ d) :
    (reindexRule R e).evolve w ψ d = 0 := by
  unfold QtmRule.evolve
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : ∃ c', reindexCfg e c' = c
  · obtain ⟨c0, rfl⟩ := hc
    rw [reindex_stepAmplitude_eq_zero R e w c0 d hd]
    simp
  · rw [hψ c (fun c' h => hc ⟨c', h⟩)]
    simp

theorem reindex_evolve (R : QtmRule Q A) (e : A ≃ C) (w : ℕ)
    (ψ : QState (QtmCfg Q A w)) (c' : QtmCfg Q A w) :
    (reindexRule R e).evolve w (reindexState e ψ) (reindexCfg e c')
      = R.evolve w ψ c' := by
  unfold QtmRule.evolve
  have hsum : (∑ d : QtmCfg Q C w,
        reindexState e ψ d * (reindexRule R e).stepAmplitude w d (reindexCfg e c'))
      = ∑ c : QtmCfg Q A w,
        reindexState e ψ (reindexCfg e c) *
          (reindexRule R e).stepAmplitude w (reindexCfg e c) (reindexCfg e c') := by
    have hzero : ∀ d ∈ (Finset.univ : Finset (QtmCfg Q C w)),
        d ∉ Finset.univ.image (fun c : QtmCfg Q A w => reindexCfg e c) →
        reindexState e ψ d * (reindexRule R e).stepAmplitude w d (reindexCfg e c')
          = 0 := by
      intro d _ hd
      have hd' : ∀ c, reindexCfg e c ≠ d := fun c h =>
        hd (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, h⟩)
      rw [reindexState_eq_zero e ψ d hd']
      simp
    rw [← Finset.sum_subset (Finset.subset_univ _) hzero, Finset.sum_image]
    intro x _ y _ h
    exact reindexCfg_injective e h
  rw [hsum]
  refine Finset.sum_congr rfl ?_
  intro c _
  rw [reindexState_apply, reindex_stepAmplitude]

theorem reindex_evolve_fun (R : QtmRule Q A) (e : A ≃ C) (w : ℕ)
    (ψ : QState (QtmCfg Q A w)) :
    (reindexRule R e).evolve w (reindexState e ψ)
      = reindexState e (R.evolve w ψ) := by
  funext d
  by_cases hd : ∃ c, reindexCfg e c = d
  · obtain ⟨c, rfl⟩ := hd
    rw [reindex_evolve R e w ψ c, reindexState_apply]
  · rw [reindexState_eq_zero e (R.evolve w ψ) d (fun c h => hd ⟨c, h⟩)]
    exact reindex_evolve_support R e w (reindexState e ψ)
      (fun d h => reindexState_eq_zero e ψ d h) d (fun c h => hd ⟨c, h⟩)

theorem reindex_runSteps (R : QtmRule Q A) (e : A ≃ C) (w : ℕ) (t : ℕ)
    (ψ : QState (QtmCfg Q A w)) :
    (reindexRule R e).runSteps w t (reindexState e ψ)
      = reindexState e (R.runSteps w t ψ) := by
  induction t generalizing ψ with
  | zero => rfl
  | succ t ih =>
    rw [QtmRule.runSteps, QtmRule.runSteps,
      Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (reindexRule R e).evolve w
        ((reindexRule R e).runSteps w t (reindexState e ψ))
      = reindexState e (R.evolve w (R.runSteps w t ψ))
    rw [ih, reindex_evolve_fun]

theorem reindex_runSteps_apply (R : QtmRule Q A) (e : A ≃ C) (w : ℕ) (t : ℕ)
    (ψ : QState (QtmCfg Q A w)) (c' : QtmCfg Q A w) :
    (reindexRule R e).runSteps w t (reindexState e ψ) (reindexCfg e c')
      = R.runSteps w t ψ c' := by
  rw [reindex_runSteps, reindexState_apply]

end Qatlib.Papers.QWeakness97.MainResults
