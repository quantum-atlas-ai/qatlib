/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.LocalMachineDefs
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

variable {Q A B : Type*} [Fintype Q] [DecidableEq Q]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {w : ℕ}

def addTrackRule (R : QtmRule Q A) (b0 : B) : QtmRule Q (A × B) where
  blank := (R.blank, b0)
  start := R.start
  step q p d q' p' := if p'.2 = p.2 then R.step q p.1 d q' p'.1 else 0

def addTrackCfg (b0 : B) (c : QtmCfg Q A w) : QtmCfg Q (A × B) w :=
  (c.1, c.2.1, fun i => (c.2.2 i, b0))

theorem addTrackCfg_injective (b0 : B) :
    Function.Injective (addTrackCfg (Q := Q) (A := A) (B := B) (w := w) b0) := by
  intro c d h
  unfold addTrackCfg at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hst, hhd, htp⟩ := h
  refine Prod.ext hst (Prod.ext hhd ?_)
  funext i
  have := congrFun htp i
  simpa using congrArg Prod.fst this

theorem update_addTrack (b0 : B) (f : Fin w → A) (i : Fin w) (a' : A) :
    Function.update (fun j => (f j, b0)) i (a', b0)
      = fun j => (Function.update f i a' j, b0) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [Function.update]
  · simp [Function.update, h]

theorem stepTarget_addTrack (b0 : B) (c : QtmCfg Q A w) (d : QtmMove)
    (q' : Q) (a' : A) :
    QtmRule.stepTarget (addTrackCfg b0 c) d q' (a', b0)
      = Option.map (addTrackCfg b0) (QtmRule.stepTarget c d q' a') := by
  unfold QtmRule.stepTarget addTrackCfg
  rcases hm : moveCell c.2.1 d with _ | j
  · simp
  · simp
    rw [update_addTrack b0 c.2.2 c.2.1 a']

theorem stepTarget_addTrack_eq_some (b0 : B) (c c' : QtmCfg Q A w)
    (d : QtmMove) (q' : Q) (a' : A) :
    QtmRule.stepTarget (addTrackCfg b0 c) d q' (a', b0) = some (addTrackCfg b0 c') ↔
      QtmRule.stepTarget c d q' a' = some c' := by
  rw [stepTarget_addTrack]
  constructor
  · intro h
    rcases hm : QtmRule.stepTarget c d q' a' with _ | z
    · simp [hm] at h
    · have hz : addTrackCfg b0 z = addTrackCfg b0 c' := by
        simpa [hm] using h
      rw [addTrackCfg_injective b0 hz]
  · intro h
    simp [h]

theorem addTrack_stepAmplitude (R : QtmRule Q A) (b0 : B) (w : ℕ)
    (c c' : QtmCfg Q A w) :
    (addTrackRule R b0).stepAmplitude w (addTrackCfg b0 c) (addTrackCfg b0 c')
      = R.stepAmplitude w c c' := by
  unfold QtmRule.stepAmplitude
  refine Finset.sum_congr rfl ?_
  intro d _
  refine Finset.sum_congr rfl ?_
  intro q' _
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro a' _
  rw [Finset.sum_eq_single b0]
  · by_cases h : QtmRule.stepTarget c d q' a' = some c'
    · have h' : QtmRule.stepTarget (addTrackCfg b0 c) d q' (a', b0)
          = some (addTrackCfg b0 c') :=
        (stepTarget_addTrack_eq_some b0 c c' d q' a').2 h
      rw [if_pos h', if_pos h]
      simp [addTrackRule, addTrackCfg]
    · have h' : ¬ QtmRule.stepTarget (addTrackCfg b0 c) d q' (a', b0)
          = some (addTrackCfg b0 c') := fun hh =>
        h ((stepTarget_addTrack_eq_some b0 c c' d q' a').1 hh)
      rw [if_neg h', if_neg h]
  · intro b' _ hb
    simp [addTrackRule, addTrackCfg, hb]
  · intro h
    exact absurd (Finset.mem_univ b0) h

theorem addTrackRule_localWellformed (R : QtmRule Q A) (h : R.LocalWellformed) (b0 : B) :
    (addTrackRule R b0).LocalWellformed := by
  obtain ⟨hn, hsc, hrs, hsl, hrl⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q p
    simp only [addTrackRule]
    simp only [Fintype.sum_prod_type]
    trans ∑ q' : Q, ∑ a' : A, ∑ d : QtmMove, ‖R.step q p.1 d q' a'‖ ^ 2
    · refine Finset.sum_congr rfl fun q' _ => Finset.sum_congr rfl fun a' _ => ?_
      rw [Finset.sum_eq_single p.2]
      · simp
      · intro b' _ hb
        simp [hb]
      · intro hmem
        exact absurd (Finset.mem_univ p.2) hmem
    · exact hn q p.1
  · intro q₁ p₁ q₂ p₂ hne
    simp only [addTrackRule]
    simp only [Fintype.sum_prod_type]
    by_cases hb : p₁.2 = p₂.2
    · trans ∑ q' : Q, ∑ a' : A, ∑ d : QtmMove,
          star (R.step q₁ p₁.1 d q' a') * R.step q₂ p₂.1 d q' a'
      · refine Finset.sum_congr rfl fun q' _ => Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.sum_eq_single p₁.2]
        · simp [hb]
        · intro b' _ hb'
          have hb'' : b' ≠ p₂.2 := by simpa [hb] using hb'
          simp [hb', hb'']
        · intro hmem
          exact absurd (Finset.mem_univ p₁.2) hmem
      · exact hsc q₁ p₁.1 q₂ p₂.1 (by
          intro hp
          have hp' := Prod.ext_iff.mp hp
          exact hne (Prod.ext hp'.1 (Prod.ext hp'.2 hb)))
    · have hz : ∀ (d : QtmMove) (q' : Q) (a' : A) (b' : B),
          star (if b' = p₁.2 then R.step q₁ p₁.1 d q' a' else 0) *
            (if b' = p₂.2 then R.step q₂ p₂.1 d q' a' else 0) = 0 := by
        intro d q' a' b'
        by_cases h1 : b' = p₁.2
        · have h2 : b' ≠ p₂.2 := fun h2 => hb (h1.symm.trans h2)
          rw [if_pos h1, if_neg h2]
          simp
        · simp [h1]
      refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun a' _ => ?_
      refine Finset.sum_eq_zero fun b' _ => Finset.sum_eq_zero fun d _ => ?_
      exact hz d q' a' b'
  · intro q₁ p₁ q₂ p₂ c d
    by_cases h1 : c.2 = p₁.2
    · by_cases h2 : d.2 = p₂.2
      · have := hrs q₁ p₁.1 q₂ p₂.1 c.1 d.1
        simpa [addTrackRule, h1, h2] using this
      · simp [addTrackRule, h1, h2]
    · simp [addTrackRule, h1]
  · intro q₁ p₁ q₂ p₂ c d
    by_cases h1 : c.2 = p₁.2
    · by_cases h2 : d.2 = p₂.2
      · have := hsl q₁ p₁.1 q₂ p₂.1 c.1 d.1
        simpa [addTrackRule, h1, h2] using this
      · simp [addTrackRule, h1, h2]
    · simp [addTrackRule, h1]
  · intro q₁ p₁ q₂ p₂ c d
    by_cases h1 : c.2 = p₁.2
    · by_cases h2 : d.2 = p₂.2
      · have := hrl q₁ p₁.1 q₂ p₂.1 c.1 d.1
        simpa [addTrackRule, h1, h2] using this
      · simp [addTrackRule, h1, h2]
    · simp [addTrackRule, h1]

def addTrackState (b0 : B) (ψ : QState (QtmCfg Q A w)) : QState (QtmCfg Q (A × B) w) :=
  fun d => ∑ c, if addTrackCfg b0 c = d then ψ c else 0

theorem addTrackState_apply (b0 : B) (ψ : QState (QtmCfg Q A w)) (c : QtmCfg Q A w) :
    addTrackState b0 ψ (addTrackCfg b0 c) = ψ c := by
  unfold addTrackState
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' _ hc'
    have hne : addTrackCfg b0 c' ≠ addTrackCfg b0 c := fun h =>
      hc' (addTrackCfg_injective b0 h)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem addTrackState_eq_zero (b0 : B) (ψ : QState (QtmCfg Q A w))
    (d : QtmCfg Q (A × B) w) (hd : ∀ c, addTrackCfg b0 c ≠ d) :
    addTrackState b0 ψ d = 0 := by
  unfold addTrackState
  exact Finset.sum_eq_zero fun c _ => by simp [hd c]

theorem addTrack_stepAmplitude_eq_zero (R : QtmRule Q A) (b0 : B) (w : ℕ)
    (c : QtmCfg Q A w) (d : QtmCfg Q (A × B) w)
    (hd : ∀ c', addTrackCfg b0 c' ≠ d) :
    (addTrackRule R b0).stepAmplitude w (addTrackCfg b0 c) d = 0 := by
  unfold QtmRule.stepAmplitude
  refine Finset.sum_eq_zero fun d' _ => ?_
  refine Finset.sum_eq_zero fun q' _ => ?_
  refine Finset.sum_eq_zero fun p' _ => ?_
  by_cases hp : p'.2 = ((addTrackCfg b0 c).2.2 (addTrackCfg b0 c).2.1).2
  · have hread : (addTrackCfg b0 c).2.2 (addTrackCfg b0 c).2.1 = (c.2.2 c.2.1, b0) := rfl
    have hb0 : p'.2 = b0 := by rw [hread] at hp; exact hp
    have hp' : p' = (p'.1, b0) := by
      have : p' = (p'.1, p'.2) := rfl
      rw [this, hb0]
    have hne : QtmRule.stepTarget (addTrackCfg b0 c) d' q' p' ≠ some d := by
      intro hsome
      rw [hp', stepTarget_addTrack] at hsome
      have h2 : Option.map (addTrackCfg b0) (QtmRule.stepTarget c d' q' p'.1) = some d := by
        simpa using hsome
      have : ∃ z, addTrackCfg b0 z = d := by
        cases h3 : QtmRule.stepTarget c d' q' p'.1 with
        | none => simp [h3] at h2
        | some z => exact ⟨z, by simpa [h3] using h2⟩
      obtain ⟨z, hz⟩ := this
      exact hd z hz
    simp [hne]
  · simp [addTrackRule, hp]

theorem addTrack_evolve_support (R : QtmRule Q A) (b0 : B) (w : ℕ)
    (ψ : QState (QtmCfg Q (A × B) w))
    (hψ : ∀ d, (∀ c, addTrackCfg b0 c ≠ d) → ψ d = 0)
    (d : QtmCfg Q (A × B) w) (hd : ∀ c, addTrackCfg b0 c ≠ d) :
    (addTrackRule R b0).evolve w ψ d = 0 := by
  unfold QtmRule.evolve
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : ∃ c', addTrackCfg b0 c' = c
  · obtain ⟨c0, rfl⟩ := hc
    rw [addTrack_stepAmplitude_eq_zero R b0 w c0 d hd]
    simp
  · rw [hψ c (fun c' h => hc ⟨c', h⟩)]
    simp

theorem addTrack_evolve (R : QtmRule Q A) (b0 : B) (w : ℕ)
    (ψ : QState (QtmCfg Q A w)) (c' : QtmCfg Q A w) :
    (addTrackRule R b0).evolve w (addTrackState b0 ψ) (addTrackCfg b0 c')
      = R.evolve w ψ c' := by
  unfold QtmRule.evolve
  have hsum : (∑ d : QtmCfg Q (A × B) w,
        addTrackState b0 ψ d * (addTrackRule R b0).stepAmplitude w d (addTrackCfg b0 c'))
      = ∑ c : QtmCfg Q A w,
        addTrackState b0 ψ (addTrackCfg b0 c) *
          (addTrackRule R b0).stepAmplitude w (addTrackCfg b0 c) (addTrackCfg b0 c') := by
    have hzero : ∀ d ∈ (Finset.univ : Finset (QtmCfg Q (A × B) w)),
        d ∉ Finset.univ.image (fun c : QtmCfg Q A w => addTrackCfg b0 c) →
        addTrackState b0 ψ d * (addTrackRule R b0).stepAmplitude w d (addTrackCfg b0 c')
          = 0 := by
      intro d _ hd
      have hd' : ∀ c, addTrackCfg b0 c ≠ d := fun c h =>
        hd (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, h⟩)
      rw [addTrackState_eq_zero b0 ψ d hd']
      simp
    rw [← Finset.sum_subset (Finset.subset_univ _) hzero, Finset.sum_image]
    intro x _ y _ h
    exact addTrackCfg_injective b0 h
  rw [hsum]
  refine Finset.sum_congr rfl ?_
  intro c _
  rw [addTrackState_apply, addTrack_stepAmplitude]

theorem addTrack_evolve_fun (R : QtmRule Q A) (b0 : B) (w : ℕ)
    (ψ : QState (QtmCfg Q A w)) :
    (addTrackRule R b0).evolve w (addTrackState b0 ψ)
      = addTrackState b0 (R.evolve w ψ) := by
  funext d
  by_cases hd : ∃ c, addTrackCfg b0 c = d
  · obtain ⟨c, rfl⟩ := hd
    rw [addTrack_evolve R b0 w ψ c, addTrackState_apply]
  · rw [addTrackState_eq_zero b0 (R.evolve w ψ) d (fun c h => hd ⟨c, h⟩)]
    exact addTrack_evolve_support R b0 w (addTrackState b0 ψ)
      (fun d h => addTrackState_eq_zero b0 ψ d h) d (fun c h => hd ⟨c, h⟩)

theorem addTrack_runSteps (R : QtmRule Q A) (b0 : B) (w : ℕ) (t : ℕ)
    (ψ : QState (QtmCfg Q A w)) :
    (addTrackRule R b0).runSteps w t (addTrackState b0 ψ)
      = addTrackState b0 (R.runSteps w t ψ) := by
  induction t generalizing ψ with
  | zero => rfl
  | succ t ih =>
    rw [QtmRule.runSteps, QtmRule.runSteps,
      Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (addTrackRule R b0).evolve w
        ((addTrackRule R b0).runSteps w t (addTrackState b0 ψ))
      = addTrackState b0 (R.evolve w (R.runSteps w t ψ))
    rw [ih, addTrack_evolve_fun]

theorem addTrack_runSteps_apply (R : QtmRule Q A) (b0 : B) (w : ℕ) (t : ℕ)
    (ψ : QState (QtmCfg Q A w)) (c' : QtmCfg Q A w) :
    (addTrackRule R b0).runSteps w t (addTrackState b0 ψ) (addTrackCfg b0 c')
      = R.runSteps w t ψ c' := by
  rw [addTrack_runSteps, addTrackState_apply]

end Qatlib.Papers.QWeakness97.MainResults
