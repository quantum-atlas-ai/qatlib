/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.LocalMachineDefs
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace Qatlib.Papers.QWeakness97.MainResults

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Foundations.PureStateMath
open scoped BigOperators

variable {Q1 Q2 A : Type*}
  [Fintype Q1] [DecidableEq Q1] [Fintype Q2] [DecidableEq Q2]
  [Fintype A] [DecidableEq A]
variable {w : ℕ}

def composeRule (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1) : QtmRule (Q1 ⊕ Q2) A where
  blank := R1.blank
  start := Sum.inl st1
  step q a d q' b :=
    match q with
    | Sum.inl q1 =>
        if q1 = hf1 then
          (if d = QtmMove.right ∧ q' = Sum.inr st2 ∧ b = a then (1 : ℂ) else 0)
        else
          match q' with
          | Sum.inl q1' => R1.step q1 a d q1' b
          | Sum.inr _ => 0
    | Sum.inr q2 =>
        if q2 = hf2 then
          (if d = QtmMove.right ∧ q' = Sum.inl st1 ∧ b = a then (1 : ℂ) else 0)
        else
          match q' with
          | Sum.inl _ => 0
          | Sum.inr q2' => R2.step q2 a d q2' b

def cfgL (c : QtmCfg Q1 A w) : QtmCfg (Q1 ⊕ Q2) A w :=
  (Sum.inl c.1, c.2.1, c.2.2)

def cfgR (c : QtmCfg Q2 A w) : QtmCfg (Q1 ⊕ Q2) A w :=
  (Sum.inr c.1, c.2.1, c.2.2)

theorem cfgL_injective : Function.Injective (cfgL (Q1 := Q1) (Q2 := Q2) (A := A) (w := w)) := by
  intro c d h
  unfold cfgL at h
  simp only [Prod.mk.injEq, Sum.inl.injEq] at h
  obtain ⟨hst, hhd, htp⟩ := h
  exact Prod.ext hst (Prod.ext hhd htp)

theorem cfgR_injective : Function.Injective (cfgR (Q1 := Q1) (Q2 := Q2) (A := A) (w := w)) := by
  intro c d h
  unfold cfgR at h
  simp only [Prod.mk.injEq, Sum.inr.injEq] at h
  obtain ⟨hst, hhd, htp⟩ := h
  exact Prod.ext hst (Prod.ext hhd htp)

theorem stepTarget_cfgL_inl (c : QtmCfg Q1 A w) (d : QtmMove) (q1' : Q1) (b : A) :
    QtmRule.stepTarget (cfgL (Q2 := Q2) c) d (Sum.inl q1') b
      = Option.map (cfgL (Q2 := Q2)) (QtmRule.stepTarget c d q1' b) := by
  unfold QtmRule.stepTarget cfgL
  rcases hm : moveCell c.2.1 d with _ | j <;> simp

theorem stepTarget_cfgL_inr (c : QtmCfg Q1 A w) (d : QtmMove) (s : Q2) (b : A)
    (c' : QtmCfg Q1 A w) :
    QtmRule.stepTarget (cfgL (Q2 := Q2) c) d (Sum.inr s) b ≠ some (cfgL (Q2 := Q2) c') := by
  intro h
  unfold QtmRule.stepTarget cfgL at h
  rcases hm : moveCell c.2.1 d with _ | j <;> simp [hm] at h

theorem stepTarget_cfgR_inr (c : QtmCfg Q2 A w) (d : QtmMove) (q2' : Q2) (b : A) :
    QtmRule.stepTarget (cfgR (Q1 := Q1) c) d (Sum.inr q2') b
      = Option.map (cfgR (Q1 := Q1)) (QtmRule.stepTarget c d q2' b) := by
  unfold QtmRule.stepTarget cfgR
  rcases hm : moveCell c.2.1 d with _ | j <;> simp

theorem stepTarget_cfgR_inl (c : QtmCfg Q2 A w) (d : QtmMove) (s : Q1) (b : A)
    (c' : QtmCfg Q2 A w) :
    QtmRule.stepTarget (cfgR (Q1 := Q1) c) d (Sum.inl s) b ≠ some (cfgR (Q1 := Q1) c') := by
  intro h
  unfold QtmRule.stepTarget cfgR at h
  rcases hm : moveCell c.2.1 d with _ | j <;> simp [hm] at h

theorem stepTarget_cfgL_eq_some (c c' : QtmCfg Q1 A w) (d : QtmMove) (q1' : Q1) (b : A) :
    QtmRule.stepTarget (cfgL (Q2 := Q2) c) d (Sum.inl q1') b = some (cfgL (Q2 := Q2) c') ↔
      QtmRule.stepTarget c d q1' b = some c' := by
  rw [stepTarget_cfgL_inl]
  constructor
  · intro h
    rcases hm : QtmRule.stepTarget c d q1' b with _ | z
    · simp [hm] at h
    · have hz : cfgL (Q2 := Q2) z = cfgL (Q2 := Q2) c' := by simpa [hm] using h
      rw [cfgL_injective hz]
  · intro h
    simp [h]

theorem stepTarget_cfgR_eq_some (c c' : QtmCfg Q2 A w) (d : QtmMove) (q2' : Q2) (b : A) :
    QtmRule.stepTarget (cfgR (Q1 := Q1) c) d (Sum.inr q2') b = some (cfgR (Q1 := Q1) c') ↔
      QtmRule.stepTarget c d q2' b = some c' := by
  rw [stepTarget_cfgR_inr]
  constructor
  · intro h
    rcases hm : QtmRule.stepTarget c d q2' b with _ | z
    · simp [hm] at h
    · have hz : cfgR (Q1 := Q1) z = cfgR (Q1 := Q1) c' := by simpa [hm] using h
      rw [cfgR_injective hz]
  · intro h
    simp [h]

theorem compose_stepAmplitude_cfgL (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (c c' : QtmCfg Q1 A w) (hc : c.1 ≠ hf1) :
    (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w (cfgL (Q2 := Q2) c) (cfgL (Q2 := Q2) c')
      = R1.stepAmplitude w c c' := by
  unfold QtmRule.stepAmplitude
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fintype.sum_sum_type]
  have hright : (∑ x : Q2, ∑ b : A,
      (if QtmRule.stepTarget (cfgL (Q2 := Q2) c) d (Sum.inr x) b = some (cfgL (Q2 := Q2) c') then
        (composeRule R1 R2 hf1 st2 hf2 st1).step (cfgL (Q2 := Q2) c).1
          ((cfgL (Q2 := Q2) c).2.2 (cfgL (Q2 := Q2) c).2.1) d (Sum.inr x) b
      else 0)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg (stepTarget_cfgL_inr c d x b c')]
  rw [hright, add_zero]
  refine Finset.sum_congr rfl fun q1' _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hm : QtmRule.stepTarget c d q1' b = some c'
  · rw [if_pos hm, if_pos ((stepTarget_cfgL_eq_some c c' d q1' b).2 hm)]
    simp only [composeRule, cfgL, hc, if_false]
  · rw [if_neg hm, if_neg (fun hh => hm ((stepTarget_cfgL_eq_some c c' d q1' b).1 hh))]

theorem compose_stepAmplitude_cfgR (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (c c' : QtmCfg Q2 A w) (hc : c.1 ≠ hf2) :
    (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w (cfgR (Q1 := Q1) c) (cfgR (Q1 := Q1) c')
      = R2.stepAmplitude w c c' := by
  unfold QtmRule.stepAmplitude
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fintype.sum_sum_type]
  have hleft : (∑ x : Q1, ∑ b : A,
      (if QtmRule.stepTarget (cfgR (Q1 := Q1) c) d (Sum.inl x) b = some (cfgR (Q1 := Q1) c') then
        (composeRule R1 R2 hf1 st2 hf2 st1).step (cfgR (Q1 := Q1) c).1
          ((cfgR (Q1 := Q1) c).2.2 (cfgR (Q1 := Q1) c).2.1) d (Sum.inl x) b
      else 0)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg (stepTarget_cfgR_inl c d x b c')]
  rw [hleft, zero_add]
  refine Finset.sum_congr rfl fun q2' _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hm : QtmRule.stepTarget c d q2' b = some c'
  · rw [if_pos hm, if_pos ((stepTarget_cfgR_eq_some c c' d q2' b).2 hm)]
    simp only [composeRule, cfgR, hc, if_false]
  · rw [if_neg hm, if_neg (fun hh => hm ((stepTarget_cfgR_eq_some c c' d q2' b).1 hh))]

def haltStepL (st2 : Q2) (a : A) (d : QtmMove) (q' : Q1 ⊕ Q2) (b : A) : ℂ :=
  if d = QtmMove.right ∧ q' = Sum.inr st2 ∧ b = a then 1 else 0

def haltStepR (st1 : Q1) (a : A) (d : QtmMove) (q' : Q1 ⊕ Q2) (b : A) : ℂ :=
  if d = QtmMove.right ∧ q' = Sum.inl st1 ∧ b = a then 1 else 0

theorem haltStepL_norm (st2 : Q2) (a : A) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove, ‖haltStepL st2 a d q' b‖ ^ 2) = 1 := by
  unfold haltStepL
  rw [Fintype.sum_sum_type]
  have hleft : (∑ x : Q1, ∑ b : A, ∑ d : QtmMove,
      ‖(if d = QtmMove.right ∧ Sum.inl x = Sum.inr st2 ∧ b = a then (1 : ℂ) else 0)‖ ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun d _ => ?_
    simp
  rw [hleft, zero_add]
  rw [Finset.sum_eq_single st2]
  · rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single QtmMove.right]
      · simp
      · intro d _ hd; simp [hd]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ a) h
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ st2) h

theorem haltStepR_norm (st1 : Q1) (a : A) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove, ‖haltStepR st1 a d q' b‖ ^ 2) = 1 := by
  unfold haltStepR
  rw [Fintype.sum_sum_type]
  have hright : (∑ x : Q2, ∑ b : A, ∑ d : QtmMove,
      ‖(if d = QtmMove.right ∧ Sum.inr x = Sum.inl st1 ∧ b = a then (1 : ℂ) else 0)‖ ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun d _ => ?_
    simp
  rw [hright, add_zero]
  rw [Finset.sum_eq_single st1]
  · rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single QtmMove.right]
      · simp
      · intro d _ hd; simp [hd]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ a) h
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ st1) h

theorem haltStepL_orth (st2 : Q2) (a1 a2 : A) (h : a1 ≠ a2) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
      star (haltStepL st2 a1 d q' b) * haltStepL st2 a2 d q' b) = 0 := by
  unfold haltStepL
  refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun d _ => ?_
  by_cases h1 : d = QtmMove.right ∧ q' = Sum.inr st2 ∧ b = a1
  · rw [if_pos h1]
    have h2 : ¬ (d = QtmMove.right ∧ q' = Sum.inr st2 ∧ b = a2) := by
      intro hh; exact h (h1.2.2.symm.trans hh.2.2)
    rw [if_neg h2]; simp
  · rw [if_neg h1]; simp

theorem haltStepR_orth (st1 : Q1) (a1 a2 : A) (h : a1 ≠ a2) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
      star (haltStepR st1 a1 d q' b) * haltStepR st1 a2 d q' b) = 0 := by
  unfold haltStepR
  refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun d _ => ?_
  by_cases h1 : d = QtmMove.right ∧ q' = Sum.inl st1 ∧ b = a1
  · rw [if_pos h1]
    have h2 : ¬ (d = QtmMove.right ∧ q' = Sum.inl st1 ∧ b = a2) := by
      intro hh; exact h (h1.2.2.symm.trans hh.2.2)
    rw [if_neg h2]; simp
  · rw [if_neg h1]; simp

def dataStepL (R1 : QtmRule Q1 A) (q1 : Q1) (a : A) (d : QtmMove) (q' : Q1 ⊕ Q2) (b : A) : ℂ :=
  match q' with
  | Sum.inl q1' => R1.step q1 a d q1' b
  | Sum.inr _ => 0

def dataStepR (R2 : QtmRule Q2 A) (q2 : Q2) (a : A) (d : QtmMove) (q' : Q1 ⊕ Q2) (b : A) : ℂ :=
  match q' with
  | Sum.inl _ => 0
  | Sum.inr q2' => R2.step q2 a d q2' b

theorem composeRule_step_inl_halt (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1) (a : A) (d : QtmMove)
    (q' : Q1 ⊕ Q2) (b : A) :
    (composeRule R1 R2 hf1 st2 hf2 st1).step (Sum.inl hf1) a d q' b
      = haltStepL st2 a d q' b := by
  simp [composeRule, haltStepL]

theorem composeRule_step_inl_data (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1) (q1 : Q1) (hq : q1 ≠ hf1)
    (a : A) (d : QtmMove) (q' : Q1 ⊕ Q2) (b : A) :
    (composeRule R1 R2 hf1 st2 hf2 st1).step (Sum.inl q1) a d q' b
      = dataStepL R1 q1 a d q' b := by
  simp only [composeRule, hq, if_false]
  rcases q' with q1' | q2' <;> rfl

theorem composeRule_step_inr_halt (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1) (a : A) (d : QtmMove)
    (q' : Q1 ⊕ Q2) (b : A) :
    (composeRule R1 R2 hf1 st2 hf2 st1).step (Sum.inr hf2) a d q' b
      = haltStepR st1 a d q' b := by
  simp [composeRule, haltStepR]

theorem composeRule_step_inr_data (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1) (q2 : Q2) (hq : q2 ≠ hf2)
    (a : A) (d : QtmMove) (q' : Q1 ⊕ Q2) (b : A) :
    (composeRule R1 R2 hf1 st2 hf2 st1).step (Sum.inr q2) a d q' b
      = dataStepR R2 q2 a d q' b := by
  simp only [composeRule, hq, if_false]
  rcases q' with q1' | q2' <;> rfl

theorem dataStepL_norm (R1 : QtmRule Q1 A) (h1 : R1.LocalWellformed) (q1 : Q1) (a : A) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove, ‖dataStepL R1 q1 a d q' b‖ ^ 2) = 1 := by
  rw [Fintype.sum_sum_type]
  have hright : (∑ x : Q2, ∑ b : A, ∑ d : QtmMove,
      ‖dataStepL R1 q1 a d (Sum.inr x) b‖ ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun d _ => ?_
    simp [dataStepL]
  rw [hright, add_zero]
  exact h1.1 q1 a

theorem dataStepR_norm (R2 : QtmRule Q2 A) (h2 : R2.LocalWellformed) (q2 : Q2) (a : A) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove, ‖dataStepR R2 q2 a d q' b‖ ^ 2) = 1 := by
  rw [Fintype.sum_sum_type]
  have hleft : (∑ x : Q1, ∑ b : A, ∑ d : QtmMove,
      ‖dataStepR R2 q2 a d (Sum.inl x) b‖ ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun d _ => ?_
    simp [dataStepR]
  rw [hleft, zero_add]
  exact h2.1 q2 a

theorem dataStepL_orth (R1 : QtmRule Q1 A) (h1 : R1.LocalWellformed)
    (q1 : Q1) (a1 : A) (q2 : Q1) (a2 : A) (hne : (q1, a1) ≠ (q2, a2)) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
      star (dataStepL R1 q1 a1 d q' b) * dataStepL R1 q2 a2 d q' b) = 0 := by
  rw [Fintype.sum_sum_type]
  have hright : (∑ x : Q2, ∑ b : A, ∑ d : QtmMove,
      star (dataStepL R1 q1 a1 d (Sum.inr x) b) * dataStepL R1 q2 a2 d (Sum.inr x) b) = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun d _ => ?_
    simp [dataStepL]
  rw [hright, add_zero]
  exact h1.2.1 q1 a1 q2 a2 hne

theorem dataStepR_orth (R2 : QtmRule Q2 A) (h2 : R2.LocalWellformed)
    (q2 : Q2) (a2 : A) (q2' : Q2) (a2' : A) (hne : (q2, a2) ≠ (q2', a2')) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
      star (dataStepR R2 q2 a2 d q' b) * dataStepR R2 q2' a2' d q' b) = 0 := by
  rw [Fintype.sum_sum_type]
  have hleft : (∑ x : Q1, ∑ b : A, ∑ d : QtmMove,
      star (dataStepR R2 q2 a2 d (Sum.inl x) b) * dataStepR R2 q2' a2' d (Sum.inl x) b) = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun d _ => ?_
    simp [dataStepR]
  rw [hleft, zero_add]
  exact h2.2.1 q2 a2 q2' a2' hne

theorem haltL_dataL_orth (R1 : QtmRule Q1 A) (st2 : Q2) (q1 : Q1)
    (a1 a2 : A) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
      star (haltStepL st2 a1 d q' b) * dataStepL R1 q1 a2 d q' b) = 0 := by
  refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rcases q' with q1' | q2'
  · simp [haltStepL]
  · simp [dataStepL]

theorem haltR_dataR_orth (R2 : QtmRule Q2 A) (st1 : Q1) (q2 : Q2)
    (a1 a2 : A) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
      star (haltStepR st1 a1 d q' b) * dataStepR R2 q2 a2 d q' b) = 0 := by
  refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rcases q' with q1' | q2'
  · simp [dataStepR]
  · simp [haltStepR]

theorem haltL_haltR_orth (st2 : Q2) (st1 : Q1) (a1 a2 : A) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
      star (haltStepL st2 a1 d q' b) * haltStepR st1 a2 d q' b) = 0 := by
  refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rcases q' with q1' | q2'
  · simp [haltStepL, haltStepR]
  · simp [haltStepL, haltStepR]

theorem haltR_haltL_orth (st2 : Q2) (st1 : Q1) (a1 a2 : A) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
      star (haltStepR st1 a1 d q' b) * haltStepL st2 a2 d q' b) = 0 := by
  refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rcases q' with q1' | q2'
  · simp [haltStepL, haltStepR]
  · simp [haltStepL, haltStepR]

theorem haltL_dataR_orth (R2 : QtmRule Q2 A) (hf2 : Q2) (st2 : Q2)
    (noin2 : ∀ (q : Q2) (a : A) (d : QtmMove) (b : A), q ≠ hf2 → R2.step q a d st2 b = 0)
    (q2 : Q2) (hq2 : q2 ≠ hf2) (a1 a2 : A) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
      star (haltStepL st2 a1 d q' b) * dataStepR R2 q2 a2 d q' b) = 0 := by
  refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rcases q' with q1' | q2'
  · simp [haltStepL]
  · by_cases hq : q2' = st2
    · rw [hq]; by_cases hb : b = a1
      · rw [hb]; by_cases hd : d = QtmMove.right
        · rw [hd]; simp [haltStepL, dataStepR, noin2 q2 a2 QtmMove.right a1 hq2]
        · simp [haltStepL, dataStepR, hd]
      · simp [haltStepL, dataStepR, hb]
    · simp [haltStepL, dataStepR, hq]

theorem haltR_dataL_orth (R1 : QtmRule Q1 A) (hf1 : Q1) (st1 : Q1)
    (noin1 : ∀ (q : Q1) (a : A) (d : QtmMove) (b : A), q ≠ hf1 → R1.step q a d st1 b = 0)
    (q1 : Q1) (hq1 : q1 ≠ hf1) (a1 a2 : A) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
      star (haltStepR st1 a1 d q' b) * dataStepL R1 q1 a2 d q' b) = 0 := by
  refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rcases q' with q1' | q2'
  · by_cases hq : q1' = st1
    · rw [hq]; by_cases hb : b = a1
      · rw [hb]; by_cases hd : d = QtmMove.right
        · rw [hd]; simp [haltStepR, dataStepL, noin1 q1 a2 QtmMove.right a1 hq1]
        · simp [haltStepR, dataStepL, hd]
      · simp [haltStepR, dataStepL, hb]
    · simp [haltStepR, dataStepL, hq]
  · simp [haltStepR]

theorem dataL_haltL_orth (R1 : QtmRule Q1 A) (st2 : Q2) (q1 : Q1) (a1 a2 : A) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
      star (dataStepL R1 q1 a1 d q' b) * haltStepL st2 a2 d q' b) = 0 := by
  refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rcases q' with q1' | q2'
  · simp [haltStepL]
  · simp [dataStepL]

theorem dataR_haltR_orth (R2 : QtmRule Q2 A) (st1 : Q1) (q2 : Q2) (a1 a2 : A) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
      star (dataStepR R2 q2 a1 d q' b) * haltStepR st1 a2 d q' b) = 0 := by
  refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rcases q' with q1' | q2'
  · simp [dataStepR]
  · simp [haltStepR]

theorem dataL_haltR_orth (R1 : QtmRule Q1 A) (hf1 : Q1) (st1 : Q1)
    (noin1 : ∀ (q : Q1) (a : A) (d : QtmMove) (b : A), q ≠ hf1 → R1.step q a d st1 b = 0)
    (q1 : Q1) (hq1 : q1 ≠ hf1) (a1 a2 : A) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
      star (dataStepL R1 q1 a1 d q' b) * haltStepR st1 a2 d q' b) = 0 := by
  refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rcases q' with q1' | q2'
  · by_cases hq : q1' = st1
    · rw [hq]; by_cases hb : b = a2
      · rw [hb]; by_cases hd : d = QtmMove.right
        · rw [hd]; simp [dataStepL, haltStepR, noin1 q1 a1 QtmMove.right a2 hq1]
        · simp [dataStepL, haltStepR, hd]
      · simp [dataStepL, haltStepR, hb]
    · simp [dataStepL, haltStepR, hq]
  · simp [dataStepL]

theorem dataR_haltL_orth (R2 : QtmRule Q2 A) (hf2 : Q2) (st2 : Q2)
    (noin2 : ∀ (q : Q2) (a : A) (d : QtmMove) (b : A), q ≠ hf2 → R2.step q a d st2 b = 0)
    (q2 : Q2) (hq2 : q2 ≠ hf2) (a1 a2 : A) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
      star (dataStepR R2 q2 a1 d q' b) * haltStepL st2 a2 d q' b) = 0 := by
  refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rcases q' with q1' | q2'
  · simp [haltStepL]
  · by_cases hq : q2' = st2
    · rw [hq]; by_cases hb : b = a2
      · rw [hb]; by_cases hd : d = QtmMove.right
        · rw [hd]; simp [dataStepR, haltStepL, noin2 q2 a1 QtmMove.right a2 hq2]
        · simp [dataStepR, haltStepL, hd]
      · simp [dataStepR, haltStepL, hb]
    · simp [dataStepR, haltStepL, hq]

theorem dataL_dataR_orth (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (q1 : Q1) (q2 : Q2) (a1 a2 : A) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
      star (dataStepL R1 q1 a1 d q' b) * dataStepR R2 q2 a2 d q' b) = 0 := by
  refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rcases q' with q1' | q2'
  · simp [dataStepR]
  · simp [dataStepL]

theorem dataR_dataL_orth (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (q1 : Q1) (q2 : Q2) (a1 a2 : A) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
      star (dataStepR R2 q2 a2 d q' b) * dataStepL R1 q1 a1 d q' b) = 0 := by
  refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rcases q' with q1' | q2'
  · simp [dataStepR]
  · simp [dataStepL]

theorem composeRule_wf_norm (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (h1 : R1.LocalWellformed) (h2 : R2.LocalWellformed) :
    ∀ (q : Q1 ⊕ Q2) (a : A),
      (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
        ‖(composeRule R1 R2 hf1 st2 hf2 st1).step q a d q' b‖ ^ 2) = 1 := by
  intro q a
  rcases q with q1 | q2
  · by_cases hq : q1 = hf1
    · rw [hq]
      simpa only [composeRule_step_inl_halt] using haltStepL_norm (Q1 := Q1) st2 a
    · simpa only [composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 q1 hq]
        using dataStepL_norm R1 h1 q1 a
  · by_cases hq : q2 = hf2
    · rw [hq]
      simpa only [composeRule_step_inr_halt] using haltStepR_norm (Q2 := Q2) st1 a
    · simpa only [composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 q2 hq]
        using dataStepR_norm R2 h2 q2 a

theorem composeRule_wf_orth (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (h1 : R1.LocalWellformed) (h2 : R2.LocalWellformed)
    (noin1 : ∀ (q : Q1) (a : A) (d : QtmMove) (b : A), q ≠ hf1 → R1.step q a d st1 b = 0)
    (noin2 : ∀ (q : Q2) (a : A) (d : QtmMove) (b : A), q ≠ hf2 → R2.step q a d st2 b = 0)
    (q1 : Q1 ⊕ Q2) (a1 : A) (q2 : Q1 ⊕ Q2) (a2 : A)
    (hne : (q1, a1) ≠ (q2, a2)) :
    (∑ q' : Q1 ⊕ Q2, ∑ b : A, ∑ d : QtmMove,
      star ((composeRule R1 R2 hf1 st2 hf2 st1).step q1 a1 d q' b)
        * (composeRule R1 R2 hf1 st2 hf2 st1).step q2 a2 d q' b) = 0 := by
  rcases q1 with q1 | q1 <;> rcases q2 with q2 | q2
  · by_cases hq1 : q1 = hf1 <;> by_cases hq2 : q2 = hf1
    · rw [hq1, hq2]
      simp only [composeRule_step_inl_halt]
      have ha : a1 ≠ a2 := by intro h; exact hne (by rw [hq1, hq2, h])
      exact haltStepL_orth (Q1 := Q1) st2 a1 a2 ha
    · rw [hq1]
      simp only [composeRule_step_inl_halt,
        composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 q2 hq2]
      exact haltL_dataL_orth R1 st2 q2 a1 a2
    · rw [hq2]
      simp only [composeRule_step_inl_halt,
        composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 q1 hq1]
      exact dataL_haltL_orth R1 st2 q1 a1 a2
    · simp only [composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 q1 hq1,
        composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 q2 hq2]
      have hne' : (q1, a1) ≠ (q2, a2) :=
        fun h => by obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h; exact hne (Prod.ext (congrArg Sum.inl h1) h2)
      exact dataStepL_orth R1 h1 q1 a1 q2 a2 hne'
  · by_cases hq1 : q1 = hf1 <;> by_cases hq2 : q2 = hf2
    · rw [hq1, hq2]
      simp only [composeRule_step_inl_halt, composeRule_step_inr_halt]
      exact haltL_haltR_orth st2 st1 a1 a2
    · rw [hq1]
      simp only [composeRule_step_inl_halt,
        composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 q2 hq2]
      exact haltL_dataR_orth R2 hf2 st2 noin2 q2 hq2 a1 a2
    · rw [hq2]
      simp only [composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 q1 hq1,
        composeRule_step_inr_halt]
      exact dataL_haltR_orth R1 hf1 st1 noin1 q1 hq1 a1 a2
    · simp only [composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 q1 hq1,
        composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 q2 hq2]
      exact dataL_dataR_orth R1 R2 q1 q2 a1 a2
  · by_cases hq1 : q1 = hf2 <;> by_cases hq2 : q2 = hf1
    · rw [hq1, hq2]
      simp only [composeRule_step_inr_halt, composeRule_step_inl_halt]
      exact haltR_haltL_orth st2 st1 a1 a2
    · rw [hq1]
      simp only [composeRule_step_inr_halt,
        composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 q2 hq2]
      exact haltR_dataL_orth R1 hf1 st1 noin1 q2 hq2 a1 a2
    · rw [hq2]
      simp only [composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 q1 hq1,
        composeRule_step_inl_halt]
      exact dataR_haltL_orth R2 hf2 st2 noin2 q1 hq1 a1 a2
    · simp only [composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 q1 hq1,
        composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 q2 hq2]
      exact dataR_dataL_orth R1 R2 q2 q1 a2 a1
  · by_cases hq1 : q1 = hf2 <;> by_cases hq2 : q2 = hf2
    · rw [hq1, hq2]
      simp only [composeRule_step_inr_halt]
      have ha : a1 ≠ a2 := by intro h; exact hne (by rw [hq1, hq2, h])
      exact haltStepR_orth (Q2 := Q2) st1 a1 a2 ha
    · rw [hq1]
      simp only [composeRule_step_inr_halt,
        composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 q2 hq2]
      exact haltR_dataR_orth R2 st1 q2 a1 a2
    · rw [hq2]
      simp only [composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 q1 hq1,
        composeRule_step_inr_halt]
      exact dataR_haltR_orth R2 st1 q1 a1 a2
    · simp only [composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 q1 hq1,
        composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 q2 hq2]
      have hne' : (q1, a1) ≠ (q2, a2) :=
        fun h => by obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h; exact hne (Prod.ext (congrArg Sum.inr h1) h2)
      exact dataStepR_orth R2 h2 q1 a1 q2 a2 hne'

theorem dataL_mul_dataL (R1 : QtmRule Q1 A) (q1 q2 : Q1) (a1 a2 c d : A)
    (m1 m2 : QtmMove)
    (hm : (∑ q' : Q1, R1.step q1 a1 m1 q' c * star (R1.step q2 a2 m2 q' d)) = 0) :
    (∑ q' : Q1 ⊕ Q2,
      dataStepL R1 q1 a1 m1 q' c * star (dataStepL R1 q2 a2 m2 q' d)) = 0 := by
  rw [Fintype.sum_sum_type]
  have hr : (∑ x : Q2, dataStepL R1 q1 a1 m1 (Sum.inr x) c
      * star (dataStepL R1 q2 a2 m2 (Sum.inr x) d)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [dataStepL]
  rw [hr, add_zero]
  simpa [dataStepL] using hm

theorem dataR_mul_dataR (R2 : QtmRule Q2 A) (q1 q2 : Q2) (a1 a2 c d : A)
    (m1 m2 : QtmMove)
    (hm : (∑ q' : Q2, R2.step q1 a1 m1 q' c * star (R2.step q2 a2 m2 q' d)) = 0) :
    (∑ q' : Q1 ⊕ Q2,
      dataStepR R2 q1 a1 m1 q' c * star (dataStepR R2 q2 a2 m2 q' d)) = 0 := by
  rw [Fintype.sum_sum_type]
  have hl : (∑ x : Q1, dataStepR R2 q1 a1 m1 (Sum.inl x) c
      * star (dataStepR R2 q2 a2 m2 (Sum.inl x) d)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [dataStepR]
  rw [hl, zero_add]
  simpa [dataStepR] using hm

theorem dataL_mul_dataR (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (q1 : Q1) (q2 : Q2) (a1 a2 c d : A) (m1 m2 : QtmMove) :
    (∑ q' : Q1 ⊕ Q2,
      dataStepL R1 q1 a1 m1 q' c * star (dataStepR R2 q2 a2 m2 q' d)) = 0 := by
  rw [Fintype.sum_sum_type]
  simp [dataStepL, dataStepR]

theorem dataR_mul_dataL (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (q1 : Q2) (q2 : Q1) (a1 a2 c d : A) (m1 m2 : QtmMove) :
    (∑ q' : Q1 ⊕ Q2,
      dataStepR R2 q1 a1 m1 q' c * star (dataStepL R1 q2 a2 m2 q' d)) = 0 := by
  rw [Fintype.sum_sum_type]
  simp [dataStepL, dataStepR]

theorem dataL_mul_haltL (R1 : QtmRule Q1 A) (st2 : Q2) (q1 : Q1)
    (a1 a2 c d : A) (m1 m2 : QtmMove) :
    (∑ q' : Q1 ⊕ Q2,
      dataStepL R1 q1 a1 m1 q' c * star (haltStepL st2 a2 m2 q' d)) = 0 := by
  rw [Fintype.sum_sum_type]
  simp [dataStepL, haltStepL]

theorem dataR_mul_haltR (R2 : QtmRule Q2 A) (st1 : Q1) (q1 : Q2)
    (a1 a2 c d : A) (m1 m2 : QtmMove) :
    (∑ q' : Q1 ⊕ Q2,
      dataStepR R2 q1 a1 m1 q' c * star (haltStepR st1 a2 m2 q' d)) = 0 := by
  rw [Fintype.sum_sum_type]
  simp [dataStepR, haltStepR]

theorem haltL_mul_dataL (R1 : QtmRule Q1 A) (st2 : Q2) (q2 : Q1)
    (a1 a2 c d : A) (m1 m2 : QtmMove) :
    (∑ q' : Q1 ⊕ Q2,
      haltStepL st2 a1 m1 q' c * star (dataStepL R1 q2 a2 m2 q' d)) = 0 := by
  rw [Fintype.sum_sum_type]
  simp [dataStepL, haltStepL]

theorem haltR_mul_dataR (R2 : QtmRule Q2 A) (st1 : Q1) (q2 : Q2)
    (a1 a2 c d : A) (m1 m2 : QtmMove) :
    (∑ q' : Q1 ⊕ Q2,
      haltStepR st1 a1 m1 q' c * star (dataStepR R2 q2 a2 m2 q' d)) = 0 := by
  rw [Fintype.sum_sum_type]
  simp [dataStepR, haltStepR]

theorem haltL_mul_haltR (st2 : Q2) (st1 : Q1) (a1 a2 c d : A) (m1 m2 : QtmMove) :
    (∑ q' : Q1 ⊕ Q2,
      haltStepL st2 a1 m1 q' c * star (haltStepR st1 a2 m2 q' d)) = 0 := by
  rw [Fintype.sum_sum_type]
  simp [haltStepL, haltStepR]

theorem haltR_mul_haltL (st2 : Q2) (st1 : Q1) (a1 a2 c d : A) (m1 m2 : QtmMove) :
    (∑ q' : Q1 ⊕ Q2,
      haltStepR st1 a1 m1 q' c * star (haltStepL st2 a2 m2 q' d)) = 0 := by
  rw [Fintype.sum_sum_type]
  simp [haltStepL, haltStepR]

theorem dataL_mul_haltR (R1 : QtmRule Q1 A) (hf1 : Q1) (st1 : Q1)
    (noin1 : ∀ (q : Q1) (a : A) (d : QtmMove) (b : A), q ≠ hf1 → R1.step q a d st1 b = 0)
    (q1 : Q1) (hq1 : q1 ≠ hf1) (a1 a2 c d : A) (m1 m2 : QtmMove) :
    (∑ q' : Q1 ⊕ Q2,
      dataStepL R1 q1 a1 m1 q' c * star (haltStepR st1 a2 m2 q' d)) = 0 := by
  rw [Fintype.sum_sum_type]
  have hr : (∑ x : Q2, dataStepL R1 q1 a1 m1 (Sum.inr x) c
      * star (haltStepR st1 a2 m2 (Sum.inr x) d)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [dataStepL]
  rw [hr, add_zero]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hm : m2 = QtmMove.right
  · rw [hm]; by_cases hx : x = st1
    · rw [hx]; by_cases hd : d = a2
      · rw [hd]; simp [dataStepL, haltStepR, noin1 q1 a1 m1 c hq1]
      · simp [dataStepL, haltStepR, hd]
    · simp [dataStepL, haltStepR, hx]
  · simp [dataStepL, haltStepR, hm]

theorem dataR_mul_haltL (R2 : QtmRule Q2 A) (hf2 : Q2) (st2 : Q2)
    (noin2 : ∀ (q : Q2) (a : A) (d : QtmMove) (b : A), q ≠ hf2 → R2.step q a d st2 b = 0)
    (q1 : Q2) (hq1 : q1 ≠ hf2) (a1 a2 c d : A) (m1 m2 : QtmMove) :
    (∑ q' : Q1 ⊕ Q2,
      dataStepR R2 q1 a1 m1 q' c * star (haltStepL st2 a2 m2 q' d)) = 0 := by
  rw [Fintype.sum_sum_type]
  have hl : (∑ x : Q1, dataStepR R2 q1 a1 m1 (Sum.inl x) c
      * star (haltStepL st2 a2 m2 (Sum.inl x) d)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [dataStepR]
  rw [hl, zero_add]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hm : m2 = QtmMove.right
  · rw [hm]; by_cases hx : x = st2
    · rw [hx]; by_cases hd : d = a2
      · rw [hd]; simp [dataStepR, haltStepL, noin2 q1 a1 m1 c hq1]
      · simp [dataStepR, haltStepL, hd]
    · simp [dataStepR, haltStepL, hx]
  · simp [dataStepR, haltStepL, hm]

theorem haltL_mul_dataR (R2 : QtmRule Q2 A) (hf2 : Q2) (st2 : Q2)
    (noin2 : ∀ (q : Q2) (a : A) (d : QtmMove) (b : A), q ≠ hf2 → R2.step q a d st2 b = 0)
    (q2 : Q2) (hq2 : q2 ≠ hf2) (a1 a2 c d : A) (m1 m2 : QtmMove) :
    (∑ q' : Q1 ⊕ Q2,
      haltStepL st2 a1 m1 q' c * star (dataStepR R2 q2 a2 m2 q' d)) = 0 := by
  rw [Fintype.sum_sum_type]
  have hl : (∑ x : Q1, haltStepL st2 a1 m1 (Sum.inl x) c
      * star (dataStepR R2 q2 a2 m2 (Sum.inl x) d)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [haltStepL]
  rw [hl, zero_add]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hm : m1 = QtmMove.right
  · rw [hm]; by_cases hx : x = st2
    · rw [hx]; by_cases hc : c = a1
      · rw [hc]; simp [haltStepL, dataStepR, noin2 q2 a2 m2 d hq2]
      · simp [haltStepL, dataStepR, hc]
    · simp [haltStepL, dataStepR, hx]
  · simp [haltStepL, dataStepR, hm]

theorem haltR_mul_dataL (R1 : QtmRule Q1 A) (hf1 : Q1) (st1 : Q1)
    (noin1 : ∀ (q : Q1) (a : A) (d : QtmMove) (b : A), q ≠ hf1 → R1.step q a d st1 b = 0)
    (q2 : Q1) (hq2 : q2 ≠ hf1) (a1 a2 c d : A) (m1 m2 : QtmMove) :
    (∑ q' : Q1 ⊕ Q2,
      haltStepR st1 a1 m1 q' c * star (dataStepL R1 q2 a2 m2 q' d)) = 0 := by
  rw [Fintype.sum_sum_type]
  have hr : (∑ x : Q2, haltStepR st1 a1 m1 (Sum.inr x) c
      * star (dataStepL R1 q2 a2 m2 (Sum.inr x) d)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [haltStepR]
  rw [hr, add_zero]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hm : m1 = QtmMove.right
  · rw [hm]; by_cases hx : x = st1
    · rw [hx]; by_cases hc : c = a1
      · rw [hc]; simp [haltStepR, dataStepL, noin1 q2 a2 m2 d hq2]
      · simp [haltStepR, dataStepL, hc]
    · simp [haltStepR, dataStepL, hx]
  · simp [haltStepR, dataStepL, hm]

theorem haltL_mul_haltL (st2 : Q2) (a1 a2 c d : A) (m1 m2 : QtmMove)
    (h : m1 ≠ QtmMove.right ∨ m2 ≠ QtmMove.right) :
    (∑ q' : Q1 ⊕ Q2,
      haltStepL st2 a1 m1 q' c * star (haltStepL st2 a2 m2 q' d)) = 0 := by
  rw [Fintype.sum_sum_type]
  have hl : (∑ x : Q1, haltStepL st2 a1 m1 (Sum.inl x) c
      * star (haltStepL st2 a2 m2 (Sum.inl x) d)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [haltStepL]
  rw [hl, zero_add]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x = st2
  · rw [hx]
    rcases h with h1 | h2
    · simp [haltStepL, h1]
    · simp [haltStepL, h2]
  · simp [haltStepL, hx]

theorem haltR_mul_haltR (st1 : Q1) (a1 a2 c d : A) (m1 m2 : QtmMove)
    (h : m1 ≠ QtmMove.right ∨ m2 ≠ QtmMove.right) :
    (∑ q' : Q1 ⊕ Q2,
      haltStepR st1 a1 m1 q' c * star (haltStepR st1 a2 m2 q' d)) = 0 := by
  rw [Fintype.sum_sum_type]
  have hr : (∑ x : Q2, haltStepR st1 a1 m1 (Sum.inr x) c
      * star (haltStepR st1 a2 m2 (Sum.inr x) d)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [haltStepR]
  rw [hr, add_zero]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x = st1
  · rw [hx]
    rcases h with h1 | h2
    · simp [haltStepR, h1]
    · simp [haltStepR, h2]
  · simp [haltStepR, hx]

theorem compose_mul_orth (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (_h1 : R1.LocalWellformed) (_h2 : R2.LocalWellformed)
    (noin1 : ∀ (q : Q1) (a : A) (d : QtmMove) (b : A), q ≠ hf1 → R1.step q a d st1 b = 0)
    (noin2 : ∀ (q : Q2) (a : A) (d : QtmMove) (b : A), q ≠ hf2 → R2.step q a d st2 b = 0)
    (m1 m2 : QtmMove)
    (hnL : ∀ (q1 : Q1) (a1 : A) (q2 : Q1) (a2 c d : A),
      (∑ q' : Q1, R1.step q1 a1 m1 q' c * star (R1.step q2 a2 m2 q' d)) = 0)
    (hnR : ∀ (q1 : Q2) (a1 : A) (q2 : Q2) (a2 c d : A),
      (∑ q' : Q2, R2.step q1 a1 m1 q' c * star (R2.step q2 a2 m2 q' d)) = 0)
    (hLnb : m1 ≠ QtmMove.right ∨ m2 ≠ QtmMove.right)
    (hRnb : m1 ≠ QtmMove.right ∨ m2 ≠ QtmMove.right)
    (q1 : Q1 ⊕ Q2) (a1 : A) (q2 : Q1 ⊕ Q2) (a2 c d : A) :
    (∑ q' : Q1 ⊕ Q2,
      (composeRule R1 R2 hf1 st2 hf2 st1).step q1 a1 m1 q' c
        * star ((composeRule R1 R2 hf1 st2 hf2 st1).step q2 a2 m2 q' d)) = 0 := by
  rcases q1 with q1 | q1 <;> rcases q2 with q2 | q2
  · by_cases hq1 : q1 = hf1 <;> by_cases hq2 : q2 = hf1
    · rw [hq1, hq2]
      simp only [composeRule_step_inl_halt]
      exact haltL_mul_haltL st2 a1 a2 c d m1 m2 hLnb
    · rw [hq1]
      simp only [composeRule_step_inl_halt,
        composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 q2 hq2]
      exact haltL_mul_dataL R1 st2 q2 a1 a2 c d m1 m2
    · rw [hq2]
      simp only [composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 q1 hq1,
        composeRule_step_inl_halt]
      exact dataL_mul_haltL R1 st2 q1 a1 a2 c d m1 m2
    · simp only [composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 q1 hq1,
        composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 q2 hq2]
      exact dataL_mul_dataL R1 q1 q2 a1 a2 c d m1 m2 (hnL q1 a1 q2 a2 c d)
  · by_cases hq1 : q1 = hf1 <;> by_cases hq2 : q2 = hf2
    · rw [hq1, hq2]
      simp only [composeRule_step_inl_halt, composeRule_step_inr_halt]
      exact haltL_mul_haltR st2 st1 a1 a2 c d m1 m2
    · rw [hq1]
      simp only [composeRule_step_inl_halt,
        composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 q2 hq2]
      exact haltL_mul_dataR R2 hf2 st2 noin2 q2 hq2 a1 a2 c d m1 m2
    · rw [hq2]
      simp only [composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 q1 hq1,
        composeRule_step_inr_halt]
      exact dataL_mul_haltR R1 hf1 st1 noin1 q1 hq1 a1 a2 c d m1 m2
    · simp only [composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 q1 hq1,
        composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 q2 hq2]
      exact dataL_mul_dataR R1 R2 q1 q2 a1 a2 c d m1 m2
  · by_cases hq1 : q1 = hf2 <;> by_cases hq2 : q2 = hf1
    · rw [hq1, hq2]
      simp only [composeRule_step_inr_halt, composeRule_step_inl_halt]
      exact haltR_mul_haltL st2 st1 a1 a2 c d m1 m2
    · rw [hq1]
      simp only [composeRule_step_inr_halt,
        composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 q2 hq2]
      exact haltR_mul_dataL R1 hf1 st1 noin1 q2 hq2 a1 a2 c d m1 m2
    · rw [hq2]
      simp only [composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 q1 hq1,
        composeRule_step_inl_halt]
      exact dataR_mul_haltL R2 hf2 st2 noin2 q1 hq1 a1 a2 c d m1 m2
    · simp only [composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 q1 hq1,
        composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 q2 hq2]
      exact dataR_mul_dataL R1 R2 q1 q2 a1 a2 c d m1 m2
  · by_cases hq1 : q1 = hf2 <;> by_cases hq2 : q2 = hf2
    · rw [hq1, hq2]
      simp only [composeRule_step_inr_halt]
      exact haltR_mul_haltR st1 a1 a2 c d m1 m2 hRnb
    · rw [hq1]
      simp only [composeRule_step_inr_halt,
        composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 q2 hq2]
      exact haltR_mul_dataR R2 st1 q2 a1 a2 c d m1 m2
    · rw [hq2]
      simp only [composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 q1 hq1,
        composeRule_step_inr_halt]
      exact dataR_mul_haltR R2 st1 q1 a1 a2 c d m1 m2
    · simp only [composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 q1 hq1,
        composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 q2 hq2]
      exact dataR_mul_dataR R2 q1 q2 a1 a2 c d m1 m2 (hnR q1 a1 q2 a2 c d)

theorem composeRule_wf_rightStay (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (h1 : R1.LocalWellformed) (h2 : R2.LocalWellformed)
    (noin1 : ∀ (q : Q1) (a : A) (d : QtmMove) (b : A), q ≠ hf1 → R1.step q a d st1 b = 0)
    (noin2 : ∀ (q : Q2) (a : A) (d : QtmMove) (b : A), q ≠ hf2 → R2.step q a d st2 b = 0) :
    ∀ (q1 : Q1 ⊕ Q2) (a1 : A) (q2 : Q1 ⊕ Q2) (a2 c d : A),
      (∑ q' : Q1 ⊕ Q2,
        (composeRule R1 R2 hf1 st2 hf2 st1).step q1 a1 QtmMove.right q' c
          * star ((composeRule R1 R2 hf1 st2 hf2 st1).step q2 a2 QtmMove.stay q' d)) = 0 := by
  intro q1 a1 q2 a2 c d
  exact compose_mul_orth R1 R2 hf1 st2 hf2 st1 h1 h2 noin1 noin2
    QtmMove.right QtmMove.stay h1.2.2.1 h2.2.2.1 (by decide) (by decide) q1 a1 q2 a2 c d

theorem composeRule_wf_stayLeft (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (h1 : R1.LocalWellformed) (h2 : R2.LocalWellformed)
    (noin1 : ∀ (q : Q1) (a : A) (d : QtmMove) (b : A), q ≠ hf1 → R1.step q a d st1 b = 0)
    (noin2 : ∀ (q : Q2) (a : A) (d : QtmMove) (b : A), q ≠ hf2 → R2.step q a d st2 b = 0) :
    ∀ (q1 : Q1 ⊕ Q2) (a1 : A) (q2 : Q1 ⊕ Q2) (a2 c d : A),
      (∑ q' : Q1 ⊕ Q2,
        (composeRule R1 R2 hf1 st2 hf2 st1).step q1 a1 QtmMove.stay q' c
          * star ((composeRule R1 R2 hf1 st2 hf2 st1).step q2 a2 QtmMove.left q' d)) = 0 := by
  intro q1 a1 q2 a2 c d
  exact compose_mul_orth R1 R2 hf1 st2 hf2 st1 h1 h2 noin1 noin2
    QtmMove.stay QtmMove.left h1.2.2.2.1 h2.2.2.2.1 (by decide) (by decide) q1 a1 q2 a2 c d

theorem composeRule_wf_rightLeft (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (h1 : R1.LocalWellformed) (h2 : R2.LocalWellformed)
    (noin1 : ∀ (q : Q1) (a : A) (d : QtmMove) (b : A), q ≠ hf1 → R1.step q a d st1 b = 0)
    (noin2 : ∀ (q : Q2) (a : A) (d : QtmMove) (b : A), q ≠ hf2 → R2.step q a d st2 b = 0) :
    ∀ (q1 : Q1 ⊕ Q2) (a1 : A) (q2 : Q1 ⊕ Q2) (a2 c d : A),
      (∑ q' : Q1 ⊕ Q2,
        (composeRule R1 R2 hf1 st2 hf2 st1).step q1 a1 QtmMove.right q' c
          * star ((composeRule R1 R2 hf1 st2 hf2 st1).step q2 a2 QtmMove.left q' d)) = 0 := by
  intro q1 a1 q2 a2 c d
  exact compose_mul_orth R1 R2 hf1 st2 hf2 st1 h1 h2 noin1 noin2
    QtmMove.right QtmMove.left h1.2.2.2.2 h2.2.2.2.2 (by decide) (by decide) q1 a1 q2 a2 c d

theorem composeRule_localWellformed (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (h1 : R1.LocalWellformed) (h2 : R2.LocalWellformed)
    (noin1 : ∀ (q : Q1) (a : A) (d : QtmMove) (b : A), q ≠ hf1 → R1.step q a d st1 b = 0)
    (noin2 : ∀ (q : Q2) (a : A) (d : QtmMove) (b : A), q ≠ hf2 → R2.step q a d st2 b = 0) :
    (composeRule R1 R2 hf1 st2 hf2 st1).LocalWellformed :=
  ⟨composeRule_wf_norm R1 R2 hf1 st2 hf2 st1 h1 h2,
   composeRule_wf_orth R1 R2 hf1 st2 hf2 st1 h1 h2 noin1 noin2,
   composeRule_wf_rightStay R1 R2 hf1 st2 hf2 st1 h1 h2 noin1 noin2,
   composeRule_wf_stayLeft R1 R2 hf1 st2 hf2 st1 h1 h2 noin1 noin2,
   composeRule_wf_rightLeft R1 R2 hf1 st2 hf2 st1 h1 h2 noin1 noin2⟩

def NormalForm {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (R : QtmRule Q A) (hf st : Q) : Prop :=
  ∀ (a : A) (d : QtmMove) (q' : Q) (b : A),
    R.step hf a d q' b = if d = QtmMove.right ∧ q' = st ∧ b = a then 1 else 0

theorem composeRule_normalForm (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1) :
    NormalForm (composeRule R1 R2 hf1 st2 hf2 st1) (Sum.inr hf2) (Sum.inl st1) := by
  intro a d q' b
  rw [composeRule_step_inr_halt]
  rfl

theorem compose_step_haltL_support (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1) (a : A) (d : QtmMove)
    (q' : Q1 ⊕ Q2) (b : A)
    (h : (composeRule R1 R2 hf1 st2 hf2 st1).step (Sum.inl hf1) a d q' b ≠ 0) :
    d = QtmMove.right ∧ q' = Sum.inr st2 ∧ b = a := by
  rw [composeRule_step_inl_halt] at h
  simp only [haltStepL] at h
  by_cases hd : d = QtmMove.right
  · by_cases hq : q' = Sum.inr st2
    · by_cases hb : b = a
      · exact ⟨hd, hq, hb⟩
      · simp [hd, hq, hb] at h
    · simp [hd, hq] at h
  · simp [hd] at h

theorem compose_step_haltR_support (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1) (a : A) (d : QtmMove)
    (q' : Q1 ⊕ Q2) (b : A)
    (h : (composeRule R1 R2 hf1 st2 hf2 st1).step (Sum.inr hf2) a d q' b ≠ 0) :
    d = QtmMove.right ∧ q' = Sum.inl st1 ∧ b = a := by
  rw [composeRule_step_inr_halt] at h
  simp only [haltStepR] at h
  by_cases hd : d = QtmMove.right
  · by_cases hq : q' = Sum.inl st1
    · by_cases hb : b = a
      · exact ⟨hd, hq, hb⟩
      · simp [hd, hq, hb] at h
    · simp [hd, hq] at h
  · simp [hd] at h

theorem stepTarget_cfgL_halt {st2 : Q2} (c : QtmCfg Q1 A w) :
    QtmRule.stepTarget (cfgL (Q2 := Q2) c) QtmMove.right (Sum.inr st2) (c.2.2 c.2.1)
      = (moveCell c.2.1 QtmMove.right).map (fun j => (Sum.inr st2, j, c.2.2)) := by
  unfold QtmRule.stepTarget cfgL
  have hupd : Function.update c.2.2 c.2.1 (c.2.2 c.2.1) = c.2.2 := by
    funext i; by_cases hi : i = c.2.1 <;> simp [Function.update, hi]
  rw [hupd]

theorem stepTarget_cfgR_halt {st1 : Q1} (c : QtmCfg Q2 A w) :
    QtmRule.stepTarget (cfgR (Q1 := Q1) c) QtmMove.right (Sum.inl st1) (c.2.2 c.2.1)
      = (moveCell c.2.1 QtmMove.right).map (fun j => (Sum.inl st1, j, c.2.2)) := by
  unfold QtmRule.stepTarget cfgR
  have hupd : Function.update c.2.2 c.2.1 (c.2.2 c.2.1) = c.2.2 := by
    funext i; by_cases hi : i = c.2.1 <;> simp [Function.update, hi]
  rw [hupd]

theorem sum_single_trans (q0 : Q1 ⊕ Q2) (a : A) (F : QtmMove → Q1 ⊕ Q2 → A → ℂ) :
    (∑ d : QtmMove, ∑ q' : Q1 ⊕ Q2, ∑ b : A,
      (if d = QtmMove.right ∧ q' = q0 ∧ b = a then F d q' b else 0))
      = F QtmMove.right q0 a := by
  rw [Finset.sum_eq_single QtmMove.right]
  · rw [Finset.sum_eq_single q0]
    · rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ a) h
    · intro q' _ hq'; simp [hq']
    · intro h; exact absurd (Finset.mem_univ q0) h
  · intro d _ hd
    refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun b _ => ?_
    simp [hd]
  · intro h; exact absurd (Finset.mem_univ QtmMove.right) h

theorem compose_stepAmplitude_haltL (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (c : QtmCfg Q1 A w) (hc : c.1 = hf1) (dT : QtmCfg (Q1 ⊕ Q2) A w) :
    (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w (cfgL (Q2 := Q2) c) dT
      = if QtmRule.stepTarget (cfgL (Q2 := Q2) c) QtmMove.right (Sum.inr st2)
            (c.2.2 c.2.1) = some dT then 1 else 0 := by
  obtain ⟨q0, h0, t0⟩ := c
  simp only [cfgL] at hc ⊢
  rw [hc]
  unfold QtmRule.stepAmplitude
  simp only [composeRule_step_inl_halt, haltStepL]
  trans (∑ d : QtmMove, ∑ q' : Q1 ⊕ Q2, ∑ b : A,
        (if d = QtmMove.right ∧ q' = Sum.inr st2 ∧ b = t0 h0
          then (if QtmRule.stepTarget (Sum.inl hf1, h0, t0) d q' b = some dT then 1 else 0)
          else 0))
  · refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun q' _ =>
      Finset.sum_congr rfl fun b _ => ?_
    by_cases hP : QtmRule.stepTarget (Sum.inl hf1, h0, t0) d q' b = some dT <;>
      by_cases hQ : d = QtmMove.right ∧ q' = Sum.inr st2 ∧ b = t0 h0 <;> simp [hP, hQ]
  · rw [sum_single_trans]
    rfl

theorem compose_stepAmplitude_haltR (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (c : QtmCfg Q2 A w) (hc : c.1 = hf2) (dT : QtmCfg (Q1 ⊕ Q2) A w) :
    (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w (cfgR (Q1 := Q1) c) dT
      = if QtmRule.stepTarget (cfgR (Q1 := Q1) c) QtmMove.right (Sum.inl st1)
            (c.2.2 c.2.1) = some dT then 1 else 0 := by
  obtain ⟨q0, h0, t0⟩ := c
  simp only [cfgR] at hc ⊢
  rw [hc]
  unfold QtmRule.stepAmplitude
  simp only [composeRule_step_inr_halt, haltStepR]
  trans (∑ d : QtmMove, ∑ q' : Q1 ⊕ Q2, ∑ b : A,
        (if d = QtmMove.right ∧ q' = Sum.inl st1 ∧ b = t0 h0
          then (if QtmRule.stepTarget (Sum.inr hf2, h0, t0) d q' b = some dT then 1 else 0)
          else 0))
  · refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun q' _ =>
      Finset.sum_congr rfl fun b _ => ?_
    by_cases hP : QtmRule.stepTarget (Sum.inr hf2, h0, t0) d q' b = some dT <;>
      by_cases hQ : d = QtmMove.right ∧ q' = Sum.inl st1 ∧ b = t0 h0 <;> simp [hP, hQ]
  · rw [sum_single_trans]
    rfl

def cfgSumEquiv : QtmCfg (Q1 ⊕ Q2) A w ≃ QtmCfg Q1 A w ⊕ QtmCfg Q2 A w where
  toFun c := match c.1 with
    | Sum.inl q => Sum.inl (q, c.2.1, c.2.2)
    | Sum.inr q => Sum.inr (q, c.2.1, c.2.2)
  invFun s := match s with
    | Sum.inl c => cfgL c
    | Sum.inr c => cfgR c
  left_inv := by
    rintro ⟨q, h, t⟩
    cases q <;> rfl
  right_inv := by
    intro s
    rcases s with c | c <;> rfl

def liftL (ψ : QState (QtmCfg Q1 A w)) : QState (QtmCfg (Q1 ⊕ Q2) A w) :=
  fun c => match c.1 with
    | Sum.inl q => ψ (q, c.2.1, c.2.2)
    | Sum.inr _ => 0

def liftR (ψ : QState (QtmCfg Q2 A w)) : QState (QtmCfg (Q1 ⊕ Q2) A w) :=
  fun c => match c.1 with
    | Sum.inl _ => 0
    | Sum.inr q => ψ (q, c.2.1, c.2.2)

def NonHaltSupported {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] {w : ℕ} (hf : Q) (ψ : QState (QtmCfg Q A w)) : Prop :=
  ∀ c, ψ c ≠ 0 → c.1 ≠ hf

def HaltSupported {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] {w : ℕ} (hf : Q) (ψ : QState (QtmCfg Q A w)) : Prop :=
  ∀ c, ψ c ≠ 0 → c.1 = hf

@[simp] theorem liftL_cfgL (ψ : QState (QtmCfg Q1 A w)) (c : QtmCfg Q1 A w) :
    liftL (Q2 := Q2) ψ (cfgL c) = ψ c := rfl

@[simp] theorem liftL_cfgR (ψ : QState (QtmCfg Q1 A w)) (c : QtmCfg Q2 A w) :
    liftL (Q2 := Q2) ψ (cfgR c) = 0 := rfl

@[simp] theorem liftR_cfgL (ψ : QState (QtmCfg Q2 A w)) (c : QtmCfg Q1 A w) :
    liftR (Q1 := Q1) ψ (cfgL c) = 0 := rfl

@[simp] theorem liftR_cfgR (ψ : QState (QtmCfg Q2 A w)) (c : QtmCfg Q2 A w) :
    liftR (Q1 := Q1) ψ (cfgR c) = ψ c := rfl

theorem sum_cfg_split (F : QtmCfg (Q1 ⊕ Q2) A w → ℂ) :
    (∑ c, F c) = (∑ c1 : QtmCfg Q1 A w, F (cfgL c1)) +
      (∑ c2 : QtmCfg Q2 A w, F (cfgR c2)) := by
  rw [← Equiv.sum_comp (cfgSumEquiv (Q1 := Q1) (Q2 := Q2) (A := A) (w := w)).symm F]
  rw [Fintype.sum_sum_type]
  rfl

theorem compose_stepAmplitude_cfgL_inr_zero (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (c : QtmCfg Q1 A w) (hc : c.1 ≠ hf1) (d' : QtmCfg Q2 A w) :
    (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w (cfgL c) (cfgR d') = 0 := by
  unfold QtmRule.stepAmplitude
  refine Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun q' _ =>
    Finset.sum_eq_zero fun b _ => ?_
  by_cases hT : QtmRule.stepTarget (cfgL (Q2 := Q2) c) d q' b = some (cfgR (Q1 := Q1) d')
  · rw [if_pos hT]
    rcases q' with q1' | q2'
    · unfold QtmRule.stepTarget cfgL cfgR at hT
      rcases hm : moveCell c.2.1 d with _ | j <;> simp [hm] at hT
    · change (composeRule R1 R2 hf1 st2 hf2 st1).step (Sum.inl c.1)
          (c.2.2 c.2.1) d (Sum.inr q2') b = 0
      rw [composeRule_step_inl_data R1 R2 hf1 st2 hf2 st1 c.1 hc]
      rfl
  · rw [if_neg hT]

theorem compose_stepAmplitude_cfgR_inl_zero (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (c : QtmCfg Q2 A w) (hc : c.1 ≠ hf2) (d' : QtmCfg Q1 A w) :
    (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w (cfgR c) (cfgL d') = 0 := by
  unfold QtmRule.stepAmplitude
  refine Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun q' _ =>
    Finset.sum_eq_zero fun b _ => ?_
  by_cases hT : QtmRule.stepTarget (cfgR (Q1 := Q1) c) d q' b = some (cfgL (Q2 := Q2) d')
  · rw [if_pos hT]
    rcases q' with q1' | q2'
    · change (composeRule R1 R2 hf1 st2 hf2 st1).step (Sum.inr c.1)
          (c.2.2 c.2.1) d (Sum.inl q1') b = 0
      rw [composeRule_step_inr_data R1 R2 hf1 st2 hf2 st1 c.1 hc]
      rfl
    · unfold QtmRule.stepTarget cfgR cfgL at hT
      rcases hm : moveCell c.2.1 d with _ | j <;> simp [hm] at hT
  · rw [if_neg hT]

theorem compose_evolve_liftL_cfgL (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (ψ : QState (QtmCfg Q1 A w)) (hψ : NonHaltSupported (A := A) (w := w) hf1 ψ)
    (c' : QtmCfg Q1 A w) :
    (composeRule R1 R2 hf1 st2 hf2 st1).evolve w (liftL (Q2 := Q2) ψ) (cfgL c')
      = R1.evolve w ψ c' := by
  show (∑ c, liftL (Q2 := Q2) ψ c *
      (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w c (cfgL c'))
      = ∑ c, ψ c * R1.stepAmplitude w c c'
  rw [sum_cfg_split (fun c => liftL (Q2 := Q2) ψ c *
    (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w c (cfgL c'))]
  have hzero : (∑ c2 : QtmCfg Q2 A w, liftL (Q2 := Q2) ψ (cfgR c2) *
      (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w (cfgR c2) (cfgL c')) = 0 := by
    refine Finset.sum_eq_zero fun c2 _ => ?_
    simp
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun c1 _ => ?_
  rw [liftL_cfgL]
  by_cases h0 : ψ c1 = 0
  · simp [h0]
  · rw [compose_stepAmplitude_cfgL R1 R2 hf1 st2 hf2 st1 c1 c' (hψ c1 h0)]

theorem compose_evolve_liftL_cfgR (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (ψ : QState (QtmCfg Q1 A w)) (hψ : NonHaltSupported (A := A) (w := w) hf1 ψ)
    (c' : QtmCfg Q2 A w) :
    (composeRule R1 R2 hf1 st2 hf2 st1).evolve w (liftL (Q2 := Q2) ψ) (cfgR c') = 0 := by
  show (∑ c, liftL (Q2 := Q2) ψ c *
      (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w c (cfgR c')) = 0
  rw [sum_cfg_split (fun c => liftL (Q2 := Q2) ψ c *
    (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w c (cfgR c'))]
  have h1 : (∑ c1 : QtmCfg Q1 A w, liftL (Q2 := Q2) ψ (cfgL c1) *
      (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w (cfgL c1) (cfgR c')) = 0 := by
    refine Finset.sum_eq_zero fun c1 _ => ?_
    rw [liftL_cfgL]
    by_cases h0 : ψ c1 = 0
    · simp [h0]
    · rw [compose_stepAmplitude_cfgL_inr_zero R1 R2 hf1 st2 hf2 st1 c1 (hψ c1 h0) c']
      simp
  have h2 : (∑ c2 : QtmCfg Q2 A w, liftL (Q2 := Q2) ψ (cfgR c2) *
      (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w (cfgR c2) (cfgR c')) = 0 := by
    refine Finset.sum_eq_zero fun c2 _ => ?_
    simp
  rw [h1, h2, add_zero]

theorem compose_evolve_liftL (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (ψ : QState (QtmCfg Q1 A w)) (hψ : NonHaltSupported (A := A) (w := w) hf1 ψ) :
    (composeRule R1 R2 hf1 st2 hf2 st1).evolve w (liftL (Q2 := Q2) ψ)
      = liftL (Q2 := Q2) (R1.evolve w ψ) := by
  funext c'
  rcases c' with ⟨q', h', t'⟩
  cases q' with
  | inl q0 =>
      exact compose_evolve_liftL_cfgL R1 R2 hf1 st2 hf2 st1 ψ hψ (q0, h', t')
  | inr q0 =>
      rw [show (composeRule R1 R2 hf1 st2 hf2 st1).evolve w (liftL (Q2 := Q2) ψ)
            (Sum.inr q0, h', t') = 0 from
            compose_evolve_liftL_cfgR R1 R2 hf1 st2 hf2 st1 ψ hψ (q0, h', t')]
      rfl

def handoffL (st2 : Q2) (ψ : QState (QtmCfg Q1 A w)) :
    QState (QtmCfg (Q1 ⊕ Q2) A w) :=
  fun c' => ∑ c : QtmCfg Q1 A w,
    ψ c * (if QtmRule.stepTarget (cfgL (Q2 := Q2) c) QtmMove.right (Sum.inr st2)
              (c.2.2 c.2.1) = some c' then (1 : ℂ) else 0)

theorem compose_stepAmplitude_haltL_indicator (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (c : QtmCfg Q1 A w) (hc : c.1 = hf1) (c' : QtmCfg (Q1 ⊕ Q2) A w) :
    (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w (cfgL c) c'
      = if QtmRule.stepTarget (cfgL (Q2 := Q2) c) QtmMove.right (Sum.inr st2)
            (c.2.2 c.2.1) = some c' then 1 else 0 := by
  obtain ⟨q0, h0, t0⟩ := c
  simp only [cfgL] at hc ⊢
  rw [hc]
  unfold QtmRule.stepAmplitude
  simp only [composeRule_step_inl_halt, haltStepL]
  trans (∑ d : QtmMove, ∑ q' : Q1 ⊕ Q2, ∑ b : A,
        (if d = QtmMove.right ∧ q' = Sum.inr st2 ∧ b = t0 h0
          then (if QtmRule.stepTarget (Sum.inl hf1, h0, t0) d q' b = some c' then 1 else 0)
          else 0))
  · refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun q' _ =>
      Finset.sum_congr rfl fun b _ => ?_
    by_cases hP : QtmRule.stepTarget (Sum.inl hf1, h0, t0) d q' b = some c' <;>
      by_cases hQ : d = QtmMove.right ∧ q' = Sum.inr st2 ∧ b = t0 h0 <;> simp [hP, hQ]
  · rw [sum_single_trans]
    rfl

theorem handoffL_cfgL (st2 : Q2) (ψ : QState (QtmCfg Q1 A w)) (c : QtmCfg Q1 A w) :
    handoffL st2 ψ (cfgL c) = 0 := by
  unfold handoffL
  refine Finset.sum_eq_zero fun c0 _ => ?_
  have hne : QtmRule.stepTarget (cfgL (Q2 := Q2) c0) QtmMove.right (Sum.inr st2)
      (c0.2.2 c0.2.1) ≠ some (cfgL (Q2 := Q2) c) := by
    rw [stepTarget_cfgL_halt]
    rcases hm : moveCell c0.2.1 QtmMove.right with _ | j <;> simp [hm, cfgL]
  simp [hne]

def handoffState (st2 : Q2) (ψ : QState (QtmCfg Q1 A w)) : QState (QtmCfg Q2 A w) :=
  fun c => handoffL st2 ψ (cfgR (Q1 := Q1) c)

theorem liftR_handoffState (st2 : Q2) (ψ : QState (QtmCfg Q1 A w)) :
    liftR (Q1 := Q1) (handoffState st2 ψ) = handoffL st2 ψ := by
  funext c'
  rcases c' with ⟨q', h', t'⟩
  cases q' with
  | inl q0 =>
      change (0 : ℂ) = handoffL st2 ψ (cfgL (Q2 := Q2) (q0, h', t'))
      rw [handoffL_cfgL]
  | inr q0 => rfl

theorem compose_evolve_liftL_halt (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (ψ : QState (QtmCfg Q1 A w)) (hψ : HaltSupported (A := A) (w := w) hf1 ψ) :
    (composeRule R1 R2 hf1 st2 hf2 st1).evolve w (liftL (Q2 := Q2) ψ) = handoffL st2 ψ := by
  funext c'
  show (∑ c, liftL (Q2 := Q2) ψ c *
      (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w c c')
      = ∑ c : QtmCfg Q1 A w, ψ c *
          (if QtmRule.stepTarget (cfgL (Q2 := Q2) c) QtmMove.right (Sum.inr st2)
            (c.2.2 c.2.1) = some c' then (1 : ℂ) else 0)
  rw [sum_cfg_split (fun c => liftL (Q2 := Q2) ψ c *
    (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w c c')]
  have h2 : (∑ c2 : QtmCfg Q2 A w, liftL (Q2 := Q2) ψ (cfgR c2) *
      (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w (cfgR c2) c') = 0 := by
    refine Finset.sum_eq_zero fun c2 _ => ?_
    simp
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun c1 _ => ?_
  rw [liftL_cfgL]
  by_cases h0 : ψ c1 = 0
  · simp [h0]
  · rw [compose_stepAmplitude_haltL_indicator R1 R2 hf1 st2 hf2 st1 c1 (hψ c1 h0) c']

theorem compose_evolve_liftR_cfgR (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (ψ : QState (QtmCfg Q2 A w)) (hψ : NonHaltSupported (A := A) (w := w) hf2 ψ)
    (c' : QtmCfg Q2 A w) :
    (composeRule R1 R2 hf1 st2 hf2 st1).evolve w (liftR (Q1 := Q1) ψ) (cfgR c')
      = R2.evolve w ψ c' := by
  show (∑ c, liftR (Q1 := Q1) ψ c *
      (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w c (cfgR c'))
      = ∑ c, ψ c * R2.stepAmplitude w c c'
  rw [sum_cfg_split (fun c => liftR (Q1 := Q1) ψ c *
    (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w c (cfgR c'))]
  have hzero : (∑ c1 : QtmCfg Q1 A w, liftR (Q1 := Q1) ψ (cfgL c1) *
      (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w (cfgL c1) (cfgR c')) = 0 := by
    refine Finset.sum_eq_zero fun c1 _ => ?_
    simp
  rw [hzero, zero_add]
  refine Finset.sum_congr rfl fun c2 _ => ?_
  rw [liftR_cfgR]
  by_cases h0 : ψ c2 = 0
  · simp [h0]
  · rw [compose_stepAmplitude_cfgR R1 R2 hf1 st2 hf2 st1 c2 c' (hψ c2 h0)]

theorem compose_evolve_liftR_cfgL (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (ψ : QState (QtmCfg Q2 A w)) (hψ : NonHaltSupported (A := A) (w := w) hf2 ψ)
    (c' : QtmCfg Q1 A w) :
    (composeRule R1 R2 hf1 st2 hf2 st1).evolve w (liftR (Q1 := Q1) ψ) (cfgL c') = 0 := by
  show (∑ c, liftR (Q1 := Q1) ψ c *
      (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w c (cfgL c')) = 0
  rw [sum_cfg_split (fun c => liftR (Q1 := Q1) ψ c *
    (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w c (cfgL c'))]
  have h1 : (∑ c1 : QtmCfg Q1 A w, liftR (Q1 := Q1) ψ (cfgL c1) *
      (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w (cfgL c1) (cfgL c')) = 0 := by
    refine Finset.sum_eq_zero fun c1 _ => ?_
    simp
  have h2 : (∑ c2 : QtmCfg Q2 A w, liftR (Q1 := Q1) ψ (cfgR c2) *
      (composeRule R1 R2 hf1 st2 hf2 st1).stepAmplitude w (cfgR c2) (cfgL c')) = 0 := by
    refine Finset.sum_eq_zero fun c2 _ => ?_
    rw [liftR_cfgR]
    by_cases h0 : ψ c2 = 0
    · simp [h0]
    · rw [compose_stepAmplitude_cfgR_inl_zero R1 R2 hf1 st2 hf2 st1 c2 (hψ c2 h0) c']
      simp
  rw [h1, h2, add_zero]

theorem compose_evolve_liftR (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (ψ : QState (QtmCfg Q2 A w)) (hψ : NonHaltSupported (A := A) (w := w) hf2 ψ) :
    (composeRule R1 R2 hf1 st2 hf2 st1).evolve w (liftR (Q1 := Q1) ψ)
      = liftR (Q1 := Q1) (R2.evolve w ψ) := by
  funext c'
  rcases c' with ⟨q', h', t'⟩
  cases q' with
  | inl q0 =>
      rw [show (composeRule R1 R2 hf1 st2 hf2 st1).evolve w (liftR (Q1 := Q1) ψ)
            (Sum.inl q0, h', t') = 0 from
            compose_evolve_liftR_cfgL R1 R2 hf1 st2 hf2 st1 ψ hψ (q0, h', t')]
      rfl
  | inr q0 =>
      exact compose_evolve_liftR_cfgR R1 R2 hf1 st2 hf2 st1 ψ hψ (q0, h', t')

theorem compose_iterate_liftL (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (ψ : QState (QtmCfg Q1 A w)) (t : ℕ)
    (h : ∀ s, s < t → NonHaltSupported (A := A) (w := w) hf1 ((R1.evolve w)^[s] ψ)) :
    ((composeRule R1 R2 hf1 st2 hf2 st1).evolve w)^[t] (liftL (Q2 := Q2) ψ)
      = liftL (Q2 := Q2) ((R1.evolve w)^[t] ψ) := by
  induction t with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply' ((composeRule R1 R2 hf1 st2 hf2 st1).evolve w) n
            (liftL (Q2 := Q2) ψ),
          Function.iterate_succ_apply' (R1.evolve w) n ψ]
      have hn : ∀ s, s < n →
          NonHaltSupported (A := A) (w := w) hf1 ((R1.evolve w)^[s] ψ) :=
        fun s hs => h s (Nat.lt_trans hs (Nat.lt_succ_self n))
      rw [ih hn,
        compose_evolve_liftL R1 R2 hf1 st2 hf2 st1 ((R1.evolve w)^[n] ψ)
          (h n (Nat.lt_succ_self n))]

theorem compose_runSteps_liftL (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (ψ : QState (QtmCfg Q1 A w)) (t : ℕ)
    (h : ∀ s, s < t → NonHaltSupported (A := A) (w := w) hf1 (R1.runSteps w s ψ)) :
    (composeRule R1 R2 hf1 st2 hf2 st1).runSteps w t (liftL (Q2 := Q2) ψ)
      = liftL (Q2 := Q2) (R1.runSteps w t ψ) := by
  simpa [QtmRule.runSteps] using
    compose_iterate_liftL R1 R2 hf1 st2 hf2 st1 ψ t h

theorem compose_iterate_liftR (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (ψ : QState (QtmCfg Q2 A w)) (t : ℕ)
    (h : ∀ s, s < t → NonHaltSupported (A := A) (w := w) hf2 ((R2.evolve w)^[s] ψ)) :
    ((composeRule R1 R2 hf1 st2 hf2 st1).evolve w)^[t] (liftR (Q1 := Q1) ψ)
      = liftR (Q1 := Q1) ((R2.evolve w)^[t] ψ) := by
  induction t with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply' ((composeRule R1 R2 hf1 st2 hf2 st1).evolve w) n
            (liftR (Q1 := Q1) ψ),
          Function.iterate_succ_apply' (R2.evolve w) n ψ]
      have hn : ∀ s, s < n →
          NonHaltSupported (A := A) (w := w) hf2 ((R2.evolve w)^[s] ψ) :=
        fun s hs => h s (Nat.lt_trans hs (Nat.lt_succ_self n))
      rw [ih hn,
        compose_evolve_liftR R1 R2 hf1 st2 hf2 st1 ((R2.evolve w)^[n] ψ)
          (h n (Nat.lt_succ_self n))]

theorem compose_runSteps_liftR (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (ψ : QState (QtmCfg Q2 A w)) (t : ℕ)
    (h : ∀ s, s < t → NonHaltSupported (A := A) (w := w) hf2 (R2.runSteps w s ψ)) :
    (composeRule R1 R2 hf1 st2 hf2 st1).runSteps w t (liftR (Q1 := Q1) ψ)
      = liftR (Q1 := Q1) (R2.runSteps w t ψ) := by
  simpa [QtmRule.runSteps] using
    compose_iterate_liftR R1 R2 hf1 st2 hf2 st1 ψ t h

theorem compose_runSteps_haltL (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (ψ : QState (QtmCfg Q1 A w)) (t1 : ℕ)
    (h : ∀ s, s < t1 → NonHaltSupported (A := A) (w := w) hf1 (R1.runSteps w s ψ))
    (hHalt : HaltSupported (A := A) (w := w) hf1 (R1.runSteps w t1 ψ)) :
    (composeRule R1 R2 hf1 st2 hf2 st1).runSteps w (t1 + 1) (liftL (Q2 := Q2) ψ)
      = liftR (Q1 := Q1) (handoffState st2 (R1.runSteps w t1 ψ)) := by
  have hstep : ((composeRule R1 R2 hf1 st2 hf2 st1).evolve w)^[t1 + 1] (liftL (Q2 := Q2) ψ)
      = (composeRule R1 R2 hf1 st2 hf2 st1).evolve w
          (((composeRule R1 R2 hf1 st2 hf2 st1).evolve w)^[t1] (liftL (Q2 := Q2) ψ)) :=
    Function.iterate_succ_apply' ((composeRule R1 R2 hf1 st2 hf2 st1).evolve w) t1
      (liftL (Q2 := Q2) ψ)
  rw [QtmRule.runSteps, hstep]
  rw [show ((composeRule R1 R2 hf1 st2 hf2 st1).evolve w)^[t1] (liftL (Q2 := Q2) ψ)
      = liftL (Q2 := Q2) (R1.runSteps w t1 ψ) from compose_runSteps_liftL R1 R2 hf1 st2 hf2 st1 ψ t1 h]
  rw [compose_evolve_liftL_halt R1 R2 hf1 st2 hf2 st1 (R1.runSteps w t1 ψ) hHalt]
  rw [liftR_handoffState]

theorem compose_runSteps_twoPhase (R1 : QtmRule Q1 A) (R2 : QtmRule Q2 A)
    (hf1 : Q1) (st2 : Q2) (hf2 : Q2) (st1 : Q1)
    (ψ : QState (QtmCfg Q1 A w)) (t1 t2 : ℕ)
    (hL : ∀ s, s < t1 → NonHaltSupported (A := A) (w := w) hf1 (R1.runSteps w s ψ))
    (hHalt : HaltSupported (A := A) (w := w) hf1 (R1.runSteps w t1 ψ))
    (hR : ∀ s, s < t2 → NonHaltSupported (A := A) (w := w) hf2
      (R2.runSteps w s (handoffState st2 (R1.runSteps w t1 ψ)))) :
    (composeRule R1 R2 hf1 st2 hf2 st1).runSteps w (t1 + 1 + t2) (liftL (Q2 := Q2) ψ)
      = liftR (Q1 := Q1) (R2.runSteps w t2 (handoffState st2 (R1.runSteps w t1 ψ))) := by
  have hsplit : (composeRule R1 R2 hf1 st2 hf2 st1).runSteps w (t1 + 1 + t2) (liftL (Q2 := Q2) ψ)
      = (composeRule R1 R2 hf1 st2 hf2 st1).runSteps w t2
          ((composeRule R1 R2 hf1 st2 hf2 st1).runSteps w (t1 + 1) (liftL (Q2 := Q2) ψ)) := by
    rw [show t1 + 1 + t2 = t2 + (t1 + 1) by ring, QtmRule.runSteps,
      Function.iterate_add_apply]
    rfl
  rw [hsplit, compose_runSteps_haltL R1 R2 hf1 st2 hf2 st1 ψ t1 hL hHalt]
  exact compose_runSteps_liftR R1 R2 hf1 st2 hf2 st1
    (handoffState st2 (R1.runSteps w t1 ψ)) t2 hR

end Qatlib.Papers.QWeakness97.MainResults
