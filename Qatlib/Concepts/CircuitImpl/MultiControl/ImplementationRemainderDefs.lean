/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis
import Qatlib.Foundations.StandardModel.WindowSim.QtmSimulationDefs

/-!
# Finite-window transitions with explicit escape outcomes

This module studies the finite-window transition of `LocalQTM` and separates the mass retained
inside the window from transitions that leave its boundary. `windowEscapeMass` records the lost
column mass, while `WindowFull` and `windowStepFull` include explicit escape outcomes in the
local quantum Turing machine setting of [BernsteinVazirani1997].

The full transition has orthonormal columns and preserves the squared norm of arbitrary complex
states. Consequently, the in-window transition and all its natural powers are contractions. The
final lemmas describe which input symbols fit in `initWindowCfg` and which initialized cells are
blank.

## Main statements

* `windowStep_columnNorm_add_windowEscapeMass`: Balance between in-window column mass and escape
  mass.
* `windowStepFull_gram`: Orthonormality of the full transition columns.
* `windowStepFull_state_add_esc`: Squared-norm preservation after including escape outputs.
* `windowStep_pow_contraction`: Contraction of every natural power of the in-window transition.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section



namespace Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Foundations.StandardDefs.WindowSim
section B3WindowWellformed

variable {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
  [DecidableEq A]

/-- Two window configurations are equal when their head positions, internal states, and tapes
are equal. -/
private theorem windowCfg_eq {c c' : WindowCfg t Q A} (h : c.head = c'.head)
    (hs : c.state = c'.state) (ht : c.tape = c'.tape) : c = c' := by
  obtain ⟨h1, s1, τ1⟩ := c
  obtain ⟨h2, s2, τ2⟩ := c'
  simp only [WindowCfg.mk.injEq] at h hs ht ⊢
  exact ⟨h, hs, ht⟩

/-- A left move from `h` reaches `k` exactly when `h` is positive and `k.val + 1 = h.val`. -/
private lemma moveCell_left_iff {h k : Fin (2 * t + 1)} :
    moveCell QtmMove.left h = some k ↔ 0 < h.val ∧ k.val + 1 = h.val := by
  by_cases hh : h.val = 0
  · simp [moveCell, hh]
  · have hlt : h.val < 2 * t + 1 := h.isLt
    constructor
    · intro hc
      simp only [moveCell, dif_neg hh] at hc
      have hv : h.val - 1 = k.val := congrArg Fin.val (Option.some.inj hc)
      omega
    · rintro ⟨_, hc⟩
      have hmc : moveCell QtmMove.left h = some ⟨h.val - 1, by omega⟩ := by
        simp only [moveCell, dif_neg hh]
      rw [hmc]
      refine congrArg some (Fin.ext ?_)
      show h.val - 1 = k.val
      omega

/-- A stationary move from `h` reaches `k` exactly when their cell indices are equal. -/
private lemma moveCell_stay_iff {h k : Fin (2 * t + 1)} :
    moveCell QtmMove.stay h = some k ↔ k.val = h.val := by
  simp only [moveCell, Option.some.injEq, Fin.ext_iff]
  exact eq_comm

/-- A right move from `h` reaches `k` exactly when `h` is below the right boundary and `k.val =
h.val + 1`. -/
private lemma moveCell_right_iff {h k : Fin (2 * t + 1)} :
    moveCell QtmMove.right h = some k ↔ h.val < 2 * t ∧ k.val = h.val + 1 := by
  by_cases hh : h.val = 2 * t
  · simp [moveCell, hh]
  · have hlt : h.val < 2 * t + 1 := h.isLt
    constructor
    · intro hc
      simp only [moveCell, dif_neg hh] at hc
      have hv : h.val + 1 = k.val := congrArg Fin.val (Option.some.inj hc)
      omega
    · rintro ⟨_, hc⟩
      have hmc : moveCell QtmMove.right h = some ⟨h.val + 1, by omega⟩ := by
        simp only [moveCell, dif_neg hh]
      rw [hmc]
      refine congrArg some (Fin.ext ?_)
      show h.val + 1 = k.val
      omega

/-- A left move leaves the window exactly when the head is at cell zero. -/
private lemma moveCell_left_none {h : Fin (2 * t + 1)} :
    moveCell QtmMove.left h = none ↔ h.val = 0 := by
  by_cases hh : h.val = 0 <;> simp [moveCell, hh]

/-- A right move leaves the window exactly when the head is at cell `2 * t`. -/
private lemma moveCell_right_none {h : Fin (2 * t + 1)} :
    moveCell QtmMove.right h = none ↔ h.val = 2 * t := by
  by_cases hh : h.val = 2 * t <;> simp [moveCell, hh]

/-- A stationary head move always remains inside the window. -/
private lemma moveCell_stay_ne_none (h : Fin (2 * t + 1)) :
    moveCell QtmMove.stay h ≠ none := by simp [moveCell]

/-- For any fixed move direction, equal optional destination cells imply equal starting cells. -/
private lemma moveCell_inj (d : QtmMove) {h₁ h₂ : Fin (2 * t + 1)}
    (h : moveCell d h₁ = moveCell d h₂) : h₁ = h₂ := by
  cases d with
  | left =>
    rcases hh : (moveCell QtmMove.left h₁) with _ | k
    · rw [hh] at h
      have e₁ := moveCell_left_none.mp hh
      have e₂ := moveCell_left_none.mp h.symm
      exact Fin.ext (by omega)
    · rw [hh] at h
      obtain ⟨_, q₁⟩ := moveCell_left_iff.mp hh
      obtain ⟨_, q₂⟩ := moveCell_left_iff.mp h.symm
      exact Fin.ext (by omega)
  | stay =>
    have hs : some h₁ = some h₂ := by simpa only [moveCell] using! h
    exact Option.some.inj hs
  | right =>
    rcases hh : (moveCell QtmMove.right h₁) with _ | k
    · rw [hh] at h
      have e₁ := moveCell_right_none.mp hh
      have e₂ := moveCell_right_none.mp h.symm
      exact Fin.ext (by omega)
    · rw [hh] at h
      obtain ⟨_, q₁⟩ := moveCell_right_iff.mp hh
      obtain ⟨_, q₂⟩ := moveCell_right_iff.mp h.symm
      exact Fin.ext (by omega)

/-- Two moves from the same starting cell that reach the same in-window destination have equal
directions. -/
private lemma moveCell_some_inj (d₁ d₂ : QtmMove) {h k : Fin (2 * t + 1)}
    (h₁e : moveCell d₁ h = some k) (h₂e : moveCell d₂ h = some k) : d₁ = d₂ := by
  rcases d₁ with _ | _ | _ <;> rcases d₂ with _ | _ | _
  any_goals rfl
  all_goals exfalso
  · have e₁ := moveCell_left_iff.mp h₁e
    have e₂ := moveCell_stay_iff.mp h₂e
    omega
  · have e₁ := moveCell_left_iff.mp h₁e
    have e₂ := moveCell_right_iff.mp h₂e
    omega
  · have e₁ := moveCell_stay_iff.mp h₁e
    have e₂ := moveCell_left_iff.mp h₂e
    omega
  · have e₁ := moveCell_stay_iff.mp h₁e
    have e₂ := moveCell_right_iff.mp h₂e
    omega
  · have e₁ := moveCell_right_iff.mp h₁e
    have e₂ := moveCell_left_iff.mp h₂e
    omega
  · have e₁ := moveCell_right_iff.mp h₁e
    have e₂ := moveCell_stay_iff.mp h₂e
    omega

/-- The transition amplitude for one specified head move between two window configurations, zero
unless the destination head is correct and the tape agrees away from the written cell. -/
private def stepAmp (M : LocalQTM Q A) (c : WindowCfg t Q A) (d : QtmMove)
    (c' : WindowCfg t Q A) : ℂ :=
  if moveCell d c.head = some c'.head ∧
      ∀ j : Fin (2 * t + 1), j ≠ c.head → c'.tape j = c.tape j
  then M.step c.state (c.tape c.head) d c'.state (c'.tape c.head) else 0

/-- A window transition entry is the sum of the move-specific amplitudes over all head
directions. -/
private lemma windowStep_apply (M : LocalQTM Q A) (c' c : WindowCfg t Q A) :
    windowStep M c' c = ∑ d : QtmMove, stepAmp M c d c' := by
  simp only [windowStep, Matrix.of_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  unfold stepAmp
  by_cases hmc : moveCell d c.head = some c'.head
  · by_cases hag : ∀ j : Fin (2 * t + 1), j ≠ c.head → c'.tape j = c.tape j
    · have hR : (∑ q' : Q, ∑ b : A,
          if moveCell d c.head = some c'.head ∧ c'.state = q' ∧
              ∀ j : Fin (2 * t + 1), c'.tape j = if j = c.head then b else c.tape j
          then M.step c.state (c.tape c.head) d q' b else 0) =
          M.step c.state (c.tape c.head) d c'.state (c'.tape c.head) := by
        rw [Finset.sum_eq_single_of_mem c'.state (Finset.mem_univ _)
          (fun q' _ hq' => Finset.sum_eq_zero fun b _ =>
            if_neg (fun ht => hq' ht.2.1.symm))]
        rw [Finset.sum_eq_single_of_mem (c'.tape c.head) (Finset.mem_univ _)
          (fun b _ hb => if_neg (fun ht => hb (by
            have hj := ht.2.2 c.head
            rw [if_pos rfl] at hj
            exact hj.symm)))]
        rw [if_pos ⟨hmc, rfl, fun j => by
          by_cases hj : j = c.head
          · simp [hj]
          · simp [hj, hag j hj]⟩]
      rw [hR, if_pos ⟨hmc, hag⟩]
    · rw [if_neg (fun h => hag h.2)]
      refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun b _ =>
        if_neg (fun ht => hag (fun j hj => (ht.2.2 j).trans (if_neg hj)))
  · rw [if_neg (fun h => hmc h.1)]
    refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun b _ =>
      if_neg (fun ht => hmc ht.1)

/-- The conjugate of a window transition entry is the sum of the conjugates of its move-specific
amplitudes. -/
private lemma star_stepAmp_sum (M : LocalQTM Q A) (c c' : WindowCfg t Q A) :
    star (windowStep M c' c) = ∑ d : QtmMove, star (stepAmp M c d c') := by
  rw [windowStep_apply, star_sum]

/-- The product of a conjugated conditional amplitude and another conditional amplitude is
nonzero only when both conditions hold. -/
private lemma star_ite_mul (p q : Prop) [Decidable p] [Decidable q] (x y : ℂ) :
    star (if p then x else 0) * (if q then y else 0) = if p ∧ q then star x * y else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- Expands the inner product of two window transition columns into a double sum over move
directions and a sum over output configurations. -/
private lemma inner_expand (M : LocalQTM Q A) (c₁ c₂ : WindowCfg t Q A) :
    ∑ c' : WindowCfg t Q A, star (windowStep M c' c₁) * windowStep M c' c₂ =
      ∑ d₁ : QtmMove, ∑ d₂ : QtmMove, ∑ c' : WindowCfg t Q A,
        star (stepAmp M c₁ d₁ c') * stepAmp M c₂ d₂ c' := by
  have h1 : ∀ c' : WindowCfg t Q A,
      star (windowStep M c' c₁) * windowStep M c' c₂ =
        ∑ d₁ : QtmMove, ∑ d₂ : QtmMove,
          star (stepAmp M c₁ d₁ c') * stepAmp M c₂ d₂ c' := by
    intro c'
    rw [star_stepAmp_sum, windowStep_apply, Finset.sum_mul_sum]
  calc ∑ c' : WindowCfg t Q A, star (windowStep M c' c₁) * windowStep M c' c₂
      = ∑ c' : WindowCfg t Q A, ∑ d₁ : QtmMove, ∑ d₂ : QtmMove,
          star (stepAmp M c₁ d₁ c') * stepAmp M c₂ d₂ c' :=
        Finset.sum_congr rfl fun c' _ => h1 c'
    _ = ∑ d₁ : QtmMove, ∑ c' : WindowCfg t Q A, ∑ d₂ : QtmMove,
          star (stepAmp M c₁ d₁ c') * stepAmp M c₂ d₂ c' := Finset.sum_comm
    _ = ∑ d₁ : QtmMove, ∑ d₂ : QtmMove, ∑ c' : WindowCfg t Q A,
          star (stepAmp M c₁ d₁ c') * stepAmp M c₂ d₂ c' :=
        Finset.sum_congr rfl fun d₁ _ => Finset.sum_comm

/-- For equal write positions and tapes agreeing away from that position, the constrained
configuration sum reduces to a sum over the output state and the single written symbol. -/
private lemma sum_write_one (k k₁ k₂ : Fin (2 * t + 1)) (σ₁ σ₂ : Fin (2 * t + 1) → A)
    (F : WindowCfg t Q A → ℂ) (hk : k₁ = k₂)
    (hcomp : ∀ j : Fin (2 * t + 1), j ≠ k₁ → σ₁ j = σ₂ j) :
    ∑ c' : WindowCfg t Q A,
      (if c'.head = k ∧ (∀ j : Fin (2 * t + 1), j ≠ k₁ → c'.tape j = σ₁ j) ∧
          (∀ j : Fin (2 * t + 1), j ≠ k₂ → c'.tape j = σ₂ j) then F c' else 0) =
      ∑ q : Q, ∑ b : A, F ⟨k, q, fun j => if j = k₁ then b else σ₁ j⟩ := by
  subst hk
  classical
  have hbij : ∑ c' ∈ (Finset.univ : Finset (WindowCfg t Q A)).filter
      (fun c' => c'.head = k ∧ (∀ j : Fin (2 * t + 1), j ≠ k₁ → c'.tape j = σ₁ j) ∧
        (∀ j : Fin (2 * t + 1), j ≠ k₁ → c'.tape j = σ₂ j)), F c'
      = ∑ p : Q × A, F ⟨k, p.1, fun j => if j = k₁ then p.2 else σ₁ j⟩ := by
    refine Finset.sum_bij
      (fun (c' : WindowCfg t Q A) (_ : c' ∈
        (Finset.univ : Finset (WindowCfg t Q A)).filter _) => (c'.state, c'.tape k₁))
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro a₁ ha₁ a₂ ha₂ hab
      have h₁ := (Finset.mem_filter.mp ha₁).2
      have h₂ := (Finset.mem_filter.mp ha₂).2
      refine windowCfg_eq (h₁.1.trans h₂.1.symm) (congrArg Prod.fst hab) ?_
      funext j
      by_cases hj : j = k₁
      · simpa [hj] using! congrArg Prod.snd hab
      · exact (h₁.2.1 j hj).trans (h₂.2.1 j hj).symm
    · intro p _
      refine ⟨⟨k, p.1, fun j => if j = k₁ then p.2 else σ₁ j⟩, ?_, by simp⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨rfl, fun j hj => by simp [hj], ?_⟩⟩
      intro j hj
      simp only [if_neg hj]
      exact hcomp j hj
    · intro a ha
      have h₁ := (Finset.mem_filter.mp ha).2
      refine congrArg F (windowCfg_eq h₁.1 rfl ?_)
      funext j
      by_cases hj : j = k₁
      · simp [hj]
      · simpa [hj] using! h₁.2.1 j hj
  rw [← Finset.sum_filter, hbij]
  exact Fintype.sum_prod_type
    (f := fun p => F ⟨k, p.1, fun j => if j = k₁ then p.2 else σ₁ j⟩)

/-- For distinct write positions and tapes agreeing away from both, the two tape constraints
uniquely determine the output tape, leaving only a sum over output states. -/
private lemma sum_pin_two (k k₁ k₂ : Fin (2 * t + 1)) (σ₁ σ₂ : Fin (2 * t + 1) → A)
    (F : WindowCfg t Q A → ℂ) (hk : k₁ ≠ k₂)
    (hcomp : ∀ j : Fin (2 * t + 1), j ≠ k₁ → j ≠ k₂ → σ₁ j = σ₂ j) :
    ∑ c' : WindowCfg t Q A,
      (if c'.head = k ∧ (∀ j : Fin (2 * t + 1), j ≠ k₁ → c'.tape j = σ₁ j) ∧
          (∀ j : Fin (2 * t + 1), j ≠ k₂ → c'.tape j = σ₂ j) then F c' else 0) =
      ∑ q : Q, F ⟨k, q, fun j => if j = k₁ then σ₂ j else σ₁ j⟩ := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun (c' : WindowCfg t Q A) (_ : c' ∈
      (Finset.univ : Finset (WindowCfg t Q A)).filter _) => c'.state)
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro a₁ ha₁ a₂ ha₂ hab
    have h₁ := (Finset.mem_filter.mp ha₁).2
    have h₂ := (Finset.mem_filter.mp ha₂).2
    refine windowCfg_eq (h₁.1.trans h₂.1.symm) hab ?_
    funext j
    by_cases hj : j = k₁
    · have hne : j ≠ k₂ := fun h => hk (hj.symm.trans h)
      rw [h₁.2.2 j hne, h₂.2.2 j hne]
    · by_cases hj' : j = k₂
      · have hne : j ≠ k₁ := fun h => hk (h.symm.trans hj')
        rw [h₁.2.1 j hne, h₂.2.1 j hne]
      · rw [h₁.2.1 j hj, h₂.2.1 j hj]
  · intro q _
    refine ⟨⟨k, q, fun j => if j = k₁ then σ₂ j else σ₁ j⟩, ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨rfl, fun j hj => by simp [hj], ?_⟩⟩
    intro j hj
    by_cases hj' : j = k₁
    · simp [hj']
    · simp only [if_neg hj']
      exact hcomp j hj' hj
  · intro a ha
    have h₁ := (Finset.mem_filter.mp ha).2
    refine congrArg F (windowCfg_eq h₁.1 rfl ?_)
    funext j
    by_cases hj : j = k₁
    · have hne : j ≠ k₂ := fun h => hk (hj.symm.trans h)
      simpa [hj] using! h₁.2.2 j hne
    · simpa [hj] using! h₁.2.1 j hj

/-- When two moves reach the same cell, their conjugate amplitude product is the product of
local transition amplitudes under the combined head and tape constraints, and is zero
otherwise. -/
private lemma stepAmp_merge (M : LocalQTM Q A) (c₁ c₂ : WindowCfg t Q A) (d₁ d₂ : QtmMove)
    (k : Fin (2 * t + 1)) (h₁e : moveCell d₁ c₁.head = some k)
    (h₂e : moveCell d₂ c₂.head = some k) (c' : WindowCfg t Q A) :
    star (stepAmp M c₁ d₁ c') * stepAmp M c₂ d₂ c' =
      if c'.head = k ∧ (∀ j : Fin (2 * t + 1), j ≠ c₁.head → c'.tape j = c₁.tape j) ∧
          (∀ j : Fin (2 * t + 1), j ≠ c₂.head → c'.tape j = c₂.tape j)
      then star (M.step c₁.state (c₁.tape c₁.head) d₁ c'.state (c'.tape c₁.head)) *
          M.step c₂.state (c₂.tape c₂.head) d₂ c'.state (c'.tape c₂.head)
      else 0 := by
  unfold stepAmp
  rw [star_ite_mul]
  by_cases p₁ : moveCell d₁ c₁.head = some c'.head ∧
      ∀ j : Fin (2 * t + 1), j ≠ c₁.head → c'.tape j = c₁.tape j
  · have hk' : c'.head = k := (Option.some.inj (h₁e.symm.trans p₁.1)).symm
    by_cases p₂ : moveCell d₂ c₂.head = some c'.head ∧
        ∀ j : Fin (2 * t + 1), j ≠ c₂.head → c'.tape j = c₂.tape j
    · rw [if_pos ⟨p₁, p₂⟩, if_pos ⟨hk', p₁.2, p₂.2⟩]
    · rw [if_neg (fun hp => p₂ hp.2), if_neg (fun hp =>
        p₂ ⟨by rw [h₂e, hp.1], hp.2.2⟩)]
  · rw [if_neg (fun hp => p₁ hp.1), if_neg (fun hp =>
      p₁ ⟨by rw [h₁e, hp.1], hp.2.1⟩)]

/-- For a common move direction, the column inner product reduces to a local transition inner
product when the tapes agree away from the head and both moves have the same in-window
destination, and is zero otherwise. -/
private lemma inner_sameMove (M : LocalQTM Q A) (c₁ c₂ : WindowCfg t Q A) (d : QtmMove) :
    ∑ c' : WindowCfg t Q A, star (stepAmp M c₁ d c') * stepAmp M c₂ d c' =
      if (∀ j : Fin (2 * t + 1), j ≠ c₁.head → c₁.tape j = c₂.tape j) ∧
          moveCell d c₁.head = moveCell d c₂.head ∧ moveCell d c₁.head ≠ none then
        ∑ q' : Q, ∑ b : A,
          star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
            M.step c₂.state (c₂.tape c₂.head) d q' b
      else 0 := by
  rcases e : (moveCell d c₁.head) with _ | k
  · have hz : ∀ c' : WindowCfg t Q A, stepAmp M c₁ d c' = 0 := by
      intro c'; unfold stepAmp; simp [e]
    rw [Finset.sum_congr rfl (fun c' _ => by rw [hz c', star_zero, zero_mul]),
      Finset.sum_const_zero, if_neg (fun h => h.2.2 rfl)]
  · have h1e : moveCell d c₁.head = some k := e
    by_cases h2e : moveCell d c₂.head = some k
    · have hhead : c₁.head = c₂.head := moveCell_inj d (by rw [h1e, h2e])
      by_cases hcomp : ∀ j : Fin (2 * t + 1), j ≠ c₁.head → c₁.tape j = c₂.tape j
      · rw [if_pos ⟨hcomp, by rw [h2e], by simp⟩]
        rw [Finset.sum_congr rfl
          (fun c' _ => stepAmp_merge M c₁ c₂ d d k h1e h2e c')]
        rw [sum_write_one k c₁.head c₂.head c₁.tape c₂.tape _ hhead hcomp]
        refine Finset.sum_congr rfl fun q' _ => Finset.sum_congr rfl fun b _ => ?_
        (try dsimp only)
        rw [if_pos rfl, if_pos hhead.symm]
      · rw [if_neg (fun h => hcomp h.1)]
        refine Finset.sum_eq_zero fun c' _ => ?_
        unfold stepAmp
        by_cases p₁ : moveCell d c₁.head = some c'.head ∧
            ∀ j : Fin (2 * t + 1), j ≠ c₁.head → c'.tape j = c₁.tape j
        · by_cases p₂ : moveCell d c₂.head = some c'.head ∧
            ∀ j : Fin (2 * t + 1), j ≠ c₂.head → c'.tape j = c₂.tape j
          · exact absurd (fun j hj =>
              (p₁.2 j hj).symm.trans (p₂.2 j (fun h => hj (h.trans hhead.symm)))) hcomp
          · simp [p₂]
        · simp [p₁]
    · rw [if_neg (fun h => h2e h.2.1.symm)]
      refine Finset.sum_eq_zero fun c' _ => ?_
      unfold stepAmp
      by_cases p₁ : moveCell d c₁.head = some c'.head ∧
          ∀ j : Fin (2 * t + 1), j ≠ c₁.head → c'.tape j = c₁.tape j
      · by_cases p₂ : moveCell d c₂.head = some c'.head ∧
          ∀ j : Fin (2 * t + 1), j ≠ c₂.head → c'.tape j = c₂.tape j
        · exact absurd (p₂.1.trans (p₁.1.symm.trans h1e)) h2e
        · simp [p₂]
      · simp [p₁]

/-- For distinct source head positions whose moves reach the same cell, the amplitude inner
product reduces to a sum over output states with written symbols fixed by the opposite
source tapes when the tapes agree away from both heads, and is zero otherwise. -/
private lemma cross_reduce (M : LocalQTM Q A) (c₁ c₂ : WindowCfg t Q A) (d₁ d₂ : QtmMove)
    (k : Fin (2 * t + 1)) (h₁e : moveCell d₁ c₁.head = some k)
    (h₂e : moveCell d₂ c₂.head = some k) (hk : c₁.head ≠ c₂.head) :
    ∑ c' : WindowCfg t Q A, star (stepAmp M c₁ d₁ c') * stepAmp M c₂ d₂ c' =
      if (∀ j : Fin (2 * t + 1), j ≠ c₁.head → j ≠ c₂.head → c₁.tape j = c₂.tape j) then
        ∑ q' : Q, star (M.step c₁.state (c₁.tape c₁.head) d₁ q' (c₂.tape c₁.head)) *
            M.step c₂.state (c₂.tape c₂.head) d₂ q' (c₁.tape c₂.head)
      else 0 := by
  by_cases hcomp : ∀ j : Fin (2 * t + 1), j ≠ c₁.head → j ≠ c₂.head → c₁.tape j = c₂.tape j
  · rw [if_pos hcomp]
    rw [Finset.sum_congr rfl (fun c' _ => stepAmp_merge M c₁ c₂ d₁ d₂ k h₁e h₂e c')]
    rw [sum_pin_two k c₁.head c₂.head c₁.tape c₂.tape _ hk hcomp]
    refine Finset.sum_congr rfl fun q' _ => ?_
    (try dsimp only)
    rw [if_pos rfl, if_neg (Ne.symm hk)]
  · rw [if_neg hcomp]
    refine Finset.sum_eq_zero fun c' _ => ?_
    unfold stepAmp
    by_cases p₁ : moveCell d₁ c₁.head = some c'.head ∧
        ∀ j : Fin (2 * t + 1), j ≠ c₁.head → c'.tape j = c₁.tape j
    · by_cases p₂ : moveCell d₂ c₂.head = some c'.head ∧
        ∀ j : Fin (2 * t + 1), j ≠ c₂.head → c'.tape j = c₂.tape j
      · exact absurd (fun j hj1 hj2 => (p₁.2 j hj1).symm.trans (p₂.2 j hj2)) hcomp
      · simp [p₂]
    · simp [p₁]

/-- A finite complex inner-product sum equals the conjugate of the sum with conjugation on the
second factor. -/
private lemma sum_star_mul_eq (x y : Q → ℂ) :
    (∑ q, star (x q) * y q) = star (∑ q, x q * star (y q)) := by
  rw [star_sum]
  exact Finset.sum_congr rfl fun q _ => by rw [star_mul, star_star, mul_comm]

/-- The summed amplitude inner product vanishes for two distinct move directions. -/
private lemma inner_diffMove (M : LocalQTM Q A) (c₁ c₂ : WindowCfg t Q A) (d₁ d₂ : QtmMove)
    (hd : d₁ ≠ d₂) :
    ∑ c' : WindowCfg t Q A, star (stepAmp M c₁ d₁ c') * stepAmp M c₂ d₂ c' = 0 := by
  by_cases hcommon : ∃ k : Fin (2 * t + 1), moveCell d₁ c₁.head = some k ∧
      moveCell d₂ c₂.head = some k
  · obtain ⟨k, h₁e, h₂e⟩ := hcommon
    have hk : c₁.head ≠ c₂.head := fun he =>
      hd (moveCell_some_inj d₁ d₂ (by rw [← he]; exact h₁e) h₂e)
    rw [cross_reduce M c₁ c₂ d₁ d₂ k h₁e h₂e hk]
    by_cases hcomp : ∀ j : Fin (2 * t + 1), j ≠ c₁.head → j ≠ c₂.head → c₁.tape j = c₂.tape j
    · rw [if_pos hcomp]
      rcases d₁ with _ | _ | _ <;> rcases d₂ with _ | _ | _
      all_goals first
      | exact absurd rfl hd
      | (rw [Finset.sum_congr rfl (fun q' _ => mul_comm _ _)];
          exact M.wf_stayLeft _ _ _ _ _ _)
      | (rw [sum_star_mul_eq, M.wf_stayLeft _ _ _ _ _ _, star_zero])
      | (rw [Finset.sum_congr rfl (fun q' _ => mul_comm _ _)];
          exact M.wf_rightStay _ _ _ _ _ _)
      | (rw [sum_star_mul_eq, M.wf_rightStay _ _ _ _ _ _, star_zero])
      | (rw [Finset.sum_congr rfl (fun q' _ => mul_comm _ _)];
          exact M.wf_rightLeft _ _ _ _ _ _)
      | (rw [sum_star_mul_eq, M.wf_rightLeft _ _ _ _ _ _, star_zero])
    · rw [if_neg hcomp]
  · refine Finset.sum_eq_zero fun c' _ => ?_
    unfold stepAmp
    by_cases p₁ : moveCell d₁ c₁.head = some c'.head ∧
        ∀ j : Fin (2 * t + 1), j ≠ c₁.head → c'.tape j = c₁.tape j
    · by_cases p₂ : moveCell d₂ c₂.head = some c'.head ∧
        ∀ j : Fin (2 * t + 1), j ≠ c₂.head → c'.tape j = c₂.tape j
      · exact absurd ⟨c'.head, p₁.1, p₂.1⟩ hcommon
      · simp [p₂]
    · simp [p₁]

/-- In the double sum over move directions, all terms with distinct directions vanish, leaving
the sum over equal directions. -/
private lemma inner_offdiag_zero (M : LocalQTM Q A) (c₁ c₂ : WindowCfg t Q A) :
    ∑ d₁ : QtmMove, ∑ d₂ : QtmMove,
        ∑ c' : WindowCfg t Q A, star (stepAmp M c₁ d₁ c') * stepAmp M c₂ d₂ c'
      = ∑ d : QtmMove,
          ∑ c' : WindowCfg t Q A, star (stepAmp M c₁ d c') * stepAmp M c₂ d c' := by
  refine Finset.sum_congr rfl fun d₁ _ => ?_
  rw [Finset.sum_eq_single_of_mem d₁ (Finset.mem_univ _)
    (fun d₂ _ hd₂ => inner_diffMove M c₁ c₂ d₁ d₂ (Ne.symm hd₂))]

/-- The squared column norm of the window transition, expressed as a complex inner product,
equals the sum of squared local amplitudes for moves that stay inside the window. -/
theorem windowStep_inner_self (M : LocalQTM Q A) (c : WindowCfg t Q A) :
    ∑ c' : WindowCfg t Q A, star (windowStep M c' c) * windowStep M c' c =
      ∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
        if moveCell d c.head = none then (0 : ℂ)
        else star (M.step c.state (c.tape c.head) d q' b) *
            M.step c.state (c.tape c.head) d q' b := by
  rw [inner_expand, inner_offdiag_zero]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [inner_sameMove M c c d]
  by_cases hn : moveCell d c.head = none
  · rw [if_neg (fun h => h.2.2 hn)]
    simp [hn]
  · rw [if_pos ⟨fun j _ => rfl, rfl, hn⟩]
    simp [hn]

/-- The sum of squared local transition amplitudes for head moves that leave the finite window. -/
def windowEscapeMass (M : LocalQTM Q A) (c : WindowCfg t Q A) : ℝ :=
  ∑ d ∈ (Finset.univ : Finset QtmMove).filter (fun d => moveCell d c.head = none),
    ∑ q' : Q, ∑ b : A, ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2

/-- The escape mass is the left-move mass at cell zero plus the right-move mass at cell `2 * t`,
with each contribution zero away from its boundary. -/
theorem windowEscapeMass_eq (M : LocalQTM Q A) (c : WindowCfg t Q A) :
    windowEscapeMass M c =
      (if c.head.val = 0 then
        ∑ q' : Q, ∑ b : A, ‖M.step c.state (c.tape c.head) QtmMove.left q' b‖ ^ 2 else 0) +
      (if c.head.val = 2 * t then
        ∑ q' : Q, ∑ b : A, ‖M.step c.state (c.tape c.head) QtmMove.right q' b‖ ^ 2 else 0) := by
  rw [windowEscapeMass, Finset.sum_filter]
  have henum : (Finset.univ : Finset QtmMove) =
      {QtmMove.left, QtmMove.stay, QtmMove.right} := by
    ext d <;> cases d <;> simp
  rw [henum]
  by_cases hl : c.head.val = 0 <;> by_cases hr : c.head.val = 2 * t <;>
    simp [moveCell_left_none, moveCell_right_none, moveCell_stay_ne_none, hl, hr]

/-- Complex conjugation by `star` agrees with the complex conjugation ring endomorphism. -/
private lemma star_eq_starRingEnd (z : ℂ) : star z = (starRingEnd ℂ) z := rfl

/-- The squared norm of a complex number is the real part of `star z * z`. -/
private lemma normSq_eq (z : ℂ) : ‖z‖ ^ 2 = (star z * z).re := by
  rw [Complex.sq_norm, star_eq_starRingEnd, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re]

/-- Taking the real part of the local diagonal amplitude sum yields the sum of squared norms for
the moves that remain in the window. -/
private lemma re_diag_sum (M : LocalQTM Q A) (c : WindowCfg t Q A) (d : QtmMove) :
    (∑ q' : Q, ∑ b : A,
        (if moveCell d c.head = none then (0 : ℂ)
          else star (M.step c.state (c.tape c.head) d q' b) *
            M.step c.state (c.tape c.head) d q' b)).re =
      ∑ q' : Q, ∑ b : A,
        if moveCell d c.head = none then (0 : ℝ)
        else ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2 := by
  have h1 : (∑ q' : Q, ∑ b : A,
      (if moveCell d c.head = none then (0 : ℂ)
        else star (M.step c.state (c.tape c.head) d q' b) *
          M.step c.state (c.tape c.head) d q' b)).re =
      ∑ q' : Q, (∑ b : A,
        (if moveCell d c.head = none then (0 : ℂ)
          else star (M.step c.state (c.tape c.head) d q' b) *
            M.step c.state (c.tape c.head) d q' b)).re := by
    simpa using! map_sum Complex.reAddGroupHom
      (fun q' => ∑ b : A,
        (if moveCell d c.head = none then (0 : ℂ)
          else star (M.step c.state (c.tape c.head) d q' b) *
            M.step c.state (c.tape c.head) d q' b)) Finset.univ
  rw [h1]
  refine Finset.sum_congr rfl fun q' _ => ?_
  have h2 : (∑ b : A,
      (if moveCell d c.head = none then (0 : ℂ)
        else star (M.step c.state (c.tape c.head) d q' b) *
          M.step c.state (c.tape c.head) d q' b)).re =
      ∑ b : A,
      ((if moveCell d c.head = none then (0 : ℂ)
        else star (M.step c.state (c.tape c.head) d q' b) *
          M.step c.state (c.tape c.head) d q' b)).re := by
    simpa using! map_sum Complex.reAddGroupHom
      (fun b => (if moveCell d c.head = none then (0 : ℂ)
        else star (M.step c.state (c.tape c.head) d q' b) *
          M.step c.state (c.tape c.head) d q' b)) Finset.univ
  rw [h2]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hn : moveCell d c.head = none
  · simp [hn]
  · simp [hn, normSq_eq]

/-- The squared norm of a window transition column plus its escape mass is one. -/
theorem windowStep_columnNorm_add_windowEscapeMass (M : LocalQTM Q A) (c : WindowCfg t Q A) :
    (∑ c' : WindowCfg t Q A, ‖windowStep M c' c‖ ^ 2) + windowEscapeMass M c = 1 := by
  have h1 : ∑ c' : WindowCfg t Q A, ‖windowStep M c' c‖ ^ 2 =
      (∑ c' : WindowCfg t Q A, star (windowStep M c' c) * windowStep M c' c).re := by
    have hcast : (∑ c' : WindowCfg t Q A, star (windowStep M c' c) * windowStep M c' c).re
        = ∑ c' : WindowCfg t Q A, (star (windowStep M c' c) * windowStep M c' c).re := by
      simpa using! map_sum Complex.reAddGroupHom
        (fun c' => star (windowStep M c' c) * windowStep M c' c) Finset.univ
    rw [hcast]
    exact Finset.sum_congr rfl fun c' _ => normSq_eq _
  have h2 := windowStep_inner_self M c
  have h2re := congrArg Complex.re h2
  have hcast : (∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
      (if moveCell d c.head = none then (0 : ℂ)
        else star (M.step c.state (c.tape c.head) d q' b) *
          M.step c.state (c.tape c.head) d q' b)).re =
      ∑ d : QtmMove, (∑ q' : Q, ∑ b : A,
      (if moveCell d c.head = none then (0 : ℂ)
        else star (M.step c.state (c.tape c.head) d q' b) *
          M.step c.state (c.tape c.head) d q' b)).re := by
    simpa using! map_sum Complex.reAddGroupHom
      (fun d => ∑ q' : Q, ∑ b : A,
        (if moveCell d c.head = none then (0 : ℂ)
          else star (M.step c.state (c.tape c.head) d q' b) *
            M.step c.state (c.tape c.head) d q' b)) Finset.univ
  rw [h1, h2re, hcast]
  have h3 : windowEscapeMass M c =
      ∑ d : QtmMove, if moveCell d c.head = none then
        (∑ q' : Q, ∑ b : A, ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2) else 0 := by
    rw [windowEscapeMass, Finset.sum_filter]
  rw [h3, ← Finset.sum_add_distrib]
  have hper : ∀ d : QtmMove,
      ((∑ q' : Q, ∑ b : A,
          if moveCell d c.head = none then (0 : ℝ)
            else ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2) +
        (if moveCell d c.head = none then
          (∑ q' : Q, ∑ b : A, ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2) else 0)) =
      ∑ q' : Q, ∑ b : A, ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2 := by
    intro d
    by_cases hn : moveCell d c.head = none <;> simp [hn]
  calc ∑ d : QtmMove, (
          (∑ q' : Q, ∑ b : A,
            (if moveCell d c.head = none then (0 : ℂ)
              else star (M.step c.state (c.tape c.head) d q' b) *
                M.step c.state (c.tape c.head) d q' b)).re +
        (if moveCell d c.head = none then
          (∑ q' : Q, ∑ b : A, ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2) else 0))
      = ∑ d : QtmMove, ∑ q' : Q, ∑ b : A, ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2 := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [re_diag_sum M c d, hper d]
    _ = 1 := by
        calc ∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
                ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2
            = ∑ q' : Q, ∑ d : QtmMove, ∑ b : A,
                ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2 := Finset.sum_comm
          _ = ∑ q' : Q, ∑ b : A, ∑ d : QtmMove,
                ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2 :=
              Finset.sum_congr rfl fun q' _ => Finset.sum_comm
          _ = 1 := M.wf_norm c.state (c.tape c.head)

/-- Each window transition column has squared norm at most one. -/
theorem windowStep_columnNorm_le_one (M : LocalQTM Q A) (c : WindowCfg t Q A) :
    ∑ c' : WindowCfg t Q A, ‖windowStep M c' c‖ ^ 2 ≤ 1 := by
  have h := windowStep_columnNorm_add_windowEscapeMass M c
  have h0 : (0 : ℝ) ≤ windowEscapeMass M c := by
    refine Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun q' _ => ?_
    exact Finset.sum_nonneg fun b _ => sq_nonneg _
  linarith

/-- A window transition column has squared norm one when its source head is at neither boundary. -/
theorem windowStep_columnNorm_interior (M : LocalQTM Q A) (c : WindowCfg t Q A)
    (h₀ : c.head.val ≠ 0) (h₂t : c.head.val ≠ 2 * t) :
    ∑ c' : WindowCfg t Q A, ‖windowStep M c' c‖ ^ 2 = 1 := by
  have h := windowStep_columnNorm_add_windowEscapeMass M c
  have hf : (Finset.univ : Finset QtmMove).filter
      (fun d => moveCell d c.head = none) = ∅ := by
    ext d <;> cases d <;>
      simp [moveCell_left_none, moveCell_right_none, moveCell_stay_ne_none, h₀, h₂t]
  rw [windowEscapeMass, hf, Finset.sum_empty] at h
  linarith

/-- The complex self-inner-product of a window transition column is the complex coercion of its
real squared norm. -/
private lemma gram_self_cast (M : LocalQTM Q A) (c : WindowCfg t Q A) :
    ∑ c' : WindowCfg t Q A, star (windowStep M c' c) * windowStep M c' c =
      ((∑ c' : WindowCfg t Q A, ‖windowStep M c' c‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : ∑ c' : WindowCfg t Q A, star (windowStep M c' c) * windowStep M c' c =
      ∑ c' : WindowCfg t Q A, ((‖windowStep M c' c‖ ^ 2 : ℝ) : ℂ) :=
    Finset.sum_congr rfl fun c' _ => by
      rw [star_eq_starRingEnd, ← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]
  rw [h1, Complex.ofReal_sum]

/-- Window transition columns whose source heads lie strictly inside the window are orthonormal. -/
theorem windowStep_gram_interior (M : LocalQTM Q A) (c₁ c₂ : WindowCfg t Q A)
    (h₁₀ : c₁.head.val ≠ 0) (h₁t : c₁.head.val ≠ 2 * t)
    (h₂₀ : c₂.head.val ≠ 0) (h₂t : c₂.head.val ≠ 2 * t) :
    ∑ c' : WindowCfg t Q A, star (windowStep M c' c₁) * windowStep M c' c₂ =
      if c₁ = c₂ then (1 : ℂ) else 0 := by
  by_cases he : c₁ = c₂
  · subst he
    rw [if_pos rfl, gram_self_cast, windowStep_columnNorm_interior M c₁ h₁₀ h₁t]
    simp
  · rw [if_neg he, inner_expand, inner_offdiag_zero]
    have hnne₁ : ∀ d : QtmMove, moveCell d c₁.head ≠ none := by
      intro d; cases d with
      | left => intro h; exact h₁₀ (moveCell_left_none.mp h)
      | stay => exact moveCell_stay_ne_none c₁.head
      | right => intro h; exact h₁t (moveCell_right_none.mp h)
    by_cases hhead : c₁.head = c₂.head
    · by_cases hcomp : ∀ j : Fin (2 * t + 1), j ≠ c₁.head → c₁.tape j = c₂.tape j
      · have hsane : (c₁.state, c₁.tape c₁.head) ≠ (c₂.state, c₂.tape c₂.head) := by
          intro hp
          refine he ?_
          refine windowCfg_eq hhead (congrArg Prod.fst hp) ?_
          funext j
          by_cases hj : j = c₁.head
          · rw [hj]
            exact (congrArg Prod.snd hp).trans (congrArg c₂.tape hhead.symm)
          · exact hcomp j hj
        calc ∑ d : QtmMove, ∑ c' : WindowCfg t Q A,
              star (stepAmp M c₁ d c') * stepAmp M c₂ d c'
            = ∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
                star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                  M.step c₂.state (c₂.tape c₂.head) d q' b := by
                  refine Finset.sum_congr rfl fun d _ => ?_
                  rw [inner_sameMove M c₁ c₂ d, if_pos ⟨hcomp, by rw [hhead], hnne₁ d⟩]
          _ = ∑ q' : Q, ∑ d : QtmMove, ∑ b : A,
              star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                M.step c₂.state (c₂.tape c₂.head) d q' b := Finset.sum_comm
          _ = ∑ q' : Q, ∑ b : A, ∑ d : QtmMove,
              star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                M.step c₂.state (c₂.tape c₂.head) d q' b :=
              Finset.sum_congr rfl fun q' _ => Finset.sum_comm
          _ = 0 := M.wf_sameCell c₁.state (c₁.tape c₁.head) c₂.state (c₂.tape c₂.head) hsane
      · have hz : ∀ d : QtmMove,
          (∑ c' : WindowCfg t Q A,
            star (stepAmp M c₁ d c') * stepAmp M c₂ d c') = 0 := by
          intro d
          rw [inner_sameMove M c₁ c₂ d, if_neg (fun h => hcomp h.1)]
        exact Finset.sum_eq_zero fun d _ => hz d
    · have hz : ∀ d : QtmMove,
        (∑ c' : WindowCfg t Q A,
          star (stepAmp M c₁ d c') * stepAmp M c₂ d c') = 0 := by
        intro d
        rw [inner_sameMove M c₁ c₂ d, if_neg (fun h => hhead (moveCell_inj d h.2.1))]
      exact Finset.sum_eq_zero fun d _ => hz d

end B3WindowWellformed

/-- The type of escape outcomes, recording a move direction, output internal state, and
resulting window tape. -/
abbrev WindowEsc (t : ℕ) (Q A : Type*) : Type _ :=
  QtmMove × Q × (Fin (2 * t + 1) → A)

/-- The disjoint union of in-window configurations and escape outcomes. -/
abbrev WindowFull (t : ℕ) (Q A : Type*) : Type _ :=
  WindowCfg t Q A ⊕ WindowEsc t Q A

section B3FullOutcome

variable {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]

/-- The amplitude of an escape outcome, zero unless the indicated move leaves the window and the
output tape agrees with the source away from its head. -/
def windowEscAmp (M : LocalQTM Q A) (c : WindowCfg t Q A) (e : WindowEsc t Q A) : ℂ :=
  if moveCell e.1 c.head = none ∧
      ∀ j : Fin (2 * t + 1), j ≠ c.head → e.2.2 j = c.tape j
  then M.step c.state (c.tape c.head) e.1 e.2.1 (e.2.2 c.head) else 0

/-- The rectangular transition matrix combining in-window transition amplitudes with explicit
escape amplitudes. -/
def windowStepFull (M : LocalQTM Q A) : Matrix (WindowFull t Q A) (WindowCfg t Q A) ℂ :=
  Matrix.of fun tgt c =>
    match tgt with
    | Sum.inl c' => windowStep M c' c
    | Sum.inr e => windowEscAmp M c e

/-- An in-window row of the full transition matrix agrees with the corresponding entry of
`windowStep`. -/
theorem windowStepFull_apply_inl (M : LocalQTM Q A) (c' c : WindowCfg t Q A) :
    windowStepFull M (Sum.inl c') c = windowStep M c' c := rfl

/-- An escape row of the full transition matrix agrees with `windowEscAmp`. -/
theorem windowStepFull_apply_inr (M : LocalQTM Q A) (e : WindowEsc t Q A)
    (c : WindowCfg t Q A) :
    windowStepFull M (Sum.inr e) c = windowEscAmp M c e := rfl

/-- Expands an escape amplitude in terms of its move, output state, and output tape, using the
local transition amplitude exactly when the escape and tape conditions hold. -/
theorem windowEscAmp_prod (M : LocalQTM Q A) (c : WindowCfg t Q A) (d : QtmMove) (q' : Q)
    (τ' : Fin (2 * t + 1) → A) :
    windowEscAmp M c (d, q', τ') =
      if moveCell d c.head = none ∧
          ∀ j : Fin (2 * t + 1), j ≠ c.head → τ' j = c.tape j
      then M.step c.state (c.tape c.head) d q' (τ' c.head) else 0 := rfl

/-- Summing over escape outcomes is the iterated sum over move directions, output states, and
output tapes. -/
private lemma sum_esc_triple {γ : Type*} [AddCommMonoid γ] (F : WindowEsc t Q A → γ) :
    ∑ e : WindowEsc t Q A, F e =
      ∑ d : QtmMove, ∑ q' : Q, ∑ τ' : Fin (2 * t + 1) → A, F (d, q', τ') := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fintype.sum_prod_type]

/-- Summing a function of one tape cell over tapes fixed at every other cell reduces to summing
over the symbol at that cell. -/
private lemma sum_tape_one {γ : Type*} [AddCommMonoid γ] (h : Fin (2 * t + 1))
    (σ : Fin (2 * t + 1) → A) (F : A → γ) :
    ∑ τ' : Fin (2 * t + 1) → A,
      (if ∀ j : Fin (2 * t + 1), j ≠ h → τ' j = σ j then F (τ' h) else 0) =
      ∑ b : A, F b := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun τ' (_ : τ' ∈ _) => τ' h) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro τ₁ hτ₁ τ₂ hτ₂ heq
    obtain ⟨_, hσ₁⟩ := Finset.mem_filter.mp hτ₁
    obtain ⟨_, hσ₂⟩ := Finset.mem_filter.mp hτ₂
    funext j
    by_cases hj : j = h
    · exact hj ▸ heq
    · exact (hσ₁ j hj).trans (hσ₂ j hj).symm
  · intro b _
    refine ⟨fun j => if j = h then b else σ j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · intro j hj
      simp [hj]
    · simp
  · intro τ' hτ'
    rfl

/-- The sum of squared escape amplitudes equals `windowEscapeMass`. -/
theorem windowEscAmp_mass (M : LocalQTM Q A) (c : WindowCfg t Q A) :
    ∑ e : WindowEsc t Q A, ‖windowEscAmp M c e‖ ^ 2 = windowEscapeMass M c := by
  classical
  rw [sum_esc_triple]
  have hper : ∀ d : QtmMove, ∀ q' : Q,
      (∑ τ' : Fin (2 * t + 1) → A, ‖windowEscAmp M c (d, q', τ')‖ ^ 2) =
        if moveCell d c.head = none then
          ∑ b : A, ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2 else 0 := by
    intro d q'
    by_cases hd : moveCell d c.head = none
    · have hτ : ∀ τ' : Fin (2 * t + 1) → A,
          ‖windowEscAmp M c (d, q', τ')‖ ^ 2 =
            (if ∀ j : Fin (2 * t + 1), j ≠ c.head → τ' j = c.tape j then
              ‖M.step c.state (c.tape c.head) d q' (τ' c.head)‖ ^ 2 else 0) := by
        intro τ'
        rw [windowEscAmp_prod]
        by_cases hc : ∀ j : Fin (2 * t + 1), j ≠ c.head → τ' j = c.tape j
        · rw [if_pos ⟨hd, hc⟩, if_pos hc]
        · rw [if_neg (fun hcon => hc hcon.2), if_neg hc]
          simp
      have hsum := sum_tape_one c.head c.tape
        (fun b : A => ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2)
      rw [if_pos hd]
      calc
        ∑ τ' : Fin (2 * t + 1) → A, ‖windowEscAmp M c (d, q', τ')‖ ^ 2
            = ∑ τ' : Fin (2 * t + 1) → A,
                (if ∀ j : Fin (2 * t + 1), j ≠ c.head → τ' j = c.tape j then
                  ‖M.step c.state (c.tape c.head) d q' (τ' c.head)‖ ^ 2 else 0) :=
              Finset.sum_congr rfl fun τ' _ => hτ τ'
        _ = ∑ b : A, ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2 := hsum
    · have hz : ∀ τ' : Fin (2 * t + 1) → A, ‖windowEscAmp M c (d, q', τ')‖ ^ 2 = 0 := by
        intro τ'
        rw [windowEscAmp_prod, if_neg]
        · simp
        · intro hcon
          exact hd hcon.1
      rw [if_neg hd]
      calc
        ∑ τ' : Fin (2 * t + 1) → A, ‖windowEscAmp M c (d, q', τ')‖ ^ 2
            = ∑ τ' : Fin (2 * t + 1) → A, (0 : ℝ) :=
              Finset.sum_congr rfl fun τ' _ => hz τ'
        _ = 0 := Finset.sum_const_zero
  rw [Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun q' _ => hper d q'))]
  have hswap : (∑ d : QtmMove, ∑ q' : Q,
      (if moveCell d c.head = none then
        ∑ b : A, ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2 else 0)) =
      ∑ d : QtmMove, (if moveCell d c.head = none then
        ∑ q' : Q, ∑ b : A, ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2 else 0) := by
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hd : moveCell d c.head = none
    · have h1 : (∑ q' : Q, (if moveCell d c.head = none then
          ∑ b : A, ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2 else 0)) =
          ∑ q' : Q, ∑ b : A, ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2 :=
        Finset.sum_congr rfl fun q' _ => if_pos hd
      rw [h1, if_pos hd]
    · have h1 : (∑ q' : Q, (if moveCell d c.head = none then
          ∑ b : A, ‖M.step c.state (c.tape c.head) d q' b‖ ^ 2 else 0)) = 0 :=
        Finset.sum_eq_zero fun q' _ => if_neg hd
      rw [h1, if_neg hd]
  rw [hswap, windowEscapeMass, ← Finset.sum_filter]

/-- The Gram entry for two window transition columns is the sum of the local same-direction
inner products for matching in-window destinations and compatible tapes. -/
private lemma windowGram_eq (M : LocalQTM Q A) (c₁ c₂ : WindowCfg t Q A) :
    ∑ c' : WindowCfg t Q A, star (windowStep M c' c₁) * windowStep M c' c₂ =
      ∑ d : QtmMove,
        if (∀ j : Fin (2 * t + 1), j ≠ c₁.head → c₁.tape j = c₂.tape j) ∧
            moveCell d c₁.head = moveCell d c₂.head ∧ moveCell d c₁.head ≠ none then
          ∑ q' : Q, ∑ b : A,
            star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
              M.step c₂.state (c₂.tape c₂.head) d q' b
        else 0 := by
  rw [inner_expand, inner_offdiag_zero]
  refine Finset.sum_congr rfl fun d _ => inner_sameMove M c₁ c₂ d

/-- The inner product of two escape-amplitude columns is zero when their source head positions
differ. -/
private lemma escGram_diffHead (M : LocalQTM Q A) (c₁ c₂ : WindowCfg t Q A)
    (hh : c₁.head ≠ c₂.head) :
    ∑ e : WindowEsc t Q A, star (windowEscAmp M c₁ e) * windowEscAmp M c₂ e = 0 := by
  refine Finset.sum_eq_zero fun e _ => ?_
  unfold windowEscAmp
  rw [star_ite_mul]
  apply if_neg
  intro hcon
  exact hh (moveCell_inj e.1 (by rw [hcon.1.1, hcon.2.1]))

/-- For equal source head positions, the escape inner product reduces to the local inner
products of escaping moves when the source tapes agree away from the head, and is zero
otherwise. -/
private lemma escGram_sameHead (M : LocalQTM Q A) (c₁ c₂ : WindowCfg t Q A)
    (hh : c₁.head = c₂.head) :
    ∑ e : WindowEsc t Q A, star (windowEscAmp M c₁ e) * windowEscAmp M c₂ e =
      if ∀ j : Fin (2 * t + 1), j ≠ c₁.head → c₁.tape j = c₂.tape j then
        ∑ d : QtmMove, if moveCell d c₁.head = none then
          ∑ q' : Q, ∑ b : A,
            star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
              M.step c₂.state (c₂.tape c₂.head) d q' b
        else (0 : ℂ)
      else 0 := by
  classical
  rw [sum_esc_triple]
  by_cases hcomp : ∀ j : Fin (2 * t + 1), j ≠ c₁.head → c₁.tape j = c₂.tape j
  · rw [if_pos hcomp]
    have hper : ∀ d : QtmMove, ∀ q' : Q,
        (∑ τ' : Fin (2 * t + 1) → A,
          star (windowEscAmp M c₁ (d, q', τ')) * windowEscAmp M c₂ (d, q', τ')) =
          if moveCell d c₁.head = none then
            ∑ b : A, star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
              M.step c₂.state (c₂.tape c₂.head) d q' b
          else (0 : ℂ) := by
      intro d q'
      have hτh : ∀ τ' : Fin (2 * t + 1) → A, τ' c₂.head = τ' c₁.head :=
        fun τ' => congrArg τ' hh.symm
      have hτ' : ∀ τ' : Fin (2 * t + 1) → A,
          star (windowEscAmp M c₁ (d, q', τ')) * windowEscAmp M c₂ (d, q', τ') =
            (if ∀ j : Fin (2 * t + 1), j ≠ c₁.head → τ' j = c₁.tape j then
              (if moveCell d c₁.head = none then
                star (M.step c₁.state (c₁.tape c₁.head) d q' (τ' c₁.head)) *
                  M.step c₂.state (c₂.tape c₂.head) d q' (τ' c₁.head)
                else 0)
              else 0) := by
        intro τ'
        rw [windowEscAmp_prod, windowEscAmp_prod, star_ite_mul]
        by_cases hc : ∀ j : Fin (2 * t + 1), j ≠ c₁.head → τ' j = c₁.tape j
        · have hc₂ : ∀ j : Fin (2 * t + 1), j ≠ c₂.head → τ' j = c₂.tape j := by
            intro j hj
            have hj' : j ≠ c₁.head := by rw [hh]; exact hj
            exact (hc j hj').trans (hcomp j hj')
          have hmv : moveCell d c₂.head = none ↔ moveCell d c₁.head = none := by rw [hh]
          by_cases hd : moveCell d c₁.head = none
          · rw [if_pos ⟨⟨hd, hc⟩, ⟨hmv.mpr hd, hc₂⟩⟩, hτh τ', if_pos hc, if_pos hd]
          · rw [if_neg (fun hcon => hd hcon.1.1), if_pos hc, if_neg hd]
        · rw [if_neg (fun hcon => hc hcon.1.2), if_neg hc]
      by_cases hd : moveCell d c₁.head = none
      · rw [if_pos hd]
        have hfold : ∀ τ' : Fin (2 * t + 1) → A,
            (if ∀ j : Fin (2 * t + 1), j ≠ c₁.head → τ' j = c₁.tape j then
              (if moveCell d c₁.head = none then
                star (M.step c₁.state (c₁.tape c₁.head) d q' (τ' c₁.head)) *
                  M.step c₂.state (c₂.tape c₂.head) d q' (τ' c₁.head)
                else 0)
              else 0) =
            (if ∀ j : Fin (2 * t + 1), j ≠ c₁.head → τ' j = c₁.tape j then
              star (M.step c₁.state (c₁.tape c₁.head) d q' (τ' c₁.head)) *
                M.step c₂.state (c₂.tape c₂.head) d q' (τ' c₁.head)
              else 0) := by
          intro τ'
          rw [if_pos hd]
        have hsum := sum_tape_one c₁.head c₁.tape
          (fun b : A => star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
            M.step c₂.state (c₂.tape c₂.head) d q' b)
        rw [Finset.sum_congr rfl (fun τ' _ => hτ' τ')]
        rw [Finset.sum_congr rfl (fun τ' _ => hfold τ'), hsum]
      · rw [if_neg hd]
        have hz : ∀ τ' : Fin (2 * t + 1) → A,
            (if ∀ j : Fin (2 * t + 1), j ≠ c₁.head → τ' j = c₁.tape j then
              (if moveCell d c₁.head = none then
                star (M.step c₁.state (c₁.tape c₁.head) d q' (τ' c₁.head)) *
                  M.step c₂.state (c₂.tape c₂.head) d q' (τ' c₁.head)
                else 0)
              else 0) = 0 := by
          intro τ'
          by_cases hc : ∀ j : Fin (2 * t + 1), j ≠ c₁.head → τ' j = c₁.tape j
          · rw [if_pos hc, if_neg hd]
          · rw [if_neg hc]
        rw [Finset.sum_congr rfl (fun τ' _ => hτ' τ'), Finset.sum_eq_zero fun τ' _ => hz τ']
    rw [Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun q' _ => hper d q'))]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hd : moveCell d c₁.head = none
    · rw [if_pos hd]
      exact Finset.sum_congr rfl fun q' _ => if_pos hd
    · have h1 : (∑ q' : Q,
          (if moveCell d c₁.head = none then
            ∑ b : A, star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
              M.step c₂.state (c₂.tape c₂.head) d q' b
            else (0 : ℂ))) = 0 :=
        Finset.sum_eq_zero fun q' _ => if_neg hd
      rw [h1, if_neg hd]
  · rw [if_neg hcomp]
    refine Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun q' _ =>
      Finset.sum_eq_zero fun τ' _ => ?_
    rw [windowEscAmp_prod, windowEscAmp_prod, star_ite_mul]
    apply if_neg
    intro hcon
    exact hcomp fun j hj => by
      have h2 : j ≠ c₂.head := by rw [← hh]; exact hj
      exact (hcon.1.2 j hj).symm.trans (hcon.2.2 j h2)

/-- The columns of the full transition matrix, including escape outcomes, are orthonormal. -/
theorem windowStepFull_gram (M : LocalQTM Q A) (c₁ c₂ : WindowCfg t Q A) :
    ∑ tgt : WindowFull t Q A, star (windowStepFull M tgt c₁) * windowStepFull M tgt c₂ =
      if c₁ = c₂ then (1 : ℂ) else 0 := by
  classical
  have hsplit : (∑ tgt : WindowFull t Q A,
      star (windowStepFull M tgt c₁) * windowStepFull M tgt c₂) =
      (∑ c' : WindowCfg t Q A, star (windowStepFull M (Sum.inl c') c₁) *
        windowStepFull M (Sum.inl c') c₂) +
      (∑ e : WindowEsc t Q A, star (windowStepFull M (Sum.inr e) c₁) *
        windowStepFull M (Sum.inr e) c₂) := Fintype.sum_sum_type _
  rw [hsplit]
  have hcfg : ∀ c₁ c₂ : WindowCfg t Q A,
      (∑ c' : WindowCfg t Q A, star (windowStepFull M (Sum.inl c') c₁) *
        windowStepFull M (Sum.inl c') c₂) =
      ∑ c' : WindowCfg t Q A, star (windowStep M c' c₁) * windowStep M c' c₂ := by
    intro c₁ c₂
    exact Finset.sum_congr rfl fun c' _ => rfl
  have hesc : ∀ c₁ c₂ : WindowCfg t Q A,
      (∑ e : WindowEsc t Q A, star (windowStepFull M (Sum.inr e) c₁) *
        windowStepFull M (Sum.inr e) c₂) =
      ∑ e : WindowEsc t Q A, star (windowEscAmp M c₁ e) * windowEscAmp M c₂ e := by
    intro c₁ c₂
    exact Finset.sum_congr rfl fun e _ => rfl
  rw [hcfg, hesc]
  by_cases hh : c₁.head = c₂.head
  · by_cases he : c₁ = c₂
    · subst he
      rw [if_pos rfl]
      have hcomp : ∀ j : Fin (2 * t + 1), j ≠ c₁.head → c₁.tape j = c₁.tape j := fun _ _ => rfl
      rw [windowGram_eq, escGram_sameHead M c₁ c₁ rfl, if_pos hcomp]
      have hmerge : (∑ d : QtmMove,
            if (∀ j : Fin (2 * t + 1), j ≠ c₁.head → c₁.tape j = c₁.tape j) ∧
                moveCell d c₁.head = moveCell d c₁.head ∧ moveCell d c₁.head ≠ none then
              ∑ q' : Q, ∑ b : A,
                star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                  M.step c₁.state (c₁.tape c₁.head) d q' b
            else 0) +
          (∑ d : QtmMove, if moveCell d c₁.head = none then
            ∑ q' : Q, ∑ b : A,
              star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                M.step c₁.state (c₁.tape c₁.head) d q' b
            else (0 : ℂ)) =
          (1 : ℂ) := by
        have hkey : ∀ d : QtmMove,
            (if (∀ j : Fin (2 * t + 1), j ≠ c₁.head → c₁.tape j = c₁.tape j) ∧
                moveCell d c₁.head = moveCell d c₁.head ∧ moveCell d c₁.head ≠ none then
              ∑ q' : Q, ∑ b : A,
                star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                  M.step c₁.state (c₁.tape c₁.head) d q' b
            else 0) +
            (if moveCell d c₁.head = none then
              ∑ q' : Q, ∑ b : A,
                star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                  M.step c₁.state (c₁.tape c₁.head) d q' b
            else 0) =
            ∑ q' : Q, ∑ b : A,
              star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                M.step c₁.state (c₁.tape c₁.head) d q' b := by
          intro d
          by_cases hd : moveCell d c₁.head = none
          · rw [if_neg, if_pos hd, zero_add]
            intro hcon
            exact hcon.2.2 hd
          · rw [if_pos, if_neg hd, add_zero]
            exact ⟨fun _ _ => rfl, rfl, hd⟩
        rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun d _ => hkey d)]
        have hre : (∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
              star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                M.step c₁.state (c₁.tape c₁.head) d q' b) =
            ((∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
              ‖M.step c₁.state (c₁.tape c₁.head) d q' b‖ ^ 2 : ℝ) : ℂ) := by
          have hper : ∀ d : QtmMove,
              (∑ q' : Q, ∑ b : A,
                star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                  M.step c₁.state (c₁.tape c₁.head) d q' b) =
              ((∑ q' : Q, ∑ b : A,
                ‖M.step c₁.state (c₁.tape c₁.head) d q' b‖ ^ 2 : ℝ) : ℂ) := by
            intro d
            have h2 : (∑ q' : Q, ∑ b : A,
                star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                  M.step c₁.state (c₁.tape c₁.head) d q' b) =
                ∑ q' : Q, ∑ b : A,
                  ((‖M.step c₁.state (c₁.tape c₁.head) d q' b‖ ^ 2 : ℝ) : ℂ) :=
              Finset.sum_congr rfl fun q' _ =>
                Finset.sum_congr rfl fun b _ => by
                  rw [star_eq_starRingEnd, ← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]
            rw [h2]
            have hA : (∑ q' : Q, ∑ b : A,
                ((‖M.step c₁.state (c₁.tape c₁.head) d q' b‖ ^ 2 : ℝ) : ℂ)) =
                ∑ q' : Q, ((∑ b : A, ‖M.step c₁.state (c₁.tape c₁.head) d q' b‖ ^ 2 : ℝ) : ℂ) :=
              Finset.sum_congr rfl fun q' _ =>
                Eq.symm (Complex.ofReal_sum (Finset.univ : Finset A)
                  (fun b => ‖M.step c₁.state (c₁.tape c₁.head) d q' b‖ ^ 2))
            rw [hA, Complex.ofReal_sum]
          rw [Finset.sum_congr rfl (fun d _ => hper d), Complex.ofReal_sum]
        rw [hre]
        have hnorm := M.wf_norm c₁.state (c₁.tape c₁.head)
        have hreorder : (∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
              ‖M.step c₁.state (c₁.tape c₁.head) d q' b‖ ^ 2) =
            ∑ q' : Q, ∑ b : A, ∑ d : QtmMove,
              ‖M.step c₁.state (c₁.tape c₁.head) d q' b‖ ^ 2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun q' _ => Finset.sum_comm
        rw [hreorder, hnorm]
        simp
      exact hmerge
    · rw [if_neg he]
      by_cases hcomp : ∀ j : Fin (2 * t + 1), j ≠ c₁.head → c₁.tape j = c₂.tape j
      · have hv : (c₁.state, c₁.tape c₁.head) ≠ (c₂.state, c₂.tape c₂.head) := by
          intro hview
          apply he
          have hs : c₁.state = c₂.state := congrArg Prod.fst hview
          have ht : c₁.tape c₁.head = c₂.tape c₂.head := congrArg Prod.snd hview
          refine windowCfg_eq hh hs ?_
          funext j
          by_cases hj : j = c₁.head
          · rw [hj]
            rw [← hh] at ht
            exact ht
          · exact hcomp j hj
        rw [windowGram_eq, escGram_sameHead M c₁ c₂ hh, if_pos hcomp]
        have hmerge : (∑ d : QtmMove,
              if (∀ j : Fin (2 * t + 1), j ≠ c₁.head → c₁.tape j = c₂.tape j) ∧
                  moveCell d c₁.head = moveCell d c₂.head ∧ moveCell d c₁.head ≠ none then
                ∑ q' : Q, ∑ b : A,
                  star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                    M.step c₂.state (c₂.tape c₂.head) d q' b
              else 0) +
            (∑ d : QtmMove, if moveCell d c₁.head = none then
              ∑ q' : Q, ∑ b : A,
                star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                  M.step c₂.state (c₂.tape c₂.head) d q' b
              else (0 : ℂ)) = (0 : ℂ) := by
          have hkey : ∀ d : QtmMove,
              (if (∀ j : Fin (2 * t + 1), j ≠ c₁.head → c₁.tape j = c₂.tape j) ∧
                  moveCell d c₁.head = moveCell d c₂.head ∧ moveCell d c₁.head ≠ none then
                ∑ q' : Q, ∑ b : A,
                  star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                    M.step c₂.state (c₂.tape c₂.head) d q' b
              else 0) +
              (if moveCell d c₁.head = none then
                ∑ q' : Q, ∑ b : A,
                  star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                    M.step c₂.state (c₂.tape c₂.head) d q' b
                else (0 : ℂ)) =
              if moveCell d c₁.head = none then
                ∑ q' : Q, ∑ b : A,
                  star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                    M.step c₂.state (c₂.tape c₂.head) d q' b
                else
                  ∑ q' : Q, ∑ b : A,
                    star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                      M.step c₂.state (c₂.tape c₂.head) d q' b := by
            intro d
            by_cases hd : moveCell d c₁.head = none
            · rw [if_neg, if_pos hd]
              · simp
              · intro hcon
                exact hcon.2.2 hd
            · rw [if_pos, if_neg hd]
              · simp
              · exact ⟨hcomp, by rw [hh], hd⟩
          rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun d _ => hkey d)]
          have hsum : (∑ d : QtmMove,
                if moveCell d c₁.head = none then
                  ∑ q' : Q, ∑ b : A,
                    star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                      M.step c₂.state (c₂.tape c₂.head) d q' b
                  else
                    ∑ q' : Q, ∑ b : A,
                      star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                        M.step c₂.state (c₂.tape c₂.head) d q' b) =
              ∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
                star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                  M.step c₂.state (c₂.tape c₂.head) d q' b := by
            refine Finset.sum_congr rfl fun d _ => ?_
            by_cases hd : moveCell d c₁.head = none <;> simp [hd]
          rw [hsum]
          have hreorder : (∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
                star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                  M.step c₂.state (c₂.tape c₂.head) d q' b) =
              ∑ q' : Q, ∑ b : A, ∑ d : QtmMove,
                star (M.step c₁.state (c₁.tape c₁.head) d q' b) *
                  M.step c₂.state (c₂.tape c₂.head) d q' b := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun q' _ => Finset.sum_comm
          rw [hreorder]
          exact M.wf_sameCell c₁.state (c₁.tape c₁.head) c₂.state (c₂.tape c₂.head) hv
        exact hmerge
      · rw [windowGram_eq, escGram_sameHead M c₁ c₂ hh, if_neg hcomp, add_zero]
        refine Finset.sum_eq_zero fun d _ => ?_
        rw [if_neg (fun hcon => hcomp hcon.1)]
  · rw [if_neg (fun h => hh (congrArg WindowCfg.head h))]
    rw [windowGram_eq, escGram_diffHead M c₁ c₂ hh, add_zero]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [if_neg]
    intro hcon
    exact hh (moveCell_inj d hcon.2.1)

/-- Every full transition column has squared norm one. -/
theorem windowStepFull_columnNorm (M : LocalQTM Q A) (c : WindowCfg t Q A) :
    ∑ tgt : WindowFull t Q A, ‖windowStepFull M tgt c‖ ^ 2 = 1 := by
  have h := windowStepFull_gram M c c
  rw [if_pos rfl] at h
  have hre : (∑ tgt : WindowFull t Q A, ‖windowStepFull M tgt c‖ ^ 2) =
      (∑ tgt : WindowFull t Q A,
        star (windowStepFull M tgt c) * windowStepFull M tgt c).re := by
    have hcast : (∑ tgt : WindowFull t Q A,
        star (windowStepFull M tgt c) * windowStepFull M tgt c).re =
        ∑ tgt : WindowFull t Q A,
          (star (windowStepFull M tgt c) * windowStepFull M tgt c).re := by
      simpa using! map_sum Complex.reAddGroupHom
        (fun tgt => star (windowStepFull M tgt c) * windowStepFull M tgt c) Finset.univ
    rw [hcast]
    exact Finset.sum_congr rfl fun tgt _ => normSq_eq _
  rw [hre, h]
  simp

/-- The in-window squared column norm plus the total squared escape amplitude is one. -/
theorem windowStepFull_window_add_esc (M : LocalQTM Q A) (c : WindowCfg t Q A) :
    (∑ c' : WindowCfg t Q A, ‖windowStep M c' c‖ ^ 2) +
      (∑ e : WindowEsc t Q A, ‖windowEscAmp M c e‖ ^ 2) = 1 := by
  have h := windowStepFull_columnNorm M c
  have hsplit : (∑ tgt : WindowFull t Q A, ‖windowStepFull M tgt c‖ ^ 2) =
      (∑ c' : WindowCfg t Q A, ‖windowStep M c' c‖ ^ 2) +
        (∑ e : WindowEsc t Q A, ‖windowEscAmp M c e‖ ^ 2) := by
    have h1 := Fintype.sum_sum_type
      (fun tgt : WindowFull t Q A => ‖windowStepFull M tgt c‖ ^ 2)
    rw [h1]
    refine congrArg₂ (· + ·) ?_ ?_
    · exact Finset.sum_congr rfl fun c' _ => by rw [windowStepFull_apply_inl]
    · exact Finset.sum_congr rfl fun e _ => by rw [windowStepFull_apply_inr]
  rw [← hsplit]
  exact h

/-- For any complex input state, the sum of the squared norms of its in-window and escape
outputs equals its input squared norm. -/
theorem windowStepFull_state_add_esc (M : LocalQTM Q A) (φ : WindowCfg t Q A → ℂ) :
    (∑ c' : WindowCfg t Q A, ‖∑ c : WindowCfg t Q A, windowStep M c' c * φ c‖ ^ 2) +
      (∑ e : WindowEsc t Q A,
        ‖∑ c : WindowCfg t Q A, windowEscAmp M c e * φ c‖ ^ 2) =
      ∑ c : WindowCfg t Q A, ‖φ c‖ ^ 2 := by
  classical
  have hgram : ∀ c₁ c₂ : WindowCfg t Q A,
      ∑ tgt : WindowFull t Q A, star (windowStepFull M tgt c₁) *
        windowStepFull M tgt c₂ = if c₁ = c₂ then (1 : ℂ) else 0 :=
    fun c₁ c₂ => windowStepFull_gram M c₁ c₂
  have hkey : (∑ tgt : WindowFull t Q A,
      ‖∑ c : WindowCfg t Q A, windowStepFull M tgt c * φ c‖ ^ 2) =
      ∑ c : WindowCfg t Q A, ‖φ c‖ ^ 2 := by
    have hnorm : (∑ tgt : WindowFull t Q A,
        ‖∑ c : WindowCfg t Q A, windowStepFull M tgt c * φ c‖ ^ 2) =
        (∑ tgt : WindowFull t Q A,
          star (∑ c : WindowCfg t Q A, windowStepFull M tgt c * φ c) *
            (∑ c : WindowCfg t Q A, windowStepFull M tgt c * φ c)).re := by
      have hcast : (∑ tgt : WindowFull t Q A,
          star (∑ c : WindowCfg t Q A, windowStepFull M tgt c * φ c) *
            (∑ c : WindowCfg t Q A, windowStepFull M tgt c * φ c)).re =
          ∑ tgt : WindowFull t Q A,
            (star (∑ c : WindowCfg t Q A, windowStepFull M tgt c * φ c) *
              (∑ c : WindowCfg t Q A, windowStepFull M tgt c * φ c)).re := by
        simpa using! map_sum Complex.reAddGroupHom
          (fun tgt => star (∑ c : WindowCfg t Q A, windowStepFull M tgt c * φ c) *
            (∑ c : WindowCfg t Q A, windowStepFull M tgt c * φ c)) Finset.univ
      rw [hcast]
      refine Finset.sum_congr rfl fun tgt _ => ?_
      rw [normSq_eq]
    rw [hnorm]
    have hexpand : (∑ tgt : WindowFull t Q A,
        star (∑ c : WindowCfg t Q A, windowStepFull M tgt c * φ c) *
          (∑ c : WindowCfg t Q A, windowStepFull M tgt c * φ c)) =
        ∑ c : WindowCfg t Q A, ∑ c' : WindowCfg t Q A,
          star (φ c) * φ c' *
            (∑ tgt : WindowFull t Q A, star (windowStepFull M tgt c) *
              windowStepFull M tgt c') := by
      have hinner : ∀ tgt : WindowFull t Q A,
          star (∑ c : WindowCfg t Q A, windowStepFull M tgt c * φ c) *
            (∑ c' : WindowCfg t Q A, windowStepFull M tgt c' * φ c') =
          ∑ c : WindowCfg t Q A, ∑ c' : WindowCfg t Q A,
            star (windowStepFull M tgt c * φ c) * (windowStepFull M tgt c' * φ c') := by
        intro tgt
        rw [star_sum, Finset.sum_mul_sum]
      calc
        (∑ tgt : WindowFull t Q A,
            star (∑ c : WindowCfg t Q A, windowStepFull M tgt c * φ c) *
              (∑ c : WindowCfg t Q A, windowStepFull M tgt c * φ c))
            = ∑ tgt : WindowFull t Q A,
                ∑ c : WindowCfg t Q A, ∑ c' : WindowCfg t Q A,
                  star (windowStepFull M tgt c * φ c) *
                    (windowStepFull M tgt c' * φ c') :=
              Finset.sum_congr rfl fun tgt _ => hinner tgt
        _ = ∑ c : WindowCfg t Q A, ∑ c' : WindowCfg t Q A,
              ∑ tgt : WindowFull t Q A,
                star (windowStepFull M tgt c * φ c) *
                  (windowStepFull M tgt c' * φ c') := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun c _ => Finset.sum_comm
        _ = ∑ c : WindowCfg t Q A, ∑ c' : WindowCfg t Q A,
              star (φ c) * φ c' *
                (∑ tgt : WindowFull t Q A, star (windowStepFull M tgt c) *
                  windowStepFull M tgt c') := by
              refine Finset.sum_congr rfl fun c _ => ?_
              refine Finset.sum_congr rfl fun c' _ => ?_
              have hswap : (∑ tgt : WindowFull t Q A,
                  star (windowStepFull M tgt c * φ c) *
                    (windowStepFull M tgt c' * φ c')) =
                  ∑ tgt : WindowFull t Q A,
                    star (φ c) * φ c' *
                      (star (windowStepFull M tgt c) * windowStepFull M tgt c') :=
                Finset.sum_congr rfl fun tgt _ => by
                  rw [star_mul]
                  ring
              rw [hswap, ← Finset.mul_sum]
    rw [hexpand]
    have hcollapse : (∑ c : WindowCfg t Q A, ∑ c' : WindowCfg t Q A,
        star (φ c) * φ c' *
          (∑ tgt : WindowFull t Q A, star (windowStepFull M tgt c) *
            windowStepFull M tgt c')) =
        ((∑ c : WindowCfg t Q A, ‖φ c‖ ^ 2 : ℝ) : ℂ) := by
      have hper : ∀ c : WindowCfg t Q A,
          (∑ c' : WindowCfg t Q A, star (φ c) * φ c' *
            (∑ tgt : WindowFull t Q A, star (windowStepFull M tgt c) *
              windowStepFull M tgt c')) =
          star (φ c) * φ c := by
        intro c
        have hsingle : (∑ c' : WindowCfg t Q A,
            star (φ c) * φ c' *
              (∑ tgt : WindowFull t Q A, star (windowStepFull M tgt c) *
                windowStepFull M tgt c')) =
            star (φ c) * φ c *
              (∑ tgt : WindowFull t Q A, star (windowStepFull M tgt c) *
                windowStepFull M tgt c) := by
          rw [Finset.sum_eq_single_of_mem c (Finset.mem_univ _)]
          intro c' _ hc'
          rw [hgram c c', if_neg (Ne.symm hc')]
          ring
        rw [hsingle, hgram c c, if_pos rfl]
        ring
      have h2 : (∑ c : WindowCfg t Q A, ∑ c' : WindowCfg t Q A,
          star (φ c) * φ c' *
            (∑ tgt : WindowFull t Q A, star (windowStepFull M tgt c) *
              windowStepFull M tgt c')) =
          ∑ c : WindowCfg t Q A, star (φ c) * φ c :=
        Finset.sum_congr rfl fun c _ => hper c
      have h3 : (∑ c : WindowCfg t Q A, star (φ c) * φ c) =
          ∑ c : WindowCfg t Q A, ((‖φ c‖ ^ 2 : ℝ) : ℂ) :=
        Finset.sum_congr rfl fun c _ => by
          rw [star_eq_starRingEnd, ← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]
      rw [h2, h3, Complex.ofReal_sum]
    rw [hcollapse, Complex.ofReal_re]
  have hsplit : (∑ tgt : WindowFull t Q A,
      ‖∑ c : WindowCfg t Q A, windowStepFull M tgt c * φ c‖ ^ 2) =
      (∑ c' : WindowCfg t Q A, ‖∑ c : WindowCfg t Q A, windowStep M c' c * φ c‖ ^ 2) +
        (∑ e : WindowEsc t Q A,
          ‖∑ c : WindowCfg t Q A, windowEscAmp M c e * φ c‖ ^ 2) := by
    have h1 := Fintype.sum_sum_type
      (fun tgt : WindowFull t Q A => ‖∑ c : WindowCfg t Q A, windowStepFull M tgt c * φ c‖ ^ 2)
    rw [h1]
    refine congrArg₂ (· + ·) ?_ ?_
    · exact Finset.sum_congr rfl fun c' _ => rfl
    · exact Finset.sum_congr rfl fun e _ => rfl
  rw [← hsplit]
  exact hkey

/-- The finite-window transition does not increase the squared norm of any complex input state. -/
theorem windowStep_state_contraction (M : LocalQTM Q A) (φ : WindowCfg t Q A → ℂ) :
    ∑ c' : WindowCfg t Q A, ‖∑ c : WindowCfg t Q A, windowStep M c' c * φ c‖ ^ 2 ≤
      ∑ c : WindowCfg t Q A, ‖φ c‖ ^ 2 := by
  have h := windowStepFull_state_add_esc M φ
  have h0 : (0 : ℝ) ≤ ∑ e : WindowEsc t Q A,
      ‖∑ c : WindowCfg t Q A, windowEscAmp M c e * φ c‖ ^ 2 :=
    Finset.sum_nonneg fun e _ => sq_nonneg _
  linarith

/-- Every natural power of the finite-window transition does not increase the squared norm of
any complex input state. -/
theorem windowStep_pow_contraction (M : LocalQTM Q A) (k : ℕ)
    (φ : WindowCfg t Q A → ℂ) :
    ∑ c' : WindowCfg t Q A,
      ‖∑ c : WindowCfg t Q A,
        ((windowStep M : Matrix (WindowCfg t Q A) (WindowCfg t Q A) ℂ) ^ k) c' c * φ c‖ ^ 2 ≤
      ∑ c : WindowCfg t Q A, ‖φ c‖ ^ 2 := by
  set W : Matrix (WindowCfg t Q A) (WindowCfg t Q A) ℂ := windowStep M
  have hW : W = windowStep M := rfl
  induction k generalizing φ with
  | zero =>
    simp only [pow_zero]
    refine le_of_eq ?_
    refine Finset.sum_congr rfl fun c' _ => ?_
    have h1 : (∑ c : WindowCfg t Q A, (1 : Matrix (WindowCfg t Q A) (WindowCfg t Q A) ℂ) c' c *
        φ c) = φ c' := by
      rw [Finset.sum_eq_single_of_mem c' (Finset.mem_univ _)]
      · rw [Matrix.one_apply, if_pos rfl, one_mul]
      · intro c _ hc
        rw [Matrix.one_apply, if_neg (Ne.symm hc), zero_mul]
    rw [h1]
  | succ k ih =>
    have hcomp : W ^ (k + 1) = W * W ^ k := by
      rw [pow_succ']
    rw [hcomp]
    have hentry : ∀ i j : WindowCfg t Q A,
        (W * W ^ k) i j = ∑ c : WindowCfg t Q A, W i c * (W ^ k) c j := by
      intro i j
      exact Matrix.mul_apply
    have hvec : ∀ c' : WindowCfg t Q A,
        (∑ x : WindowCfg t Q A, (W * W ^ k) c' x * φ x) =
          ∑ y : WindowCfg t Q A,
            W c' y * (∑ x : WindowCfg t Q A, (W ^ k) y x * φ x) := by
      intro c'
      have h1 : (∑ x : WindowCfg t Q A, (W * W ^ k) c' x * φ x) =
          ∑ x : WindowCfg t Q A,
            (∑ y : WindowCfg t Q A, W c' y * (W ^ k) y x) * φ x :=
        Finset.sum_congr rfl fun x _ => by rw [hentry]
      have h2 : (∑ x : WindowCfg t Q A,
          (∑ y : WindowCfg t Q A, W c' y * (W ^ k) y x) * φ x) =
          ∑ x : WindowCfg t Q A, ∑ y : WindowCfg t Q A,
            W c' y * ((W ^ k) y x * φ x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
      have h3 : (∑ x : WindowCfg t Q A, ∑ y : WindowCfg t Q A,
          W c' y * ((W ^ k) y x * φ x)) =
          ∑ y : WindowCfg t Q A, ∑ x : WindowCfg t Q A,
            W c' y * ((W ^ k) y x * φ x) := Finset.sum_comm
      have h4 : (∑ y : WindowCfg t Q A, ∑ x : WindowCfg t Q A,
          W c' y * ((W ^ k) y x * φ x)) =
          ∑ y : WindowCfg t Q A,
            W c' y * (∑ x : WindowCfg t Q A, (W ^ k) y x * φ x) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
      rw [h1, h2, h3, h4]
    have hvec' : (∑ c' : WindowCfg t Q A,
        ‖∑ c : WindowCfg t Q A, (W * W ^ k) c' c * φ c‖ ^ 2) =
        ∑ c' : WindowCfg t Q A,
          ‖∑ c : WindowCfg t Q A, W c' c *
            (∑ c₂ : WindowCfg t Q A, (W ^ k) c c₂ * φ c₂)‖ ^ 2 :=
      Finset.sum_congr rfl fun c' _ => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hvec c')
    rw [hvec']
    have hle : (∑ c' : WindowCfg t Q A,
        ‖∑ c : WindowCfg t Q A, W c' c *
          (∑ c₂ : WindowCfg t Q A, (W ^ k) c c₂ * φ c₂)‖ ^ 2) ≤
        ∑ c : WindowCfg t Q A,
          ‖∑ c₂ : WindowCfg t Q A, (W ^ k) c c₂ * φ c₂‖ ^ 2 := by
      have h := windowStep_state_contraction M
        (fun c => ∑ c₂ : WindowCfg t Q A, (W ^ k) c c₂ * φ c₂)
      simpa only [← hW] using! h
    exact hle.trans (ih φ)

/-- For an input index `i` with `i.val < t`, the initialized window tape contains `x i` at cell
`t + 1 + i.val`. -/
theorem initWindowCfg_tape_of_lt (M : LocalQTM Q A) {n : ℕ} (x : Fin n → A) (i : Fin n)
    (hi : i.val < t) :
    (initWindowCfg (t := t) M n x).tape ⟨t + 1 + i.val, by omega⟩ = x i := by
  have hilt := i.isLt
  have hj : (⟨t + 1 + i.val, by omega⟩ : Fin (2 * t + 1)).val = t + 1 + i.val := rfl
  have hp : t < (⟨t + 1 + i.val, by omega⟩ : Fin (2 * t + 1)).val ∧
      (⟨t + 1 + i.val, by omega⟩ : Fin (2 * t + 1)).val ≤ t + n := by
    rw [hj]
    exact ⟨by omega, by omega⟩
  unfold initWindowCfg
  simp only
  rw [dif_pos hp]
  refine congrArg x (Fin.ext ?_)
  show t + 1 + i.val - t - 1 = i.val
  omega

/-- An initialized tape cell strictly beyond `t + n` contains the machine's blank symbol. -/
theorem initWindowCfg_tape_blank (M : LocalQTM Q A) {n : ℕ} (x : Fin n → A)
    (j : Fin (2 * t + 1)) (hj : t + n < j.val) :
    (initWindowCfg (t := t) M n x).tape j = M.blank := by
  have hneg : ¬ (t < j.val ∧ j.val ≤ t + n) := by
    intro hcon
    omega
  unfold initWindowCfg
  simp only
  rw [dif_neg hneg]

/-- An input index with `t ≤ i.val` has no corresponding cell `t + 1 + i.val` in the window. -/
theorem initWindowCfg_input_outside {n : ℕ} (i : Fin n)
    (hi : t ≤ i.val) :
    ¬ ∃ j : Fin (2 * t + 1), j.val = t + 1 + i.val := by
  intro hcon
  obtain ⟨j, hj⟩ := hcon
  have hlt := j.isLt
  omega

/-- For `t = 0`, the initialized window tape is blank at every cell. -/
theorem initWindowCfg_tape_zero_width (M : LocalQTM Q A) {n : ℕ} (x : Fin n → A) :
    (initWindowCfg M n x : WindowCfg 0 Q A).tape = fun _ => M.blank := by
  funext j
  have hj : j.val = 0 := by
    have hlt := j.isLt
    omega
  have hneg : ¬ (0 < j.val ∧ j.val ≤ 0 + n) := by
    intro hcon
    omega
  unfold initWindowCfg
  simp only
  rw [dif_neg hneg]

end B3FullOutcome

end Qatlib.Concepts.CircuitImpl.MultiControl
