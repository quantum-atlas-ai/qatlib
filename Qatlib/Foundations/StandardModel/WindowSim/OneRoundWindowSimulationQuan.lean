/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StandardModel.WindowSim.OneRoundWindowSimulationStat
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# One round of window simulation

This module proves `oneRoundWindowSimulation`: a sweep of three-cell gates followed by a marker
swap implements one transition of a local quantum Turing machine on an encoded configuration
with an interior head. The proof tracks the transition superposition through each sweep prefix
using local projections and agreement outside the active window.

The mathematical background is discussed in [Yao1993].

## Main statements

* `sweep_run_prefix`: describes the state after a prefix of the local gate sweep.
* `iSwap_sweepState`: identifies the marker-swapped superposition with the embedded machine
  step.
* `oneRoundWindowSimulation`: establishes the one-round simulation contract.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Qatlib.Foundations.StandardDefs.WindowSim

open Matrix

/-- A sum over head directions is the sum of its left, stationary, and right contributions. -/
private theorem sum_qtmMove {β : Type} [AddCommMonoid β] (f : QtmMove → β) :
    ∑ d : QtmMove, f d = f QtmMove.left + f QtmMove.stay + f QtmMove.right := by
  classical
  have hsub : ({QtmMove.left, QtmMove.stay, QtmMove.right} : Finset QtmMove) ⊆ Finset.univ :=
    Finset.subset_univ _
  rw [← Finset.sum_subset hsub (by intro x _ hx; exact absurd (Finset.mem_univ x) hx)]
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton,
    add_assoc]

/-- A condition independent of the summation index can be moved outside a finite sum whose false
branch is zero. -/
private theorem sum_ite_const {ι β : Type} [AddCommMonoid β] (b : Prop) [Decidable b]
    (s : Finset ι) (f : ι → β) :
    ∑ i ∈ s, (if b then f i else 0) = if b then ∑ i ∈ s, f i else 0 := by
  by_cases hb : b
  · simp [hb]
  · simp [hb]

/-- Matrix action distributes over a finite sum of states. -/
private theorem mulVec_sum {I ι : Type} [Fintype I] [DecidableEq I] (s : Finset ι)
    (U : Matrix I I ℂ) (f : ι → QState I) :
    U *ᵥ (∑ i ∈ s, f i) = ∑ i ∈ s, (U *ᵥ f i) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun j _ => Finset.mul_sum ..),
    Finset.sum_comm]

/-- Appending a gate to a circuit applies its matrix to the circuit's output state. -/
private theorem run_snoc {I : Type} [Fintype I] [DecidableEq I] (oracle U : Matrix I I ℂ)
    (C : Circuit I) (ψ : QState I) :
    Run oracle (C ++ [Step.gate U]) ψ = U *ᵥ (Run oracle C ψ) := by
  rw [run_append]
  simp [run_gate, run_nil, ApplyGate]

section Window

variable {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]

/-- Restrict a full window register to the three cells selected by `gUnitCells`. -/
private abbrev winProj (t : ℕ) (k : Fin (2 * t - 1)) (x : WReg t Q A) : GWindow Q A :=
  fun q => x (gUnitCells t k q)

/-- Agreement of two registers at every cell outside the selected three-cell window. -/
private abbrev offEq (t : ℕ) (k : Fin (2 * t - 1)) (x y : WReg t Q A) : Prop :=
  ∀ j : Fin (2 * t + 1), (∀ q : Fin 3, gUnitCells t k q ≠ j) → x j = y j

/-- Replace the selected three-cell window of a register by `w`, retaining all other cells. -/
private def winGlue (t : ℕ) (k : Fin (2 * t - 1)) (x : WReg t Q A) (w : GWindow Q A) :
    WReg t Q A := Function.extend (gUnitCells t k) w x

/-- Every register agrees with itself outside the selected window. -/
private theorem offEq_refl (t : ℕ) (k : Fin (2 * t - 1)) (x : WReg t Q A) :
    offEq t k x x := fun _ _ => rfl

/-- Agreement outside the selected window is symmetric. -/
private theorem offEq_symm {t : ℕ} {k : Fin (2 * t - 1)} {x y : WReg t Q A}
    (h : offEq t k x y) : offEq t k y x := fun j hj => (h j hj).symm

/-- Agreement outside the selected window is transitive. -/
private theorem offEq_trans {t : ℕ} {k : Fin (2 * t - 1)} {x y z : WReg t Q A}
    (h : offEq t k x y) (h' : offEq t k y z) : offEq t k x z := fun j hj => (h j hj).trans (h' j hj)

/-- The global index of local cell `q` is the window's starting index plus `q.val`. -/
private theorem gUnitCells_val (t : ℕ) (k : Fin (2 * t - 1)) (q : Fin 3) :
    (gUnitCells t k q).val = k.val + q.val := by
  fin_cases q <;> simp [gUnitCells]

/-- The three local cell positions map to distinct global cell positions. -/
private theorem gUnitCells_injective (t : ℕ) (k : Fin (2 * t - 1)) :
    Function.Injective (gUnitCells t k) := by
  intro q₁ q₂ h
  have h' := congrArg Fin.val h
  rw [gUnitCells_val, gUnitCells_val] at h'
  exact Fin.ext (by omega)

/-- Projecting a register after replacing its active window recovers the replacement window. -/
private theorem winGlue_proj (t : ℕ) (k : Fin (2 * t - 1)) (x : WReg t Q A) (w : GWindow Q A) :
    winProj t k (winGlue t k x w) = w :=
  funext fun q => Function.Injective.extend_apply (gUnitCells_injective t k) w x q

/-- Replacing an active window preserves agreement with the original register outside that
window. -/
private theorem offEq_glue_self (t : ℕ) (k : Fin (2 * t - 1)) (x : WReg t Q A)
    (w : GWindow Q A) : offEq t k (winGlue t k x w) x := by
  intro j hj
  simp only [winGlue]
  exact Function.extend_apply' _ _ _ (fun h => by obtain ⟨q, hq⟩ := h; exact hj q hq)

/-- A register agreeing with `x` outside the active window is recovered by inserting its
projection into `x`. -/
private theorem winGlue_proj' (t : ℕ) (k : Fin (2 * t - 1)) (x y : WReg t Q A)
    (h : offEq t k x y) : winGlue t k x (winProj t k y) = y := by
  funext j
  by_cases hj : ∃ q, gUnitCells t k q = j
  · obtain ⟨q, hq⟩ := hj
    rw [← hq]
    exact Function.Injective.extend_apply (gUnitCells_injective t k) _ _ q
  · simp only [winGlue]
    rw [Function.extend_apply' _ _ _ hj]
    exact h j (fun q hq => hj ⟨q, hq⟩)

/-- Registers with equal window projections and agreement outside the window are equal. -/
private theorem eq_of_offEq_winProj {t : ℕ} {k : Fin (2 * t - 1)} {x y : WReg t Q A}
    (h : offEq t k x y) (hp : winProj t k x = winProj t k y) : x = y := by
  funext j
  by_cases hj : ∃ q, gUnitCells t k q = j
  · obtain ⟨q, hq⟩ := hj
    subst hq
    show winProj t k x q = winProj t k y q
    rw [hp]
  · exact h j (fun q hq => hj ⟨q, hq⟩)

/-- The lifted gate has the local matrix entry when its two registers agree outside the active
window, and zero otherwise. -/
private theorem gUnitFull_apply (t : ℕ) (G : Matrix (GWindow Q A) (GWindow Q A) ℂ)
    (k : Fin (2 * t - 1)) (x y : WReg t Q A) :
    gUnitFull G k x y = if offEq t k x y then G (winProj t k x) (winProj t k y) else 0 := rfl

/-- Lifted local gates at window indices with equal values coincide. -/
private theorem gUnitFull_congr {t : ℕ} {G : Matrix (GWindow Q A) (GWindow Q A) ℂ}
    {k k' : Fin (2 * t - 1)} (h : k.val = k'.val) : gUnitFull G k = gUnitFull G k' := by
  have hcells : gUnitCells t k = gUnitCells t k' := by
    funext q
    exact Fin.ext (by simp only [gUnitCells_val, h])
  unfold gUnitFull
  rw [hcells]

/-- The amplitude after a lifted gate is a sum over replacement windows, weighted by the
corresponding local gate entries. -/
private theorem gUnitFull_mulVec_apply (t : ℕ) (G : Matrix (GWindow Q A) (GWindow Q A) ℂ)
    (k : Fin (2 * t - 1)) (ψ : QState (WReg t Q A)) (x : WReg t Q A) :
    (gUnitFull G k *ᵥ ψ) x
      = ∑ w : GWindow Q A, G (winProj t k x) w * ψ (winGlue t k x w) := by
  classical
  simp only [Matrix.mulVec, dotProduct, gUnitFull_apply, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have himg : (Finset.univ.filter fun y => offEq t k x y)
      = Finset.univ.image (winGlue t k x) := by
    ext y
    constructor
    · intro hy
      have hy' := (Finset.mem_filter.mp hy).2
      exact Finset.mem_image.mpr ⟨winProj t k y, Finset.mem_univ _, winGlue_proj' t k x y hy'⟩
    · intro hymem
      rw [Finset.mem_image] at hymem
      obtain ⟨w, _, hw⟩ := hymem
      rw [← hw]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, offEq_symm (offEq_glue_self t k x w)⟩
  rw [himg, Finset.sum_image]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [winGlue_proj]
  · intro w₁ _ w₂ _ heq
    rw [← winGlue_proj t k x w₁, ← winGlue_proj t k x w₂, heq]

/-- Embed a local state into full registers that agree with `y` outside the active window,
assigning zero elsewhere. -/
private def liftWin (t : ℕ) (k : Fin (2 * t - 1)) (y : WReg t Q A) (φ : QState (GWindow Q A)) :
    QState (WReg t Q A) := fun x => if offEq t k x y then φ (winProj t k x) else 0

/-- Acting by a lifted local gate commutes with embedding a local state using `liftWin`. -/
private theorem gUnitFull_mulVec_liftWin (t : ℕ) (G : Matrix (GWindow Q A) (GWindow Q A) ℂ)
    (k : Fin (2 * t - 1)) (y : WReg t Q A) (φ : QState (GWindow Q A)) :
    gUnitFull G k *ᵥ (liftWin t k y φ) = liftWin t k y (G *ᵥ φ) := by
  funext x
  rw [gUnitFull_mulVec_apply]
  by_cases hx : offEq t k x y
  · have hglue : ∀ w : GWindow Q A, offEq t k (winGlue t k x w) y := fun w =>
      offEq_trans (offEq_glue_self t k x w) hx
    simp only [liftWin, if_pos hx, if_pos (hglue _), winGlue_proj,
      Matrix.mulVec, dotProduct]
  · have hzero : ∀ w : GWindow Q A, liftWin t k y φ (winGlue t k x w) = 0 := by
      intro w
      have h1 : offEq t k (winGlue t k x w) x := offEq_glue_self t k x w
      have h2 : ¬ offEq t k (winGlue t k x w) y := fun hc => hx (offEq_trans (offEq_symm h1) hc)
      simp only [liftWin, if_neg h2]
    rw [Finset.sum_congr rfl (fun w _ => by rw [hzero w, mul_zero])]
    simp only [Finset.sum_const_zero, liftWin, if_neg hx]

/-- A register basis state is the lift of its window basis state relative to any register
agreeing outside the window. -/
private theorem ket_eq_liftWin' (t : ℕ) (k : Fin (2 * t - 1)) (y y' : WReg t Q A)
    (w : GWindow Q A) (hproj : winProj t k y = w) (hoff : offEq t k y y') :
    Qatlib.Foundations.PureStateMath.Ket y = liftWin t k y' (Qatlib.Foundations.PureStateMath.Ket w) := by
  funext x
  rw [ket_apply, liftWin]
  by_cases hx : offEq t k x y'
  · rw [if_pos hx, ket_apply]
    by_cases hxy : x = y
    · rw [if_pos hxy, if_pos (by rw [hxy, hproj])]
    · rw [if_neg hxy, if_neg]
      intro hp
      exact hxy (eq_of_offEq_winProj (offEq_trans hx (offEq_symm hoff))
        (by rw [hp, hproj]))
  · rw [if_neg hx, if_neg]
    intro hxy
    subst hxy
    exact hx hoff

/-- A gate satisfying `GUnitFixesH` fixes any full register basis state whose active window is
of type I. -/
private theorem gUnitFull_mulVec_ket_fix (t : ℕ) {M : LocalQTM Q A}
    {G : Matrix (GWindow Q A) (GWindow Q A) ℂ} (hfix : GUnitFixesH M G)
    (k : Fin (2 * t - 1)) (y : WReg t Q A) (hz : IsTypeI (winProj t k y)) :
    gUnitFull G k *ᵥ Qatlib.Foundations.PureStateMath.Ket y = Qatlib.Foundations.PureStateMath.Ket y := by
  have h1 : Qatlib.Foundations.PureStateMath.Ket y = liftWin t k y (Qatlib.Foundations.PureStateMath.Ket (winProj t k y)) :=
    ket_eq_liftWin' t k y y (winProj t k y) rfl (offEq_refl t k y)
  rw [h1, gUnitFull_mulVec_liftWin, hfix.1 _ hz]

/-- Two three-cell windows are equal exactly when their entries at all three positions agree. -/
private theorem gw_eq_iff (z w : GWindow Q A) :
    z = w ↔ z 0 = w 0 ∧ z 1 = w 1 ∧ z 2 = w 2 := by
  constructor
  · intro h; exact ⟨h ▸ rfl, h ▸ rfl, h ▸ rfl⟩
  · rintro ⟨h0, h1, h2⟩
    funext q
    fin_cases q <;> simp [h0, h1, h2]

/-- The basis state of a specified three-cell pattern evaluates to one exactly on that pattern
and to zero elsewhere. -/
private theorem ket_pat_apply (P0 P1 P2 : CellState Q A) (w : GWindow Q A) :
    Qatlib.Foundations.PureStateMath.Ket ![P0, P1, P2] w = if w 0 = P0 ∧ w 1 = P1 ∧ w 2 = P2 then (1 : ℂ) else 0 := by
  rw [ket_apply]
  by_cases h : w 0 = P0 ∧ w 1 = P1 ∧ w 2 = P2
  · rw [if_pos h, if_pos]
    funext q
    fin_cases q <;> simp [h.1, h.2.1, h.2.2]
  · rw [if_neg h, if_neg]
    intro he
    exact h ⟨by rw [he]; simp, by rw [he]; simp, by rw [he]; simp⟩

/-- The head basis state is the ket of the three-cell pattern with marker one at the central
head. -/
private theorem headBasis_eq_ket (q : Q) (a b c : A) :
    headBasis q a b c = Qatlib.Foundations.PureStateMath.Ket ![(0, none, b), (1, some q, a), (0, none, c)] := by
  funext z
  rw [headBasis, ket_apply]
  by_cases h : z 1 = (1, some q, a) ∧ z 0 = (0, none, b) ∧ z 2 = (0, none, c)
  · have hz : z = ![(0, none, b), (1, some q, a), (0, none, c)] := by
      funext q₀
      fin_cases q₀ <;> simp [h.1, h.2.1, h.2.2]
    rw [if_pos h, if_pos hz]
  · rw [if_neg h, if_neg]
    intro he
    exact h ⟨by rw [he]; simp, by rw [he]; simp, by rw [he]; simp⟩

/-- Expand a local transition superposition into the basis-state contributions for left,
stationary, and right moves. -/
private theorem stepSuperposition_apply (M : LocalQTM Q A) (q : Q) (a b c : A)
    (z : GWindow Q A) :
    stepSuperposition M q a b c z =
      (∑ q' : Q, ∑ a' : A,
        M.step q a QtmMove.left q' a' * Qatlib.Foundations.PureStateMath.Ket ![(2, some q', b), (0, none, a'), (0, none, c)] z)
      + (∑ q' : Q, ∑ a' : A,
        M.step q a QtmMove.stay q' a' * Qatlib.Foundations.PureStateMath.Ket ![(0, none, b), (2, some q', a'), (0, none, c)] z)
      + (∑ q' : Q, ∑ a' : A,
        M.step q a QtmMove.right q' a'
          * Qatlib.Foundations.PureStateMath.Ket ![(0, none, b), (0, none, a'), (2, some q', c)] z) := by
  simp only [stepSuperposition, ← ket_pat_apply]

/-- Expand `vFamily` at a window into its stationary and right-moving basis-state contributions. -/
private theorem vFamily_apply (M : LocalQTM Q A) (q₀ : Q) (a₀ b c : A) (z : GWindow Q A) :
    vFamily M q₀ a₀ b c z =
      (∑ q' : Q, ∑ a' : A,
        M.step q₀ a₀ QtmMove.stay q' a' * Qatlib.Foundations.PureStateMath.Ket ![(2, some q', a'), (0, none, b), (0, none, c)] z)
      + (∑ q' : Q, ∑ a' : A,
        M.step q₀ a₀ QtmMove.right q' a'
          * Qatlib.Foundations.PureStateMath.Ket ![(0, none, a'), (2, some q', b), (0, none, c)] z) := by
  simp only [vFamily, ← ket_pat_apply]

/-- Expand `uFamily` at a window as a sum over new internal states for a fixed right-moving
write symbol. -/
private theorem uFamily_apply (M : LocalQTM Q A) (q₀ : Q) (a₀ a'' b c d : A)
    (z : GWindow Q A) :
    uFamily M q₀ a₀ a'' b c d z =
      ∑ q' : Q,
        M.step q₀ a₀ QtmMove.right q' a''
          * Qatlib.Foundations.PureStateMath.Ket ![(2, some q', b), (0, none, c), (0, none, d)] z := by
  simp only [uFamily, ← ket_pat_apply]

end Window

section Encoding

variable {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]

/-- An encoded configuration has marker zero at every cell distinct from its head. -/
private theorem windowEncode_marker_zero (t : ℕ) (c : WindowCfg t Q A)
    {j : Fin (2 * t + 1)} (h : j ≠ c.head) :
    (windowEncode c j).1 = 0 := by
  simp [windowEncode, h]

/-- Encoding window configurations as cell registers is injective. -/
private theorem windowEncode_injective {t : ℕ} {Q A : Type} [DecidableEq Q] [DecidableEq A] :
    Function.Injective (windowEncode (t := t) (Q := Q) (A := A)) := by
  intro c₁ c₂ h
  have hhead : c₁.head = c₂.head := by
    by_contra hne
    have h1 : windowEncode c₁ c₁.head = (1, some c₁.state, c₁.tape c₁.head) := by
      simp [windowEncode]
    have h2 : windowEncode c₂ c₁.head = ((0 : Fin 3), none, c₂.tape c₁.head) := by
      simp [windowEncode, hne]
    have hfun := congrFun h c₁.head
    rw [h1, h2] at hfun
    exact absurd (congrArg Prod.fst hfun) (by simp)
  have hstate : c₁.state = c₂.state := by
    have h1 : windowEncode c₁ c₁.head = (1, some c₁.state, c₁.tape c₁.head) := by
      simp [windowEncode]
    have h2 : windowEncode c₂ c₁.head = (1, some c₂.state, c₂.tape c₁.head) := by
      simp [windowEncode, hhead]
    have hfun := congrFun h c₁.head
    rw [h1, h2] at hfun
    simp only [Prod.mk.injEq, Option.some.injEq] at hfun
    exact hfun.2.1
  have htape : c₁.tape = c₂.tape := by
    funext j
    have hfun := congrFun h j
    by_cases hj : j = c₁.head
    · have h1 : windowEncode c₁ j = (1, some c₁.state, c₁.tape j) := by
        simp [windowEncode, hj]
      have h2 : windowEncode c₂ j = (1, some c₂.state, c₂.tape j) := by
        simp [windowEncode, hj.trans hhead]
      rw [h1, h2] at hfun
      simp only [Prod.mk.injEq, hstate] at hfun
      exact hfun.2.2
    · have h1 : windowEncode c₁ j = ((0 : Fin 3), none, c₁.tape j) := by
        simp [windowEncode, hj]
      have hjc₂ : ¬ (j = c₂.head) := fun he => hj (he.trans hhead.symm)
      have h2 : windowEncode c₂ j = ((0 : Fin 3), none, c₂.tape j) := by
        simp [windowEncode, hjc₂]
      rw [h1, h2] at hfun
      simp only [Prod.mk.injEq] at hfun
      exact hfun.2.2
  obtain ⟨h₁, s₁, tp₁⟩ := c₁
  obtain ⟨h₂, s₂, tp₂⟩ := c₂
  simp only [WindowCfg.mk.injEq]
  exact ⟨hhead, hstate, htape⟩

/-- An embedded state evaluated at an encoded configuration has the original configuration
amplitude. -/
private theorem windowEmbed_apply {t : ℕ} (φ : QState (WindowCfg t Q A))
    (c : WindowCfg t Q A) :
    windowEmbed φ (windowEncode c) = φ c := by
  simp only [windowEmbed]
  exact windowEncode_injective.extend_apply φ 0 c

/-- An embedded state vanishes on registers outside the image of configuration encoding. -/
private theorem windowEmbed_eq_zero {t : ℕ} (φ : QState (WindowCfg t Q A))
    (r : WReg t Q A) (h : ∀ c₀, windowEncode c₀ ≠ r) :
    windowEmbed φ r = 0 := by
  simp only [windowEmbed]
  exact Function.extend_apply' _ _ _ (fun hc => by obtain ⟨c₀, hc₀⟩ := hc; exact h c₀ hc₀)

end Encoding

section Sweep

variable {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]

/-- The cell immediately to the left of a head with positive index. -/
private def winL {t : ℕ} {Q A : Type} (c : WindowCfg t Q A) (h1 : 0 < c.head.val) :
    Fin (2 * t + 1) := ⟨c.head.val - 1, by have := c.head.isLt; omega⟩

/-- The cell immediately to the right of a head below the right boundary. -/
private def winR {t : ℕ} {Q A : Type} (c : WindowCfg t Q A) (h2 : c.head.val < 2 * t) :
    Fin (2 * t + 1) := ⟨c.head.val + 1, by have := c.head.isLt; omega⟩

/-- The left neighbor's index is the head index minus one. -/
private theorem winL_val {t : ℕ} {Q A : Type} (c : WindowCfg t Q A) (h1 : 0 < c.head.val) :
    (winL c h1).val = c.head.val - 1 := rfl

/-- The right neighbor's index is the head index plus one. -/
private theorem winR_val {t : ℕ} {Q A : Type} (c : WindowCfg t Q A) (h2 : c.head.val < 2 * t) :
    (winR c h2).val = c.head.val + 1 := rfl

/-- The left neighbor is distinct from the head cell. -/
private theorem winL_ne_head {t : ℕ} {Q A : Type} (c : WindowCfg t Q A) (h1 : 0 < c.head.val) :
    winL c h1 ≠ c.head := by
  intro he
  have := congrArg Fin.val he
  rw [winL_val] at this
  omega

/-- The left neighbor is distinct from the right neighbor. -/
private theorem winL_ne_winR {t : ℕ} {Q A : Type} (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) : winL c h1 ≠ winR c h2 := by
  intro he
  have := congrArg Fin.val he
  rw [winL_val, winR_val] at this
  omega

/-- The right neighbor is distinct from the left neighbor. -/
private theorem winR_ne_winL {t : ℕ} {Q A : Type} (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) : winR c h2 ≠ winL c h1 :=
  (winL_ne_winR c h1 h2).symm

/-- The right neighbor is distinct from the head cell. -/
private theorem winR_ne_head {t : ℕ} {Q A : Type} (c : WindowCfg t Q A)
    (h2 : c.head.val < 2 * t) : winR c h2 ≠ c.head := by
  intro he
  have := congrArg Fin.val he
  rw [winR_val] at this
  omega

/-- The starting index `c.head.val - 1` of the window that triggers an interior head transition. -/
private def trigK {t : ℕ} {Q A : Type} (c : WindowCfg t Q A) (h2 : c.head.val < 2 * t) :
    Fin (2 * t - 1) := ⟨c.head.val - 1, by have := c.head.isLt; omega⟩

/-- The triggering window starts at the head index minus one. -/
private theorem trigK_val {t : ℕ} {Q A : Type} (c : WindowCfg t Q A)
    (h2 : c.head.val < 2 * t) : (trigK c h2).val = c.head.val - 1 := rfl

/-- The triggering window consists of the left neighbor, head, and right neighbor, in that
order. -/
private theorem gUnitCells_trigK (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) :
    gUnitCells t (trigK c h2) = ![winL c h1, c.head, winR c h2] := by
  have hv : ∀ q : Fin 3, (gUnitCells t (trigK c h2) q).val
      = (![winL c h1, c.head, winR c h2] q).val := by
    intro q
    rw [gUnitCells_val, trigK_val]
    fin_cases q <;> simp [winL_val, winR_val] <;> omega
  funext q
  exact Fin.ext (hv q)

/-- The register after a prescribed transition, with the written symbol at the old head and
marker two at the new head. -/
private def afterReg (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) : QtmMove → Q → A → WReg t Q A :=
  fun d q' a' j =>
    match d with
    | QtmMove.left =>
      if j = winL c h1 then (2, some q', c.tape j)
      else if j = c.head then ((0 : Fin 3), none, a')
      else windowEncode c j
    | QtmMove.stay =>
      if j = c.head then (2, some q', a') else windowEncode c j
    | QtmMove.right =>
      if j = c.head then ((0 : Fin 3), none, a')
      else if j = winR c h2 then (2, some q', c.tape j)
      else windowEncode c j

/-- For a left move, the left neighbor receives the new head state and the old head receives the
written symbol. -/
private theorem afterReg_left (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (q' : Q) (a' : A) (j : Fin (2 * t + 1)) :
    afterReg t c h1 h2 QtmMove.left q' a' j =
      (if j = winL c h1 then (2, some q', c.tape j)
      else if j = c.head then ((0 : Fin 3), none, a')
      else windowEncode c j) := rfl

/-- For a stationary move, only the head cell changes, receiving marker two, the new state, and
the written symbol. -/
private theorem afterReg_stay (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (q' : Q) (a' : A) (j : Fin (2 * t + 1)) :
    afterReg t c h1 h2 QtmMove.stay q' a' j =
      (if j = c.head then (2, some q', a') else windowEncode c j) := rfl

/-- For a right move, the old head receives the written symbol and the right neighbor receives
the new head state. -/
private theorem afterReg_right (t : ℕ) (c : WindowCfg t Q A)
    (h1 : 0 < c.head.val) (h2 : c.head.val < 2 * t) (q' : Q) (a' : A)
    (j : Fin (2 * t + 1)) :
    afterReg t c h1 h2 QtmMove.right q' a' j =
      (if j = c.head then ((0 : Fin 3), none, a')
      else if j = winR c h2 then (2, some q', c.tape j)
      else windowEncode c j) := rfl

/-- A transition leaves cells outside the old head and its two neighbors unchanged. -/
private theorem afterReg_of_ne (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (d : QtmMove) (q' : Q) (a' : A) (j : Fin (2 * t + 1))
    (hL : j ≠ winL c h1) (hH : j ≠ c.head) (hR : j ≠ winR c h2) :
    afterReg t c h1 h2 d q' a' j = windowEncode c j := by
  cases d
  · rw [afterReg_left, if_neg hL, if_neg hH]
  · rw [afterReg_stay, if_neg hH]
  · rw [afterReg_right, if_neg hH, if_neg hR]

/-- After a transition, cells outside the old head and its two neighbors have marker zero. -/
private theorem afterReg_marker_zero (t : ℕ) (c : WindowCfg t Q A)
    (h1 : 0 < c.head.val) (h2 : c.head.val < 2 * t) (d : QtmMove) (q' : Q) (a' : A)
    (j : Fin (2 * t + 1)) (hL : j ≠ winL c h1) (hH : j ≠ c.head) (hR : j ≠ winR c h2) :
    (afterReg t c h1 h2 d q' a' j).1 = 0 := by
  rw [afterReg_of_ne t c h1 h2 d q' a' j hL hH hR, windowEncode_marker_zero t c hH]

/-- A transition register agrees with the original encoding outside the triggering window. -/
private theorem offEq_after_trig (t : ℕ) (c : WindowCfg t Q A)
    (h1 : 0 < c.head.val) (h2 : c.head.val < 2 * t) (d : QtmMove) (q' : Q) (a' : A) :
    offEq t (trigK c h2) (afterReg t c h1 h2 d q' a') (windowEncode c) := by
  intro j hj
  have hL : j ≠ winL c h1 := fun he =>
    hj 0 (by rw [gUnitCells_trigK t c h1 h2]; simp [he])
  have hH : j ≠ c.head := fun he =>
    hj 1 (by rw [gUnitCells_trigK t c h1 h2]; simp [he])
  have hR : j ≠ winR c h2 := fun he =>
    hj 2 (by rw [gUnitCells_trigK t c h1 h2]; simp [he])
  rw [afterReg_of_ne t c h1 h2 d q' a' j hL hH hR]

/-- The triggering projection of an encoded configuration has its head in the central cell and
unmarked neighbors. -/
private theorem winProj_trig_enc (t : ℕ) (c : WindowCfg t Q A)
    (h1 : 0 < c.head.val) (h2 : c.head.val < 2 * t) :
    winProj t (trigK c h2) (windowEncode c)
      = ![((0 : Fin 3), none, c.tape (winL c h1)), (1, some c.state, c.tape c.head),
          ((0 : Fin 3), none, c.tape (winR c h2))] := by
  funext q
  simp only [winProj, gUnitCells_trigK t c h1 h2]
  fin_cases q <;> simp [windowEncode, winL_ne_head c h1, winR_ne_head c h2]

/-- Compute the triggering window after a left move, with marker two in its leftmost cell. -/
private theorem winProj_trig_afterL (t : ℕ) (c : WindowCfg t Q A)
    (h1 : 0 < c.head.val) (h2 : c.head.val < 2 * t) (q' : Q) (a' : A) :
    winProj t (trigK c h2) (afterReg t c h1 h2 QtmMove.left q' a')
      = ![(2, some q', c.tape (winL c h1)), ((0 : Fin 3), none, a'),
          ((0 : Fin 3), none, c.tape (winR c h2))] := by
  funext q
  simp only [winProj, gUnitCells_trigK t c h1 h2]
  fin_cases q <;>
    simp [afterReg_left, windowEncode, (winL_ne_head c h1).symm, winR_ne_winL c h1 h2,
      winR_ne_head c h2]

/-- Compute the triggering window after a stationary move, with marker two in its central cell. -/
private theorem winProj_trig_afterS (t : ℕ) (c : WindowCfg t Q A)
    (h1 : 0 < c.head.val) (h2 : c.head.val < 2 * t) (q' : Q) (a' : A) :
    winProj t (trigK c h2) (afterReg t c h1 h2 QtmMove.stay q' a')
      = ![((0 : Fin 3), none, c.tape (winL c h1)), (2, some q', a'),
          ((0 : Fin 3), none, c.tape (winR c h2))] := by
  funext q
  simp only [winProj, gUnitCells_trigK t c h1 h2]
  fin_cases q <;>
    simp [afterReg_stay, windowEncode, winL_ne_head c h1, winR_ne_head c h2]

/-- Compute the triggering window after a right move, with marker two in its rightmost cell. -/
private theorem winProj_trig_afterR (t : ℕ) (c : WindowCfg t Q A)
    (h1 : 0 < c.head.val) (h2 : c.head.val < 2 * t) (q' : Q) (a' : A) :
    winProj t (trigK c h2) (afterReg t c h1 h2 QtmMove.right q' a')
      = ![((0 : Fin 3), none, c.tape (winL c h1)), ((0 : Fin 3), none, a'),
          (2, some q', c.tape (winR c h2))] := by
  funext q
  simp only [winProj, gUnitCells_trigK t c h1 h2]
  fin_cases q <;>
    simp [afterReg_right, windowEncode, winL_ne_head c h1, winR_ne_head c h2,
      winL_ne_winR c h1 h2]

/-- On registers agreeing with the original encoding outside the triggering window, a transition
ket evaluates through its local projection. -/
private theorem ket_after_trig (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (d : QtmMove) (q' : Q) (a' : A) (x : WReg t Q A)
    (hx : offEq t (trigK c h2) x (windowEncode c)) :
    Qatlib.Foundations.PureStateMath.Ket (afterReg t c h1 h2 d q' a') x
      = Qatlib.Foundations.PureStateMath.Ket (winProj t (trigK c h2) (afterReg t c h1 h2 d q' a'))
          (winProj t (trigK c h2) x) := by
  have hoff := offEq_after_trig t c h1 h2 d q' a'
  rw [ket_apply, ket_apply]
  by_cases hxa : x = afterReg t c h1 h2 d q' a'
  · rw [if_pos hxa, if_pos (by rw [hxa])]
  · rw [if_neg hxa, if_neg]
    intro hp
    exact hxa (eq_of_offEq_winProj (offEq_trans hx (offEq_symm hoff)) hp)

/-- The transition amplitude from the configuration's current state and scanned symbol to a
prescribed direction, state, and write symbol. -/
private def sweepAmp {t : ℕ} (M : LocalQTM Q A) (c : WindowCfg t Q A) (d : QtmMove) (q' : Q)
    (a' : A) : ℂ := M.step c.state (c.tape c.head) d q' a'

/-- The superposition of transition registers weighted by the machine's transition amplitudes,
before the final marker swap. -/
private def sweepState (t : ℕ) (M : LocalQTM Q A) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) : QState (WReg t Q A) :=
  ∑ d : QtmMove, ∑ q' : Q, ∑ a' : A,
    sweepAmp M c d q' a' • Qatlib.Foundations.PureStateMath.Ket (afterReg t c h1 h2 d q' a')

/-- The contribution to `sweepState` from transitions in a fixed head direction. -/
private def dirState (t : ℕ) (M : LocalQTM Q A) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (d : QtmMove) : QState (WReg t Q A) :=
  ∑ q' : Q, ∑ a' : A, sweepAmp M c d q' a' • Qatlib.Foundations.PureStateMath.Ket (afterReg t c h1 h2 d q' a')

/-- The sweep state is the sum of its left, stationary, and right directional contributions. -/
private theorem sweepState_eq_dirs (t : ℕ) (M : LocalQTM Q A) (c : WindowCfg t Q A)
    (h1 : 0 < c.head.val) (h2 : c.head.val < 2 * t) :
    sweepState t M c h1 h2
      = dirState t M c h1 h2 QtmMove.left
        + (dirState t M c h1 h2 QtmMove.stay + dirState t M c h1 h2 QtmMove.right) := by
  simp only [sweepState, sum_qtmMove, dirState]
  exact add_assoc _ _ _

/-- Evaluate a directional sweep state as the sum of transition amplitudes times the
corresponding register kets. -/
private theorem dirState_apply (t : ℕ) (M : LocalQTM Q A) (c : WindowCfg t Q A)
    (h1 : 0 < c.head.val) (h2 : c.head.val < 2 * t) (d : QtmMove) (x : WReg t Q A) :
    dirState t M c h1 h2 d x
      = ∑ q' : Q, ∑ a' : A,
          M.step c.state (c.tape c.head) d q' a' * Qatlib.Foundations.PureStateMath.Ket (afterReg t c h1 h2 d q' a') x := by
  simp [dirState, Finset.sum_apply, sweepAmp]

/-- Evaluate the sweep state by summing register ket amplitudes over directions, new states, and
write symbols. -/
private theorem sweepState_apply (t : ℕ) (M : LocalQTM Q A) (c : WindowCfg t Q A)
    (h1 : 0 < c.head.val) (h2 : c.head.val < 2 * t) (x : WReg t Q A) :
    sweepState t M c h1 h2 x = ∑ d : QtmMove, ∑ q' : Q, ∑ a' : A,
      M.step c.state (c.tape c.head) d q' a' * Qatlib.Foundations.PureStateMath.Ket (afterReg t c h1 h2 d q' a') x := by
  simp [sweepState, Finset.sum_apply, sweepAmp]

/-- A gate satisfying `GUnitSteps` transforms the encoded configuration ket into its transition
sweep state at the triggering window. -/
private theorem gUnitFull_trig (t : ℕ) (M : LocalQTM Q A) (G : Matrix (GWindow Q A)
    (GWindow Q A) ℂ) (hstep : GUnitSteps M G) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) :
    gUnitFull G (trigK c h2) *ᵥ Qatlib.Foundations.PureStateMath.Ket (windowEncode c) = sweepState t M c h1 h2 := by
  have hket : Qatlib.Foundations.PureStateMath.Ket (windowEncode c)
      = liftWin t (trigK c h2) (windowEncode c)
          (Qatlib.Foundations.PureStateMath.Ket (winProj t (trigK c h2) (windowEncode c))) :=
    ket_eq_liftWin' t _ _ _ _ rfl (offEq_refl _ _ _)
  rw [hket, gUnitFull_mulVec_liftWin]
  have hhead : Qatlib.Foundations.PureStateMath.Ket (winProj t (trigK c h2) (windowEncode c))
      = headBasis c.state (c.tape c.head) (c.tape (winL c h1)) (c.tape (winR c h2)) := by
    rw [winProj_trig_enc, headBasis_eq_ket]
  rw [hhead, hstep c.state (c.tape c.head) (c.tape (winL c h1)) (c.tape (winR c h2))]
  funext x
  by_cases hx : offEq t (trigK c h2) x (windowEncode c)
  · have hconv : ∀ d : QtmMove, (∑ q' : Q, ∑ a' : A,
          M.step c.state (c.tape c.head) d q' a' * Qatlib.Foundations.PureStateMath.Ket (afterReg t c h1 h2 d q' a') x)
        = ∑ q' : Q, ∑ a' : A, M.step c.state (c.tape c.head) d q' a'
          * Qatlib.Foundations.PureStateMath.Ket (winProj t (trigK c h2) (afterReg t c h1 h2 d q' a'))
              (winProj t (trigK c h2) x) := by
      intro d
      exact Finset.sum_congr rfl fun q' _ => Finset.sum_congr rfl fun a' _ => by
        rw [ket_after_trig t c h1 h2 d q' a' x hx]
    simp only [liftWin, if_pos hx, sweepState_apply, hconv, sum_qtmMove,
      winProj_trig_afterL, winProj_trig_afterS, winProj_trig_afterR,
      stepSuperposition_apply]
  · have hzero : ∀ d : QtmMove, ∀ q' : Q, ∀ a' : A,
        (M.step c.state (c.tape c.head) d q' a' * Qatlib.Foundations.PureStateMath.Ket (afterReg t c h1 h2 d q' a') x) = 0 := by
      intro d q' a'
      have hxa : ¬ (x = afterReg t c h1 h2 d q' a') := fun he =>
        hx (by rw [he]; exact offEq_after_trig t c h1 h2 d q' a')
      rw [ket_apply, if_neg hxa, mul_zero]
    simp only [liftWin, if_neg hx, sweepState_apply, hzero, Finset.sum_const_zero]

/-- The cell two positions to the right of the head, under the stated boundary bound. -/
private def winRR {t : ℕ} {Q A : Type} (c : WindowCfg t Q A) (h3 : c.head.val < 2 * t - 1) :
    Fin (2 * t + 1) := ⟨c.head.val + 2, by have := h3; omega⟩

/-- The second right neighbor has index `c.head.val + 2`. -/
private theorem winRR_val {t : ℕ} {Q A : Type} (c : WindowCfg t Q A)
    (h3 : c.head.val < 2 * t - 1) : (winRR c h3).val = c.head.val + 2 := rfl

/-- The cell three positions to the right of the head, under the stated boundary bound. -/
private def winRRR {t : ℕ} {Q A : Type} (c : WindowCfg t Q A) (h4 : c.head.val < 2 * t - 2) :
    Fin (2 * t + 1) := ⟨c.head.val + 3, by have := h4; omega⟩

/-- The third right neighbor has index `c.head.val + 3`. -/
private theorem winRRR_val {t : ℕ} {Q A : Type} (c : WindowCfg t Q A)
    (h4 : c.head.val < 2 * t - 2) : (winRRR c h4).val = c.head.val + 3 := rfl

/-- The second right neighbor is distinct from the head. -/
private theorem winRR_ne_head {t : ℕ} {Q A : Type} (c : WindowCfg t Q A)
    (h3 : c.head.val < 2 * t - 1) : winRR c h3 ≠ c.head := by
  intro he
  have hv := congrArg Fin.val he
  rw [winRR_val] at hv
  omega

/-- The second right neighbor is distinct from the first right neighbor. -/
private theorem winRR_ne_winR {t : ℕ} {Q A : Type} (c : WindowCfg t Q A)
    (h2 : c.head.val < 2 * t) (h3 : c.head.val < 2 * t - 1) : winRR c h3 ≠ winR c h2 := by
  intro he
  have hv := congrArg Fin.val he
  rw [winRR_val, winR_val] at hv
  omega

/-- The second right neighbor is distinct from the left neighbor. -/
private theorem winRR_ne_winL {t : ℕ} {Q A : Type} (c : WindowCfg t Q A)
    (h1 : 0 < c.head.val) (h3 : c.head.val < 2 * t - 1) : winRR c h3 ≠ winL c h1 := by
  intro he
  have hv := congrArg Fin.val he
  rw [winRR_val, winL_val] at hv
  omega

/-- The third right neighbor is distinct from the head. -/
private theorem winRRR_ne_head {t : ℕ} {Q A : Type} (c : WindowCfg t Q A)
    (h4 : c.head.val < 2 * t - 2) : winRRR c h4 ≠ c.head := by
  intro he
  have hv := congrArg Fin.val he
  rw [winRRR_val] at hv
  omega

/-- The third right neighbor is distinct from the first right neighbor. -/
private theorem winRRR_ne_winR {t : ℕ} {Q A : Type} (c : WindowCfg t Q A)
    (h2 : c.head.val < 2 * t) (h4 : c.head.val < 2 * t - 2) : winRRR c h4 ≠ winR c h2 := by
  intro he
  have hv := congrArg Fin.val he
  rw [winRRR_val, winR_val] at hv
  omega

/-- The third right neighbor is distinct from the left neighbor. -/
private theorem winRRR_ne_winL {t : ℕ} {Q A : Type} (c : WindowCfg t Q A)
    (h1 : 0 < c.head.val) (h4 : c.head.val < 2 * t - 2) : winRRR c h4 ≠ winL c h1 := by
  intro he
  have hv := congrArg Fin.val he
  rw [winRRR_val, winL_val] at hv
  omega

/-- A window starting at the head consists of the head and its first two right neighbors. -/
private theorem gUnitCells_head (t : ℕ) (c : WindowCfg t Q A) (h2 : c.head.val < 2 * t)
    (h3 : c.head.val < 2 * t - 1) {k : Fin (2 * t - 1)} (hk : k.val = c.head.val) :
    gUnitCells t k = ![c.head, winR c h2, winRR c h3] := by
  have hv : ∀ q : Fin 3, (gUnitCells t k q).val = (![c.head, winR c h2, winRR c h3] q).val := by
    intro q
    rw [gUnitCells_val]
    fin_cases q <;> simp [winR_val, winRR_val, hk]
  funext q
  exact Fin.ext (hv q)

/-- A window starting one cell right of the head consists of its first three right neighbors. -/
private theorem gUnitCells_headR (t : ℕ) (c : WindowCfg t Q A) (h2 : c.head.val < 2 * t)
    (h3 : c.head.val < 2 * t - 1) (h4 : c.head.val < 2 * t - 2)
    {k : Fin (2 * t - 1)} (hk : k.val = c.head.val + 1) :
    gUnitCells t k = ![winR c h2, winRR c h3, winRRR c h4] := by
  have hv : ∀ q : Fin 3, (gUnitCells t k q).val
      = (![winR c h2, winRR c h3, winRRR c h4] q).val := by
    intro q
    rw [gUnitCells_val]
    fin_cases q <;> simp [winR_val, winRR_val, winRRR_val, hk]
  funext q
  exact Fin.ext (hv q)

/-- After a left move, the window starting at the old head contains the written symbol followed
by two unmarked tape cells. -/
private theorem winProj_head_afterL (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (h3 : c.head.val < 2 * t - 1) (q' : Q) (a' : A)
    {k : Fin (2 * t - 1)} (hk : k.val = c.head.val) :
    winProj t k (afterReg t c h1 h2 QtmMove.left q' a')
      = ![((0 : Fin 3), none, a'), ((0 : Fin 3), none, c.tape (winR c h2)),
          ((0 : Fin 3), none, c.tape (winRR c h3))] := by
  funext q
  simp only [winProj, gUnitCells_head t c h2 h3 hk]
  fin_cases q <;>
    simp [afterReg_left, windowEncode, (winL_ne_head c h1).symm, winR_ne_head c h2,
      winR_ne_winL c h1 h2, winRR_ne_head c h3, winRR_ne_winL c h1 h3]

/-- After a stationary move, the window starting at the old head has the new marked head
followed by two unmarked tape cells. -/
private theorem winProj_head_afterS (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (h3 : c.head.val < 2 * t - 1) (q' : Q) (a' : A)
    {k : Fin (2 * t - 1)} (hk : k.val = c.head.val) :
    winProj t k (afterReg t c h1 h2 QtmMove.stay q' a')
      = ![(2, some q', a'), ((0 : Fin 3), none, c.tape (winR c h2)),
          ((0 : Fin 3), none, c.tape (winRR c h3))] := by
  funext q
  simp only [winProj, gUnitCells_head t c h2 h3 hk]
  fin_cases q <;>
    simp [afterReg_stay, windowEncode, winR_ne_head c h2, winRR_ne_head c h3]

/-- After a right move, the window starting at the old head contains the written symbol, the new
marked head, and an unmarked cell. -/
private theorem winProj_head_afterR (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (h3 : c.head.val < 2 * t - 1) (q' : Q) (a' : A)
    {k : Fin (2 * t - 1)} (hk : k.val = c.head.val) :
    winProj t k (afterReg t c h1 h2 QtmMove.right q' a')
      = ![((0 : Fin 3), none, a'), (2, some q', c.tape (winR c h2)),
          ((0 : Fin 3), none, c.tape (winRR c h3))] := by
  funext q
  simp only [winProj, gUnitCells_head t c h2 h3 hk]
  fin_cases q <;>
    simp [afterReg_right, windowEncode, winR_ne_head c h2, winRR_ne_head c h3,
      winRR_ne_winR c h2 h3]

/-- After a left move, the window starting right of the old head consists of three unchanged
unmarked tape cells. -/
private theorem winProj_headR_afterL (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (h3 : c.head.val < 2 * t - 1) (h4 : c.head.val < 2 * t - 2)
    (q' : Q) (a' : A) {k : Fin (2 * t - 1)} (hk : k.val = c.head.val + 1) :
    winProj t k (afterReg t c h1 h2 QtmMove.left q' a')
      = ![((0 : Fin 3), none, c.tape (winR c h2)), ((0 : Fin 3), none, c.tape (winRR c h3)),
          ((0 : Fin 3), none, c.tape (winRRR c h4))] := by
  funext q
  simp only [winProj, gUnitCells_headR t c h2 h3 h4 hk]
  fin_cases q <;>
    simp [afterReg_left, windowEncode, winR_ne_head c h2, winR_ne_winL c h1 h2,
      winRR_ne_head c h3, winRR_ne_winL c h1 h3, winRRR_ne_head c h4, winRRR_ne_winL c h1 h4]

/-- After a stationary move, the window starting right of the old head consists of three
unchanged unmarked tape cells. -/
private theorem winProj_headR_afterS (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (h3 : c.head.val < 2 * t - 1) (h4 : c.head.val < 2 * t - 2)
    (q' : Q) (a' : A) {k : Fin (2 * t - 1)} (hk : k.val = c.head.val + 1) :
    winProj t k (afterReg t c h1 h2 QtmMove.stay q' a')
      = ![((0 : Fin 3), none, c.tape (winR c h2)), ((0 : Fin 3), none, c.tape (winRR c h3)),
          ((0 : Fin 3), none, c.tape (winRRR c h4))] := by
  funext q
  simp only [winProj, gUnitCells_headR t c h2 h3 h4 hk]
  fin_cases q <;>
    simp [afterReg_stay, windowEncode, winR_ne_head c h2, winRR_ne_head c h3,
      winRRR_ne_head c h4]

/-- After a right move, the window starting right of the old head has the new marked head in its
first cell. -/
private theorem winProj_headR_afterR (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (h3 : c.head.val < 2 * t - 1) (h4 : c.head.val < 2 * t - 2)
    (q' : Q) (a' : A) {k : Fin (2 * t - 1)} (hk : k.val = c.head.val + 1) :
    winProj t k (afterReg t c h1 h2 QtmMove.right q' a')
      = ![(2, some q', c.tape (winR c h2)), ((0 : Fin 3), none, c.tape (winRR c h3)),
          ((0 : Fin 3), none, c.tape (winRRR c h4))] := by
  funext q
  simp only [winProj, gUnitCells_headR t c h2 h3 h4 hk]
  fin_cases q <;>
    simp [afterReg_right, windowEncode, winR_ne_head c h2, winRR_ne_head c h3,
      winRRR_ne_head c h4, winRR_ne_winR c h2 h3, winRRR_ne_winR c h2 h4]

/-- After a left move, the window starting at the old head is of type I. -/
private theorem isTypeI_head_afterL (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (h3 : c.head.val < 2 * t - 1) (q' : Q) (a' : A)
    {k : Fin (2 * t - 1)} (hk : k.val = c.head.val) :
    IsTypeI (winProj t k (afterReg t c h1 h2 QtmMove.left q' a')) := by
  rw [winProj_head_afterL t c h1 h2 h3 q' a' hk]
  exact ⟨by simp, by intro j; fin_cases j <;> simp⟩

/-- After a left move, the window starting right of the old head is of type I. -/
private theorem isTypeI_headR_afterL (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (h3 : c.head.val < 2 * t - 1) (h4 : c.head.val < 2 * t - 2)
    (q' : Q) (a' : A) {k : Fin (2 * t - 1)} (hk : k.val = c.head.val + 1) :
    IsTypeI (winProj t k (afterReg t c h1 h2 QtmMove.left q' a')) := by
  rw [winProj_headR_afterL t c h1 h2 h3 h4 q' a' hk]
  exact ⟨by simp, by intro j; fin_cases j <;> simp⟩

/-- After a stationary move, the window starting right of the old head is of type I. -/
private theorem isTypeI_headR_afterS (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (h3 : c.head.val < 2 * t - 1) (h4 : c.head.val < 2 * t - 2)
    (q' : Q) (a' : A) {k : Fin (2 * t - 1)} (hk : k.val = c.head.val + 1) :
    IsTypeI (winProj t k (afterReg t c h1 h2 QtmMove.stay q' a')) := by
  rw [winProj_headR_afterS t c h1 h2 h3 h4 q' a' hk]
  exact ⟨by simp, by intro j; fin_cases j <;> simp⟩

/-- If a transition register and a test register agree with a common register outside a window,
the transition ket evaluates through that window's projections. -/
private theorem ket_after_win (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (d : QtmMove) (q' : Q) (a' : A)
    {k : Fin (2 * t - 1)} {y : WReg t Q A} (x : WReg t Q A)
    (hoff : offEq t k (afterReg t c h1 h2 d q' a') y) (hx : offEq t k x y) :
    Qatlib.Foundations.PureStateMath.Ket (afterReg t c h1 h2 d q' a') x
      = Qatlib.Foundations.PureStateMath.Ket (winProj t k (afterReg t c h1 h2 d q' a')) (winProj t k x) := by
  rw [ket_apply, ket_apply]
  by_cases hxa : x = afterReg t c h1 h2 d q' a'
  · rw [if_pos hxa, if_pos (by rw [hxa])]
  · rw [if_neg hxa, if_neg]
    intro hp
    exact hxa (eq_of_offEq_winProj (offEq_trans hx (offEq_symm hoff)) hp)

/-- A stationary transition register agrees with the original encoding outside the window
starting at the old head. -/
private theorem offEq_head_afterS (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (h3 : c.head.val < 2 * t - 1) (q' : Q) (a' : A)
    {k : Fin (2 * t - 1)} (hk : k.val = c.head.val) :
    offEq t k (afterReg t c h1 h2 QtmMove.stay q' a') (windowEncode c) := by
  intro j hj
  rw [gUnitCells_head t c h2 h3 hk] at hj
  have hH : j ≠ c.head := fun he => hj 0 (by simp [he])
  rw [afterReg_stay t c h1 h2 q' a' j, if_neg hH]

/-- A right-moving transition register agrees with the original encoding outside the window
starting at the old head. -/
private theorem offEq_head_afterR (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (h3 : c.head.val < 2 * t - 1) (q' : Q) (a' : A)
    {k : Fin (2 * t - 1)} (hk : k.val = c.head.val) :
    offEq t k (afterReg t c h1 h2 QtmMove.right q' a') (windowEncode c) := by
  intro j hj
  rw [gUnitCells_head t c h2 h3 hk] at hj
  have hH : j ≠ c.head := fun he => hj 0 (by simp [he])
  have hR : j ≠ winR c h2 := fun he => hj 1 (by simp [he])
  rw [afterReg_right t c h1 h2 q' a' j, if_neg hH, if_neg hR]

/-- The original encoded register with its old head cell replaced by an unmarked cell carrying
`a''`. -/
private def offTplR (t : ℕ) (c : WindowCfg t Q A) (a'' : A) : WReg t Q A :=
  fun j => if j = c.head then ((0 : Fin 3), none, a'') else windowEncode c j

/-- A right-moving transition register agrees with `offTplR` outside the window starting right
of the old head. -/
private theorem offEq_headR_afterR (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (h3 : c.head.val < 2 * t - 1) (h4 : c.head.val < 2 * t - 2)
    (q' : Q) (a'' : A) {k : Fin (2 * t - 1)} (hk : k.val = c.head.val + 1) :
    offEq t k (afterReg t c h1 h2 QtmMove.right q' a'') (offTplR t c a'') := by
  intro j hj
  rw [gUnitCells_headR t c h2 h3 h4 hk] at hj
  have hR : j ≠ winR c h2 := fun he => hj 0 (by simp [he])
  by_cases hH : j = c.head
  · subst hH
    simp [afterReg_right, offTplR]
  · rw [afterReg_right t c h1 h2 q' a'' j, if_neg hH, if_neg hR]
    simp [offTplR, hH]

/-- The stationary and right-moving contributions combine into a lift of `vFamily` at the window
starting at the head. -/
private theorem vMerge (t : ℕ) (M : LocalQTM Q A) (c : WindowCfg t Q A)
    (h1 : 0 < c.head.val) (h2 : c.head.val < 2 * t) (h3 : c.head.val < 2 * t - 1)
    {k : Fin (2 * t - 1)} (hk : k.val = c.head.val) :
    dirState t M c h1 h2 QtmMove.stay + dirState t M c h1 h2 QtmMove.right
      = liftWin t k (windowEncode c)
          (vFamily M c.state (c.tape c.head) (c.tape (winR c h2)) (c.tape (winRR c h3))) := by
  funext x
  by_cases hx : offEq t k x (windowEncode c)
  · have convS : ∀ q' : Q, ∀ a' : A,
        M.step c.state (c.tape c.head) QtmMove.stay q' a'
          * Qatlib.Foundations.PureStateMath.Ket (afterReg t c h1 h2 QtmMove.stay q' a') x
        = M.step c.state (c.tape c.head) QtmMove.stay q' a'
          * Qatlib.Foundations.PureStateMath.Ket ![(2, some q', a'), ((0 : Fin 3), none, c.tape (winR c h2)),
              ((0 : Fin 3), none, c.tape (winRR c h3))] (winProj t k x) := by
      intro q' a'
      rw [ket_after_win t c h1 h2 QtmMove.stay q' a' x
          (offEq_head_afterS t c h1 h2 h3 q' a' hk) hx, winProj_head_afterS t c h1 h2 h3 q' a' hk]
    have convR : ∀ q' : Q, ∀ a' : A,
        M.step c.state (c.tape c.head) QtmMove.right q' a'
          * Qatlib.Foundations.PureStateMath.Ket (afterReg t c h1 h2 QtmMove.right q' a') x
        = M.step c.state (c.tape c.head) QtmMove.right q' a'
          * Qatlib.Foundations.PureStateMath.Ket ![((0 : Fin 3), none, a'), (2, some q', c.tape (winR c h2)),
              ((0 : Fin 3), none, c.tape (winRR c h3))] (winProj t k x) := by
      intro q' a'
      rw [ket_after_win t c h1 h2 QtmMove.right q' a' x
          (offEq_head_afterR t c h1 h2 h3 q' a' hk) hx, winProj_head_afterR t c h1 h2 h3 q' a' hk]
    simp only [Pi.add_apply, dirState_apply, liftWin, if_pos hx, vFamily_apply]
    rw [Finset.sum_congr rfl (fun q' _ => Finset.sum_congr rfl (fun a' _ => convS q' a')),
      Finset.sum_congr rfl (fun q' _ => Finset.sum_congr rfl (fun a' _ => convR q' a'))]
  · have hzeroS : ∀ q' : Q, ∀ a' : A,
        (M.step c.state (c.tape c.head) QtmMove.stay q' a'
          * Qatlib.Foundations.PureStateMath.Ket (afterReg t c h1 h2 QtmMove.stay q' a') x) = 0 := by
      intro q' a'
      have hxa : ¬ (x = afterReg t c h1 h2 QtmMove.stay q' a') := by
        intro he
        have hx' := hx
        rw [he] at hx'
        exact hx' (offEq_head_afterS t c h1 h2 h3 q' a' hk)
      rw [ket_apply, if_neg hxa, mul_zero]
    have hzeroR : ∀ q' : Q, ∀ a' : A,
        (M.step c.state (c.tape c.head) QtmMove.right q' a'
          * Qatlib.Foundations.PureStateMath.Ket (afterReg t c h1 h2 QtmMove.right q' a') x) = 0 := by
      intro q' a'
      have hxa : ¬ (x = afterReg t c h1 h2 QtmMove.right q' a') := by
        intro he
        have hx' := hx
        rw [he] at hx'
        exact hx' (offEq_head_afterR t c h1 h2 h3 q' a' hk)
      rw [ket_apply, if_neg hxa, mul_zero]
    simp only [Pi.add_apply, dirState_apply, liftWin, if_neg hx, hzeroS, hzeroR,
      Finset.sum_const_zero, add_zero]

/-- The right-moving contribution is a sum over write symbols of lifted `uFamily` states at the
window starting right of the head. -/
private theorem uMerge (t : ℕ) (M : LocalQTM Q A) (c : WindowCfg t Q A)
    (h1 : 0 < c.head.val) (h2 : c.head.val < 2 * t) (h3 : c.head.val < 2 * t - 1)
    (h4 : c.head.val < 2 * t - 2) {k : Fin (2 * t - 1)} (hk : k.val = c.head.val + 1) :
    dirState t M c h1 h2 QtmMove.right
      = ∑ a'' : A, liftWin t k (offTplR t c a'')
          (uFamily M c.state (c.tape c.head) a'' (c.tape (winR c h2))
            (c.tape (winRR c h3)) (c.tape (winRRR c h4))) := by
  funext x
  rw [dirState_apply]
  have key : ∀ a'' : A,
      (∑ q' : Q, M.step c.state (c.tape c.head) QtmMove.right q' a''
        * Qatlib.Foundations.PureStateMath.Ket (afterReg t c h1 h2 QtmMove.right q' a'') x)
      = liftWin t k (offTplR t c a'')
          (uFamily M c.state (c.tape c.head) a'' (c.tape (winR c h2))
            (c.tape (winRR c h3)) (c.tape (winRRR c h4))) x := by
    intro a''
    by_cases hx : offEq t k x (offTplR t c a'')
    · simp only [liftWin, if_pos hx, uFamily_apply]
      exact Finset.sum_congr rfl fun q' _ => by
        rw [ket_after_win t c h1 h2 QtmMove.right q' a'' x
            (offEq_headR_afterR t c h1 h2 h3 h4 q' a'' hk) hx,
          winProj_headR_afterR t c h1 h2 h3 h4 q' a'' hk]
    · have hzero : ∀ q' : Q,
          (M.step c.state (c.tape c.head) QtmMove.right q' a''
            * Qatlib.Foundations.PureStateMath.Ket (afterReg t c h1 h2 QtmMove.right q' a'') x) = 0 := by
        intro q'
        have hxa : ¬ (x = afterReg t c h1 h2 QtmMove.right q' a'') := by
          intro he
          have hx' := hx
          rw [he] at hx'
          exact hx' (offEq_headR_afterR t c h1 h2 h3 h4 q' a'' hk)
        rw [ket_apply, if_neg hxa, mul_zero]
      simp only [liftWin, if_neg hx]
      rw [Finset.sum_congr rfl fun q' _ => hzero q', Finset.sum_const_zero]
  rw [Finset.sum_comm, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a'' _ => key a''

/-- Every cell at least two positions right of the old head is unchanged by a transition. -/
private theorem afterReg_of_gt (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (d : QtmMove) (q' : Q) (a' : A) {j : Fin (2 * t + 1)}
    (hj : c.head.val + 2 ≤ j.val) : afterReg t c h1 h2 d q' a' j = windowEncode c j := by
  refine afterReg_of_ne t c h1 h2 d q' a' j ?_ ?_ ?_
  · intro he
    have hv := congrArg Fin.val he
    rw [winL_val] at hv
    omega
  · intro he
    have hv := congrArg Fin.val he
    omega
  · intro he
    have hv := congrArg Fin.val he
    rw [winR_val] at hv
    omega

/-- After a transition, every window starting at least two positions right of the old head is of
type I. -/
private theorem isTypeI_after_ge (t : ℕ) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) (d : QtmMove) (q' : Q) (a' : A)
    {k : Fin (2 * t - 1)} (hk : c.head.val + 2 ≤ k.val) :
    IsTypeI (winProj t k (afterReg t c h1 h2 d q' a')) := by
  have hcell : ∀ q : Fin 3, c.head.val + 2 ≤ (gUnitCells t k q).val := by
    intro q
    rw [gUnitCells_val]
    omega
  have hne : ∀ q : Fin 3, gUnitCells t k q ≠ c.head := by
    intro q he
    have hv := congrArg Fin.val he
    rw [gUnitCells_val] at hv
    omega
  refine ⟨?_, ?_⟩
  · show (afterReg t c h1 h2 d q' a' (gUnitCells t k 1)).1 ≠ 1
    have h0 := afterReg_of_gt t c h1 h2 d q' a' (hcell 1)
    rw [h0, windowEncode_marker_zero t c (hne 1)]
    decide
  · intro q
    show (afterReg t c h1 h2 d q' a' (gUnitCells t k q)).1 ≠ 2
    have h0 := afterReg_of_gt t c h1 h2 d q' a' (hcell q)
    rw [h0, windowEncode_marker_zero t c (hne q)]
    decide

/-- A matrix fixing each ket in a family also fixes every finite weighted sum of those kets
indexed by states and symbols. -/
private theorem mulVec_ketSum2_fix {t : ℕ} {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] {U : Matrix (WReg t Q A) (WReg t Q A) ℂ}
    (f : Q → A → ℂ) (v : Q → A → WReg t Q A)
    (h : ∀ q' : Q, ∀ a' : A, U *ᵥ Qatlib.Foundations.PureStateMath.Ket (v q' a') = Qatlib.Foundations.PureStateMath.Ket (v q' a')) :
    U *ᵥ (∑ q' : Q, ∑ a' : A, f q' a' • Qatlib.Foundations.PureStateMath.Ket (v q' a'))
      = ∑ q' : Q, ∑ a' : A, f q' a' • Qatlib.Foundations.PureStateMath.Ket (v q' a') := by
  rw [mulVec_sum]
  refine Finset.sum_congr rfl fun q' _ => ?_
  rw [mulVec_sum]
  exact Finset.sum_congr rfl fun a' _ => by rw [Matrix.mulVec_smul, h q' a']

/-- A gate satisfying `GUnitFixesH` fixes the sweep state at every window starting at or right
of the old head. -/
private theorem gUnitFull_fix_sweepState (t : ℕ) (M : LocalQTM Q A)
    (G : Matrix (GWindow Q A) (GWindow Q A) ℂ) (hfix : GUnitFixesH M G)
    (c : WindowCfg t Q A) (h1 : 0 < c.head.val) (h2 : c.head.val < 2 * t)
    {k : Fin (2 * t - 1)} (hk : c.head.val ≤ k.val) :
    gUnitFull G k *ᵥ sweepState t M c h1 h2 = sweepState t M c h1 h2 := by
  have hklt := k.isLt
  rw [sweepState_eq_dirs]
  rcases Nat.lt_or_ge k.val (c.head.val + 1) with hk1 | hk1
  · have hk' : k.val = c.head.val := Nat.le_antisymm (by omega) hk
    have h3 : c.head.val < 2 * t - 1 := by omega
    have eL : gUnitFull G k *ᵥ dirState t M c h1 h2 QtmMove.left
        = dirState t M c h1 h2 QtmMove.left := by
      simp only [dirState]
      exact mulVec_ketSum2_fix _ _ fun q' a' =>
        gUnitFull_mulVec_ket_fix t hfix k _ (isTypeI_head_afterL t c h1 h2 h3 q' a' hk')
    have eSR : gUnitFull G k *ᵥ (dirState t M c h1 h2 QtmMove.stay
        + dirState t M c h1 h2 QtmMove.right)
        = dirState t M c h1 h2 QtmMove.stay + dirState t M c h1 h2 QtmMove.right := by
      rw [vMerge t M c h1 h2 h3 hk', gUnitFull_mulVec_liftWin, hfix.2.1]
    rw [Matrix.mulVec_add, eL, eSR]
  rcases Nat.lt_or_ge k.val (c.head.val + 2) with hk2 | hk2
  · have hk' : k.val = c.head.val + 1 := Nat.le_antisymm (by omega) (by omega)
    have h3 : c.head.val < 2 * t - 1 := by omega
    have h4 : c.head.val < 2 * t - 2 := by omega
    have eL : gUnitFull G k *ᵥ dirState t M c h1 h2 QtmMove.left
        = dirState t M c h1 h2 QtmMove.left := by
      simp only [dirState]
      exact mulVec_ketSum2_fix _ _ fun q' a' =>
        gUnitFull_mulVec_ket_fix t hfix k _ (isTypeI_headR_afterL t c h1 h2 h3 h4 q' a' hk')
    have eS : gUnitFull G k *ᵥ dirState t M c h1 h2 QtmMove.stay
        = dirState t M c h1 h2 QtmMove.stay := by
      simp only [dirState]
      exact mulVec_ketSum2_fix _ _ fun q' a' =>
        gUnitFull_mulVec_ket_fix t hfix k _ (isTypeI_headR_afterS t c h1 h2 h3 h4 q' a' hk')
    have eR : gUnitFull G k *ᵥ dirState t M c h1 h2 QtmMove.right
        = dirState t M c h1 h2 QtmMove.right := by
      rw [uMerge t M c h1 h2 h3 h4 hk', mulVec_sum]
      refine Finset.sum_congr rfl fun a'' _ => ?_
      rw [gUnitFull_mulVec_liftWin, hfix.2.2]
    rw [Matrix.mulVec_add, eL, Matrix.mulVec_add, eS, eR]
  · have eL : gUnitFull G k *ᵥ dirState t M c h1 h2 QtmMove.left
        = dirState t M c h1 h2 QtmMove.left := by
      simp only [dirState]
      exact mulVec_ketSum2_fix _ _ fun q' a' =>
        gUnitFull_mulVec_ket_fix t hfix k _
          (isTypeI_after_ge t c h1 h2 QtmMove.left q' a' hk2)
    have eS : gUnitFull G k *ᵥ dirState t M c h1 h2 QtmMove.stay
        = dirState t M c h1 h2 QtmMove.stay := by
      simp only [dirState]
      exact mulVec_ketSum2_fix _ _ fun q' a' =>
        gUnitFull_mulVec_ket_fix t hfix k _
          (isTypeI_after_ge t c h1 h2 QtmMove.stay q' a' hk2)
    have eR : gUnitFull G k *ᵥ dirState t M c h1 h2 QtmMove.right
        = dirState t M c h1 h2 QtmMove.right := by
      simp only [dirState]
      exact mulVec_ketSum2_fix _ _ fun q' a' =>
        gUnitFull_mulVec_ket_fix t hfix k _
          (isTypeI_after_ge t c h1 h2 QtmMove.right q' a' hk2)
    rw [Matrix.mulVec_add, eL, Matrix.mulVec_add, eS, eR]

/-- An encoded configuration has a type I window whenever the head is not its central cell. -/
private theorem isTypeI_enc (t : ℕ) (c : WindowCfg t Q A) {k : Fin (2 * t - 1)}
    (hk : k.val + 1 ≠ c.head.val) : IsTypeI (winProj t k (windowEncode c)) := by
  refine ⟨?_, ?_⟩
  · intro hm
    simp only [winProj] at hm
    by_cases hc : gUnitCells t k 1 = c.head
    · exact hk (by have hv := congrArg Fin.val hc; rw [gUnitCells_val] at hv; omega)
    · rw [windowEncode_marker_zero t c hc] at hm
      simp at hm
  · intro q
    simp only [winProj]
    by_cases hc : gUnitCells t k q = c.head
    · have h1' : (windowEncode c (gUnitCells t k q)).1 = 1 := by
        simp only [windowEncode, if_pos hc]
      rw [h1']
      decide
    · have h0 := windowEncode_marker_zero t c hc
      rw [h0]
      decide

/-- The circuit consisting of the first `m` lifted three-cell gates in the sweep. -/
private def unitList {t : ℕ} (G : Matrix (GWindow Q A) (GWindow Q A) ℂ)
    {m : ℕ} (hm : m ≤ 2 * t - 1) : Circuit (WReg t Q A) :=
  (List.finRange m).map fun i => Step.gate (gUnitFull G (Fin.castLE hm i))

/-- A sweep prefix produces the transition superposition once it has passed the triggering
window and otherwise leaves the encoded configuration ket unchanged. -/
private theorem sweep_run_prefix {t : ℕ} (M : LocalQTM Q A)
    (G : Matrix (GWindow Q A) (GWindow Q A) ℂ) (hfix : GUnitFixesH M G)
    (hstep : GUnitSteps M G) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) {m : ℕ} (hm : m ≤ 2 * t - 1) :
    Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) (unitList G hm) (Qatlib.Foundations.PureStateMath.Ket (windowEncode c))
      = if c.head.val ≤ m then sweepState t M c h1 h2 else Qatlib.Foundations.PureStateMath.Ket (windowEncode c) := by
  induction m with
  | zero =>
      simp only [unitList, List.finRange_zero, List.map_nil, run_nil]
      rw [if_neg (by omega)]
  | succ m ih =>
      have h0 : m ≤ 2 * t - 1 := Nat.le_of_succ_le hm
      have hsucc : unitList G hm
          = unitList G h0 ++ [Step.gate (gUnitFull G (Fin.castLE hm (Fin.last m)))] := by
        simp only [unitList, List.finRange_succ_last, List.map_append, List.map_map,
          List.map_cons, List.map_nil]
        congr 1
      have kval : (Fin.castLE hm (Fin.last m)).val = m := by simp
      rw [hsucc, run_snoc, ih h0]
      by_cases hcase : c.head.val ≤ m
      · rw [if_pos hcase, if_pos (by omega)]
        exact gUnitFull_fix_sweepState t M G hfix c h1 h2 (by rw [kval]; exact hcase)
      · rw [if_neg hcase]
        rcases Nat.lt_or_ge (m + 1) c.head.val with hlt | hge
        · rw [if_neg (by omega)]
          exact gUnitFull_mulVec_ket_fix t hfix _ _
            (isTypeI_enc t c (by rw [kval]; omega))
        · rw [if_pos (by omega)]
          have hk : Fin.castLE hm (Fin.last m) = trigK c h2 := by
            apply Fin.ext
            rw [kval, trigK_val]
            omega
          rw [hk, gUnitFull_trig t M G hstep c h1 h2]

/-- Swapping markers one and two twice restores the original cell state. -/
private theorem markSwap_involutive {Q A : Type} [DecidableEq Q] [DecidableEq A] :
    Function.Involutive (markSwap (Q := Q) (A := A)) := by
  intro r
  obtain ⟨m, s⟩ := r
  fin_cases m <;> simp [markSwap]

/-- The full marker-swap matrix sends a register ket to the ket obtained by swapping markers in
every cell. -/
private theorem iSwapFull_ket {t : ℕ} {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (y : WReg t Q A) :
    iSwapFull t *ᵥ Qatlib.Foundations.PureStateMath.Ket y = Qatlib.Foundations.PureStateMath.Ket (fun j => markSwap (y j)) := by
  have hi : Function.Involutive
      (fun (r : WReg t Q A) => fun j => markSwap (r j)) := by
    intro r
    funext j
    exact markSwap_involutive (r j)
  exact applyGate_permMatrix_ket hi y

/-- The configuration obtained by moving the head in the specified direction, changing its
internal state, and writing at the old head. -/
private def cfgAfter {t : ℕ} {Q A : Type} (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) : QtmMove → Q → A → WindowCfg t Q A :=
  fun d q' a' =>
    match d with
    | QtmMove.left => ⟨winL c h1, q', fun j => if j = c.head then a' else c.tape j⟩
    | QtmMove.stay => ⟨c.head, q', fun j => if j = c.head then a' else c.tape j⟩
    | QtmMove.right => ⟨winR c h2, q', fun j => if j = c.head then a' else c.tape j⟩

/-- A left move from a positive head index returns the left neighbor. -/
private theorem moveCell_left {t : ℕ} {Q A : Type} (c : WindowCfg t Q A)
    (h1 : 0 < c.head.val) : moveCell QtmMove.left c.head = some (winL c h1) := by
  simp only [moveCell]
  rw [dif_neg (by omega)]
  rfl

/-- A stationary move returns the original head cell. -/
private theorem moveCell_stay {t : ℕ} {Q A : Type} (c : WindowCfg t Q A) :
    moveCell QtmMove.stay c.head = some c.head := rfl

/-- A right move below the right boundary returns the right neighbor. -/
private theorem moveCell_right {t : ℕ} {Q A : Type} (c : WindowCfg t Q A)
    (h2 : c.head.val < 2 * t) : moveCell QtmMove.right c.head = some (winR c h2) := by
  simp only [moveCell]
  rw [dif_neg (by omega)]
  rfl

/-- Swapping all markers in a transition register yields the encoding of the corresponding
updated configuration. -/
private theorem markSwap_after_eq_enc {t : ℕ} {Q A : Type} [DecidableEq Q] [DecidableEq A]
    (c : WindowCfg t Q A) (h1 : 0 < c.head.val) (h2 : c.head.val < 2 * t)
    (d : QtmMove) (q' : Q) (a' : A) :
    (fun j => markSwap (afterReg t c h1 h2 d q' a' j))
      = windowEncode (cfgAfter c h1 h2 d q' a') := by
  funext j
  cases d
  · by_cases hjL : j = winL c h1
    · subst hjL
      simp [afterReg_left, markSwap, windowEncode, cfgAfter, winL_ne_head c h1]
    · by_cases hjH : j = c.head
      · subst hjH
        simp [afterReg_left, markSwap, windowEncode, cfgAfter, (winL_ne_head c h1).symm]
      · simp [afterReg_left, markSwap, windowEncode, cfgAfter, hjL, hjH]
  · by_cases hjH : j = c.head
    · subst hjH
      simp [afterReg_stay, markSwap, windowEncode, cfgAfter]
    · simp [afterReg_stay, markSwap, windowEncode, cfgAfter, hjH]
  · by_cases hjH : j = c.head
    · subst hjH
      simp [afterReg_right, markSwap, windowEncode, cfgAfter, (winR_ne_head c h2).symm]
    · by_cases hjR : j = winR c h2
      · subst hjR
        simp [afterReg_right, markSwap, windowEncode, cfgAfter, winR_ne_head c h2]
      · simp [afterReg_right, markSwap, windowEncode, cfgAfter, hjH, hjR]

/-- A ket of an encoded configuration evaluates to one on the same configuration's encoding and
to zero on other encoded configurations. -/
private theorem ket_enc_eq {t : ℕ} {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (c₀ cfg : WindowCfg t Q A) :
    Qatlib.Foundations.PureStateMath.Ket (windowEncode cfg) (windowEncode c₀) = if cfg = c₀ then (1 : ℂ) else 0 := by
  rw [ket_apply]
  by_cases h : cfg = c₀
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg]
    intro he
    exact h (windowEncode_injective he).symm

/-- An updated configuration equals `c₀` exactly when its head move, internal state, and
single-cell tape update match `c₀`. -/
private theorem cfgAfter_eq_iff {t : ℕ} {Q A : Type} [DecidableEq Q] [DecidableEq A]
    (c : WindowCfg t Q A) (h1 : 0 < c.head.val) (h2 : c.head.val < 2 * t)
    (d : QtmMove) (q' : Q) (a' : A) (c₀ : WindowCfg t Q A) :
    cfgAfter c h1 h2 d q' a' = c₀ ↔
      moveCell d c.head = some c₀.head ∧ c₀.state = q' ∧
        ∀ j : Fin (2 * t + 1), c₀.tape j = if j = c.head then a' else c.tape j := by
  obtain ⟨h₀, s₀, tp₀⟩ := c₀
  cases d
  · rw [show cfgAfter c h1 h2 QtmMove.left q' a'
        = ⟨winL c h1, q', fun j => if j = c.head then a' else c.tape j⟩ from rfl,
      WindowCfg.mk.injEq, funext_iff, moveCell_left c h1, Option.some.injEq]
    constructor
    · rintro ⟨hhead, hstate, htape⟩
      exact ⟨hhead, hstate.symm, fun j => (htape j).symm⟩
    · rintro ⟨hmove, hstate, htape⟩
      exact ⟨hmove, hstate.symm, fun j => (htape j).symm⟩
  · rw [show cfgAfter c h1 h2 QtmMove.stay q' a'
        = ⟨c.head, q', fun j => if j = c.head then a' else c.tape j⟩ from rfl,
      WindowCfg.mk.injEq, funext_iff, moveCell_stay c, Option.some.injEq]
    constructor
    · rintro ⟨hhead, hstate, htape⟩
      exact ⟨hhead, hstate.symm, fun j => (htape j).symm⟩
    · rintro ⟨hmove, hstate, htape⟩
      exact ⟨hmove, hstate.symm, fun j => (htape j).symm⟩
  · rw [show cfgAfter c h1 h2 QtmMove.right q' a'
        = ⟨winR c h2, q', fun j => if j = c.head then a' else c.tape j⟩ from rfl,
      WindowCfg.mk.injEq, funext_iff, moveCell_right c h2, Option.some.injEq]
    constructor
    · rintro ⟨hhead, hstate, htape⟩
      exact ⟨hhead, hstate.symm, fun j => (htape j).symm⟩
    · rintro ⟨hmove, hstate, htape⟩
      exact ⟨hmove, hstate.symm, fun j => (htape j).symm⟩

/-- Evaluation commutes with three nested finite sums of complex-valued functions. -/
private theorem sum_apply3 {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    {X : Type} (F : I → J → K → X → ℂ) (x : X) :
    (∑ i : I, ∑ j : J, ∑ k : K, F i j k) x = ∑ i : I, ∑ j : J, ∑ k : K, F i j k x := by
  simp only [Finset.sum_apply]

/-- Swapping markers in the sweep state gives the embedding of the machine's one-step transition
state. -/
private theorem iSwap_sweepState (t : ℕ) (M : LocalQTM Q A) (c : WindowCfg t Q A)
    (h1 : 0 < c.head.val) (h2 : c.head.val < 2 * t) :
    iSwapFull t *ᵥ sweepState t M c h1 h2 = windowEmbed (windowStep M *ᵥ Qatlib.Foundations.PureStateMath.Ket c) := by
  have hexpand : ∀ x : WReg t Q A,
      (iSwapFull t *ᵥ sweepState t M c h1 h2) x
        = ∑ d : QtmMove, ∑ q' : Q, ∑ a' : A,
            M.step c.state (c.tape c.head) d q' a'
              * Qatlib.Foundations.PureStateMath.Ket (windowEncode (cfgAfter c h1 h2 d q' a')) x := by
    intro x
    have hfun : iSwapFull t *ᵥ sweepState t M c h1 h2
        = ∑ d : QtmMove, ∑ q' : Q, ∑ a' : A,
            M.step c.state (c.tape c.head) d q' a'
              • (iSwapFull t *ᵥ Qatlib.Foundations.PureStateMath.Ket (afterReg t c h1 h2 d q' a')) := by
      simp only [sweepState, sweepAmp]
      rw [mulVec_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [mulVec_sum]
      refine Finset.sum_congr rfl fun q' _ => ?_
      rw [mulVec_sum]
      exact Finset.sum_congr rfl fun a' _ => by rw [Matrix.mulVec_smul]
    rw [hfun, sum_apply3 (fun d q' a' =>
        M.step c.state (c.tape c.head) d q' a'
          • (iSwapFull t *ᵥ Qatlib.Foundations.PureStateMath.Ket (afterReg t c h1 h2 d q' a'))) x]
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun q' _ => ?_
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, iSwapFull_ket, markSwap_after_eq_enc c h1 h2 d q' a']
  funext r
  rw [hexpand r]
  by_cases hex : ∃ c₀ : WindowCfg t Q A, windowEncode c₀ = r
  · obtain ⟨c₀, hc₀⟩ := hex
    rw [← hc₀, windowEmbed_apply]
    have hR : (windowStep M *ᵥ Qatlib.Foundations.PureStateMath.Ket c) c₀
        = ∑ d : QtmMove, ∑ q' : Q, ∑ a' : A,
            (if moveCell d c.head = some c₀.head ∧ c₀.state = q' ∧
                ∀ j : Fin (2 * t + 1), c₀.tape j = if j = c.head then a' else c.tape j
              then M.step c.state (c.tape c.head) d q' a' else 0) := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single c]
      · rw [ket_apply, if_pos rfl, mul_one]
        rfl
      · intro c' _ hc'
        rw [ket_apply, if_neg hc', mul_zero]
      · intro hmem
        exact absurd (Finset.mem_univ c) hmem
    rw [hR]
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun q' _ => ?_
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [ket_enc_eq]
    by_cases hc : cfgAfter c h1 h2 d q' a' = c₀
    · rw [if_pos hc, mul_one, if_pos]
      exact (cfgAfter_eq_iff c h1 h2 d q' a' c₀).mp hc
    · rw [if_neg hc, mul_zero, if_neg]
      exact fun hcond => hc ((cfgAfter_eq_iff c h1 h2 d q' a' c₀).mpr hcond)
  · have hzero : windowEmbed (windowStep M *ᵥ Qatlib.Foundations.PureStateMath.Ket c) r = 0 := by
      refine windowEmbed_eq_zero (windowStep M *ᵥ Qatlib.Foundations.PureStateMath.Ket c) r ?_
      intro c₀ hc₀
      exact hex ⟨c₀, hc₀⟩
    rw [hzero]
    have hterm : ∀ d : QtmMove, ∀ q' : Q, ∀ a' : A,
        (M.step c.state (c.tape c.head) d q' a'
          * Qatlib.Foundations.PureStateMath.Ket (windowEncode (cfgAfter c h1 h2 d q' a')) r) = 0 := by
      intro d q' a'
      rw [ket_apply, if_neg (fun he => hex ⟨_, he.symm⟩), mul_zero]
    simp only [hterm, Finset.sum_const_zero]

/-- The complete left-to-right sweep followed by a marker swap implements one window transition
on an interior configuration ket. -/
private theorem sweep_run_leftToRight {t : ℕ} (M : LocalQTM Q A)
    (G : Matrix (GWindow Q A) (GWindow Q A) ℂ) (hfix : GUnitFixesH M G)
    (hstep : GUnitSteps M G) (c : WindowCfg t Q A) (h1 : 0 < c.head.val)
    (h2 : c.head.val < 2 * t) :
    Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ)
        ((List.finRange (2 * t - 1)).map (fun k => Step.gate (gUnitFull G k))
          ++ [Step.gate (iSwapFull t)])
        (Qatlib.Foundations.PureStateMath.Ket (windowEncode c))
      = windowEmbed (windowStep M *ᵥ Qatlib.Foundations.PureStateMath.Ket c) := by
  rw [run_snoc]
  have hlist : (List.finRange (2 * t - 1)).map (fun k => Step.gate (gUnitFull G k))
      = unitList G (Nat.le_refl (2 * t - 1)) := by
    simp only [unitList]
    exact List.map_congr_left fun k _ => rfl
  rw [hlist, sweep_run_prefix M G hfix hstep c h1 h2 (Nat.le_refl (2 * t - 1)),
    if_pos (by omega), iSwap_sweepState t M c h1 h2]

end Sweep

/-- Every local machine and gate satisfying `GUnitFixesH` and `GUnitSteps` satisfy the one-round
window simulation contract. See [Yao1993]. -/
theorem oneRoundWindowSimulation : OneRoundWindowSimulation := by
  unfold OneRoundWindowSimulation
  intro Q _ _ A _ _ M t _ht G hfix hstep c h1 h2
  rw [kRoundCircuit, sweep_run_leftToRight M G hfix hstep c h1 h2]

end Qatlib.Foundations.StandardDefs.WindowSim
