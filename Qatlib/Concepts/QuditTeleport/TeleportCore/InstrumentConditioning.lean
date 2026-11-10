/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuditTeleport.TeleportCore

open Matrix
open scoped ComplexOrder

theorem instrumentProb_smul_ofReal {O : Type*} [Fintype O] {E F : ℕ}
    (J : Instrument O E F) (r : ℝ) (ψ : Operator E) (o : O) :
    instrumentProb J (((r : ℝ) : ℂ) • ψ) o = r * instrumentProb J ψ o := by
  simp only [instrumentProb, map_smul, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem Instrument.conditionalState_reconstruction {O : Type*} [Fintype O] {D E : ℕ}
    (I : Instrument O D E) (ρ : Operator D) (o : O) (h : 0 < instrumentProb I ρ o) :
    ((instrumentProb I ρ o : ℝ) : ℂ) • I.conditionalState ρ o h = I.branch o ρ ∧
    (IsDensityOperator ρ → IsDensityOperator (I.conditionalState ρ o h)) := by
  have hne : ((instrumentProb I ρ o : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h
  refine ⟨?_, fun hρ => I.isDensityOperator_conditionalState hρ o h⟩
  rw [Instrument.conditionalState, smul_smul, mul_inv_cancel₀ hne, one_smul]

noncomputable def weightedConditionalBranch {O : Type*} [Fintype O] {D E : ℕ}
    (I : Instrument O D E) (ρ : Operator D) (o : O) : Operator E := by
  classical
  exact if h : 0 < instrumentProb I ρ o then
    ((instrumentProb I ρ o : ℝ) : ℂ) • I.conditionalState ρ o h else 0

theorem Instrument.weightedConditional_reconstruction {O : Type*} [Fintype O] {D E : ℕ}
    (I : Instrument O D E) (ρ : Operator D) (hρ : ρ.PosSemidef) :
    (∀ o, weightedConditionalBranch I ρ o = I.branch o ρ) ∧
    (∑ o, weightedConditionalBranch I ρ o) = I.forget.map ρ := by
  have hbranch : ∀ o : O, weightedConditionalBranch I ρ o = I.branch o ρ := by
    intro o
    unfold weightedConditionalBranch
    by_cases h : 0 < instrumentProb I ρ o
    · rw [dif_pos h]
      exact (Instrument.conditionalState_reconstruction I ρ o h).1
    · have hnn : 0 ≤ instrumentProb I ρ o := instrumentProb_nonneg I hρ o
      have h0 : instrumentProb I ρ o = 0 := le_antisymm (not_lt.mp h) hnn
      rw [dif_neg h, (instrumentProb_eq_zero_iff I hρ o).mp h0]
  refine ⟨hbranch, ?_⟩
  rw [Instrument.forget_apply]
  refine Finset.sum_congr rfl fun o _ => ?_
  exact hbranch o

theorem instrumentProb_feedForward_conditional_laws {O : Type*} [Fintype O]
    {Q : O → Type*} [∀ o, Fintype (Q o)] {D E F : ℕ} (I : Instrument O D E)
    (J : ∀ o, Instrument (Q o) E F) (ρ : Operator D) (hρ : ρ.PosSemidef) (o : O)
    (p : Q o) :
    (∀ h : 0 < instrumentProb I ρ o,
      instrumentProb (I.feedForward J) ρ ⟨o, p⟩ = instrumentProb I ρ o *
        instrumentProb (J o) (I.conditionalState ρ o h) p) ∧
    (instrumentProb I ρ o = 0 → instrumentProb (I.feedForward J) ρ ⟨o, p⟩ = 0) := by
  refine ⟨fun h => ?_, fun h0 => ?_⟩
  · rw [instrumentProb_feedForward,
      ← (Instrument.conditionalState_reconstruction I ρ o h).1,
      instrumentProb_smul_ofReal]
  · rw [instrumentProb, I.feedForward_zero_branch J hρ h0 p]
    simp

set_option linter.unusedVariables false in

theorem instrumentProb_seq_conditional {O P : Type*} [Fintype O] [Fintype P]
    [DecidableEq P] {D E F : ℕ} (I : Instrument O D E) (J : Instrument P E F)
    (ρ : Operator D) (hρ : ρ.PosSemidef) (o : O) (p : P)
    (h : 0 < instrumentProb I ρ o) :
    instrumentProb (I.seq J) ρ (o, p) = instrumentProb I ρ o *
      instrumentProb J (I.conditionalState ρ o h) p := by
  rw [instrumentProb_seq,
    ← (Instrument.conditionalState_reconstruction I ρ o h).1,
    instrumentProb_smul_ofReal]

end Qatlib.Concepts.QuditTeleport.TeleportCore
