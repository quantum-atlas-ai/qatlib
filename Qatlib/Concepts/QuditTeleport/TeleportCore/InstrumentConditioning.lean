/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument

/-!
# Conditioning and probability laws for instruments

This module relates conditional output states to unnormalized instrument branches.
`weightedConditionalBranch` handles zero probability outcomes by assigning zero, and positivity
ensures that these weighted outputs reconstruct both the individual branches and their forgotten
sum.

The feed forward and sequential probability identities express the product rule for conditioned
quantum operations in the finite dimensional instrument setting of [Watrous2018].

## Main statements

* `Instrument.conditionalState_reconstruction`: recovers a branch from its probability and
  conditional state.
* `Instrument.weightedConditional_reconstruction`: reconstruction including zero probability
  outcomes.
* `instrumentProb_feedForward_conditional_laws`: conditional product rule for feed forward
  instruments.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuditTeleport.TeleportCore

open Matrix
open scoped ComplexOrder

/-- Scaling an instrument input by a real scalar scales every outcome probability by that
scalar. -/
theorem instrumentProb_smul_ofReal {O : Type*} [Fintype O] {E F : ℕ}
    (J : Instrument O E F) (r : ℝ) (ψ : Operator E) (o : O) :
    instrumentProb J (((r : ℝ) : ℂ) • ψ) o = r * instrumentProb J ψ o := by
  simp only [instrumentProb, map_smul, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Multiplying a positive probability conditional state by its outcome probability reconstructs
the branch operator. If the input is a density operator, the conditional state is also a
density operator. -/
theorem Instrument.conditionalState_reconstruction {O : Type*} [Fintype O] {D E : ℕ}
    (I : Instrument O D E) (ρ : Operator D) (o : O) (h : 0 < instrumentProb I ρ o) :
    ((instrumentProb I ρ o : ℝ) : ℂ) • I.conditionalState ρ o h = I.branch o ρ ∧
    (IsDensityOperator ρ → IsDensityOperator (I.conditionalState ρ o h)) := by
  have hne : ((instrumentProb I ρ o : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h
  refine ⟨?_, fun hρ => I.isDensityOperator_conditionalState hρ o h⟩
  rw [Instrument.conditionalState, smul_smul, mul_inv_cancel₀ hne, one_smul]

/-- The conditional state weighted by its outcome probability when that probability is positive,
and zero otherwise. -/
noncomputable def weightedConditionalBranch {O : Type*} [Fintype O] {D E : ℕ}
    (I : Instrument O D E) (ρ : Operator D) (o : O) : Operator E := by
  classical
  exact if h : 0 < instrumentProb I ρ o then
    ((instrumentProb I ρ o : ℝ) : ℂ) • I.conditionalState ρ o h else 0

/-- For a positive semidefinite input, each weighted conditional branch equals the corresponding
instrument branch, and their sum is the forgotten instrument output. -/
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

/-- For a positive semidefinite input, a feed forward outcome probability factors into the first
outcome probability and the conditional second probability whenever the first is positive. A
zero first outcome probability gives zero joint probability. -/
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


/-- For a positive semidefinite input and a positive first outcome probability, a sequential
outcome probability is the first probability times the second instrument's probability on
the conditional state. -/
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
