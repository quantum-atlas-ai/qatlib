/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Amplification.Theorem413MajorityVoteAmpStat
import Qatlib.Concepts.QueryComplexity.Amplification.MajorityVote
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Majority vote amplification theorem

This module proves `theorem4_13MajorityVoteAmplification` by executing an odd number of tensor
copies and applying the majority failure estimate. The result applies to unitary circuits with
zero queries, tracks the exact gate count, and realizes the finite circuit amplification
statement associated with Theorem 4.13 of [BennettEtAl1997].

## Main statements

* `theorem4_13MajorityVoteAmplification`: amplify success from at least 2/3 to at least 1 − ε by
  majority voting.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.Amplification

open Matrix

open scoped Classical

/-- The identity matrix is unitary. -/
private theorem one_mem_unitaryGroup' {I : Type} [Fintype I] [DecidableEq I] :
    (1 : Matrix I I ℂ) ∈ Matrix.unitaryGroup I ℂ := by
  refine Matrix.mem_unitaryGroup_iff'.mpr ?_
  simp

/-- For a normalized state, the probability of a complementary event is one minus the
probability of the event. -/
private theorem measureProb_compl {I : Type} [Fintype I] [DecidableEq I] {ψ : QState I}
    (hψ : Normalized ψ) (S : Finset I) :
    MeasureProb ψ Sᶜ = 1 - MeasureProb ψ S := by
  have hsum : MeasureProb ψ S + MeasureProb ψ Sᶜ = MeasureProb ψ Finset.univ :=
    Finset.sum_add_sum_compl S _
  rw [measureProb_univ hψ] at hsum
  linarith

/-- Any unitary circuit with zero queries and success probability at least 2/3 has an odd
repetition circuit with majority success at least 1 − ε for every ε > 0 and gate count equal
to the copy count times the original count. This is the finite circuit amplification
statement associated with [Bennett et al., Theorem 4.13][BennettEtAl1997]. -/
theorem theorem4_13MajorityVoteAmplification : Theorem4_13MajorityVoteAmplification := by
  intro I _ _ C x₀ v b ε hC hC0 hb hε
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (8 / 9 : ℝ) < 1)
  refine ⟨r, SeqCopiesCircuit (2 * r + 1) C, isUnitaryCircuit_seqCopiesCircuit _ hC, ?_, ?_, ?_⟩
  · rw [queryCount_seqCopiesCircuit, hC0, mul_zero]
  · exact gateCount_seqCopiesCircuit _ C
  · set φ : QState I := Run 1 C (Ket x₀) with hφdef
    have hφnorm : Normalized φ := hC.normalized_run one_mem_unitaryGroup' (normalized_ket x₀)
    set S : Finset I := Finset.univ.filter fun y => v y = b with hSdef
    have hq : MeasureProb φ Sᶜ ≤ 1 / 3 := by
      rw [measureProb_compl hφnorm S]
      linarith [hb]

    have hfilter : ∀ ω : Fin (2 * r + 1) → I,
        (Finset.univ.filter fun j => ω j ∈ S) = Finset.univ.filter fun j => v (ω j) = b := by
      intro ω
      ext j
      simp [hSdef]

    have hmem : ∀ ω : Fin (2 * r + 1) → I,
        (¬ MajorityBit (fun j => v (ω j)) = b) ↔
          (Finset.univ.filter fun j => ω j ∈ S).card ≤ r := by
      intro ω
      rw [hfilter ω]
      rcases b with hb' | hb'
      · have hcard : (Finset.univ.filter fun j => v (ω j) = false).card
            + MajorityCount (fun j => v (ω j)) = 2 * r + 1 := by
          have h := Finset.card_filter_add_card_filter_not
            (p := fun j => v (ω j) = true) (s := Finset.univ)
          have hcount : (Finset.univ.filter fun j => v (ω j) = false).card
              = (Finset.univ.filter fun j => ¬(v (ω j) = true)).card := by
            congr 1
          simp only [MajorityCount, hcount]
          rw [Finset.card_univ, Fintype.card_fin] at h
          omega
        constructor
        · intro hne
          have h1 : ¬ (MajorityCount (fun j => v (ω j)) ≤ r) :=
            (majorityBit_eq_false_iff r _).not.mp hne
          have h2 : r < MajorityCount (fun j => v (ω j)) := Nat.lt_of_not_le h1
          omega
        · intro hle
          have h2 : r < MajorityCount (fun j => v (ω j)) := by omega
          have h3 : MajorityBit (fun j => v (ω j)) = true :=
            (majorityBit_eq_true_iff r _).mpr h2
          simp [h3]
      · have hmc : (Finset.univ.filter fun j => v (ω j) = true).card
            = MajorityCount (fun j => v (ω j)) := rfl
        constructor
        · intro hne
          have h1 : ¬ (r < MajorityCount (fun j => v (ω j))) :=
            (majorityBit_eq_true_iff r _).not.mp hne
          have h2 : MajorityCount (fun j => v (ω j)) ≤ r := Nat.le_of_not_gt h1
          rw [hmc]
          exact h2
        · intro hle
          have h1 : MajorityCount (fun j => v (ω j)) ≤ r := by
            rw [hmc] at hle
            exact hle
          have h2 : MajorityBit (fun j => v (ω j)) ≠ true :=
            fun h => absurd ((majorityBit_eq_true_iff r _).mp h) (by omega)
          simpa using h2

    have hrun : Run 1 (SeqCopiesCircuit (2 * r + 1) C) (Ket fun _ => x₀)
        = PiTensorState (fun _ : Fin (2 * r + 1) => φ) := by
      rw [← piTensorState_const_ket x₀]
      exact run_seqCopiesCircuit_piTensorState (2 * r + 1) C hC0 1 _
    have hbound := majority_copies_fail_mass r φ hφnorm S hq
    have hnormAll : Normalized (PiTensorState fun _ : Fin (2 * r + 1) => φ) :=
      normalized_piTensorState (fun _ => hφnorm)
    rw [hrun]
    have hEq : MeasureProb (PiTensorState fun _ : Fin (2 * r + 1) => φ)
          (Finset.univ.filter fun ω => MajorityBit (fun j => v (ω j)) = b)
        = 1 - MeasureProb (PiTensorState fun _ : Fin (2 * r + 1) => φ)
          (Finset.univ.filter fun ω => (Finset.univ.filter fun j => ω j ∈ S).card ≤ r) := by
      have hsetEq : (Finset.univ.filter fun ω => MajorityBit (fun j => v (ω j)) = b)
          = (Finset.univ.filter
              (fun ω : Fin (2 * r + 1) → I =>
                (Finset.univ.filter fun j => ω j ∈ S).card ≤ r))ᶜ := by
        ext ω
        simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (not_not (a := MajorityBit (fun j => v (ω j)) = b)).symm.trans (hmem ω).not
      rw [hsetEq, measureProb_compl hnormAll]
    rw [hEq]
    linarith [hbound, hr]

end Qatlib.Concepts.QueryComplexity.Amplification
