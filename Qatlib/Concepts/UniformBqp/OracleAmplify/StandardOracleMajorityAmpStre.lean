/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.OracleAmplify.StandardOracleMajorityAmpStat
import Qatlib.Concepts.UniformBqp.OracleAmplify.StandardOracleSequentialCopiesStre

/-!
# Majority amplification for a standard bit oracle

`standardOracleMajorityAmplification` proves the standard-oracle majority amplification
specification using sequential routed copies. The proof combines a binomial majority bound with
an explicit logarithmic choice of repetition count. The background is described in
[BennettEtAl1997].

## Main statements

* `majority_success`: success bound for an odd tensor power.
* `standardOracleMajorityAmplification`: the complete majority amplification guarantee.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.Amplification

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.UniformBqp.OracleAmplify
open Matrix
open scoped Classical

/-- For a normalized finite state, the measurement probability of the complement of an event is
one minus the probability of that event. -/
private theorem measureProb_compl {I : Type} [Fintype I] [DecidableEq I] {ψ : QState I}
    (hψ : Normalized ψ) (S : Finset I) :
    MeasureProb ψ Sᶜ = 1 - MeasureProb ψ S := by
  have hsum : MeasureProb ψ S + MeasureProb ψ Sᶜ = MeasureProb ψ Finset.univ :=
    Finset.sum_add_sum_compl S _
  rw [measureProb_univ hψ] at hsum
  linarith

/-- For `2*r + 1` tensor copies of a normalized state with single-copy success at least `2/3`,
majority vote succeeds with probability at least `1 - (8/9)^r`. -/
private theorem majority_success {I : Type} [Fintype I] [DecidableEq I]
    (r : ℕ) (φ : QState I) (hφnorm : Normalized φ) (v : I → Bool) (b : Bool)
    (hb : (2 / 3 : ℝ) ≤ MeasureProb φ (Finset.univ.filter fun y => v y = b)) :
    1 - (8 / 9 : ℝ) ^ r ≤ MeasureProb (PiTensorState fun _ : Fin (2 * r + 1) => φ)
      (Finset.univ.filter fun ω => MajorityBit (fun j => v (ω j)) = b) := by
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
  have hbound := majority_copies_fail_mass r φ hφnorm S hq
  have hnormAll : Normalized (PiTensorState fun _ : Fin (2 * r + 1) => φ) :=
    normalized_piTensorState (fun _ => hφnorm)
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
  linarith [hbound]

/-- For positive `ε`, choosing the ceiling of `log (1/ε) / log (9/8)` makes the geometric error
term at most `ε`. -/
private theorem precision_tail (ε : ℝ) (hε : 0 < ε) :
    (8 / 9 : ℝ) ^ Nat.ceil (Real.log (1 / ε) / Real.log (9 / 8)) ≤ ε := by
  have hd : 0 < Real.log (9 / 8 : ℝ) := Real.log_pos (by norm_num)
  have hc := Nat.le_ceil (Real.log (1 / ε) / Real.log (9 / 8))
  have hmul := (div_le_iff₀ hd).mp hc
  have hlog : Real.log (8 / 9 : ℝ) = -Real.log (9 / 8 : ℝ) := by
    rw [show (8 / 9 : ℝ) = (9 / 8 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hεlog : Real.log (1 / ε) = -Real.log ε := by
    rw [one_div, Real.log_inv]
  apply (Real.log_le_log_iff (by positivity) hε).mp
  rw [Real.log_pow, hlog]
  rw [hεlog] at hmul ⊢
  nlinarith

/-- Every unitary standard bit-oracle circuit with success at least `2/3` satisfies the majority
amplification specification, including its repetition and exact cost bounds
[BennettEtAl1997]. -/
theorem standardOracleMajorityAmplification : StandardOracleMajorityAmplification := by
  intro n hn W X _ _ _ _ _ C seed v input b ε hC hb hε
  let r := Nat.ceil (Real.log (1 / ε) / Real.log (9 / 8))
  obtain ⟨D, hu, hq, hg, hr⟩ := standardOracleSequentialCopies n (2 * r + 1) hn W C hC
  refine ⟨r, D, by omega, hu, hq, hg, ?_⟩
  intro x
  rw [← tensorState_ket_ket, ← piTensorState_const_ket seed, hr]
  have hnorm := hC.normalized_run (workspaceBitOracle_unitary (input x)) (normalized_ket seed)
  have hmass := majority_success r _ hnorm v (b x) (hb x)
  have hevent : (Finset.univ.filter fun z : (Fin n × Bool) ×
      (Fin (2 * r + 1) → (Fin n × Bool) × W) =>
      MajorityBit (fun j => v (z.2 j)) = b x) =
      Finset.univ ×ˢ (Finset.univ.filter fun ω => MajorityBit (fun j => v (ω j)) = b x) := by
    ext z; simp
  rw [hevent, measureProb_tensorState_right (normalized_ket _)]
  exact (sub_le_sub_left (precision_tail ε hε) 1).trans hmass

end Qatlib.Concepts.UniformBqp.OracleAmplify
