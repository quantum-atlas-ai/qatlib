/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.MutuallyUnbiased
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option warningAsError false
open Qatlib.Concepts.UnbiasedBases.ThreeBasis
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Papers.MUBCompletion26.Completion
open Finset

def offPairs : Finset (Fin 6 × Fin 6) := univ.filter (fun p => p.1 ≠ p.2)
def missingPairs (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] :
    Finset (Fin 6 × Fin 6) := offPairs.filter (fun p => ¬ G.Adj p.1 p.2)

theorem twelve_missing (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) : 12 ≤ (missingPairs G).card := by
  have hedge : G.edgeFinset.card ≤ 9 := by
    simpa [SimpleGraph.turanNumber_two] using
        (SimpleGraph.CliqueFree.card_edgeFinset_le (r := 2) hG)
  let e := (univ : Finset (Fin 6 × Fin 6)).filter (fun p => G.Adj p.1 p.2)
  have he : offPairs.filter (fun p => G.Adj p.1 p.2) = e := by
    ext p
    simp only [offPairs, e, mem_filter, mem_univ, true_and]
    constructor
    · exact And.right
    · intro ha
      exact ⟨ha.ne, ha⟩
  have he_count : e.card = 2 * G.edgeFinset.card := G.two_mul_card_edgeFinset.symm
  have hcount := Finset.card_filter_add_card_filter_not (s := offPairs)
    (fun p => G.Adj p.1 p.2)
  rw [he] at hcount
  change e.card + (missingPairs G).card = offPairs.card at hcount
  have hpairs : offPairs.card = 30 := by decide
  omega

noncomputable def gramDefectSquared {d : ℕ} (B : Fin 6 → QState (Fin d)) : ℝ :=
  ∑ p : Fin 6 × Fin 6,
    Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (B p.1) (B p.2) - if p.1 = p.2 then 1 else 0)

theorem gram_gap_of_triangleFree {d : ℕ} (B : Fin 6 → QState (Fin d))
    (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hsep : ∀ i j, i ≠ j → ¬ G.Adj i j → μ < Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (B i) (B j))) :
    12 * μ < gramDefectSquared B := by
  let S := missingPairs G
  let f := fun p : Fin 6 × Fin 6 =>
    Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (B p.1) (B p.2) - if p.1 = p.2 then 1 else 0)
  have hcard : 12 ≤ S.card := twelve_missing G hG
  have hpoint (p) (hp : p ∈ S) : μ < f p := by
    have hm := (Finset.mem_filter.mp hp)
    have hne := (Finset.mem_filter.mp hm.1).2
    simpa only [f, if_neg hne, sub_zero] using hsep p.1 p.2 hne hm.2
  have hsum : (S.card : ℝ) * μ < ∑ p ∈ S, f p := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_lt_sum (fun p hp => (hpoint p hp).le)
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
    exact ⟨p,hp,hpoint p hp⟩
  have hall : (∑ p ∈ S, f p) ≤ gramDefectSquared B := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    intro p _ _
    exact Complex.normSq_nonneg _
  have hcast : (12 : ℝ) ≤ S.card := by exact_mod_cast hcard
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast hμ) (hsum.trans_le hall)

theorem gramDefectSquared_eq_zero (B : Fin 6 → QState (Fin 6))
    (hB : Qatlib.Concepts.UnbiasedBases.ThreeBasis.OrthonormalColumns B) : gramDefectSquared B = 0 := by
  unfold Qatlib.Concepts.UnbiasedBases.ThreeBasis.OrthonormalColumns at hB
  simp only [gramDefectSquared, hB, sub_self, Complex.normSq_zero, Finset.sum_const_zero]

theorem gram_gap_one_over_1200 {d : ℕ} (B : Fin 6 → QState (Fin d))
    (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hsep : ∀ i j, i ≠ j → ¬ G.Adj i j → (1 : ℝ) / 120 < ‖Qatlib.Foundations.PureStateMath.Inner (B i) (B j)‖) :
    (1 : ℝ) / 1200 < gramDefectSquared B := by
  have h := gram_gap_of_triangleFree B G hG ((1 : ℝ) / 14400) (by norm_num) (by
    intro i j hij hno
    have hs := hsep i j hij hno
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (Qatlib.Foundations.PureStateMath.Inner (B i) (B j))])
  norm_num at h ⊢
  exact h

theorem not_orthonormal_of_graph_gap (B : Fin 6 → QState (Fin 6))
    (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hsep : ∀ i j, i ≠ j → ¬ G.Adj i j → (1 : ℝ) / 120 < ‖Qatlib.Foundations.PureStateMath.Inner (B i) (B j)‖) :
    ¬ Qatlib.Concepts.UnbiasedBases.ThreeBasis.OrthonormalColumns B := by
  intro hb
  have hg := gram_gap_one_over_1200 B G hG hsep
  rw [gramDefectSquared_eq_zero B hb] at hg
  norm_num at hg

end Qatlib.Papers.MUBCompletion26.Completion
