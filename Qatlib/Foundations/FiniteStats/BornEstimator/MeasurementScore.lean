/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.EffectNormalize

/-!
# Bounding measurement scores by state scores

This module defines the supremal state score `stateScoreValue` and the effect-based
`measurementScore`. It proves boundedness for nonnegative observable weights and rewrites each
nonzero effect's contribution using the state obtained by normalizing that effect.

The theorem `measurementScore_le_stateValue` bounds the measurement score whenever all nonzero
normalized effects belong to the specified state set. This is the normalized-effect comparison
used in [XuEtAl2026].

## Main statements

* `effect_score_identity`: A nonzero positive effect's measurement-score contribution equals its
  trace divided by the dimension times the quadratic score of its normalized state.
* `measurementScore_le_stateValue`: For nonnegative observable weights, a POVM's measurement
  score is at most the supremal score over `K` if every nonzero normalized effect lies in `K`;
  this is the normalized-effect comparison in [XuEtAl2026].

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators RealInnerProductSpace
variable {d V Ω : Type*} [Fintype d] [DecidableEq d] [Nonempty d] [Fintype V] [Fintype Ω]

/-- The supremum of the quadratic scores of states in `K`. -/
def stateScoreValue (S : V → HermitianMat d ℂ) (w : V → ℝ) (K : Set (MState d)) : ℝ :=
  sSup (quadraticScore S w '' K)

/-- The sum of weighted squared effect-observable inner products divided by dimension times
effect trace. -/
def measurementScore (S : V → HermitianMat d ℂ) (w : V → ℝ) (P : POVM Ω d) : ℝ :=
  ∑ s,(∑ i,w i*⟪P.mats s,S i⟫^2)/((Fintype.card d:ℝ)*(P.mats s).trace)

omit [Nonempty d] in

/-- For nonnegative observable weights, quadratic scores over any state set are bounded above. -/
theorem stateScore_bddAbove (S : V → HermitianMat d ℂ) (w : V → ℝ) (hw : ∀ i,0 ≤ w i) (K : Set (MState d)) :
    BddAbove (quadraticScore S w '' K) := by
  refine ⟨∑ i,w i*‖S i‖^2,?_⟩
  rintro _ ⟨ρ,_,rfl⟩
  exact quadraticScore_le S w hw ρ

omit [Nonempty d] in

/-- For nonnegative weights, the quadratic score of a state in `K` is at most `stateScoreValue S
w K`. -/
theorem stateScore_le_value (S : V → HermitianMat d ℂ) (w : V → ℝ) (hw : ∀ i,0 ≤ w i)
    (K : Set (MState d)) (ρ : MState d) (hρ : ρ∈K) : quadraticScore S w ρ ≤ stateScoreValue S w K :=
  le_csSup (stateScore_bddAbove S w hw K) ⟨ρ,hρ,rfl⟩

omit [Nonempty d] in

/-- The trace of a finite sum of Hermitian matrices is the sum of their traces. -/
theorem trace_finite_sum (E : Ω → HermitianMat d ℂ) :
    (∑ s,E s).trace=∑ s,(E s).trace := by
  have h (s : Finset Ω) : (∑ x∈s,E x).trace=∑ x∈s,(E x).trace := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih => simp [hx,ih]
  exact h Finset.univ

omit [Nonempty d] in

/-- The sum of the traces of a POVM's effects equals the Hilbert-space dimension. -/
theorem povm_trace_total (P : POVM Ω d) : (∑ s,(P.mats s).trace)=(Fintype.card d:ℝ) := by
  rw [← trace_finite_sum,P.normalized,HermitianMat.trace_one]

omit [Nonempty d] in

/-- A nonzero positive effect's measurement-score contribution equals its trace divided by the
dimension times the quadratic score of its normalized state. -/
theorem effect_score_identity (S : V → HermitianMat d ℂ) (w : V → ℝ)
    (E : HermitianMat d ℂ) (hE : 0 ≤ E) (hne : E≠0) :
    (∑ i,w i*⟪E,S i⟫^2)/((Fintype.card d:ℝ)*E.trace)=
      (E.trace/(Fintype.card d:ℝ))*quadraticScore S w (normalizedEffect E hE hne) := by
  unfold quadraticScore
  simp_rw [normalizedEffect_exp]
  rw [Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have ht := (effect_trace_pos E hE hne).ne'
  field_simp

/-- For nonnegative observable weights, a POVM's measurement score is at most the supremal score
over `K` if every nonzero normalized effect lies in `K`; this is the normalized-effect
comparison in [XuEtAl2026]. -/
theorem measurementScore_le_stateValue (S : V → HermitianMat d ℂ) (w : V → ℝ)
    (hw : ∀ i,0 ≤ w i) (K : Set (MState d)) (P : POVM Ω d)
    (hP : ∀ s (hne : P.mats s≠0),normalizedEffect (P.mats s) (P.nonneg s) hne∈K) :
    measurementScore S w P ≤ stateScoreValue S w K := by
  have hd : (0:ℝ)<Fintype.card d := by exact_mod_cast Fintype.card_pos
  have ht : (∑ s,(P.mats s).trace/(Fintype.card d:ℝ))=1 := by
    rw [← Finset.sum_div,povm_trace_total,div_self hd.ne']
  calc _ ≤ ∑ s,((P.mats s).trace/(Fintype.card d:ℝ))*stateScoreValue S w K := by
        apply Finset.sum_le_sum
        intro s _
        by_cases he : P.mats s=0
        · simp [he]
        · rw [effect_score_identity S w (P.mats s) (P.nonneg s) he]
          exact mul_le_mul_of_nonneg_left (stateScore_le_value S w hw K _ (hP s he))
            (div_nonneg (HermitianMat.trace_nonneg (P.nonneg s)) hd.le)
       _ = _ := by rw [← Finset.sum_mul,ht,one_mul]

end Qatlib.Foundations.FiniteStats.BornEstimator
