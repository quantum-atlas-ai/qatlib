/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.Theorem3LCUFiberCorrectedHami

/-!
# Failure mass as a signed mixture of state means

This module rewrites the corrected signed LCU output using the positive and negative coefficient
distributions. The means `cwStateMeanPositive` and `cwStateMeanNegative` average the Euclidean
vectors obtained by applying the system unitaries to the input, providing the state geometry
used in the failure analysis of Theorem 3 in [ChildsWiebe2012].

For normalized input, `cwFailureProbCorrected_complement` identifies failure mass with one minus
the squared norm of the zero ancilla fiber. `cw_failure_signed_mix` then expresses it using a
signed mixture of the two means, while `cw_state_means_bounds` controls each mean's norm loss
under the pairwise distance hypothesis.

## Main statements

* `cw_positive_coeff_normalized` and `cw_negative_coeff_normalized` prove that the two sign
  distributions have nonnegative weights summing to one.
* `cw_state_means_bounds` bounds both mean norms by one and both squared norm losses by `Δ^2 /
  2`.
* `cw_success_vector_signed_mix` identifies the success vector with the mass-weighted difference
  of the means.
- `cw_failure_signed_mix` gives the corresponding exact failure identity for normalized input.

## References

- [Childs and Wiebe, 2012][ChildsWiebe2012], Theorem 3.
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.LCUDeferred
open Matrix
open scoped Classical Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The positive-sign coefficient distribution, assigning `c q / cwPositiveWeight k c` to
positive terms and zero to all other indices. -/
def cwPositiveCoeff (k : ℕ) (c : Fin (k+1)→ℝ) (q : Fin (k+1)) : ℝ :=
  if 0<c q then c q/cwPositiveWeight k c else 0

/-- The negative-sign coefficient distribution, assigning `|c q| / cwNegativeWeight k c` to
negative terms and zero to all other indices. -/
def cwNegativeCoeff (k : ℕ) (c : Fin (k+1)→ℝ) (q : Fin (k+1)) : ℝ :=
  if c q<0 then |c q|/cwNegativeWeight k c else 0

/-- The weighted Euclidean mean of the vectors `U q *ᵥ ψ`, using the positive-sign coefficient
distribution. -/
def cwStateMeanPositive (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ) (ψ : QState I) :=
  nearbyLCUMean (cwPositiveCoeff k c) (fun q=>stateVector (U q*ᵥψ))

/-- The weighted Euclidean mean of the vectors `U q *ᵥ ψ`, using the negative-sign coefficient
distribution. -/
def cwStateMeanNegative (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ) (ψ : QState I) :=
  nearbyLCUMean (cwNegativeCoeff k c) (fun q=>stateVector (U q*ᵥψ))

/-- If a positive coefficient exists, all positive-sign distribution weights are nonnegative and
their sum is one. -/
theorem cw_positive_coeff_normalized (k : ℕ) (c : Fin (k+1)→ℝ) (hp : ∃ q,0<c q) :
    (∀ q,0≤cwPositiveCoeff k c q) ∧ ∑ q,cwPositiveCoeff k c q=1 := by
  constructor
  · intro q
    unfold cwPositiveCoeff
    split_ifs with h
    · exact div_nonneg h.le (cw_positive_weight_pos k c hp).le
    · exact le_rfl
  · unfold cwPositiveCoeff
    have hh : (∑ q,if 0<c q then c q/cwPositiveWeight k c else 0)=
        (∑ q,if 0<c q then c q else 0)/cwPositiveWeight k c := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> simp
    rw [hh]
    have hsum : (∑ q,if 0<c q then c q else 0)=cwPositiveWeight k c := by
      simp only [cwPositiveWeight,cwPositiveTerms,Finset.sum_filter]
    rw [hsum,div_self (cw_positive_weight_pos k c hp).ne']

/-- If a negative coefficient exists, all negative-sign distribution weights are nonnegative and
their sum is one. -/
theorem cw_negative_coeff_normalized (k : ℕ) (c : Fin (k+1)→ℝ) (hn : ∃ q,c q<0) :
    (∀ q,0≤cwNegativeCoeff k c q) ∧ ∑ q,cwNegativeCoeff k c q=1 := by
  constructor
  · intro q
    unfold cwNegativeCoeff
    split_ifs
    · exact div_nonneg (abs_nonneg _) (cw_negative_weight_pos k c hn).le
    · exact le_rfl
  · unfold cwNegativeCoeff
    have hh : (∑ q,if c q<0 then |c q|/cwNegativeWeight k c else 0)=
        (∑ q,if c q<0 then |c q| else 0)/cwNegativeWeight k c := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> simp
    rw [hh]
    have hsum : (∑ q,if c q<0 then |c q| else 0)=cwNegativeWeight k c := by
      simp only [cwNegativeWeight,cwNegativeTerms,Finset.sum_filter]
    rw [hsum,div_self (cw_negative_weight_pos k c hn).ne']

/-- For normalized input, unitary payloads, and nonzero coefficients of both signs, corrected
failure probability equals one minus the total squared amplitude on the zero ancilla fiber. -/
theorem cwFailureProbCorrected_complement (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ)
    (hU : ∀ q,U q∈Matrix.unitaryGroup I ℂ) (hc : ∀ q,c q≠0)
    (hp : ∃ q,0<c q) (hn : ∃ q,c q<0) (ψ : QState I) (hψ : Normalized ψ) :
    cwFailureProbCorrected k c U ψ=1-∑ x : I,‖cwOutputCorrected k c U ψ (cwZero k,x)‖^2 := by
  have hnorm : Normalized (cwOutputCorrected k c U ψ) :=
    normalized_applyGate (cwProtocolCorrected_unitary k c U hU hc hp hn)
      (normalized_tensorState (normalized_ket _) hψ)
  change (∑ p : (Fin (k+1)→Bool)×I,‖cwOutputCorrected k c U ψ p‖^2)=1 at hnorm
  rw [Fintype.sum_prod_type] at hnorm
  unfold cwFailureProbCorrected MeasureProb BornProb
  rw [Finset.sum_product]
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin (k+1)→Bool))
    (fun z=>∑ x : I,‖cwOutputCorrected k c U ψ (z,x)‖^2) (by simp : cwZero k∈Finset.univ)
  rw [hnorm] at he
  linarith

/-- For normalized input and unitary payloads with both coefficient signs present, each sign
mean has norm at most one. Under the uniform pairwise squared-distance bound `Δ^2`, each
mean also satisfies `1 - ‖mean‖^2 ≤ Δ^2 / 2`. -/
theorem cw_state_means_bounds (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ)
    (hU : ∀ q,U q∈Matrix.unitaryGroup I ℂ) (hp : ∃ q,0<c q) (hn : ∃ q,c q<0)
    (Δ : ℝ) (hΔ : ∀ q q',∀ φ : QState I,Normalized φ→∑ x : I,‖((U q-U q')*ᵥφ) x‖^2≤Δ^2)
    (ψ : QState I) (hψ : Normalized ψ) :
    ‖cwStateMeanPositive k c U ψ‖≤1 ∧ ‖cwStateMeanNegative k c U ψ‖≤1 ∧
      1-‖cwStateMeanPositive k c U ψ‖^2≤Δ^2/2 ∧ 1-‖cwStateMeanNegative k c U ψ‖^2≤Δ^2/2 := by
  have hv (q : Fin (k+1)) : ‖stateVector (U q*ᵥψ)‖=1 :=
    (normalized_iff_stateVector_norm _).mp (normalized_applyGate (hU q) hψ)
  have hd (q q' : Fin (k+1)) : ‖stateVector (U q*ᵥψ)-stateVector (U q'*ᵥψ)‖^2≤Δ^2 := by
    have hh := hΔ q q' ψ hψ
    change MeasureProb ((U q-U q')*ᵥψ) Finset.univ≤Δ^2 at hh
    rw [← stateVector_norm_sq,Matrix.sub_mulVec] at hh
    exact hh
  have ha := cw_positive_coeff_normalized k c hp
  have hb := cw_negative_coeff_normalized k c hn
  exact ⟨nearbyLCUMean_norm_le_one _ _ ha.1 ha.2 hv,
    nearbyLCUMean_norm_le_one _ _ hb.1 hb.2 hv,
    nearbyLCUMean_loss_le _ _ Δ ha.1 ha.2 hv hd,
    nearbyLCUMean_loss_le _ _ Δ hb.1 hb.2 hv hd⟩
omit [DecidableEq I] in

/-- Each coordinate of the positive mean equals the positive weighted matrix sum applied to `ψ`,
divided by the positive coefficient mass. -/
theorem cw_positive_mean_coordinate (k : ℕ) (c : Fin (k+1)→ℝ)
    (U : Fin (k+1)→Matrix I I ℂ) (ψ : QState I) (x : I) :
    cwStateMeanPositive k c U ψ x=((∑ q∈cwPositiveTerms k c,c q • U q)*ᵥψ) x/(cwPositiveWeight k c:ℂ) := by
  unfold cwStateMeanPositive nearbyLCUMean
  change (WithLp.ofLp (∑ q : Fin (k+1),(cwPositiveCoeff k c q:ℂ) • stateVector (U q*ᵥψ))) x=_
  simp only [WithLp.ofLp_sum,WithLp.ofLp_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [Matrix.sum_mulVec]
  simp only [Finset.sum_apply,Matrix.smul_mulVec,Pi.smul_apply,Complex.real_smul]
  unfold cwPositiveTerms cwPositiveCoeff
  rw [Finset.sum_filter,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> push_cast <;> ring

omit [DecidableEq I] in

/-- Each coordinate of the negative mean equals the absolute-weight negative matrix sum applied
to `ψ`, divided by the negative coefficient mass. -/
theorem cw_negative_mean_coordinate (k : ℕ) (c : Fin (k+1)→ℝ)
    (U : Fin (k+1)→Matrix I I ℂ) (ψ : QState I) (x : I) :
    cwStateMeanNegative k c U ψ x=((∑ q∈cwNegativeTerms k c,|c q| • U q)*ᵥψ) x/(cwNegativeWeight k c:ℂ) := by
  unfold cwStateMeanNegative nearbyLCUMean
  change (WithLp.ofLp (∑ q : Fin (k+1),(cwNegativeCoeff k c q:ℂ) • stateVector (U q*ᵥψ))) x=_
  simp only [WithLp.ofLp_sum,WithLp.ofLp_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [Matrix.sum_mulVec]
  simp only [Finset.sum_apply,Matrix.smul_mulVec,Pi.smul_apply,Complex.real_smul]
  unfold cwNegativeTerms cwNegativeCoeff
  rw [Finset.sum_filter,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> push_cast <;> ring

/-- Under the corrected Theorem 3 hypotheses, the zero ancilla success vector is the positive
mean times its fraction of total absolute mass minus the negative mean times its fraction of
that mass. The identity holds for arbitrary input vectors and uses the corrected fiber
result associated with [ChildsWiebe2012]. -/
theorem cw_success_vector_signed_mix (k : ℕ) (hk : 1≤k) (c : Fin (k+1)→ℝ)
    (U : Fin (k+1)→Matrix I I ℂ) (hU : ∀ q,U q∈Matrix.unitaryGroup I ℂ)
    (hc : ∀ q,c q≠0) (hp : ∃ q,0<c q) (hn : ∃ q,c q<0) (ψ : QState I) :
    stateVector (fun x=>cwOutputCorrected k c U ψ (cwZero k,x))=
      ((cwPositiveWeight k c/(cwPositiveWeight k c+cwNegativeWeight k c):ℝ):ℂ) • cwStateMeanPositive k c U ψ-
      ((cwNegativeWeight k c/(cwPositiveWeight k c+cwNegativeWeight k c):ℝ):ℂ) • cwStateMeanNegative k c U ψ := by
  ext x
  change cwOutputCorrected k c U ψ (cwZero k,x)=_
  rw [show cwOutputCorrected k c U ψ (cwZero k,x)=
      (((∑ q,c q • U q)*ᵥψ) x)/((∑ q,|c q|:ℝ):ℂ) from
      theorem3LCUFiberCorrected k I hk U hU c hc hp hn ψ x]
  simp only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  rw [cw_positive_mean_coordinate,cw_negative_mean_coordinate,← cw_signed_weighted k c U,← cw_weight_sum k c]
  rw [Matrix.sub_mulVec,Pi.sub_apply]
  have ha : (cwPositiveWeight k c:ℂ)≠0 := by exact_mod_cast (cw_positive_weight_pos k c hp).ne'
  have hb : (cwNegativeWeight k c:ℂ)≠0 := by exact_mod_cast (cw_negative_weight_pos k c hn).ne'
  have hs : ((cwPositiveWeight k c+cwNegativeWeight k c:ℝ):ℂ)≠0 := by
    exact_mod_cast (ne_of_gt (add_pos (cw_positive_weight_pos k c hp) (cw_negative_weight_pos k c hn)))
  push_cast at ha hb hs ⊢
  field_simp [ha,hb,hs]

/-- For normalized input under the corrected Theorem 3 hypotheses, failure probability is one
minus the squared norm of the mass-weighted difference of the positive and negative means.
This exact identity supports the failure analysis of [ChildsWiebe2012]. -/
theorem cw_failure_signed_mix (k : ℕ) (hk : 1≤k) (c : Fin (k+1)→ℝ)
    (U : Fin (k+1)→Matrix I I ℂ) (hU : ∀ q,U q∈Matrix.unitaryGroup I ℂ)
    (hc : ∀ q,c q≠0) (hp : ∃ q,0<c q) (hn : ∃ q,c q<0) (ψ : QState I) (hψ : Normalized ψ) :
    cwFailureProbCorrected k c U ψ=1-
      ‖((cwPositiveWeight k c/(cwPositiveWeight k c+cwNegativeWeight k c):ℝ):ℂ) • cwStateMeanPositive k c U ψ-
      ((cwNegativeWeight k c/(cwPositiveWeight k c+cwNegativeWeight k c):ℝ):ℂ) • cwStateMeanNegative k c U ψ‖^2 := by
  rw [cwFailureProbCorrected_complement k c U hU hc hp hn ψ hψ]
  have hh := cw_success_vector_signed_mix k hk c U hU hc hp hn ψ
  rw [← hh,stateVector_norm_sq]
  rfl
end Qatlib.Papers.HamLCUSim12.LCUDeferred
