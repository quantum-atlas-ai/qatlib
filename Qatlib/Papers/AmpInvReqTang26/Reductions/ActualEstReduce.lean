/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.Reductions.ActualMarking
import Qatlib.Papers.AmpInvReqTang26.TraceConcent.ActualMixture
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.GoodEvent

/-!
# Reducing trace discrimination to amplitude estimation

The threshold rule `traceDecision` turns estimates obtained from `tracePreparation` into Boolean
outputs. Accuracy of an amplitude estimator gives high success on separated normalized-trace
branches and, after averaging the actual ensembles, proves the reduction in Proposition 2.8.
This development supports the treatment in [TangWright2025].

## Main statements

* `traceEstimator_accuracy`: transfer of estimation accuracy to normalized trace magnitude.
* `traceEstimator_branch0` and `traceEstimator_branch1`: branch success at least `0.99`.
* `actual_proposition28`: average distinguishing success at least `0.9` in the stated parameter
  regime.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.Reductions
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.GoodEvent
open Qatlib.Papers.AmpInvReqTang26.AccessModel
open Qatlib.Papers.AmpInvReqTang26.TraceConcent

/-- The Boolean threshold test that returns true when the absolute estimate is at least `0.15 *
eps`. -/
def traceDecision (eps v : ℝ) : Bool := decide (0.15*eps ≤ |v|)

/-- The Born mass of preparation-algorithm outputs whose reported values yield Boolean decision
`b` under `traceDecision`. -/
def traceEstimatorOutProb {d anc : ℕ} {S : Type} (eps : ℝ) (hd : 0<d) (phi : S → ℂ)
    (Alg : PreparationAlgorithm (Fin d×Bool) (Fin anc)) (n : ℕ) (U : Fin d → S) (b : Bool) : ℝ :=
  ∑x,if traceDecision eps (Alg.value x)=b then
    ‖preparationRun Alg (tracePreparation d hd (fun i => phi (U i))) n x‖^2 else 0

/-- Every thresholded trace-estimator output mass is nonnegative. -/
theorem traceEstimatorOutProb_nonneg {d anc : ℕ} {S : Type} (eps : ℝ) (hd : 0<d) (phi : S → ℂ)
    (Alg : PreparationAlgorithm (Fin d×Bool) (Fin anc)) (n : ℕ) (U : Fin d → S) (b : Bool) :
    0 ≤ traceEstimatorOutProb eps hd phi Alg n U b := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs <;> positivity

/-- An estimator solving the stated amplitude-estimation task is within `0.05 * eps` of the
normalized trace magnitude with output mass at least `0.99`, for unit-modulus phases and the
specified start and marking. -/
theorem traceEstimator_accuracy {d anc : ℕ} {S : Type} (eps : ℝ) (hd : 0<d) (phi : S → ℂ)
    (hphi : ∀s,‖phi s‖=1) (Alg : PreparationAlgorithm (Fin d×Bool) (Fin anc)) (n : ℕ)
    (hstart : Alg.start=((⟨0,hd⟩:Fin d),false)) (hgood : Alg.goodData=(fun x => !x.2))
    (hAE : SolvesEstimation Alg n (0.05*eps)) (U : Fin d → S) :
    (0.99:ℝ) ≤ ∑x,if |Alg.value x-‖normTrace phi U‖|<0.05*eps then
      ‖preparationRun Alg (tracePreparation d hd (fun i => phi (U i))) n x‖^2 else 0 := by
  have hX := tracePreparation_unitary d hd (fun i => phi (U i)) (fun i => hphi (U i))
  have hXu : (tracePreparation d hd (fun i => phi (U i)))ᴴ*
      tracePreparation d hd (fun i => phi (U i))=1 := Matrix.mem_unitaryGroup_iff'.mp hX
  have h := hAE (tracePreparation d hd (fun i => phi (U i))) hXu
  rw [hstart,hgood,tracePreparation_amplitude] at h
  exact h

/-- An estimate within `0.05 * eps` of a nonnegative value below `0.1 * eps` yields decision
false when `eps > 0`. -/
private theorem decision_zero (eps v m : ℝ) (he : 0<eps) (hm : 0 ≤ m)
    (ht : m<0.1*eps) (ha : |v-m|<0.05*eps) : traceDecision eps v=false := by
  have ha' := abs_lt.mp ha
  have hv : |v|<0.15*eps := abs_lt.mpr ⟨by nlinarith,by nlinarith⟩
  simp [traceDecision,not_le.mpr hv]

/-- An estimate within `0.05 * eps` of a value at least `0.2 * eps` yields decision true. -/
private theorem decision_one (eps v m : ℝ) (ht : 0.2*eps ≤ m)
    (ha : |v-m|<0.05*eps) : traceDecision eps v=true := by
  have ha' := abs_lt.mp ha
  have hv : 0.15*eps ≤ |v| := (show 0.15*eps ≤ v by nlinarith).trans (le_abs_self v)
  simp [traceDecision,hv]

/-- With the specified estimator, start, and marking, normalized trace magnitude below `0.1 *
eps` yields decision false with probability at least `0.99`. -/
theorem traceEstimator_branch0 {d anc : ℕ} {S : Type} (eps : ℝ) (he : 0<eps) (hd : 0<d)
    (phi : S → ℂ) (hphi : ∀s,‖phi s‖=1) (Alg : PreparationAlgorithm (Fin d×Bool) (Fin anc))
    (n : ℕ) (hstart : Alg.start=((⟨0,hd⟩:Fin d),false)) (hgood : Alg.goodData=(fun x => !x.2))
    (hAE : SolvesEstimation Alg n (0.05*eps)) (U : Fin d → S)
    (ht : ‖normTrace phi U‖<0.1*eps) : 0.99 ≤ traceEstimatorOutProb eps hd phi Alg n U false := by
  apply (traceEstimator_accuracy eps hd phi hphi Alg n hstart hgood hAE U).trans
  apply Finset.sum_le_sum
  intro x _
  by_cases ha : |Alg.value x-‖normTrace phi U‖|<0.05*eps
  · rw [if_pos ha,if_pos (decision_zero eps (Alg.value x) _ he (norm_nonneg _) ht ha)]
  · rw [if_neg ha]
    split_ifs <;> positivity

/-- With the specified estimator, start, and marking, normalized trace magnitude at least `0.2 *
eps` yields decision true with probability at least `0.99`. -/
theorem traceEstimator_branch1 {d anc : ℕ} {S : Type} (eps : ℝ) (hd : 0<d)
    (phi : S → ℂ) (hphi : ∀s,‖phi s‖=1) (Alg : PreparationAlgorithm (Fin d×Bool) (Fin anc))
    (n : ℕ) (hstart : Alg.start=((⟨0,hd⟩:Fin d),false)) (hgood : Alg.goodData=(fun x => !x.2))
    (hAE : SolvesEstimation Alg n (0.05*eps)) (U : Fin d → S)
    (ht : 0.2*eps ≤ ‖normTrace phi U‖) : 0.99 ≤ traceEstimatorOutProb eps hd phi Alg n U true := by
  apply (traceEstimator_accuracy eps hd phi hphi Alg n hstart hgood hAE U).trans
  apply Finset.sum_le_sum
  intro x _
  by_cases ha : |Alg.value x-‖normTrace phi U‖|<0.05*eps
  · rw [if_pos ha,if_pos (decision_one eps (Alg.value x) _ ht ha)]
  · rw [if_neg ha]
    split_ifs <;> positivity

/-- There is an absolute cutoff such that, in the stated root-order and dimension regime, any
estimator with error `0.05 * eps` and the specified start and marking induces average
ensemble-distinguishing success at least `0.9` [Tang and Wright, Proposition
2.8][TangWright2025]. -/
theorem actual_proposition28 :
    ∃ C : ℕ, ∀ (q : ℕ) (_hq : max C 4800 ≤ q) (d : ℕ) (hd : 0<d)
      (eps : ℝ) (he0 : 0<eps) (he1 : eps ≤ 1),
      ((max C 4800:ℕ):ℝ)/eps^2 ≤ (d:ℝ) →
      ∀ (anc n : ℕ) (Alg : PreparationAlgorithm (Fin d×Bool) (Fin anc)),
      Alg.start=((⟨0,hd⟩:Fin d),false) → Alg.goodData=(fun x => !x.2) →
      SolvesEstimation Alg n (0.05*eps) →
      (0.9:ℝ) ≤ (1/2)*
        ((ensemble0 d q (by omega)).expect
          (fun U => traceEstimatorOutProb eps hd (phase q) Alg n U false) +
        (ensemble1 d q eps (by omega) he0.le he1).expect
          (fun U => traceEstimatorOutProb eps hd (phaseEps q) Alg n U true)) := by
  obtain ⟨Q,hQ⟩ := actual_ensemble1_trace
  refine ⟨max Q 2,fun q hq d hd eps he0 he1 hdim anc n Alg hstart hgood hAE => ?_⟩
  have hq2 : 1<q := by omega
  have he2 : 0<eps^2 := sq_pos_of_pos he0
  have hdim' : 48/(0.1*eps)^2 ≤ (d:ℝ) := by
    have hconst : (4800:ℝ) ≤ (max (max Q 2) 4800:ℕ) := by
      exact_mod_cast (Nat.le_max_right (max Q 2) 4800)
    have hd' : (max (max Q 2) 4800:ℕ) ≤ (d:ℝ)*eps^2 := (div_le_iff₀ he2).mp hdim
    apply (div_le_iff₀ (by positivity : 0<(0.1*eps)^2)).mpr
    nlinarith
  have hmass0 := lemma27_ensemble0 hd hq2 eps he0 hdim'
  have hmass1 := hQ q (by omega) d hd eps he0 he1 hdim'
  have hphi1 : ∀s : Fin q ⊕ Fin (halfCount q),‖phaseEps q s‖=1 := by
    intro s
    cases s with
    | inl k => exact norm_phase q k
    | inr k => exact norm_rightPhase q k
  have h0 := expect_ge_on_good (ensemble0 d q (by omega))
    (fun U => ‖normTrace (phase q) U‖<0.1*eps)
    (fun U => traceEstimatorOutProb eps hd (phase q) Alg n U false)
    (fun U => traceEstimatorOutProb_nonneg eps hd (phase q) Alg n U false)
    0.99 0.99 (by norm_num)
    (fun U hU => traceEstimator_branch0 eps he0 hd (phase q) (norm_phase q) Alg n hstart hgood hAE U hU) hmass0
  have h1 := expect_ge_on_good (ensemble1 d q eps (by omega) he0.le he1)
    (fun U => 0.2*eps ≤ ‖normTrace (phaseEps q) U‖)
    (fun U => traceEstimatorOutProb eps hd (phaseEps q) Alg n U true)
    (fun U => traceEstimatorOutProb_nonneg eps hd (phaseEps q) Alg n U true)
    0.99 0.99 (by norm_num)
    (fun U hU => traceEstimator_branch1 eps hd (phaseEps q) hphi1 Alg n hstart hgood hAE U hU) hmass1
  nlinarith

end Qatlib.Papers.AmpInvReqTang26.Reductions
