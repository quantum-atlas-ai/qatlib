/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.TraceConcent.Lemma27
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.AmpInvReqTang26.TraceConcent
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Papers.AmpInvReqTang26.AccessModel
open Qatlib.Papers.AmpInvReqTang26.RootLaws
set_option warningAsError false

theorem actual_mixture_mean (q : ℕ) (hq : 0 < q) (eps : ℝ)
    (h0 : 0 ≤ eps) (h1 : eps ≤ 1) :
    cExpect (muEps eps q hq h0 h1) (phaseEps q) =
      ((1-eps : ℝ) : ℂ) * cExpect (mu0 q hq) (phase q) +
        (eps : ℂ) * cExpect (mu1 q) (rightPhase q) := by
  simp only [cExpect,muEps,phaseEps,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,mu0,mu1]
  push_cast
  rw [Finset.mul_sum,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem actual_expected_trace {X : Type} [Fintype X] {d : ℕ} (hd : 0 < d)
    (p : FinDist X) (phi : X → ℂ) :
    expectedTrace (fun _ : Fin d => p) (fun _ => phi) = cExpect p phi := by
  simp only [expectedTrace,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp

theorem actual_biased_mean_window :
    ∃ Q : ℕ, ∀ (q : ℕ) (_hq : max Q 2 ≤ q), ∀ (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1),
      let m := cExpect (muEps eps q (by omega) h0.le h1) (phaseEps q)
      m.im = 0 ∧ eps/2 < ‖m‖ ∧ ‖m‖ < eps := by
  obtain ⟨Q,hQ⟩ := lemma23_mu1_bounds
  refine ⟨Q,fun q hq eps h0 h1 => ?_⟩
  have hq2 : 1 < q := by omega
  obtain ⟨hi,hl,hu⟩ := hQ q (by omega)
  (try dsimp only)
  rw [actual_mixture_mean,cExpect_mu0_phase q hq2,mul_zero,zero_add]
  have hz : cExpect (mu1 q) (rightPhase q) =
      ((cExpect (mu1 q) (rightPhase q)).re : ℂ) := by
    apply Complex.ext <;> simp [hi]
  rw [hz,← Complex.ofReal_mul]
  have hp : 0 ≤ eps * (cExpect (mu1 q) (rightPhase q)).re := by positivity
  simp only [Complex.ofReal_im,Complex.norm_of_nonneg hp,true_and]
  constructor <;> nlinarith

theorem actual_ensemble1_trace :
    ∃ Q : ℕ, ∀ (q : ℕ) (_hq : max Q 2 ≤ q), ∀ (d : ℕ) (hd : 0 < d)
      (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1),
      48/(0.1*eps)^2 ≤ (d:ℝ) →
      eventMass (ensemble1 d q eps (by omega) h0.le h1)
        (fun U => 0.2*eps ≤ ‖normTrace (phaseEps q) U‖) ≥ 0.99 := by
  obtain ⟨Q,hQ⟩ := actual_biased_mean_window
  refine ⟨Q,fun q hq d hd eps h0 h1 hdC => ?_⟩
  have hm := hQ q (by omega) eps h0 h1
  have he := actual_expected_trace hd (muEps eps q (by omega) h0.le h1) (phaseEps q)
  have hu : ∀ (_i : Fin d) (x : Fin q ⊕ Fin (halfCount q)), ‖phaseEps q x‖=1 := by
    intro i x
    cases x with
    | inl k => exact norm_phase q k
    | inr k => exact norm_rightPhase q k
  have ht := lemma27_ensemble1_abstract hd
    (fun _ : Fin d => muEps eps q (by omega) h0.le h1) (fun _ => phaseEps q) hu
    eps h0 (by rw [he]; exact hm.2.1) (by rw [he]; exact hm.2.2) hdC
  simpa [ensemble1,normTrace] using! ht

end Qatlib.Papers.AmpInvReqTang26.TraceConcent
