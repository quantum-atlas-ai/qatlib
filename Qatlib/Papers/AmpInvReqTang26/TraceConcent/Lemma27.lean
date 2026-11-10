/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.TraceConcent.Concentration
import Qatlib.Papers.AmpInvReqTang26.RootLaws.Lemma23
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.AmpInvReqTang26.TraceConcent

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Papers.AmpInvReqTang26.AccessModel
open Qatlib.Papers.AmpInvReqTang26.RootLaws
set_option warningAsError false

theorem eventMass_compl {X : Type} [Fintype X] (p : FinDist X) (E : X → Prop)
    [DecidablePred E] :
    eventMass p (fun x => ¬ E x) = 1 - eventMass p E := by
  have h : eventMass p E + eventMass p (fun x => ¬ E x) = 1 := by
    rw [eventMass, eventMass,
      Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := E)
        (f := p.prob)]
    exact p.sum_one
  linarith

theorem trace_eq_deviation_add_expected {d : ℕ} {X : Fin d → Type}
    [∀ i, Fintype (X i)] (p : ∀ i, FinDist (X i)) (phi : ∀ i, X i → ℂ)
    (ω : ∀ i, X i) :
    ((d : ℝ)⁻¹ : ℂ) * ∑ i, phi i (ω i) =
      traceDeviation p phi ω + expectedTrace p phi := by
  unfold traceDeviation expectedTrace
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem lemma27_ensemble0_abstract {d : ℕ} (hd : 0 < d) {X : Fin d → Type}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (phi : ∀ i, X i → ℂ)
    (hunit : ∀ i x, ‖phi i x‖ = 1) (hE0 : expectedTrace p phi = 0)
    (ε : ℝ) (hε : 0 < ε) (hdC : 48 / (0.1 * ε) ^ 2 ≤ (d : ℝ)) :
    eventMass (independent p)
      (fun ω => ‖((d : ℝ)⁻¹ : ℂ) * ∑ i, phi i (ω i)‖ < 0.1 * ε) ≥ 0.99 := by
  classical
  have ht : 0 < 0.1 * ε := by positivity
  have hconc := trace_concentration hd p phi hunit (0.1 * ε) ht hdC
  have hcompl := eventMass_compl (independent p)
    (fun ω => 0.1 * ε ≤ ‖traceDeviation p phi ω‖)
  have hmono : eventMass (independent p)
        (fun ω => ¬ (0.1 * ε ≤ ‖traceDeviation p phi ω‖)) ≤
      eventMass (independent p)
        (fun ω => ‖((d : ℝ)⁻¹ : ℂ) * ∑ i, phi i (ω i)‖ < 0.1 * ε) := by
    apply eventMass_mono
    intro ω hω
    have hdev : ‖traceDeviation p phi ω‖ < 0.1 * ε := not_le.mp hω
    rw [trace_eq_deviation_add_expected, hE0, add_zero]
    exact hdev
  calc eventMass (independent p)
        (fun ω => ‖((d : ℝ)⁻¹ : ℂ) * ∑ i, phi i (ω i)‖ < 0.1 * ε)
      ≥ eventMass (independent p) (fun ω => ¬ (0.1 * ε ≤ ‖traceDeviation p phi ω‖)) :=
        hmono
    _ = 1 - eventMass (independent p) (fun ω => 0.1 * ε ≤ ‖traceDeviation p phi ω‖) :=
        hcompl
    _ ≥ 0.99 := by linarith

theorem lemma27_ensemble1_abstract {d : ℕ} (hd : 0 < d) {X : Fin d → Type}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (phi : ∀ i, X i → ℂ)
    (hunit : ∀ i x, ‖phi i x‖ = 1) (ε : ℝ) (hε : 0 < ε)
    (hE1lower : ε / 2 < ‖expectedTrace p phi‖)
    (hE1upper : ‖expectedTrace p phi‖ < ε)
    (hdC : 48 / (0.1 * ε) ^ 2 ≤ (d : ℝ)) :
    eventMass (independent p)
      (fun ω => 0.2 * ε ≤ ‖((d : ℝ)⁻¹ : ℂ) * ∑ i, phi i (ω i)‖) ≥ 0.99 := by
  classical
  have ht : 0 < 0.1 * ε := by positivity
  have hconc := trace_concentration hd p phi hunit (0.1 * ε) ht hdC
  have hcompl := eventMass_compl (independent p)
    (fun ω => 0.1 * ε ≤ ‖traceDeviation p phi ω‖)
  have hmono : eventMass (independent p)
        (fun ω => ¬ (0.1 * ε ≤ ‖traceDeviation p phi ω‖)) ≤
      eventMass (independent p)
        (fun ω => 0.2 * ε ≤ ‖((d : ℝ)⁻¹ : ℂ) * ∑ i, phi i (ω i)‖) := by
    apply eventMass_mono
    intro ω hω
    have hdev : ‖traceDeviation p phi ω‖ < 0.1 * ε := not_le.mp hω
    rw [trace_eq_deviation_add_expected]
    have htri : ‖expectedTrace p phi‖ ≤
        ‖expectedTrace p phi + traceDeviation p phi ω‖ +
          ‖traceDeviation p phi ω‖ := by
      have h := norm_add_le (expectedTrace p phi + traceDeviation p phi ω)
        (-(traceDeviation p phi ω))
      simpa using! h
    rw [add_comm (traceDeviation p phi ω) (expectedTrace p phi)]
    nlinarith [htri, hE1lower, hdev, hε]
  calc eventMass (independent p)
        (fun ω => 0.2 * ε ≤ ‖((d : ℝ)⁻¹ : ℂ) * ∑ i, phi i (ω i)‖)
      ≥ eventMass (independent p) (fun ω => ¬ (0.1 * ε ≤ ‖traceDeviation p phi ω‖)) :=
        hmono
    _ = 1 - eventMass (independent p) (fun ω => 0.1 * ε ≤ ‖traceDeviation p phi ω‖) :=
        hcompl
    _ ≥ 0.99 := by linarith

theorem expectedTrace_ensemble0 {d q : ℕ} (hq : 1 < q) :
    expectedTrace (fun _ : Fin d => mu0 q (by omega))
      (fun _ : Fin d => phase q) = 0 := by
  unfold expectedTrace
  have hsum : (∑ _i : Fin d, cExpect (mu0 q (by omega)) (phase q)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact cExpect_mu0_phase q hq
  rw [hsum, mul_zero]

theorem lemma27_ensemble0 {d : ℕ} (hd : 0 < d) {q : ℕ} (hq : 1 < q)
    (ε : ℝ) (hε : 0 < ε) (hdC : 48 / (0.1 * ε) ^ 2 ≤ (d : ℝ)) :
    eventMass (ensemble0 d q (by omega))
      (fun U => ‖normTrace (phase q) U‖ < 0.1 * ε) ≥ 0.99 := by
  have hq0 : 0 < q := by omega
  have h := lemma27_ensemble0_abstract hd
    (p := fun _ : Fin d => mu0 q hq0) (phi := fun _ : Fin d => phase q)
    (fun _ k => norm_phase q k) (expectedTrace_ensemble0 (d := d) hq) ε hε hdC
  simpa [ensemble0, normTrace] using! h

theorem lemma27_ensemble1 {d : ℕ} (hd : 0 < d) {X : Fin d → Type}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (phi : ∀ i, X i → ℂ)
    (hunit : ∀ i x, ‖phi i x‖ = 1) (ε : ℝ) (hε : 0 < ε)
    (hE1lower : ε / 2 < ‖expectedTrace p phi‖)
    (hE1upper : ‖expectedTrace p phi‖ < ε)
    (hdC : 48 / (0.1 * ε) ^ 2 ≤ (d : ℝ)) :
    eventMass (independent p)
      (fun ω => 0.2 * ε ≤ ‖((d : ℝ)⁻¹ : ℂ) * ∑ i, phi i (ω i)‖) ≥ 0.99 :=
  lemma27_ensemble1_abstract hd p phi hunit ε hε hE1lower hE1upper hdC

end Qatlib.Papers.AmpInvReqTang26.TraceConcent
