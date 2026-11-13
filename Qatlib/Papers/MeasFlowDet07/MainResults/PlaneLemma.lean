/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCoreDefs
import Qatlib.Papers.MeasFlowDet07.MainResults.PlaneAnachronical

/-!
# Proportionality tests for measurement-plane projections

The XZ-plane projection formulas at angles `0`, `π`, and `π / 2` imply global
proportionality when the two slices of the comparison state are linearly
independent. The module also gives a counterexample to the unqualified
proportionality statement encoded here: angle-dependent unit phases alone do
not force a single global proportionality factor.

The measurement-flow context is [BrowneEtAl2007] and
[Danos & Kashefi, one-way determinism][DanosKashefi2006]. The independence
hypothesis and the counterexample are explicit parts of this formal treatment.
-/
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open Matrix

namespace Qatlib.Papers.MeasFlowDet07.MainResults

/-- The action of a qubit operator on the final index of an array of qubit amplitudes. -/
def planeProjAct {m : ℕ} (P : Operator 2) (Ψ : Fin m → Fin 2 → ℂ) : Fin m → Fin 2 → ℂ :=
  fun x k => ∑ j : Fin 2, P k j * Ψ x j

/-- The false-outcome `XZ` projector at angle zero keeps the zeroth component and sets the other
component to zero. -/
theorem planeProjAct_XZ_zero_apply {m : ℕ} (Ψ : Fin m → Fin 2 → ℂ) (x : Fin m) (k : Fin 2) :
    planeProjAct (MbqcPlaneBasis .XZ 0 false) Ψ x k = if k = 0 then Ψ x 0 else 0 := by
  fin_cases k <;>
    simp [planeProjAct, Fin.sum_univ_two, MbqcPlaneBasis, mbqcPlaneAxisA, mbqcPlaneAxisB,
      pauliX, pauliZ, Real.cos_zero, Real.sin_zero]
  all_goals ring

/-- The false-outcome `XZ` projector at angle `π` keeps the first component and sets the other
component to zero. -/
theorem planeProjAct_XZ_pi_apply {m : ℕ} (Ψ : Fin m → Fin 2 → ℂ) (x : Fin m) (k : Fin 2) :
    planeProjAct (MbqcPlaneBasis .XZ Real.pi false) Ψ x k = if k = 1 then Ψ x 1 else 0 := by
  fin_cases k <;>
    simp [planeProjAct, Fin.sum_univ_two, MbqcPlaneBasis, mbqcPlaneAxisA, mbqcPlaneAxisB,
      pauliX, pauliZ, Real.cos_pi, Real.sin_pi]
  all_goals ring

/-- The false-outcome `XZ` projector at angle `π / 2` sends each component to half the sum of
the two input components. -/
theorem planeProjAct_XZ_pi_div_two_apply {m : ℕ} (Ψ : Fin m → Fin 2 → ℂ) (x : Fin m)
    (k : Fin 2) :
    planeProjAct (MbqcPlaneBasis .XZ (Real.pi / 2) false) Ψ x k
      = (2 : ℂ)⁻¹ * (Ψ x 0 + Ψ x 1) := by
  fin_cases k <;>
    simp [planeProjAct, Fin.sum_univ_two, MbqcPlaneBasis, mbqcPlaneAxisA, mbqcPlaneAxisB,
      pauliX, pauliZ, Real.cos_pi_div_two, Real.sin_pi_div_two] <;>
    ring

/-- Proportional XZ projections at three angles imply global proportionality
under linear independence of the comparison slices. For measurement-plane
background, see [Browne et al., generalized flow][BrowneEtAl2007]. -/
theorem planeLemma_of_linearIndependent {m : ℕ} (Ψ Ψ' : Fin m → Fin 2 → ℂ)
    (hli : LinearIndependent ℂ ![fun x => Ψ' x 0, fun x => Ψ' x 1])
    (h0 : ∃ c : ℂ, planeProjAct (MbqcPlaneBasis .XZ 0 false) Ψ
      = c • planeProjAct (MbqcPlaneBasis .XZ 0 false) Ψ')
    (h1 : ∃ c : ℂ, planeProjAct (MbqcPlaneBasis .XZ Real.pi false) Ψ
      = c • planeProjAct (MbqcPlaneBasis .XZ Real.pi false) Ψ')
    (hp : ∃ c : ℂ, planeProjAct (MbqcPlaneBasis .XZ (Real.pi / 2) false) Ψ
      = c • planeProjAct (MbqcPlaneBasis .XZ (Real.pi / 2) false) Ψ') :
    ∃ c : ℂ, Ψ = c • Ψ' := by
  obtain ⟨c0, hc0⟩ := h0
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨cp, hcp⟩ := hp
  have e0 : ∀ x : Fin m, Ψ x 0 = c0 * Ψ' x 0 := by
    intro x
    simpa [planeProjAct_XZ_zero_apply] using congrFun (congrFun hc0 x) 0
  have e1 : ∀ x : Fin m, Ψ x 1 = c1 * Ψ' x 1 := by
    intro x
    simpa [planeProjAct_XZ_pi_apply] using congrFun (congrFun hc1 x) 1
  have ep : ∀ x : Fin m, Ψ x 0 + Ψ x 1 = cp * (Ψ' x 0 + Ψ' x 1) := by
    intro x
    have hx : (2 : ℂ)⁻¹ * (Ψ x 0 + Ψ x 1)
        = cp * ((2 : ℂ)⁻¹ * (Ψ' x 0 + Ψ' x 1)) := by
      simpa [planeProjAct_XZ_pi_div_two_apply] using congrFun (congrFun hcp x) 0
    have h2 : (2 : ℂ) * (2 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (by norm_num)
    calc Ψ x 0 + Ψ x 1 = (2 : ℂ) * ((2 : ℂ)⁻¹ * (Ψ x 0 + Ψ x 1)) := by
          rw [← mul_assoc, h2, one_mul]
      _ = (2 : ℂ) * (cp * ((2 : ℂ)⁻¹ * (Ψ' x 0 + Ψ' x 1))) := by rw [hx]
      _ = cp * (Ψ' x 0 + Ψ' x 1) := by
          rw [← mul_assoc (2 : ℂ) cp, mul_comm (2 : ℂ) cp, mul_assoc cp (2 : ℂ),
            ← mul_assoc (2 : ℂ) (2 : ℂ)⁻¹ (Ψ' x 0 + Ψ' x 1), h2, one_mul]
  have hgsum : (∑ i : Fin 2,
      (if i = 0 then (c0 - cp) else (c1 - cp)) •
        (![fun x => Ψ' x 0, fun x => Ψ' x 1] i)) = 0 := by
    funext x
    have hx : (c0 - cp) * Ψ' x 0 + (c1 - cp) * Ψ' x 1 = 0 := by
      have := ep x
      rw [e0 x, e1 x] at this
      linear_combination this
    simpa [Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc] using hx
  have hgsum' : (∑ i : Fin 2, (if i = 0 then (c0 - cp) else (c1 - cp)) •
        (![fun x => Ψ' x 0, fun x => Ψ' x 1] i))
      = ∑ i : Fin 2, (0 : Fin 2 → ℂ) i • (![fun x => Ψ' x 0, fun x => Ψ' x 1] i) := by
    simpa using hgsum
  have hcoef := (Fintype.linearIndependent_iffₛ.mp hli)
    (fun i : Fin 2 => if i = 0 then (c0 - cp) else (c1 - cp)) 0 hgsum'
  have h0c : c0 = cp := sub_eq_zero.mp (by simpa using hcoef 0)
  have h1c : c1 = cp := sub_eq_zero.mp (by simpa using hcoef 1)
  refine ⟨cp, ?_⟩
  funext x k
  fin_cases k
  · simp [e0 x, h0c]
  · simp [e1 x, h1c]

/-- The qubit vector with real components `cos (a / 2)` and `sin (a / 2)`. -/
def mbqcPlaneStateXZ (a : ℝ) : Fin 2 → ℂ :=
  ![Complex.ofReal (Real.cos (a / 2)), Complex.ofReal (Real.sin (a / 2))]

/-- The false-outcome `XZ` plane basis operator is the rank one matrix formed from
`mbqcPlaneStateXZ a`. -/
theorem mbqcPlaneBasis_XZ_false_rankOne (a : ℝ) :
    MbqcPlaneBasis .XZ a false
      = Matrix.of fun k j => mbqcPlaneStateXZ a k * mbqcPlaneStateXZ a j := by
  have hc : Complex.cos (↑a : ℂ) = 2 * Complex.cos (↑a / 2) ^ 2 - 1 := by
    have h := Complex.cos_two_mul (↑a / 2 : ℂ)
    rwa [show 2 * (↑a / 2 : ℂ) = ↑a by ring] at h
  have hs : Complex.sin (↑a : ℂ) = 2 * Complex.sin (↑a / 2) * Complex.cos (↑a / 2) := by
    have h := Complex.sin_two_mul (↑a / 2 : ℂ)
    rwa [show 2 * (↑a / 2 : ℂ) = ↑a by ring] at h
  ext k j
  fin_cases k <;> fin_cases j <;>
    simp [mbqcPlaneBasis_eq_observable, mbqcPlaneObservable, mbqcPlaneAxisA, mbqcPlaneAxisB,
      pauliX, pauliZ, mbqcPlaneStateXZ]
  · rw [hc]; ring
  · rw [hs]; ring
  · rw [hs]; ring
  · rw [hc]; ring_nf
    have h := Complex.sin_sq_add_cos_sq (↑a * (1 / 2 : ℂ))
    linear_combination -h

/-- Expresses the action of the false-outcome `XZ` projector as its defining vector times the
scalar contraction with the input amplitudes. -/
theorem planeProjAct_XZ_rankOne {m : ℕ} (a : ℝ) (Ψ : Fin m → Fin 2 → ℂ) (x : Fin m)
    (k : Fin 2) :
    planeProjAct (MbqcPlaneBasis .XZ a false) Ψ x k
      = mbqcPlaneStateXZ a k *
          (mbqcPlaneStateXZ a 0 * Ψ x 0 + mbqcPlaneStateXZ a 1 * Ψ x 1) := by
  rw [mbqcPlaneBasis_XZ_false_rankOne]
  simp only [planeProjAct, Matrix.of_apply, Fin.sum_univ_two]
  ring

/-- The complex number formed by the zeroth component plus `i` times the first component of
`mbqcPlaneStateXZ a` is nonzero. -/
theorem mbqcPlaneStateXZ_sum_ne_zero (a : ℝ) :
    mbqcPlaneStateXZ a 0 + mbqcPlaneStateXZ a 1 * Complex.I ≠ 0 := by
  intro h
  have hnsq : Complex.normSq (mbqcPlaneStateXZ a 0 + mbqcPlaneStateXZ a 1 * Complex.I) = 1 := by
    have hval : mbqcPlaneStateXZ a 0 + mbqcPlaneStateXZ a 1 * Complex.I
        = ↑(Real.cos (a / 2)) + ↑(Real.sin (a / 2)) * Complex.I := by
      simp [mbqcPlaneStateXZ]
    rw [hval, Complex.normSq_add_mul_I]
    nlinarith [Real.cos_sq_add_sin_sq (a / 2)]
  rw [h] at hnsq
  simp at hnsq

/-- The ratio of the zeroth component minus `i` times the first component to the corresponding
sum for `mbqcPlaneStateXZ a`. -/
def planeLemmaPhase (a : ℝ) : ℂ :=
  (mbqcPlaneStateXZ a 0 - mbqcPlaneStateXZ a 1 * Complex.I)
    / (mbqcPlaneStateXZ a 0 + mbqcPlaneStateXZ a 1 * Complex.I)

/-- The complex phase `planeLemmaPhase a` has norm one. -/
theorem planeLemmaPhase_norm (a : ℝ) : ‖planeLemmaPhase a‖ = 1 := by
  have hy := mbqcPlaneStateXZ_sum_ne_zero a
  have hconj : (mbqcPlaneStateXZ a 0 - mbqcPlaneStateXZ a 1 * Complex.I)
      = starRingEnd ℂ (mbqcPlaneStateXZ a 0 + mbqcPlaneStateXZ a 1 * Complex.I) := by
    simp only [mbqcPlaneStateXZ, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [planeLemmaPhase, hconj, norm_div, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr hy)]

/-- The amplitude array with one spectator index and qubit components `1` and `-i`. -/
def planeLemmaCounterA : Fin 1 → Fin 2 → ℂ :=
  fun _ k => if k = 0 then 1 else -Complex.I

/-- The amplitude array with one spectator index and qubit components `1` and `i`. -/
def planeLemmaCounterB : Fin 1 → Fin 2 → ℂ :=
  fun _ k => if k = 0 then 1 else Complex.I

/-- Counterexample to dropping the independence requirement in the local
measurement-plane formulation motivated by [BrowneEtAl2007]. -/
theorem planeLemma_literal_false :
    ∃ Ψ Ψ' : Fin 1 → Fin 2 → ℂ,
      (∀ a : ℝ, ∃ c : ℂ, ‖c‖ = 1 ∧
        planeProjAct (MbqcPlaneBasis .XZ a false) Ψ
          = c • planeProjAct (MbqcPlaneBasis .XZ a false) Ψ') ∧
      ¬ ∃ c : ℂ, Ψ = c • Ψ' := by
  refine ⟨planeLemmaCounterA, planeLemmaCounterB, ?_, ?_⟩
  · intro a
    refine ⟨planeLemmaPhase a, planeLemmaPhase_norm a, ?_⟩
    funext x k
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [planeProjAct_XZ_rankOne a planeLemmaCounterA x k,
      planeProjAct_XZ_rankOne a planeLemmaCounterB x k]
    simp [planeLemmaCounterA, planeLemmaCounterB]
    rw [planeLemmaPhase]
    have hy := mbqcPlaneStateXZ_sum_ne_zero a
    field_simp
    ring
  · rintro ⟨c, hc⟩
    have h0 : (1 : ℂ) = c := by
      simpa [planeLemmaCounterA, planeLemmaCounterB] using congrFun (congrFun hc 0) 0
    have h1 : -Complex.I = c * Complex.I := by
      simpa [planeLemmaCounterA, planeLemmaCounterB] using congrFun (congrFun hc 0) 1
    rw [← h0, one_mul] at h1
    have hsum : (0 : ℂ) = 2 * Complex.I := by linear_combination h1
    exact Complex.I_ne_zero ((mul_eq_zero.mp hsum.symm).resolve_left (by norm_num))

end Qatlib.Papers.MeasFlowDet07.MainResults
