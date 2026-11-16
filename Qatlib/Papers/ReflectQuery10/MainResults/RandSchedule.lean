/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.Reflections.ReflectionsPhaseBridge
public import Qatlib.Concepts.ConversionCore.WitnessCompile.ReflectionsQueryProgram

@[expose] public section


/-! # The original random-power schedule

Algorithm 2 of 1005.1601v1 samples powers from one through `ceil (100 * W)`.
The resolvent estimate proves the false-input bound at this exact horizon.
The circuit below implements its interference readout with all oracle calls paid.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Papers.ReflectQuery10.MainResults.RandSchedule
open Qatlib.Concepts.QueryComplexity.Reflections
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

variable {X : Type} [Fintype X] [DecidableEq X] {n m : ℕ}

/-- The paper's random-power horizon is positive for every allowed witness budget. -/
theorem horizonPos (W : ℝ) (hW : 1 ≤ W) : 0 < Nat.ceil (100 * W) := by
  apply Nat.ceil_pos.mpr
  linarith

/-- At the exact source horizon, the false-input interference probability is at most `3/5`. -/
theorem falseMean (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (hd : SourceDualFeasible input f v W)
    (hW : 1 ≤ W) (Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ)
    (hΔ : IsOrthogonalProjector Δ)
    (hk : ∀ z, adjacency input f v W *ᵥ z = 0 ↔ Δ *ᵥ z = z)
    (x : X) (hx : f x = false) :
    reflectionsPowerMean (Nat.ceil (100 * W)) (twoReflectionUnitary input f x Δ)
      (Ket (Sum.inr (Sum.inl ()))) ≤ (3 / 5 : ℝ) := by
  obtain ⟨η, he, hn⟩ := reflections_false_root_inverse input f v W hd hW Δ hΔ hk x hx
  have hp := (twoReflectionConstruction X n m input f v W).2.1 x
  have hU := reflections_product_unitary _ _ hp hΔ
  have hτ := horizonPos W hW
  have hm := reflections_inverse_power_mean_upper (twoReflectionUnitary input f x Δ) hU
    η (Ket (Sum.inr (Sum.inl ()))) (normalized_ket _) he (Nat.ceil (100 * W)) hτ
  have hnorm : ‖toEuclidean_fromVec η‖ ≤ 2 * W := by
    rw [← norm_toEuclidean_fromVec_sq] at hn
    nlinarith [norm_nonneg (toEuclidean_fromVec η), sq_nonneg W]
  have hcost : 100 * W ≤ (Nat.ceil (100 * W) : ℝ) := Nat.le_ceil _
  have htail : ‖toEuclidean_fromVec η‖ / (Nat.ceil (100 * W) : ℝ) ≤ (1 / 10 : ℝ) := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hτ)).mpr
    nlinarith
  linarith

/-- Algorithm 2 has a genuine unitary query circuit at its original clock, with true
probability at least `9/10`, false probability at most `3/5`, and explicit paid costs. -/
theorem sourceTrial (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (hd : SourceDualFeasible input f v W)
    (hW : 1 ≤ W) (hn : 0 < n)
    (Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ)
    (hΔ : IsOrthogonalProjector Δ)
    (hk : ∀ z, adjacency input f v W *ᵥ z = 0 ↔ Δ *ᵥ z = z) :
    ∃ C : Circuit ((Fin n × Bool) ×
        ((Fin (Nat.ceil (100 * W)) × Bool) × Vertex X f n m)),
      IsUnitaryCircuit C ∧ QueryCount C = 2 * Nat.ceil (100 * W) ∧
      GateCount C = 2 * Nat.ceil (100 * W) + 2 ∧
      ∀ x, let S := Finset.univ.filter (fun p : (Fin n × Bool) ×
          ((Fin (Nat.ceil (100 * W)) × Bool) × Vertex X f n m) => p.2.1.2 = false)
        let r := Ket ((⟨0, hn⟩, false),
          ((⟨0, horizonPos W hW⟩, false), Sum.inr (Sum.inl ())))
        Run (workspaceBitOracle (input x)) C r =
          reflectionsFrame (reflectionsVertexAddress (m := m) f hn)
            (reflectionsTrialOutput (Nat.ceil (100 * W)) (twoReflectionUnitary input f x Δ)
              (Ket (Sum.inr (Sum.inl ())))) ∧
        if f x then (9 / 10 : ℝ) ≤ MeasureProb (Run (workspaceBitOracle (input x)) C r) S
        else MeasureProb (Run (workspaceBitOracle (input x)) C r) S ≤ (3 / 5 : ℝ) := by
  let τ := Nat.ceil (100 * W)
  have hτ : 0 < τ := horizonPos W hW
  let addr := reflectionsVertexAddress (m := m) f hn
  let root : Vertex X f n m := Sum.inr (Sum.inl ())
  let j : (Fin τ × Bool) × Vertex X f n m := ((⟨0, hτ⟩, false), root)
  let S : Finset ((Fin n × Bool) × ((Fin τ × Bool) × Vertex X f n m)) :=
    Finset.univ.filter (fun p => p.2.1.2 = false)
  obtain ⟨C, hC, hQ, hG, hrun⟩ := reflections_actual_trial X n m τ f hn hτ input Δ hΔ
  refine ⟨C, hC, hQ, hG, ?_⟩
  intro x
  refine ⟨hrun x, ?_⟩
  change if f x then (9 / 10 : ℝ) ≤
    MeasureProb (Run (workspaceBitOracle (input x)) C (Ket ((⟨0, hn⟩, false), j))) S
    else MeasureProb (Run (workspaceBitOracle (input x)) C
      (Ket ((⟨0, hn⟩, false), j))) S ≤ (3 / 5 : ℝ)
  have he := reflections_frame_readout addr
    (reflectionsTrialOutput τ (twoReflectionUnitary input f x Δ) (Ket root))
    (Finset.univ.filter (fun p : (Fin τ × Bool) × Vertex X f n m => p.1.2 = false))
  have hs : Finset.univ.filter
      (fun p : (Fin n × Bool) × ((Fin τ × Bool) × Vertex X f n m) =>
        p.2 ∈ Finset.univ.filter (fun q => q.1.2 = false)) = S := by
    ext p
    simp [S]
  rw [hs, reflections_trial_born] at he
  rw [hrun, he]
  cases hx : f x
  · simp only [Bool.false_eq_true, ite_false]
    exact falseMean input f v W hd hW Δ hΔ hk x hx
  · simp only [ite_true]
    exact reflections_true_power_mean input f v W hd hW Δ hΔ hk x hx τ hτ

end Qatlib.Papers.ReflectQuery10.MainResults.RandSchedule
