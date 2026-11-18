/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.SourceModel
public import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureKraus

@[expose] public section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators

open Matrix
open Qatlib.Papers.QShannonWilde11.MainResults.Model
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring

namespace Qatlib.Papers.QShannonWilde11.MainResults.StatesChannels

/-- Choi--Kraus with at most input-dimension times output-dimension operators,
transporting the actual public Choi factorization to the original paper model. -/
theorem completely_positive_trace_preserving_iff_exists_bounded_kraus {a b : ℕ}
    (T : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ) :
    (CompletelyPositive T ∧ TracePreserving T) ↔
      ∃ (ι : Type) (hι : Fintype ι) (K : ι → Matrix (Fin b) (Fin a) ℂ),
        @IsKraus a b T ι hι K ∧ @Fintype.card ι hι ≤ a * b := by
  classical
  constructor
  · rintro ⟨hCP, hTP⟩
    obtain ⟨n, K, hK, hn⟩ := (clause2_conj2 T).mp hCP
    refine ⟨Fin n, inferInstance, K, ⟨hK, krausComplete_of_tracePreserving hK hTP⟩, ?_⟩
    simpa using hn
  · rintro ⟨ι, hι, K, hK, _⟩
    let : Fintype ι := hι
    obtain ⟨hform, hcomplete⟩ := hK
    have hmap : T = ∑ j, conjBranch (K j) := by
      apply LinearMap.ext
      intro X
      simpa only [LinearMap.sum_apply, conjBranch_apply] using hform X
    constructor
    · rw [hmap]
      exact CompletelyPositive.sum fun j _ => completelyPositive_conjBranch (K j)
    · intro X
      rw [hform X]
      calc
        Matrix.trace (∑ j, K j * X * (K j)ᴴ) =
            Matrix.trace ((∑ j, (K j)ᴴ * K j) * X) := by
          rw [Matrix.trace_sum, Finset.sum_mul, Matrix.trace_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [Matrix.trace_mul_comm (K j * X) (K j)ᴴ, ← Matrix.mul_assoc]
        _ = Matrix.trace X := by rw [hcomplete, Matrix.one_mul]

/-- The Hilbert--Schmidt adjoint of a finite quantum channel is completely
positive and unital, using its actual finite Kraus representation. -/
theorem channel_adjoint_completely_positive_and_unital {a b : ℕ}
    (N : QuantumChannel a b)
    (M : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ)
    (hM : IsAdjoint N.map M) :
    CompletelyPositive M ∧ M 1 = 1 := by
  classical
  obtain ⟨n, K, hK, hcomplete, _⟩ := (clause2_conj11 N).2
  have hKM : KrausForm M (fun j => (K j)ᴴ) := by
    intro Y
    simp only [Matrix.conjTranspose_conjTranspose]
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro X
    have hadj := hM Xᴴ Y
    rw [Matrix.conjTranspose_conjTranspose] at hadj
    calc
      Matrix.trace (X * M Y) = Matrix.trace ((N.map Xᴴ)ᴴ * Y) := hadj.symm
      _ = Matrix.trace (X * ∑ j, (K j)ᴴ * Y * K j) := by
        rw [hK Xᴴ]
        simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose]
        rw [Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum, Matrix.trace_sum]
        apply Finset.sum_congr rfl
        intro j _
        calc
          Matrix.trace (K j * (X * (K j)ᴴ) * Y) =
              Matrix.trace (K j * (X * ((K j)ᴴ * Y))) := by
            simp only [Matrix.mul_assoc]
          _ = Matrix.trace ((X * ((K j)ᴴ * Y)) * K j) := Matrix.trace_mul_comm _ _
          _ = Matrix.trace (X * ((K j)ᴴ * Y * K j)) := by
            simp only [Matrix.mul_assoc]
  refine ⟨completelyPositive_of_krausForm hKM, ?_⟩
  rw [hKM 1]
  simp only [Matrix.mul_one, Matrix.conjTranspose_conjTranspose]
  exact hcomplete

end Qatlib.Papers.QShannonWilde11.MainResults.StatesChannels
