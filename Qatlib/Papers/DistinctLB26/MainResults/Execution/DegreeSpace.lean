/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.DistinctLB26.MainResults.Execution.BornSuccess
public import Qatlib.Papers.DistinctLB26.MainResults.Execution.FixedCorrect

@[expose] public section

/-!
# The actual degree subspace reached by an executed oracle algorithm

The subspace is defined by Fourier support and transported through the actual
normalized Fourier readout. Every final column belongs to it because each
executed query changes one Fourier coordinate. A fixed correctness-projector
anti-concentration estimate on this concrete subspace therefore bounds the
actual uniform Born success of every such algorithm.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DistinctLB26.MainResults.Execution

variable {n q : ℕ} [NeZero q] {W : Type*} [Fintype W]

/-- The normalized computational-input Fourier decoder as a complex linear map. -/
def decodeLinear : EuclideanSpace ℂ (Label n q) →ₗ[ℂ] EuclideanSpace ℂ (Label n q) where
  toFun := decode
  map_add' v w := by
    ext x
    simp only [decode_apply, PiLp.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    ext x
    simp only [decode_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro σ _
    ring

/-- The Fourier label subspace of degree at most the specified query count. -/
def degreeSpace (t : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Label n q)) where
  carrier := {v | ∀ σ : Label n q, t < (support σ).card → v σ = 0}
  zero_mem' := by intro σ _; rfl
  add_mem' := by
    intro v w hv hw σ hσ
    simp only [PiLp.add_apply, hv σ hσ, hw σ hσ, zero_add]
  smul_mem' := by
    intro c v hv σ hσ
    simp only [PiLp.smul_apply, smul_eq_mul, hv σ hσ, mul_zero]

/-- The actual computational-input image of the Fourier degree subspace. -/
def computationalSpace (t : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Label n q)) :=
  (degreeSpace t).map decodeLinear

omit [NeZero q] [Fintype W] in
/-- Preparing a common work state without input access gives zero Fourier degree. -/
theorem zeroInput_support (φ : Local n q W) : Supported 0 (zeroInput φ) := by
  intro σ a hnonzero
  have hσ : σ = 0 := by
    by_contra hσ
    exact hnonzero (by simp [zeroInput, hσ])
  rw [hσ]
  simp [support]

omit [NeZero q] [Fintype W] in
/-- Every fixed-work column of a degree-supported joint vector has that same degree. -/
theorem degree_column {t : ℕ} {ψ : Joint n q W} (hψ : Supported t ψ)
    (a : Work n q W) : inputColumn ψ a ∈ degreeSpace t := by
  intro σ hlarge
  by_contra hnonzero
  exact (not_le_of_gt hlarge) (hψ σ a hnonzero)

omit [Fintype W] in
/-- Fourier readout transports every column into the concrete computational degree space. -/
theorem readout_strong {t : ℕ} {ψ : Joint n q W} (hψ : Supported t ψ) :
    FixedCorrect.Strong (computationalSpace t) (readout ψ) := by
  intro a
  exact ⟨inputColumn ψ a, degree_column hψ a, rfl⟩

/-- The final state of any executed query program lies in its counted degree subspace. -/
theorem algorithm_strong (prog : List (Instr n q W)) (φ : Local n q W) :
    FixedCorrect.Strong (computationalSpace (queryCount prog))
      (readout (execute prog (zeroInput φ))) := by
  apply readout_strong
  simpa using execute_support prog (zeroInput_support φ)

/-- The zero Fourier input embeds the common work state without changing its norm. -/
theorem zeroInput_norm (φ : Local n q W) : ‖zeroInput φ‖ = ‖φ‖ := by
  classical
  have hs : ‖zeroInput φ‖ ^ 2 = ‖φ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp [zeroInput, apply_ite]
  nlinarith [norm_nonneg (zeroInput φ), norm_nonneg φ]

/-- A fixed-projector estimate on the concrete query-degree space bounds actual algorithm success. -/
theorem actual_anti_bound {R : Type*} (M : R → Label n q → Prop)
    [∀ r, DecidablePred (M r)] (γ : ℝ) (prog : List (Instr n q W))
    (hanti : FixedCorrect.AntiConc M γ (computationalSpace (queryCount prog)))
    (φ : Local n q W) (hφ : ‖φ‖ = 1) (answer : Work n q W → R) :
    averageSuccess (fun x a => M (answer a) x) prog φ ≤ γ ^ 2 := by
  classical
  let ψ := readout (execute prog (zeroInput φ))
  have hnorm : ‖ψ‖ = 1 := by
    dsimp [ψ]
    rw [readout_norm, execute_norm, zeroInput_norm, hφ]
  have hb := FixedCorrect.success_bound M γ (computationalSpace (queryCount prog)) hanti
    ψ (algorithm_strong prog φ) answer (LinearIsometryEquiv.refl ℂ _)
  have heq : jointSuccess (fun x a => M (answer a) x) prog φ =
      FixedCorrect.successProb M answer (LinearIsometryEquiv.refl ℂ _) ψ := by
    have hr : FixedCorrect.rotate (LinearIsometryEquiv.refl ℂ _) ψ = ψ := by
      ext z
      rfl
    unfold jointSuccess FixedCorrect.successProb
    rw [hr, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro z _
    by_cases h : M (answer z.2) z.1 <;> simp [h, FixedCorrect.successful, ψ]
  rw [← joint_average, heq]
  simpa only [hnorm, one_pow, mul_one] using hb

end Qatlib.Papers.DistinctLB26.MainResults.Execution
