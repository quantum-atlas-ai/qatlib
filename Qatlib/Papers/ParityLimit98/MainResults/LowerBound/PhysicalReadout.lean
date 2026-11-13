/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParityLimit98.MainResults.LowerBound.ActualBalance
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws

/-!
# Physical projective readout for parity

This module relates `projectorAcceptance` to projective branch mass and, for orthogonal
projectors, to Born expectation. For normalized unitary executions it proves conservation and
probability bounds, then derives the parity query lower bound and rigidity using
`projectorCorrectness`. These results support the parity analysis of [FarhiEtAl1998].

## Main statements

* `physical_positive_bias_query_bound`: A normalized unitary circuit whose orthogonal-projector
  readout has a uniform positive parity bias satisfies `n ≤ 2 * QueryCount C`.
* `physical_half_rigidity`: Below the parity query threshold, correctness at least one half on
  every input forces both complementary projector acceptance values to equal one half.

## References

* [Farhi et al., 1998][FarhiEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ParityLimit98.MainResults.LowerBound
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.QueryWordCore.QueryMachinery

/-- The source bit oracle tensored with the workspace identity is unitary. See [Farhi et al.,
1998][FarhiEtAl1998]. -/
theorem source_oracle_unitary {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (f : Fin n → Bool) :
    TensorGate (BitOracleOn f) (1 : Matrix W W ℂ) ∈
      Matrix.unitaryGroup (PolynomialWorkspace (Fin n) W) ℂ := by
  apply tensorGate_unitary
  · apply permMatrix_unitary
    rintro ⟨x,b⟩
    cases h : f x <;> cases b <;> simp [BitFlip, h]
  · exact (Matrix.unitaryGroup W ℂ).one_mem

/-- A unitary circuit with the source bit oracle preserves normalization of its initial state. -/
theorem source_run_normalized {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (hC : IsUnitaryCircuit C)
    (ψ : QState (PolynomialWorkspace (Fin n) W)) (hn : Normalized ψ) (f : Fin n → Bool) :
    Normalized (Run (TensorGate (BitOracleOn f) 1) C ψ) :=
  hC.normalized_run (source_oracle_unitary f) hn

/-- Projector acceptance is the true-branch mass of the final state for the matrix `P`. -/
theorem projectorAcceptance_branch {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (ψ : QState (PolynomialWorkspace (Fin n) W))
    (P : Matrix (PolynomialWorkspace (Fin n) W) (PolynomialWorkspace (Fin n) W) ℂ)
    (f : Fin n → Bool) :
    projectorAcceptance C ψ P f =
      ProjectiveBranchMass P true (Run (TensorGate (BitOracleOn f) 1) C ψ) := rfl

/-- For an orthogonal projector, acceptance equals the real part of its expectation in the final
state. See [Farhi et al., 1998][FarhiEtAl1998]. -/
theorem projectorAcceptance_expectation {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (ψ : QState (PolynomialWorkspace (Fin n) W))
    (P : Matrix (PolynomialWorkspace (Fin n) W) (PolynomialWorkspace (Fin n) W) ℂ)
    (hP : IsOrthogonalProjector P) (f : Fin n → Bool) :
    projectorAcceptance C ψ P f =
      (Inner (Run (TensorGate (BitOracleOn f) 1) C ψ)
        (ApplyGate P (Run (TensorGate (BitOracleOn f) 1) C ψ))).re := by
  let ξ := Run (TensorGate (BitOracleOn f) 1) C ψ
  have hp : Inner (ApplyGate P ξ) (ApplyGate P ξ) = Inner ξ (ApplyGate P ξ) := by
    have hPP : Pᴴ * P = P := by rw [show Pᴴ = P from hP.2]; exact hP.1
    simp only [Qatlib.Foundations.PureStateMath.Inner, ApplyGate]
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hPP,
      Matrix.dotProduct_mulVec]
  rw [← hp, inner_self, ← Complex.ofReal_sum]
  rfl

/-- For a normalized unitary execution, acceptance for an orthogonal projector and its
complement sums to one. -/
theorem projectorAcceptance_conservation {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (hC : IsUnitaryCircuit C)
    (ψ : QState (PolynomialWorkspace (Fin n) W)) (hn : Normalized ψ)
    (P : Matrix (PolynomialWorkspace (Fin n) W) (PolynomialWorkspace (Fin n) W) ℂ)
    (hP : IsOrthogonalProjector P) (f : Fin n → Bool) :
    projectorAcceptance C ψ P f + projectorAcceptance C ψ (1 - P) f = 1 := by
  have h := projectiveBranchMass_add hP (Run (TensorGate (BitOracleOn f) 1) C ψ)
  rw [measureProb_univ (source_run_normalized C hC ψ hn f)] at h
  change projectorAcceptance C ψ (1 - P) f + projectorAcceptance C ψ P f = 1 at h
  linarith

/-- For a normalized unitary execution and an orthogonal projector, acceptance lies in the
interval from zero to one. -/
theorem projectorAcceptance_range {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (hC : IsUnitaryCircuit C)
    (ψ : QState (PolynomialWorkspace (Fin n) W)) (hn : Normalized ψ)
    (P : Matrix (PolynomialWorkspace (Fin n) W) (PolynomialWorkspace (Fin n) W) ℂ)
    (hP : IsOrthogonalProjector P) (f : Fin n → Bool) :
    0 ≤ projectorAcceptance C ψ P f ∧ projectorAcceptance C ψ P f ≤ 1 := by
  have hp : 0 ≤ projectorAcceptance C ψ P f := measureProb_nonneg _ _
  have hq : 0 ≤ projectorAcceptance C ψ (1 - P) f := measureProb_nonneg _ _
  have h := projectorAcceptance_conservation C hC ψ hn P hP f
  exact ⟨hp, by linarith⟩

/-- The mass of the correct parity outcome, using `P` for even inputs and its complement for odd
inputs. -/
def projectorCorrectness {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (ψ : QState (PolynomialWorkspace (Fin n) W))
    (P : Matrix (PolynomialWorkspace (Fin n) W) (PolynomialWorkspace (Fin n) W) ℂ)
    (f : Fin n → Bool) : ℝ :=
  if parityOddB f then projectorAcceptance C ψ (1 - P) f else projectorAcceptance C ψ P f

/-- For a normalized unitary execution and an orthogonal projector, correctness is one half plus
the parity sign times centered acceptance. -/
theorem projectorCorrectness_centered {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (hC : IsUnitaryCircuit C)
    (ψ : QState (PolynomialWorkspace (Fin n) W)) (hn : Normalized ψ)
    (P : Matrix (PolynomialWorkspace (Fin n) W) (PolynomialWorkspace (Fin n) W) ℂ)
    (hP : IsOrthogonalProjector P) (f : Fin n → Bool) :
    projectorCorrectness C ψ P f = 1 / 2 + boolSign f * (projectorAcceptance C ψ P f - 1 / 2) := by
  have h := projectorAcceptance_conservation C hC ψ hn P hP f
  rw [projectorCorrectness, boolSign_eq_ite]
  cases parityOddB f <;> simp only [Bool.false_eq_true, if_false, if_true, one_mul, neg_one_mul] <;>
    linarith

/-- If `2 * QueryCount C < n`, the uniform average correctness of a normalized unitary circuit
with orthogonal-projector readout is one half. See [Farhi et al., 1998][FarhiEtAl1998]. -/
theorem projector_uniform_correct_half {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (hC : IsUnitaryCircuit C)
    (ψ : QState (PolynomialWorkspace (Fin n) W)) (hn : Normalized ψ)
    (P : Matrix (PolynomialWorkspace (Fin n) W) (PolynomialWorkspace (Fin n) W) ℂ)
    (hP : IsOrthogonalProjector P) (hk : 2 * QueryCount C < n) :
    (∑ f : Fin n → Bool, projectorCorrectness C ψ P f) / (2 : ℝ) ^ n = 1 / 2 := by
  simp_rw [projectorCorrectness_centered C hC ψ hn P hP]
  rw [Finset.sum_add_distrib, projector_centered_sum C ψ P hk]
  simp only [add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

/-- A normalized unitary circuit whose orthogonal-projector readout has a uniform positive
parity bias satisfies `n ≤ 2 * QueryCount C`. See [Farhi et al., 1998][FarhiEtAl1998]. -/
theorem physical_positive_bias_query_bound {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (hC : IsUnitaryCircuit C)
    (ψ : QState (PolynomialWorkspace (Fin n) W)) (hn : Normalized ψ)
    (P : Matrix (PolynomialWorkspace (Fin n) W) (PolynomialWorkspace (Fin n) W) ℂ)
    (hP : IsOrthogonalProjector P) (ε : ℝ) (hε : 0 < ε)
    (hs : ∀ f, 1 / 2 + ε ≤ projectorCorrectness C ψ P f) :
    n ≤ 2 * QueryCount C := by
  apply projector_positive_bias_query_bound C ψ P ε hε
  · intro f hf
    simpa only [projectorCorrectness, hf, Bool.false_eq_true, if_false] using hs f
  · intro f hf
    have h := hs f
    simp only [projectorCorrectness, hf, if_true] at h
    have hc := projectorAcceptance_conservation C hC ψ hn P hP f
    linarith

/-- Below the parity query threshold, correctness at least one half on every input forces both
complementary projector acceptance values to equal one half. See [Farhi et al.,
1998][FarhiEtAl1998]. -/
theorem physical_half_rigidity {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (hC : IsUnitaryCircuit C)
    (ψ : QState (PolynomialWorkspace (Fin n) W)) (hn : Normalized ψ)
    (P : Matrix (PolynomialWorkspace (Fin n) W) (PolynomialWorkspace (Fin n) W) ℂ)
    (hP : IsOrthogonalProjector P) (hk : 2 * QueryCount C < n)
    (hs : ∀ f, 1 / 2 ≤ projectorCorrectness C ψ P f) :
    ∀ f, projectorAcceptance C ψ P f = 1 / 2 ∧ projectorAcceptance C ψ (1 - P) f = 1 / 2 := by
  have hhalf := projector_half_rigidity C ψ P hk (fun f hf => by
    simpa only [projectorCorrectness, hf, Bool.false_eq_true, if_false] using hs f) (fun f hf => by
      have h := hs f
      simp only [projectorCorrectness, hf, if_true] at h
      have hc := projectorAcceptance_conservation C hC ψ hn P hP f
      linarith)
  intro f
  exact ⟨hhalf f, by linarith [projectorAcceptance_conservation C hC ψ hn P hP f, hhalf f]⟩

/-- Acceptance for the coordinate projector of `E` equals the measurement mass of `E` in the
final state. -/
theorem projectorAcceptance_event {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (ψ : QState (PolynomialWorkspace (Fin n) W))
    (E : Finset (PolynomialWorkspace (Fin n) W)) (f : Fin n → Bool) :
    projectorAcceptance C ψ (Projector E) f =
      MeasureProb (Run (TensorGate (BitOracleOn f) 1) C ψ) E := by
  exact sum_normSq_collapse _ _

/-- The complement of a coordinate projector is the coordinate projector of the complementary
event. -/
theorem source_projector_compl {H : Type} [Fintype H] [DecidableEq H] (E : Finset H) :
    1 - Projector E = Projector (Finset.univ \ E) := by
  ext i j
  by_cases h : i = j
  · subst j
    by_cases hi : i ∈ E <;> simp [Projector, hi]
  · simp [Projector, h]

/-- Correctness for the coordinate projector of `E` is the measurement mass of `E` on even
inputs and of its complement on odd inputs. -/
theorem projectorCorrectness_event {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (ψ : QState (PolynomialWorkspace (Fin n) W))
    (E : Finset (PolynomialWorkspace (Fin n) W)) (f : Fin n → Bool) :
    projectorCorrectness C ψ (Projector E) f =
      MeasureProb (Run (TensorGate (BitOracleOn f) 1) C ψ)
        (if parityOddB f then Finset.univ \ E else E) := by
  rw [projectorCorrectness]
  split_ifs
  · rw [source_projector_compl, projectorAcceptance_event]
  · rw [projectorAcceptance_event]

end Qatlib.Papers.ParityLimit98.MainResults.LowerBound
