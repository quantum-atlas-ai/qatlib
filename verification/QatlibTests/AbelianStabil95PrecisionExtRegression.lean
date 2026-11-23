module

public import Qatlib.Papers.AbelianStabil95.PrecisionExt.Lemma3EuclideanState
public import Qatlib.Papers.AbelianStabil95.PrecisionExt.Lemma5CleanInput
public import Qatlib.Papers.AbelianStabil95.PrecisionExt.PartialChain

@[expose] public section

/-!
# Consumer regression for the AbelianStabil95 precision increment

This ordinary-module consumer specializes the new Euclidean state bound, the source-form
swap instantiation, and the finite chain bound to concrete non-degenerate instances: a
two-qubit register with a numerical controlled phase on the all-ones input, the two-qubit
wire swap with precision `3`, and three-step identity and negation chains on the
two-dimensional complex Euclidean space.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace QatlibTests.AbelianStabil95PrecisionExtRegression

open scoped Matrix Matrix.Norms.L2Operator BigOperators

open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.NumericalWord.MixedWordError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Papers.AbelianStabil95.AbelianStabil.PrecisionBound
open Qatlib.Papers.AbelianStabil95.PrecisionExt.Lemma3EuclideanState
open Qatlib.Papers.AbelianStabil95.PrecisionExt.Lemma5CleanInput
open Qatlib.Papers.AbelianStabil95.PrecisionExt.PartialChain

/-- A controlled phase at precision `3` acts on the all-ones basis input, giving the explicit
Euclidean bound `uniformConstant * 2⁻³` from `lemma3_euclidean_state_error`. -/
theorem euclidean_state_error_controlled_phase :
    ∃ C : ℝ, 0 < C ∧
      ‖(EuclideanSpace.equiv (Reg 2) ℂ).symm
          ((word (le_refl 2) unitOracle [.known (.cp 0 1 3 false) 3] -
            mixedWordMatrix (le_refl 2) unitOracle [.known (.cp 0 1 3 false) 3]) *ᵥ
            toEuclidean_fromVec (Ket (fun _ : Fin 2 => true)))‖ ≤ C * ((1 : ℝ) / 8) := by
  obtain ⟨C, hC, hmodel⟩ := lemma3_euclidean_state_error
  refine ⟨C, hC, ?_⟩
  have h := hmodel 2 (by norm_num) 2 (le_refl 2) Unit unitOracle
    [.known (.cp 0 1 3 false) 3]
    (by intro s hs; rcases List.mem_singleton.mp hs with rfl; exact True.intro)
    unitOracle_unitary (Ket (fun _ : Fin 2 => true)) (normalized_ket _)
  have hb : budget ([.known (.cp 0 1 3 false) 3] : List (MixedStep 2 2 Unit))
      = (1 : ℝ) / 8 := by
    simp [budget, knownPrecs]
    norm_num
  rwa [hb] at h

/-- A concrete consumer of `lemma5_swap_source_form` on the two-qubit swap with precision `3`,
dyadic tolerance `δ = 2⁻³`, zero target error, and the clean basis input `Ket x`.  The ideal
correctness hypothesis holds with certainty, so the implemented word answers the swapped
register within `2 * L * 2⁻³` of certainty. -/
theorem swap_source_form_two_qubits (x : Reg 2) :
    ∃ C : ℝ, 0 < C ∧
      |MeasureProb (ApplyGate (word (le_refl 2) unitOracle (swapTwoWord 3)) (Ket x))
          {swapTwoFun x} - 1| ≤ 0 + C * ((swapTwoWord 3).length : ℝ) * ((1 : ℝ) / 8) := by
  obtain ⟨C, hC, hmodel⟩ := lemma5_swap_source_form
  refine ⟨C, hC, ?_⟩
  have hideal : |MeasureProb
      (ApplyGate (mixedWordMatrix (le_refl 2) unitOracle (swapTwoWord 3)) (Ket x))
      {swapTwoFun x} - 1| ≤ (0 : ℝ) := by
    rw [swapTwoWord_ideal_correct 3 x]
    norm_num
  have hδ0 : (0 : ℝ) ≤ (1 / 8 : ℝ) := by norm_num
  have hδ : ((2 : ℝ)⁻¹) ^ (3 : ℕ) ≤ (1 / 8 : ℝ) := by norm_num
  have hε : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
  exact hmodel 3 (1 / 8 : ℝ) 0 hδ0 hδ hε x hideal

/-- The identity partial operator on the full two-dimensional complex Euclidean space, used as
a concrete non-degenerate chain step. -/
noncomputable def idTopOp₂ : PartialOp (EuclideanSpace ℂ (Fin 2)) where
  dom := ⊤
  cod := ⊤
  iso := LinearIsometryEquiv.refl ℂ ↥(⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2)))

/-- Negation as a partial operator on the entire two-dimensional complex Euclidean space. -/
noncomputable def negTopOp₂ : PartialOp (EuclideanSpace ℂ (Fin 2)) where
  dom := ⊤
  cod := ⊤
  iso := LinearIsometryEquiv.neg ℂ

/-- The displacement between identity and negation is at most twice the input norm. -/
theorem negTopOp₂_represents_identity :
    PartialOp.Represents idTopOp₂ negTopOp₂ 2 := by
  refine ⟨le_rfl, le_rfl, ?_⟩
  intro ξ
  change ‖ξ.1 - (-ξ.1)‖ ≤ 2 * ‖ξ.1‖
  simpa only [sub_neg_eq_add, two_mul] using norm_add_le ξ.1 ξ.1

/-- Compare three identity steps with three negation steps on the two-dimensional complex
Euclidean space through `partialChain_error`, with per-step tolerance two. -/
theorem partial_chain_three_negation_steps :
    ∃ C : ℝ, 0 < C ∧
      ∀ ξ : ↥(⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2))),
        ‖chainApplyLM (fun _ : Fin 3 => idTopOp₂) (fun _ => le_rfl) ξ -
            chainApplyLM (fun _ : Fin 3 => negTopOp₂) (fun _ => le_rfl)
              ⟨ξ.1, negTopOp₂_represents_identity.dom_le ξ.2⟩‖
          ≤ C * 6 * ‖ξ.1‖ := by
  obtain ⟨C, hC, hmodel⟩ := partialChain_error
  have hsum : (∑ _i : Fin 3, (2 : ℝ)) = 6 := by
    rw [Fin.sum_univ_three]
    norm_num
  refine ⟨C, hC, fun ξ => ?_⟩
  have h := hmodel 2 (fun _ : Fin 3 => idTopOp₂) (fun _ : Fin 3 => negTopOp₂)
    (fun _ : Fin 3 => 2) (fun _ => negTopOp₂_represents_identity)
    (fun _ => le_rfl) (fun _ => le_rfl) ξ
  rwa [hsum] at h

end QatlibTests.AbelianStabil95PrecisionExtRegression
