/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AbelianStabil95.AbelianStabil.PrecisionBound.Lemmas3To5
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

@[expose] public section

/-!
# Euclidean state-level form of the mixed-word error

Fixed source: [Kitaev 1995, Abelian Stabilizer Problem](https://arxiv.org/abs/quant-ph/9511026),
Lemma 3 (printed p. 12).  The library's operator-norm bridge between a mixed operation word
and its implemented matrix is transported to individual normalized states, measured in the
true complex Euclidean norm of the amplitude-vector representation — never the weak
pointwise maximum norm.  A uniform constant `1` is placed outside all quantifiers, and the
register is required to hold at least one qubit so the state space is non-degenerate.

## Main statements

* `lemma3_euclidean_state_error`: on any normalized state, the Euclidean distance between the
  implemented word and the exact ideal word is at most the word's precision budget.

## References

* [Kitaev1995], Lemma 3
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.AbelianStabil95.PrecisionExt.Lemma3EuclideanState

open scoped Matrix Matrix.Norms.L2Operator

open Qatlib.Papers.AbelianStabil95.AbelianStabil.PrecisionBound
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.NumericalWord.MixedWordError
open Qatlib.Foundations.PureStateMath

/-- On any normalized amplitude vector, the implemented mixed word and its exact ideal differ
by at most the precision budget, measured in the Euclidean norm.  The uniform constant `1` is
fixed before all parameters; the register length `n` is required to be positive so the state
space is non-degenerate.  This is the state-level form of
[Kitaev1995], Lemma 3, for the library's mixed operation words: the bound is
uniform in the word, the oracles, and the state, with no dimension-dependent constant. -/
theorem lemma3_euclidean_state_error :
    ∃ uniformConstant : ℝ, 0 < uniformConstant ∧
      ∀ (n : ℕ), 0 < n → ∀ (w : ℕ) (hw : w ≤ n) (S : Type) [DecidableEq S]
        (O : S → Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S))
        (_hv : ValidControls W) (_hO : ∀ s, O s ∈ Matrix.unitaryGroup (Reg w) ℂ)
        (ψ : QState (Reg n)), Normalized ψ →
        ‖(EuclideanSpace.equiv (Reg n) ℂ).symm
            ((word hw O W - mixedWordMatrix hw O W) *ᵥ toEuclidean_fromVec ψ)‖
          ≤ uniformConstant * budget W := by
  refine ⟨1, one_pos, fun n _ w hw S _ O W hv hO ψ hψ => ?_⟩
  have hmul := Matrix.l2_opNorm_mulVec
    (word hw O W - mixedWordMatrix hw O W) (toEuclidean_fromVec ψ)
  have hop := lemma3_bridge_mixedWord hw S O W hv hO
  have hψ1 : ‖toEuclidean_fromVec ψ‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ
  have hbudget : (0 : ℝ) ≤ budget W := by
    unfold budget
    refine List.sum_nonneg fun x hx => ?_
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
    exact pow_nonneg (by norm_num) k
  calc ‖(EuclideanSpace.equiv (Reg n) ℂ).symm
          ((word hw O W - mixedWordMatrix hw O W) *ᵥ toEuclidean_fromVec ψ)‖
      ≤ ‖word hw O W - mixedWordMatrix hw O W‖ * ‖toEuclidean_fromVec ψ‖ := hmul
    _ ≤ budget W * 1 := mul_le_mul hop hψ1.le (norm_nonneg _) hbudget
    _ = budget W := mul_one _
    _ = 1 * budget W := (one_mul _).symm

end Qatlib.Papers.AbelianStabil95.PrecisionExt.Lemma3EuclideanState
