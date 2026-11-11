/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic.State
import QuantumInfo.ForMathlib.Isometry

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic

/-! An imperfect public inverse never licenses discarding its residual.
The actual rectangular basis map below is isometric for every guess,
including a completely wrong one and noninjective forward labels.
No running-time or source-recall hypothesis is encoded as a conclusion. -/

set_option autoImplicit false
namespace Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources

open Matrix
open scoped BigOperators Classical

variable {K L : Type} [AddGroup K]

/-- Definition of pqc Residual Encode in the Modular Fourier construction. -/
def pqcResidualEncode (f : K → L) (guess : L → K) (k : K) : L × K :=
  (f k, k-guess (f k))

/-- Definition of pqc Residual Recover in the Modular Fourier construction. -/
def pqcResidualRecover (guess : L → K) (z : L × K) : K :=
  z.2+guess z.1

/-- The actual finite-label construction satisfies `pqc_residual_recover_encode` with all displayed hypotheses. -/
theorem pqc_residual_recover_encode (f : K → L) (guess : L → K) (k : K) :
    pqcResidualRecover guess (pqcResidualEncode f guess k) = k := by
  simp [pqcResidualRecover, pqcResidualEncode]

/-- The actual finite-label construction satisfies `pqc_residual_encode_injective` with all displayed hypotheses. -/
theorem pqc_residual_encode_injective (f : K → L) (guess : L → K) :
    Function.Injective (pqcResidualEncode f guess) :=
  (show Function.LeftInverse (pqcResidualRecover guess) (pqcResidualEncode f guess) from
    pqc_residual_recover_encode f guess).injective

/-- The actual finite-label construction satisfies `pqc_residual_zero_iff` with all displayed hypotheses. -/
theorem pqc_residual_zero_iff (f : K → L) (guess : L → K) (k : K) :
    (pqcResidualEncode f guess k).2 = 0 ↔ guess (f k) = k := by
  simp [pqcResidualEncode, sub_eq_zero, eq_comm]

section Finite
variable [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]

/-- Definition of pqc Residual Frame in the Modular Fourier construction. -/
noncomputable def pqcResidualFrame (f : K → L) (guess : L → K) :
    Matrix (L × K) K ℂ :=
  (1 : Matrix (L × K) (L × K) ℂ).submatrix id (pqcResidualEncode f guess)

/-- The actual finite-label construction satisfies `pqc_residual_frame_isometry` with all displayed hypotheses. -/
theorem pqc_residual_frame_isometry (f : K → L) (guess : L → K) :
    (pqcResidualFrame f guess).Isometry :=
  Matrix.submatrix_one_id_right_isometry (pqc_residual_encode_injective f guess)

/-- Definition of pqc Residual State in the Modular Fourier construction. -/
noncomputable def pqcResidualState (f : K → L) (guess : L → K)
    (ψ : QState K) : QState (L × K) :=
  pqcResidualFrame f guess *ᵥ ψ

/-- The actual finite-label construction satisfies `pqc_residual_state_normalized` with all displayed hypotheses. -/
theorem pqc_residual_state_normalized (f : K → L) (guess : L → K)
    (ψ : QState K) (hψ : Normalized ψ) : Normalized (pqcResidualState f guess ψ) := by
  have hE : (pqcResidualFrame f guess)ᴴ * pqcResidualFrame f guess = 1 :=
    pqc_residual_frame_isometry f guess
  have hi : Inner (pqcResidualState f guess ψ) (pqcResidualState f guess ψ) = Inner ψ ψ := by
    simp only [pqcResidualState, Qatlib.Foundations.PureStateMath.Inner,
      Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul]
    rw [hE, Matrix.vecMul_one]
  rw [normalized_iff_inner_self]
  exact hi.trans ((normalized_iff_inner_self ψ).mp hψ)

omit [Fintype L] in
/-- The actual finite-label construction satisfies `pqc_residual_state_apply_image` with all displayed hypotheses. -/
theorem pqc_residual_state_apply_image (f : K → L) (guess : L → K)
    (ψ : QState K) (k : K) :
    pqcResidualState f guess ψ (pqcResidualEncode f guess k) = ψ k := by
  have hinj := pqc_residual_encode_injective f guess
  simp [pqcResidualState, pqcResidualFrame, Matrix.mulVec, dotProduct,
    Matrix.one_apply, hinj.eq_iff]

omit [Fintype L] in
/-- The zero-residual row has a single possible preimage, with an explicit
forward-image check. It is not the sum of colliding input amplitudes. -/
theorem pqc_residual_state_apply_zero (f : K → L) (guess : L → K)
    (ψ : QState K) (l : L) :
    pqcResidualState f guess ψ (l,0) =
      if f (guess l) = l then ψ (guess l) else 0 := by
  classical
  unfold pqcResidualState pqcResidualFrame
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq, Matrix.one_apply]
  rw [Finset.sum_eq_single (guess l)]
  · by_cases h : f (guess l) = l
    · simp [pqcResidualEncode, h]
    · have hl : l ≠ f (guess l) := Ne.symm h
      simp [pqcResidualEncode, h, hl]
  · intro k _ hk
    have hn : (l, (0 : K)) ≠ pqcResidualEncode f guess k := by
      intro he
      have hc : guess l = k := calc
        guess l = pqcResidualRecover guess (l,0) := by simp [pqcResidualRecover]
        _ = pqcResidualRecover guess (pqcResidualEncode f guess k) :=
          congrArg (pqcResidualRecover guess) he
        _ = k := pqc_residual_recover_encode f guess k
      exact hk hc.symm
    simp [hn]
  · simp

/-- Actual right-register Born mass, for arbitrary complex source amplitudes.
The forward check remains present even when the guess is wrong. -/
theorem pqc_residual_zero_born_mass (f : K → L) (guess : L → K)
    (ψ : QState K) :
    MarginalProbRight (pqcResidualState f guess ψ) {0} =
      ∑ l : L, if f (guess l) = l then BornProb ψ (guess l) else 0 := by
  simp only [MarginalProbRight, MeasureProb, Finset.sum_product,
    Finset.sum_singleton]
  apply Finset.sum_congr rfl
  intro l _
  simp only [BornProb, pqc_residual_state_apply_zero]
  split_ifs <;> simp_all

end Finite
end Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources
