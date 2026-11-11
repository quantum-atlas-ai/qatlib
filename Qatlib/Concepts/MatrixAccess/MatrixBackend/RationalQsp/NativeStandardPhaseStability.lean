/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativePhaseOutputRounding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Linear, whole-W-word phase sensitivity. This concerns actual matrix products,
not the exponentially growing monomial coefficient score. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords

open Matrix Polynomial
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Matrix.Norms.L2Operator

/-- The finite construction in `NativeStandardPhaseStability` satisfies `standardPhaseMatrix_norm_le` under the displayed hypotheses. -/
theorem standardPhaseMatrix_norm_le (z : ℂ) : ‖standardPhaseMatrix z‖≤‖z‖ := by
  have he : standardPhaseMatrix z=diagonal (fun b : Bool => if b then star z else z) := by
    ext i j
    cases i <;> cases j <;> simp [standardPhaseMatrix]
  rw [he,l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
  intro b
  cases b <;> simp

/-- The estimate `standardPhaseMatrix_error` retains the actual parameter, input-error and normalization budgets. -/
theorem standardPhaseMatrix_error (z w : ℂ) :
    ‖standardPhaseMatrix z-standardPhaseMatrix w‖≤‖z-w‖ := by
  have he : standardPhaseMatrix z-standardPhaseMatrix w=standardPhaseMatrix (z-w) := by
    ext i j
    cases i <;> cases j <;> simp [standardPhaseMatrix]
  rw [he]
  exact standardPhaseMatrix_norm_le _

/-- The actual finite word or frame satisfies `standardSignalMatrix_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem standardSignalMatrix_unitary (x s : ℝ) (hs : s*s=1-x*x) :
    standardSignalMatrix x s∈unitaryGroup Bool ℂ := by
  have hsc : (s : ℂ)*(s : ℂ)=1-(x : ℂ)*(x : ℂ) := by exact_mod_cast hs
  rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose]
  ext i j
  cases i <;> cases j <;>
    simp [standardSignalMatrix,Matrix.mul_apply,
      Matrix.conjTranspose_apply,map_mul,Complex.conj_I] <;>
      ring_nf <;> simp only [Complex.I_sq,neg_mul,neg_neg,one_mul] <;> linear_combination hsc

/-- The finite construction in `NativeStandardPhaseStability` satisfies `standardMatrixWord_norm_le_one` under the displayed hypotheses. -/
theorem standardMatrixWord_norm_le_one (base : ℂ) (zs : List ℂ) (x s : ℝ)
    (hs : s*s=1-x*x) (hb : ‖base‖=1) (hz : ∀ z∈zs,‖z‖=1) :
    ‖standardMatrixWord base x s zs‖≤1 := by
  have hW := unitary_norm_le_one (standardSignalMatrix_unitary x s hs)
  induction zs with
  | nil => simpa only [standardMatrixWord,hb] using standardPhaseMatrix_norm_le base
  | cons z zs ih =>
    have hD : ‖standardPhaseMatrix z‖≤1 :=
      (standardPhaseMatrix_norm_le z).trans_eq (hz z (by simp))
    have hM := ih (fun w hw => hz w (by simp [hw]))
    calc
      _≤(‖standardPhaseMatrix z‖*‖standardSignalMatrix x s‖)*
          ‖standardMatrixWord base x s zs‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _≤(1*1)*1 := by gcongr
      _=1 := by norm_num

/-- Base and every listed phase error are paid once, in the actual matrix order.
Neither endpoint s0 nor odd/even lengths require a division or special estimate. -/
theorem standardMatrixWord_error (base other : ℂ) (zs ws : List ℂ) (x s δ : ℝ)
    (hs : s*s=1-x*x) (_hb : ‖base‖=1) (ho : ‖other‖=1)
    (hz : ∀ z∈zs,‖z‖=1) (hw : ∀ w∈ws,‖w‖=1)
    (hδ : 0≤δ) (hphases : List.Forall₂ (fun z w => ‖z-w‖≤δ) zs ws) :
    ‖standardMatrixWord base x s zs-standardMatrixWord other x s ws‖≤
      ‖base-other‖+(zs.length : ℝ)*δ := by
  have hW := unitary_norm_le_one (standardSignalMatrix_unitary x s hs)
  revert hz hw
  induction hphases with
  | nil =>
    intro _ _
    simpa only [standardMatrixWord,List.length_nil,Nat.cast_zero,zero_mul,add_zero]
      using standardPhaseMatrix_error base other
  | @cons z w zs ws hzw htail ih =>
    intro hz hw
    have hzt : ∀ v∈zs,‖v‖=1 := fun v hv => hz v (by simp [hv])
    have hwt : ∀ v∈ws,‖v‖=1 := fun v hv => hw v (by simp [hv])
    have hM := standardMatrixWord_norm_le_one other ws x s hs ho hwt
    have hD : ‖standardPhaseMatrix z‖≤1 :=
      (standardPhaseMatrix_norm_le z).trans_eq (hz z (by simp))
    have hdiff := (standardPhaseMatrix_error z w).trans hzw
    have hrec := ih hzt hwt
    let M := standardMatrixWord base x s zs
    let N := standardMatrixWord other x s ws
    have he : standardMatrixWord base x s (z::zs)-standardMatrixWord other x s (w::ws)=
        (standardPhaseMatrix z-standardPhaseMatrix w)*standardSignalMatrix x s*N+
          standardPhaseMatrix z*standardSignalMatrix x s*(M-N) := by
      dsimp [standardMatrixWord,M,N]
      noncomm_ring
    rw [he]
    calc
      _ ≤ ‖(standardPhaseMatrix z-standardPhaseMatrix w)*standardSignalMatrix x s*N‖+
          ‖standardPhaseMatrix z*standardSignalMatrix x s*(M-N)‖ := norm_add_le _ _
      _≤(‖standardPhaseMatrix z-standardPhaseMatrix w‖*‖standardSignalMatrix x s‖)*‖N‖+
          (‖standardPhaseMatrix z‖*‖standardSignalMatrix x s‖)*‖M-N‖ := by
        apply add_le_add
        all_goals exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _≤(δ*1)*1+(1*1)*(‖base-other‖+(zs.length : ℝ)*δ) := by gcongr
      _=‖base-other‖+((z::zs).length : ℝ)*δ := by simp; ring

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
