/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceCircleInput
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Original-input CFD source bridge: CircleBounds.
The nonconstant branch uses the computed surviving degree.
This module does not certify spectral completion, deflation, interpreter refinement or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Polynomial

/-- Construction for source F in the native source circle bounds model. -/
def sourceF (cs : List ℚ) (N : ℕ) (E : ℚ) : ℂ[X] :=
  (X^sourceDegree cs N E-(sourceInputP cs N E)^2 : ℚ[X]).map (Rat.castHom ℂ)

/-- Construction for source Mu in the native source circle bounds model. -/
def sourceMu (cs : List ℚ) (N : ℕ) (E : ℚ) : ℝ :=
  3*(sourceInputU cs N E : ℝ)/32

/-- The finite construction in `NativeSourceCircleBounds` satisfies `sourceMu_pos` under the displayed hypotheses. -/
theorem sourceMu_pos (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E) :
    0<sourceMu cs N E := by
  have hu : (0 : ℝ)<(sourceInputU cs N E : ℝ) :=
    (Rat.cast_pos (K := ℝ)).mpr (sourceInputU_pos cs N E hE)
  unfold sourceMu
  positivity

/-- The finite construction in `NativeSourceCircleBounds` satisfies `sourceMu_le_one` under the displayed hypotheses. -/
theorem sourceMu_le_one (cs : List ℚ) (N : ℕ) (E : ℚ) :
    sourceMu cs N E ≤ 1 := by
  have hu : (sourceInputU cs N E : ℝ) ≤ 1/2 := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr (sourceInputU_le_half cs N E)
  unfold sourceMu
  linarith

/-- The finite construction in `NativeSourceCircleBounds` satisfies `sourceF_exp` under the displayed hypotheses. -/
theorem sourceF_exp (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) (theta : ℝ) :
    (sourceF cs N E).eval (Complex.exp (2*((theta : ℂ)*Complex.I)))=
      Complex.exp ((sourceDegree cs N E : ℂ)*((theta : ℂ)*Complex.I))^2 *
        (((1-((nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)).eval
          (Real.cos theta))^2 : ℝ) : ℂ)) := by
  simp only [sourceF,Polynomial.eval_map,Polynomial.eval₂_sub,Polynomial.eval₂_pow,
    Polynomial.eval₂_X]
  rw [sourceInputP_circle cs N E hparity hd theta]
  have he : Complex.exp (2*((theta : ℂ)*Complex.I))^sourceDegree cs N E=
      Complex.exp ((sourceDegree cs N E : ℂ)*((theta : ℂ)*Complex.I))^2 := by
    rw [← Complex.exp_nat_mul,← Complex.exp_nat_mul]
    congr 1
    ring
  rw [he]
  push_cast
  ring

/-- The estimate `sourceF_circle_bounds` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceF_circle_bounds (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (z : ℂ) (hz : ‖z‖=1) :
    sourceMu cs N E ≤ ‖(sourceF cs N E).eval z‖ ∧ ‖(sourceF cs N E).eval z‖ ≤ 1 := by
  obtain ⟨phi,hphi⟩ := (Complex.norm_eq_one_iff z).mp hz
  let theta := phi/2
  have hzexp : z=Complex.exp (2*((theta : ℂ)*Complex.I)) := by
    rw [← hphi]
    congr 1
    dsimp [theta]
    push_cast
    ring
  rw [hzexp,sourceF_exp cs N E hparity hd theta,norm_mul,norm_pow]
  have hphase : ‖Complex.exp ((sourceDegree cs N E : ℂ)*((theta : ℂ)*Complex.I))‖=1 := by
    have harg : (sourceDegree cs N E : ℂ)*((theta : ℂ)*Complex.I)=
        ((((sourceDegree cs N E : ℝ)*theta : ℝ) : ℂ)*Complex.I) := by push_cast; ring
    rw [harg,Complex.norm_exp_ofReal_mul_I]
  rw [hphase,one_pow,one_mul,Complex.norm_real,Real.norm_eq_abs]
  let a := (nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)).eval (Real.cos theta)
  have ha : |a| ≤ 1-sourceMu cs N E :=
    sourceOutput_uniform_gap cs N E hE htail hnorm (Real.cos theta)
      ⟨Real.neg_one_le_cos theta,Real.cos_le_one theta⟩
  have hm0 := (sourceMu_pos cs N E hE).le
  have hm1 := sourceMu_le_one cs N E
  have hasq : a^2 ≤ (1-sourceMu cs N E)^2 := by
    nlinarith [sq_nonneg (1-sourceMu cs N E-|a|),abs_nonneg a,sq_abs a]
  have hnonneg : 0 ≤ 1-a^2 := by nlinarith
  change sourceMu cs N E ≤ |1-a^2| ∧ |1-a^2| ≤ 1
  rw [abs_of_nonneg hnonneg]
  constructor <;> nlinarith [sq_nonneg a]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
