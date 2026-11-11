/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceRegularization
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeSourceIntegerization
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Original-input CFD source bridge: OriginalComplement.
The nonconstant branch uses the computed surviving degree.
This module does not certify spectral completion, deflation, interpreter refinement or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Polynomial

/-- Construction for source Input P in the native source original complement model. -/
def sourceInputP (cs : List ℚ) (N : ℕ) (E : ℚ) : ℚ[X] :=
  Polynomial.ofFn (sourceDegree cs N E+1) (sourceP (sourceLiftedArray cs N E))

/-- Construction for source Rational Complement in the native source original complement model. -/
def sourceRationalComplement (cs : List ℚ) (N : ℕ) (E : ℚ) : List ℚ :=
  List.ofFn (sourceComplementCell (sourceLiftedArray cs N E))

/-- Construction for source Integer Complement in the native source original complement model. -/
def sourceIntegerComplement (cs : List ℚ) (N : ℕ) (E : ℚ) : List ℤ :=
  sourceIntegerTarget (sourceRationalComplement cs N E)

/-- The finite construction in `NativeSourceOriginalComplement` satisfies `sourceLeading_ne_zero` under the displayed hypotheses. -/
private theorem sourceLeading_ne_zero (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hd : 0<sourceDegree cs N E) :
    sourceCoefficient cs N E ⟨sourceDegree cs N E,by have h := sourceDegree_le cs N E; omega⟩≠0 := by
  obtain ⟨i,hi,hv⟩ := sourceArrayDegree_leading (sourceCoefficient cs N E) hd
  have he : i=⟨sourceDegree cs N E,by have h := sourceDegree_le cs N E; omega⟩ := by
    apply Fin.ext
    exact hv.symm
  rw [he] at hi
  exact hi

/-- The finite construction in `NativeSourceOriginalComplement` satisfies `sourceP_zero` under the displayed hypotheses. -/
private theorem sourceP_zero (cs : List ℚ) (N : ℕ) (E : ℚ) :
    sourceP (sourceLiftedArray cs N E) (⟨0,Nat.succ_pos _⟩ : Fin (sourceDegree cs N E+1))=
      sourceCoefficient cs N E ⟨sourceDegree cs N E,by have h := sourceDegree_le cs N E; omega⟩ := by
  unfold sourceP sourceLiftedArray
  congr 1
  apply Fin.ext
  change Nat.dist 0 (sourceDegree cs N E)=sourceDegree cs N E
  simp [Nat.dist]

/-- The finite construction in `NativeSourceOriginalComplement` satisfies `sourceRationalComplement_nonzero` under the displayed hypotheses. -/
theorem sourceRationalComplement_nonzero (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) : ∃ q∈sourceRationalComplement cs N E,q≠0 := by
  let d := sourceDegree cs N E
  have hp := sourceOriginalComplement_polynomial cs N E hparity hd
  have hc := congrArg (fun p : ℚ[X] => p.coeff 0) hp
  change (Polynomial.ofFn (d+d+1) (sourceComplementCell (sourceLiftedArray cs N E))).coeff 0=
    (X^d-(Polynomial.ofFn (d+1) (sourceP (sourceLiftedArray cs N E)))^2).coeff 0 at hc
  rw [Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega),Polynomial.coeff_sub,
    Polynomial.coeff_X_pow,ite_eq_right (show (0 : ℕ)≠d from (Nat.ne_of_gt hd).symm),
    zero_sub,pow_two,Polynomial.mul_coeff_zero,
    Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega),sourceP_zero] at hc
  have hq : sourceComplementCell (sourceLiftedArray cs N E) (⟨0,by omega⟩ : Fin (d+d+1))≠0 := by
    rw [hc]
    exact neg_ne_zero.mpr (mul_ne_zero (sourceLeading_ne_zero cs N E hd)
      (sourceLeading_ne_zero cs N E hd))
  refine ⟨sourceComplementCell (sourceLiftedArray cs N E) (⟨0,by omega⟩ : Fin (d+d+1)),?_,hq⟩
  exact List.mem_ofFn.mpr ⟨⟨0,by omega⟩,rfl⟩

/-- Full actual integer target, not an externally supplied H-polynomial law. -/
theorem sourceIntegerComplement_polynomial (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) :
    rootIntegerListPolynomial (sourceIntegerComplement cs N E)=
      C ((sourceDenominator (sourceRationalComplement cs N E) : ℂ)/
        (sourceContent (sourceRationalComplement cs N E) : ℂ))*
      ((X^sourceDegree cs N E-(sourceInputP cs N E)^2 : ℚ[X]).map (Rat.castHom ℂ)) := by
  rw [sourceIntegerComplement,sourceIntegerTarget_polynomial _
    (sourceRationalComplement_nonzero cs N E hparity hd)]
  congr 1
  change (Polynomial.ofFn _ (sourceComplementCell (sourceLiftedArray cs N E))).map (Rat.castHom ℂ)=_
  rw [sourceOriginalComplement_polynomial cs N E hparity hd]
  rfl

/-- The finite construction in `NativeSourceOriginalComplement` satisfies `sourceIntegerComplement_scalar_ne_zero` under the displayed hypotheses. -/
theorem sourceIntegerComplement_scalar_ne_zero (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) :
    (sourceDenominator (sourceRationalComplement cs N E) : ℂ)/
      (sourceContent (sourceRationalComplement cs N E) : ℂ)≠0 := by
  apply div_ne_zero
  · exact_mod_cast (sourceDenominator_pos (sourceRationalComplement cs N E)).ne'
  · exact_mod_cast (sourceContent_pos _ (sourceRationalComplement_nonzero cs N E hparity hd)).ne'

/-- Every actual H zero is a zero of the same original-input complement. -/
theorem sourceIntegerComplement_eval_zero_iff (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) (z : ℂ) :
    (rootIntegerListPolynomial (sourceIntegerComplement cs N E)).eval z=0 ↔
      (((X^sourceDegree cs N E-(sourceInputP cs N E)^2 : ℚ[X]).map (Rat.castHom ℂ)).eval z)=0 := by
  rw [sourceIntegerComplement_polynomial cs N E hparity hd,
    Polynomial.eval_mul,Polynomial.eval_C,mul_eq_zero]
  simp only [sourceIntegerComplement_scalar_ne_zero cs N E hparity hd,false_or]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
