/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Polynomial.Fourier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceCircleBounds
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Original-input CFD source bridge: RadialGap.
The nonconstant branch uses the computed surviving degree.
This module does not certify spectral completion, deflation, interpreter refinement or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


open Polynomial MeasureTheory
open scoped BigOperators

/-- The finite construction in `NativeSourceRadialGap` satisfies `coeff_norm_le_of_circle` under the displayed hypotheses. -/
private theorem coeff_norm_le_of_circle (p : ℂ[X])
    (hp : ∀ z : ℂ, ‖z‖=1 → ‖p.eval z‖ ≤ 1) (n : ℕ) : ‖p.coeff n‖ ≤ 1 := by
  let : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩
  rw [← p.fourierCoeff_toAddCircle_natCast n, fourierCoeff]
  have h : ∀ᵐ t : AddCircle (2*Real.pi) ∂AddCircle.haarAddCircle,
      ‖fourier (-(n : ℤ)) t • p.toAddCircle t‖ ≤ 1 := by
    apply ae_of_all
    intro t
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    have heval : p.toAddCircle t=p.eval (t.toCircle : ℂ) := by
      change (ContinuousMap.evalAlgHom ℂ ℂ t) (Polynomial.aeval _ p)=_
      rw [← Polynomial.aeval_algHom_apply]
      simp only [ContinuousMap.evalAlgHom,Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id]
      rfl
    rw [heval]
    exact hp _ (Circle.norm_coe _)
  simpa using norm_integral_le_of_norm_le_const h

/-- The finite construction in `NativeSourceRadialGap` satisfies `pow_sub_norm_le` under the displayed hypotheses. -/
private theorem pow_sub_norm_le (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (n : ℕ) :
    ‖x^n-y^n‖ ≤ (n : ℝ)*‖x-y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : ‖x^n‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hx
    have he : x^(n+1)-y^(n+1)=x^n*(x-y)+(x^n-y^n)*y := by ring
    rw [he]
    calc
      _ ≤ ‖x^n*(x-y)‖+‖(x^n-y^n)*y‖ := norm_add_le _ _
      _ = ‖x^n‖*‖x-y‖+‖x^n-y^n‖*‖y‖ := by rw [norm_mul,norm_mul]
      _ ≤ 1*‖x-y‖+((n : ℝ)*‖x-y‖)*1 :=
        add_le_add (mul_le_mul_of_nonneg_right hxn (norm_nonneg _))
          (mul_le_mul ih hy (norm_nonneg _) (by positivity))
      _ = ((n+1 : ℕ) : ℝ)*‖x-y‖ := by push_cast; ring

/-- The finite construction in `NativeSourceRadialGap` satisfies `polynomial_sub_norm_le` under the displayed hypotheses. -/
private theorem polynomial_sub_norm_le (p : ℂ[X]) (m : ℕ) (hm : p.natDegree < m)
    (hc : ∀ j : ℕ, ‖p.coeff j‖ ≤ 1)
    (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖p.eval x-p.eval y‖ ≤ (∑ j ∈ Finset.range m,(j : ℝ))*‖x-y‖ := by
  have hp := p.as_sum_range' m hm
  have he : p.eval x-p.eval y=
      ∑ j ∈ Finset.range m,p.coeff j*(x^j-y^j) := by
    conv_lhs => rw [hp]
    simp only [Polynomial.eval_finsetSum,Polynomial.eval_monomial]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul]
  calc
    _ ≤ 1*((j : ℝ)*‖x-y‖) :=
      mul_le_mul (hc j) (pow_sub_norm_le x y hx hy j) (norm_nonneg _) (by norm_num)
    _ = (j : ℝ)*‖x-y‖ := one_mul _

/-- The finite construction in `NativeSourceRadialGap` satisfies `sum_range_real` under the displayed hypotheses. -/
private theorem sum_range_real (m : ℕ) :
    (∑ j ∈ Finset.range (m+1),(j : ℝ))=(m : ℝ)*(m+1)/2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ,ih]
    push_cast
    ring

/-- Radial separation follows from the circle bounds, rather than being an input. -/
private theorem inside_root_radial_bound (p : ℂ[X]) (d : ℕ) (hd : 0<d)
    (hdeg : p.natDegree ≤ 2*d) (mu : ℝ) (hm1 : mu ≤ 1)
    (hcircle : ∀ z : ℂ, ‖z‖=1 → mu ≤ ‖p.eval z‖ ∧ ‖p.eval z‖ ≤ 1)
    (x : ℂ) (hx : ‖x‖<1) (hroot : p.eval x=0) :
    ‖x‖ ≤ 1-mu/(4*(d : ℝ)^2) := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hden : 0<4*(d : ℝ)^2 := by positivity
  by_cases hx0 : x=0
  · rw [hx0,norm_zero]
    have hsmall : mu/(4*(d : ℝ)^2) ≤ 1 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith
    linarith
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx0
  let y := x/(‖x‖ : ℂ)
  have hy : ‖y‖=1 := by
    simp [y,Complex.norm_real,hr.ne']
  have he : x=(‖x‖ : ℂ)*y := by
    dsimp [y]
    have hn : (‖x‖ : ℂ)≠0 := by exact_mod_cast hr.ne'
    field_simp
  have hdist : ‖y-x‖=1-‖x‖ := by
    conv_lhs => rw [he]
    rw [show y-(‖x‖ : ℂ)*y=(1-(‖x‖ : ℂ))*y by ring,norm_mul,hy,mul_one]
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr hx)]
  have hLip := polynomial_sub_norm_le p (2*d+1) (by omega)
    (coeff_norm_le_of_circle p (fun z hz => (hcircle z hz).2))
    y x hy.le hx.le
  rw [hroot,sub_zero,hdist,sum_range_real] at hLip
  have hlow := (hcircle y hy).1
  have hprod : mu ≤ 4*(d : ℝ)^2*(1-‖x‖) := by
    push_cast at hLip
    have hnonneg : 0 ≤ 1-‖x‖ := by linarith
    have hfactor : (2*(d : ℝ))*(2*d+1)/2 ≤ 4*(d : ℝ)^2 := by nlinarith
    exact hlow.trans (hLip.trans (mul_le_mul_of_nonneg_right hfactor hnonneg))
  have hgap : mu/(4*(d : ℝ)^2) ≤ 1-‖x‖ := (div_le_iff₀ hden).mpr (by nlinarith [hprod])
  linarith

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Polynomial

/-- Construction for source Gamma0 in the native source radial gap model. -/
def sourceGamma0 (cs : List ℚ) (N : ℕ) (E : ℚ) : ℚ :=
  3*sourceInputU cs N E/(128*(sourceDegree cs N E : ℚ)^2)

/-- The finite construction in `NativeSourceRadialGap` satisfies `sourceGamma0_pos` under the displayed hypotheses. -/
theorem sourceGamma0_pos (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (hd : 0<sourceDegree cs N E) : 0<sourceGamma0 cs N E := by
  have hu := sourceInputU_pos cs N E hE
  have hdQ : (0 : ℚ)<(sourceDegree cs N E : ℚ) := by exact_mod_cast hd
  unfold sourceGamma0
  positivity

/-- The finite construction in `NativeSourceRadialGap` satisfies `sourceGamma0_le_one` under the displayed hypotheses. -/
theorem sourceGamma0_le_one (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hd : 0<sourceDegree cs N E) : sourceGamma0 cs N E ≤ 1 := by
  have hu := sourceInputU_le_half cs N E
  have hdQ : (1 : ℚ) ≤ (sourceDegree cs N E : ℚ) := by exact_mod_cast hd
  unfold sourceGamma0
  apply (div_le_iff₀ (by positivity : (0 : ℚ)<128*(sourceDegree cs N E : ℚ)^2)).mpr
  nlinarith

/-- The finite construction in `NativeSourceRadialGap` satisfies `sourceF_natDegree_le` under the displayed hypotheses. -/
theorem sourceF_natDegree_le (cs : List ℚ) (N : ℕ) (E : ℚ) :
    (sourceF cs N E).natDegree ≤ 2*sourceDegree cs N E := by
  have hP : (sourceInputP cs N E).natDegree ≤ sourceDegree cs N E := by
    unfold sourceInputP
    have h := Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ sourceDegree cs N E+1)
      (sourceP (sourceLiftedArray cs N E))
    omega
  unfold sourceF
  apply Polynomial.natDegree_map_le.trans
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · rw [Polynomial.natDegree_X_pow]
    omega
  · exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hP)

/-- Same actual source H; original interval promise and finite source guards
are enough to derive the producer's gamma0. -/
theorem sourceIntegerComplement_inside_gap (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (rho : ℂ) (hrho : ‖rho‖<1)
    (hroot : (rootIntegerListPolynomial (sourceIntegerComplement cs N E)).eval rho=0) :
    ‖rho‖ ≤ 1-(sourceGamma0 cs N E : ℝ) := by
  have hF : (sourceF cs N E).eval rho=0 :=
    (sourceIntegerComplement_eval_zero_iff cs N E hparity hd rho).mp hroot
  have h := inside_root_radial_bound (sourceF cs N E) (sourceDegree cs N E) hd
    (sourceF_natDegree_le cs N E) (sourceMu cs N E) (sourceMu_le_one cs N E)
    (sourceF_circle_bounds cs N E hE htail hparity hd hnorm) rho hrho hF
  have he : (sourceGamma0 cs N E : ℝ)=sourceMu cs N E/(4*(sourceDegree cs N E : ℝ)^2) := by
    norm_num [sourceGamma0,sourceMu]
    ring
  rw [he]
  exact h

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
