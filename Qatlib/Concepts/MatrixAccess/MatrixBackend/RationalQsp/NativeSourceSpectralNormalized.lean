/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceProducerGuards
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceSpectralRoots
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceSpectralInput
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Same original-input spectral completion: SpectralNormalized.
This does not certify the full proposer, iterative deflation, interpreter or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section SpectralRatio

open Polynomial

/-- Construction for root Ratio in the native source spectral normalized model. -/
private def rootRatio (l : Multiset ℂ) (z : ℂ) : ℂ :=
  (l.map (fun r => (z-r)/(1-r))).prod

/-- The finite construction in `NativeSourceSpectralNormalized` satisfies `reciprocal_pair_ratio` under the displayed hypotheses. -/
private theorem reciprocal_pair_ratio (r z : ℂ) (hr0 : r≠0) (hr1 : r≠1)
    (hz : z*star z=1) :
    (z-sourceReciprocalConjugate r)/(1-sourceReciprocalConjugate r)=z*star ((z-r)/(1-r)) := by
  have hs0 : star r≠0 := by simpa using hr0
  have hs1 : star r≠1 := by
    intro h
    have he := congrArg star h
    exact hr1 (by simpa using he)
  have hd : 1-star r≠0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hds : star r-1≠0 := sub_ne_zero.mpr hs1
  have hds' : -1+star r≠0 := by simpa only [sub_eq_add_neg,add_comm] using hds
  have hdi : 1-(star r)⁻¹≠0 := by
    intro h
    exact hs1 (inv_eq_one.mp (sub_eq_zero.mp h).symm)
  have he : (z-sourceReciprocalConjugate r)/(1-sourceReciprocalConjugate r)=
      (1-z*star r)/(1-star r) := by
    unfold sourceReciprocalConjugate
    field_simp [hs0,hd,hdi,hds,hds']
    ring
  rw [he,star_div₀,star_sub,star_sub,star_one,← mul_div_assoc]
  congr 1
  rw [mul_sub,hz]

/-- The finite construction in `NativeSourceSpectralNormalized` satisfies `rootRatio_cons` under the displayed hypotheses. -/
private theorem rootRatio_cons (r : ℂ) (l : Multiset ℂ) (z : ℂ) :
    rootRatio (r::ₘl) z=((z-r)/(1-r))*rootRatio l z := by
  simp only [rootRatio,Multiset.map_cons,Multiset.prod_cons]

/-- The finite construction in `NativeSourceSpectralNormalized` satisfies `paired_ratio` under the displayed hypotheses. -/
private theorem paired_ratio (l : Multiset ℂ) (z : ℂ) (hz : z*star z=1) :
    (∀ r∈l,r≠0) → (∀ r∈l,r≠1) →
      rootRatio (l.map sourceReciprocalConjugate) z=z^l.card*star (rootRatio l z) := by
  induction l using Multiset.induction_on with
  | empty => intro _ _; simp [rootRatio]
  | @cons r l ih =>
    intro h0 h1
    have ht0 : ∀ x∈l,x≠0 := fun x hx => h0 x (Multiset.mem_cons_of_mem hx)
    have ht1 : ∀ x∈l,x≠1 := fun x hx => h1 x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.map_cons,rootRatio_cons,rootRatio_cons,
      reciprocal_pair_ratio r z (h0 r (by simp)) (h1 r (by simp)) hz,
      ih ht0 ht1,Multiset.card_cons,pow_succ,star_mul]
    ring

/-- The finite construction in `NativeSourceSpectralNormalized` satisfies `paired_product_ratio` under the displayed hypotheses. -/
private theorem paired_product_ratio (l : Multiset ℂ) (z : ℂ) (hz : ‖z‖=1)
    (h0 : ∀ r∈l,r≠0) (h1 : ∀ r∈l,r≠1) :
    rootRatio (l+l.map sourceReciprocalConjugate) z=
      z^l.card*((‖rootRatio l z‖^2 : ℝ) : ℂ) := by
  have hm : z*star z=1 := by
    simpa only [Complex.normSq_eq_norm_sq,hz,one_pow,Complex.ofReal_one, starRingEnd_apply] using Complex.mul_conj z
  have he : rootRatio (l+l.map sourceReciprocalConjugate) z=
      rootRatio l z*rootRatio (l.map sourceReciprocalConjugate) z := by
    simp only [rootRatio,Multiset.map_add,Multiset.prod_add]
  rw [he,paired_ratio l z hm h0 h1]
  have hsq : rootRatio l z*star (rootRatio l z)=((‖rootRatio l z‖^2 : ℝ) : ℂ) := by
    simpa only [Complex.normSq_eq_norm_sq, starRingEnd_apply] using Complex.mul_conj (rootRatio l z)
  calc
    _=z^l.card*(rootRatio l z*star (rootRatio l z)) := by ring
    _=_ := by rw [hsq]

/-- The finite construction in `NativeSourceSpectralNormalized` satisfies `eval_root_product` under the displayed hypotheses. -/
private theorem eval_root_product (p : ℂ[X]) (z : ℂ) :
    p.eval z=p.leadingCoeff*(p.roots.map (fun r => z-r)).prod := by
  have h := congrArg (fun q : ℂ[X] => q.eval z)
    (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.card_roots_eq_natDegree (p := p)))
  simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_multiset_prod,
    Multiset.map_map,Polynomial.eval_sub,Polynomial.eval_X,Function.comp_def] using h.symm

/-- The finite construction in `NativeSourceSpectralNormalized` satisfies `polynomial_ratio` under the displayed hypotheses. -/
private theorem polynomial_ratio (p : ℂ[X]) (hp : p≠0) (z : ℂ) :
    p.eval z/p.eval 1=rootRatio p.roots z := by
  have hl := Polynomial.leadingCoeff_ne_zero.mpr hp
  rw [eval_root_product p z,eval_root_product p 1]
  unfold rootRatio
  rw [Multiset.prod_map_div]
  exact mul_div_mul_left _ _ hl

end SpectralRatio

section SpectralNormalized

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- Construction for source Inside Roots in the native source spectral normalized model. -/
def sourceInsideRoots (cs : List ℚ) (N : ℕ) (E : ℚ) : Multiset ℂ :=
  (rootIntegerListPolynomial (sourceIntegerComplement cs N E)).roots.filter (fun z => ‖z‖<1)

/-- Construction for source Ideal Product in the native source spectral normalized model. -/
def sourceIdealProduct (cs : List ℚ) (N : ℕ) (E : ℚ) (z : ℂ) : ℂ :=
  ((sourceInsideRoots cs N E).map (fun r => z-r)).prod

/-- The finite construction in `NativeSourceSpectralNormalized` satisfies `sourceIdealProduct_ne_zero` under the displayed hypotheses. -/
theorem sourceIdealProduct_ne_zero (cs : List ℚ) (N : ℕ) (E : ℚ) (z : ℂ) (hz : ‖z‖=1) :
    sourceIdealProduct cs N E z≠0 := by
  classical
  unfold sourceIdealProduct
  apply Multiset.prod_ne_zero
  intro hx
  obtain ⟨r,hr,he⟩ := Multiset.mem_map.mp hx
  have hrz : z=r := sub_eq_zero.mp he
  have hi := (Multiset.mem_filter.mp hr).2
  rw [← hrz,hz] at hi
  exact (lt_irrefl (1 : ℝ)) hi

/-- The finite construction in `NativeSourceSpectralNormalized` satisfies `sourceRatio_eq` under the displayed hypotheses. -/
private theorem sourceRatio_eq (cs : List ℚ) (N : ℕ) (E : ℚ) (z : ℂ) :
    rootRatio (sourceInsideRoots cs N E) z=
      sourceIdealProduct cs N E z/sourceIdealProduct cs N E 1 := by
  exact Multiset.prod_map_div

/-- The finite construction in `NativeSourceSpectralNormalized` satisfies `sourceNormalizedSpectralIdentity` under the displayed hypotheses. -/
theorem sourceNormalizedSpectralIdentity (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (z : ℂ) (hz : ‖z‖=1) :
    (sourceF cs N E).eval z=(sourceActualH1 cs N E : ℂ)*z^sourceDegree cs N E*
      ((‖sourceIdealProduct cs N E z/sourceIdealProduct cs N E 1‖^2 : ℝ) : ℂ) := by
  have hp : sourceF cs N E≠0 := by
    intro he
    exact sourceF_eval_zero_ne cs N E hd (by rw [he,Polynomial.eval_zero])
  have h0 : ∀ r∈sourceInsideRoots cs N E,r≠0 := by
    intro r hr he
    have hzH := Polynomial.isRoot_of_mem_roots (Multiset.mem_filter.mp hr).1
    have hzF := (sourceIntegerComplement_eval_zero_iff cs N E hparity hd r).mp hzH
    subst r
    exact sourceF_eval_zero_ne cs N E hd hzF
  have h1 : ∀ r∈sourceInsideRoots cs N E,r≠1 := by
    intro r hr he
    have hi := (Multiset.mem_filter.mp hr).2
    rw [he,norm_one] at hi
    exact (lt_irrefl (1 : ℝ)) hi
  have hsplit : (sourceF cs N E).roots=sourceInsideRoots cs N E+
      (sourceInsideRoots cs N E).map sourceReciprocalConjugate := by
    unfold sourceInsideRoots
    rw [sourceIntegerComplement_roots cs N E hparity hd]
    exact sourceF_roots_split cs N E hE htail hparity hd hnorm
  have hcard : (sourceInsideRoots cs N E).card=sourceDegree cs N E :=
    sourceIntegerComplement_inside_count cs N E hE htail hparity hd hnorm
  have h := polynomial_ratio (sourceF cs N E) hp z
  rw [hsplit,paired_product_ratio _ z hz h0 h1,hcard,sourceRatio_eq,
    sourceF_eval_one cs N E hparity hd] at h
  have hnz : (sourceActualH1 cs N E : ℂ)≠0 := by
    exact_mod_cast (sourceActualH1_pos cs N E hE htail hnorm).ne'
  have he := (div_eq_iff hnz).mp h
  exact he.trans (by ring)

/-- The finite construction in `NativeSourceSpectralNormalized` satisfies `sourceIdealNormalized_norm_le_one` under the displayed hypotheses. -/
theorem sourceIdealNormalized_norm_le_one (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (z : ℂ) (hz : ‖z‖=1) :
    Real.sqrt (sourceActualH1 cs N E : ℝ)*
      ‖sourceIdealProduct cs N E z/sourceIdealProduct cs N E 1‖ ≤ 1 := by
  have hp : (0 : ℝ)<(sourceActualH1 cs N E : ℝ) := by
    exact_mod_cast sourceActualH1_pos cs N E hE htail hnorm
  have hh : ‖(sourceActualH1 cs N E : ℂ)‖=(sourceActualH1 cs N E : ℝ) := by
    rw [← Complex.ofReal_ratCast,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  have h := (sourceF_circle_bounds cs N E hE htail hparity hd hnorm z hz).2
  rw [sourceNormalizedSpectralIdentity cs N E hE htail hparity hd hnorm z hz,
    norm_mul,norm_mul,norm_pow,hz,one_pow,mul_one,hh,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)] at h
  have hs : (Real.sqrt (sourceActualH1 cs N E : ℝ)*
      ‖sourceIdealProduct cs N E z/sourceIdealProduct cs N E 1‖)^2 ≤ 1 := by
    rw [mul_pow,Real.sq_sqrt hp.le]
    exact h
  have hn : 0 ≤ Real.sqrt (sourceActualH1 cs N E : ℝ)*
      ‖sourceIdealProduct cs N E z/sourceIdealProduct cs N E 1‖ := by positivity
  nlinarith

end SpectralNormalized

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
