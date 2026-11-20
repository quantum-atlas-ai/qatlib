/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceRadialGap
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeRootCompletionAccuracy
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Original-input CFD source bridge: CertificateCap.
The nonconstant branch uses the computed surviving degree.
This module does not certify spectral completion, deflation, interpreter refinement or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open scoped BigOperators

/-- For positive E and positive source degree d, the root tolerance is at most the guaranteed
radial gap divided by 128(d + 1). -/
theorem sourceEta_le_gamma_budget (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (hd : 0<sourceDegree cs N E) :
    sourceInputEta cs N E ≤ sourceGamma0 cs N E/(128*((sourceDegree cs N E : ℚ)+1)) := by
  let u := sourceInputU cs N E
  let d : ℚ := sourceDegree cs N E
  let v : ℚ := N+1
  have hu : 0<u := sourceInputU_pos cs N E hE
  have hu1 : u ≤ 1/2 := sourceInputU_le_half cs N E
  have hd1 : (1 : ℚ) ≤ d := by dsimp [d]; exact_mod_cast hd
  have hv1 : 1 ≤ v := by
    dsimp [v]
    have hn : (0 : ℚ) ≤ N := by positivity
    linarith
  have hdv : d+1 ≤ v := by
    dsimp [d,v]
    exact_mod_cast Nat.succ_le_succ (sourceDegree_le cs N E)
  have hprod : d^2*(d+1) ≤ v^3 := by
    calc
      _ ≤ v^2*v := mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith : d ≤ v) 2)
        hdv (by linarith) (by positivity)
      _ = v^3 := by ring
  have hpow : v^3 ≤ v^7 := pow_le_pow_right₀ hv1 (by norm_num : (3 : ℕ) ≤ 7)
  have hD : (128*d^2)*(128*(d+1)) ≤ 3*((2 : ℚ)^30*v^7) := by
    have hpos : 0 ≤ v^7 := by positivity
    nlinarith [hprod.trans hpow]
  have hu2 : u^2 ≤ 1 := by nlinarith
  have hsmall : u^3/((2 : ℚ)^30*v^7) ≤ (3*u/(128*d^2))/(128*(d+1)) := by
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      _ = u*(u^2*((128*d^2)*(128*(d+1)))) := by ring
      _ ≤ u*(1*((128*d^2)*(128*(d+1)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hu2 (by positivity)) hu.le
      _ ≤ u*(3*((2 : ℚ)^30*v^7)) := mul_le_mul_of_nonneg_left (by simpa using hD) hu.le
      _ = _ := by ring
  exact (source_input_eta_small cs N E hE).trans hsmall

/-- If a disk with radius between zero and gamma/4 contains a point of norm at most 1 − gamma, its
rational inside margin is at least gamma/8 for gamma in (0, 1]. -/
private theorem margin_of_radial (c : ℚ×ℚ) (r gamma : ℚ) (rho : ℂ)
    (hr : 0 ≤ r) (hg : 0<gamma) (hg1 : gamma ≤ 1) (hrg : r ≤ gamma/4)
    (hroot : ‖rho‖ ≤ 1-(gamma : ℝ))
    (hdisk : ‖rho-rootRationalCoordinate c‖ ≤ (r : ℝ)) :
    gamma/8 ≤ rootCertificateDiskMargin c r := by
  have hrR : (0 : ℝ) ≤ r := by exact_mod_cast hr
  have hgR : (0 : ℝ)<gamma := by exact_mod_cast hg
  have hg1R : (gamma : ℝ) ≤ 1 := by exact_mod_cast hg1
  have hrgR : (r : ℝ) ≤ (gamma : ℝ)/4 := by exact_mod_cast hrg
  have hc : ‖rootRationalCoordinate c‖ ≤ 1-(gamma : ℝ)+(r : ℝ) := by
    have htri : ‖rootRationalCoordinate c‖ ≤ ‖rho‖+‖rho-rootRationalCoordinate c‖ := by
      calc
        _ = ‖rho-(rho-rootRationalCoordinate c)‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hleft : (gamma : ℝ)/2 ≤ 1-(r : ℝ)-‖rootRationalCoordinate c‖ := by linarith
  have hright : (1/2 : ℝ) ≤ 1-(r : ℝ)+‖rootRationalCoordinate c‖ := by
    have hn := norm_nonneg (rootRationalCoordinate c)
    linarith
  have hprod := mul_le_mul hleft hright (by norm_num : (0 : ℝ) ≤ 1/2) (by linarith)
  have hm : (rootCertificateDiskMargin c r : ℝ)=
      ((1-(r : ℝ))^2-‖rootRationalCoordinate c‖^2)/2 := by
    rw [rootRationalCoordinate_sq_norm]
    norm_num [rootCertificateDiskMargin]
  have hbound : (gamma : ℝ)/8 ≤ (rootCertificateDiskMargin c r : ℝ) := by
    rw [hm]
    nlinarith
  exact_mod_cast hbound

/-- A lower bound shared by the starting value and every list entry also bounds the running
minimum from below. -/
private theorem min_fold_lower (l : List ℚ) (a b : ℚ) (ha : b ≤ a)
    (hl : ∀ x∈l,b ≤ x) : b ≤ l.foldl min a := by
  induction l generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    rw [List.foldl_cons]
    apply ih (min a x) (le_min ha (hl x (by simp)))
    intro y hy
    exact hl y (List.mem_cons_of_mem x hy)

/-- For a positive budget and source degree, a degree-bounded Chebyshev target of matching parity
and norm at most one, and an accepted factorization of the integer complement with nonzero
content, the decoded gap is at least one eighth of the source radial gap. -/
theorem sourceCertificateGap_lower (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (m : ℕ) (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients (sourceIntegerComplement cs N E))
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) (sourceInputEta cs N E)) :
    sourceGamma0 cs N E/8 ≤ rootDecodedCertificateGap f := by
  have hg := sourceGamma0_pos cs N E hE hd
  have hg1 := sourceGamma0_le_one cs N E hd
  have heta : 0 ≤ sourceInputEta cs N E := by unfold sourceInputEta; positivity
  have hsmall := sourceEta_le_gamma_budget cs N E hE hd
  have hmul := (le_div_iff₀ (by positivity :
    (0 : ℚ)<128*((sourceDegree cs N E : ℚ)+1))).mp hsmall
  have he4 : sourceInputEta cs N E ≤ sourceGamma0 cs N E/4 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℚ)<4)).mpr
    have hl := mul_le_mul_of_nonneg_left
      (show (4 : ℚ) ≤ 128*((sourceDegree cs N E : ℚ)+1) by
        have hz : (0 : ℚ) ≤ sourceDegree cs N E := by positivity
        linarith) heta
    linarith
  obtain ⟨w,hw,_hinj,hroots,hside,_hreturn⟩ := rootDecodedCertificate_sound m
    (sourceIntegerComplement cs N E) content f (sourceInputEta cs N E) hcontent hguard haccepted
  apply min_fold_lower _ _ _ (by linarith : sourceGamma0 cs N E/8 ≤ 1)
  intro x hx
  unfold rootCertificateMarginValues at hx
  obtain ⟨j,_,hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  by_cases ht : rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i)=true
  · simp only [ite_eq_left ht]
    have hmem : w j i∈(rootIntegerListPolynomial (sourceIntegerComplement cs N E)).roots := by
      rw [hroots]
      apply Multiset.mem_bind.mpr
      refine ⟨j,by simp,Multiset.mem_nsmul.mpr ⟨(haccepted j).exponent_pos.ne',?_⟩⟩
      change w j i∈(Finset.univ.image (w j) : Finset ℂ)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    have hrad := sourceIntegerComplement_inside_gap cs N E hE htail hparity hd hnorm
      (w j i) ((hside j i).mpr ht) (Polynomial.isRoot_of_mem_roots hmem)
    have hb := (haccepted j).budget i ht
    have hr : (f j).radii i ≤ sourceInputEta cs N E := by
      have ha := abs_nonneg ((rootGridPoint ((f j).centers i)
        (sourceInputEta cs N E/16)).1-((f j).centers i).1)
      have hb' := abs_nonneg ((rootGridPoint ((f j).centers i)
        (sourceInputEta cs N E/16)).2-((f j).centers i).2)
      linarith
    exact margin_of_radial _ _ _ _ ((haccepted j).radius_pos i).le hg hg1
      (hr.trans he4) hrad (hw j i).2
  · simp only [ite_eq_right ht]
    linarith

/-- Under the positive-budget, nonconstant bounded-target and degree and parity hypotheses,
suppose the guarded factors reconstruct the integer complement with nonzero content and the
returned root count equals the source degree. The count times the root tolerance divided by
the decoded gap is then at most one quarter. -/
theorem sourceCertificate_numeric_cap (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (m : ℕ) (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients (sourceIntegerComplement cs N E))
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) (sourceInputEta cs N E))
    (hcount : (rootDecodedReturnList f (sourceInputEta cs N E)).length=sourceDegree cs N E) :
    ((rootDecodedReturnList f (sourceInputEta cs N E)).length : ℚ)*sourceInputEta cs N E/
      rootDecodedCertificateGap f ≤ 1/4 := by
  have hG := sourceCertificateGap_lower cs N E hE htail hparity hd hnorm
    m content f hcontent hguard haccepted
  have hsmall := sourceEta_le_gamma_budget cs N E hE hd
  have heta : 0 ≤ sourceInputEta cs N E := by unfold sourceInputEta; positivity
  have hmul := (le_div_iff₀ (by positivity :
    (0 : ℚ)<128*((sourceDegree cs N E : ℚ)+1))).mp hsmall
  have hGpos := rootDecodedCertificateGap_pos f (sourceInputEta cs N E) haccepted
  rw [hcount]
  apply (div_le_iff₀ hGpos).mpr
  nlinarith

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
