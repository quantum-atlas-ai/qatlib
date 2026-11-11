/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeRootCompletionMonic
import Mathlib.Algebra.Order.Group.Multiset
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! A computable rational inside-gap lower bound from the SAME accepted disks.
No ideal-root gap or root catalogue is supplied as an answer. Outside/none
values use1 only in the numeric list; soundness consumes successful guards. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


/-- Half the actual squared inside-test surplus, entirely rational. -/
def rootCertificateDiskMargin (c : ℚ×ℚ) (r : ℚ) : ℚ :=
  ((1-r)^2-(c.1^2+c.2^2))/2

/-- The finite construction in `NativeRootCertificateGap` satisfies `rootCertificateDiskMargin_pos` under the displayed hypotheses. -/
theorem rootCertificateDiskMargin_pos (c : ℚ×ℚ) (r : ℚ)
    (hc : rootRationalDiskClassify c r=some true) : 0<rootCertificateDiskMargin c r := by
  have h := (rootRationalDiskClassify_true c r hc).2
  dsimp only [rootCertificateDiskMargin]
  linarith

/-- Every point in the accepted disk is below1 by the computed margin. -/
theorem rootCertificateDiskMargin_norm (c : ℚ×ℚ) (r : ℚ) (hr : 0<r)
    (hc : rootRationalDiskClassify c r=some true) (rho : ℂ)
    (hd : ‖rho-rootRationalCoordinate c‖≤(r : ℝ)) :
    ‖rho‖≤1-(rootCertificateDiskMargin c r : ℝ) := by
  have hi := rootRationalDiskClassify_true c r hc
  have hr0 : (0 : ℝ)<r := by exact_mod_cast hr
  have hr1 : (r : ℝ)<1 := by exact_mod_cast hi.1
  have hs : ‖rootRationalCoordinate c‖^2<(1-(r : ℝ))^2 := by
    rw [rootRationalCoordinate_sq_norm]
    exact_mod_cast hi.2
  have hx0 := norm_nonneg (rootRationalCoordinate c)
  have hx : ‖rootRationalCoordinate c‖<1-(r : ℝ) := by nlinarith
  have hm : (rootCertificateDiskMargin c r : ℝ)=
      ((1-(r : ℝ))^2-‖rootRationalCoordinate c‖^2)/2 := by
    rw [rootRationalCoordinate_sq_norm]
    norm_num [rootCertificateDiskMargin]
  have hprod : 0≤(1-(r : ℝ)-‖rootRationalCoordinate c‖)*
      (1+(r : ℝ)-‖rootRationalCoordinate c‖) :=
    mul_nonneg (by linarith) (by linarith)
  have hmargin : (rootCertificateDiskMargin c r : ℝ)≤
      1-(r : ℝ)-‖rootRationalCoordinate c‖ := by rw [hm]; nlinarith
  have hnorm : ‖rho‖≤(r : ℝ)+‖rootRationalCoordinate c‖ := by
    calc
      _=‖(rho-rootRationalCoordinate c)+rootRationalCoordinate c‖ := by congr 1; ring
      _≤‖rho-rootRationalCoordinate c‖+‖rootRationalCoordinate c‖ := norm_add_le _ _
      _≤_ := add_le_add hd le_rfl
  linarith

/-- One numeric entry per original disk position, no deduplication. -/
def rootCertificateMarginValues {m : ℕ} (f : Fin m → RootIntegerFactorData) : List ℚ :=
  (List.finRange m).flatMap (fun j => (List.finRange ((f j).n+1)).map (fun i =>
    if rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i)=true
    then rootCertificateDiskMargin ((f j).centers i) ((f j).radii i) else 1))

/-- Empty/outside-only data yield1; every actual inside margin participates. -/
def rootDecodedCertificateGap {m : ℕ} (f : Fin m → RootIntegerFactorData) : ℚ :=
  (rootCertificateMarginValues f).foldl min 1

/-- The finite construction in `NativeRootCertificateGap` satisfies `rootMarginFold_le_init` under the displayed hypotheses. -/
private theorem rootMarginFold_le_init (l : List ℚ) (s : ℚ) : (l.foldl min s) ≤ s := by
  induction l generalizing s with
  | nil => exact le_rfl
  | cons a l ih =>
    rw [List.foldl_cons]
    exact (ih (min s a)).trans (min_le_left _ _)

/-- The finite construction in `NativeRootCertificateGap` satisfies `rootMarginFold_le_mem` under the displayed hypotheses. -/
private theorem rootMarginFold_le_mem (l : List ℚ) (s x : ℚ) (hx : x∈l) :
    (l.foldl min s) ≤ x := by
  induction l generalizing s with
  | nil => cases hx
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with he|he
    · subst x
      exact (rootMarginFold_le_init l (min s a)).trans (min_le_right _ _)
    · exact ih (min s a) he

/-- The finite construction in `NativeRootCertificateGap` satisfies `rootMarginFold_pos` under the displayed hypotheses. -/
private theorem rootMarginFold_pos (l : List ℚ) :
    ∀ s,0<s → (∀ x∈l,0<x) → 0 < (l.foldl min s) := by
  induction l with
  | nil => intro s hs _; exact hs
  | cons a l ih =>
    intro s hs h
    rw [List.foldl_cons]
    exact ih (min s a) (lt_min hs (h a (by simp)))
      (fun x hx => h x (List.mem_cons_of_mem a hx))

/-- The finite construction in `NativeRootCertificateGap` satisfies `rootDecodedCertificateGap_le_one` under the displayed hypotheses. -/
theorem rootDecodedCertificateGap_le_one {m : ℕ} (f : Fin m → RootIntegerFactorData) :
    rootDecodedCertificateGap f≤1 := rootMarginFold_le_init _ _

/-- The finite construction in `NativeRootCertificateGap` satisfies `rootDecodedCertificateGap_le_margin` under the displayed hypotheses. -/
theorem rootDecodedCertificateGap_le_margin {m : ℕ} (f : Fin m → RootIntegerFactorData)
    (j : Fin m) (i : Fin ((f j).n+1))
    (ht : rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i)=true) :
    rootDecodedCertificateGap f≤rootCertificateDiskMargin ((f j).centers i) ((f j).radii i) := by
  apply rootMarginFold_le_mem
  unfold rootCertificateMarginValues
  apply List.mem_flatMap.mpr
  refine ⟨j,by simp,?_⟩
  apply List.mem_map.mpr
  exact ⟨i,by simp,by simp only [ite_eq_left ht]⟩

/-- The finite construction in `NativeRootCertificateGap` satisfies `rootDecodedCertificateGap_pos` under the displayed hypotheses. -/
theorem rootDecodedCertificateGap_pos {m : ℕ} (f : Fin m → RootIntegerFactorData) (eta : ℚ)
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) eta) : 0<rootDecodedCertificateGap f := by
  apply rootMarginFold_pos _ _ (by norm_num)
  intro x hx
  unfold rootCertificateMarginValues at hx
  obtain ⟨j,_,hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  by_cases ht : rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i)=true
  · simp only [ite_eq_left ht]
    apply rootCertificateDiskMargin_pos
    have h := rootRationalDiskClassify_computed_tag ((f j).centers i)
      ((f j).radii i) ((haccepted j).classified i)
    simpa only [ht] using h
  · simp only [ite_eq_right ht]
    norm_num

/-- ALL original inside roots have the rational gap computed from raw disks.
The catalogue and side information are obtained from the original certificate. -/
theorem rootDecodedCertificate_inside_gap (m : ℕ) (target : List ℤ) (content : ℤ)
    (f : Fin m → RootIntegerFactorData) (eta : ℚ) (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients target)
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) eta) :
    ∀ rho∈(rootIntegerListPolynomial target).roots,‖rho‖<1 →
      ‖rho‖≤1-(rootDecodedCertificateGap f : ℝ) := by
  obtain ⟨w,hw,hinj,hroots,hside,hreturn⟩ :=
    rootDecodedCertificate_sound m target content f eta hcontent hguard haccepted
  intro rho hmem hi
  rw [hroots] at hmem
  obtain ⟨j,_,hj⟩ := Multiset.mem_bind.mp hmem
  have himg : rho∈(Finset.univ.image (w j)).val := Multiset.mem_of_mem_nsmul hj
  have himg' : rho∈Finset.univ.image (w j) := himg
  obtain ⟨i,_,he⟩ := Finset.mem_image.mp himg'
  subst rho
  have ht := (hside j i).mp hi
  have hc := rootRationalDiskClassify_computed_tag ((f j).centers i)
    ((f j).radii i) ((haccepted j).classified i)
  have hd := rootCertificateDiskMargin_norm ((f j).centers i) ((f j).radii i)
    ((haccepted j).radius_pos i) (by simpa only [ht] using hc) (w j i) (hw j i).2
  have hg : (rootDecodedCertificateGap f : ℝ)≤
      (rootCertificateDiskMargin ((f j).centers i) ((f j).radii i) : ℝ) := by
    exact_mod_cast rootDecodedCertificateGap_le_margin f j i ht
  linarith

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
