/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceSpectralNormalized
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceCompletionSqrt
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Same original-input spectral completion: StoredResponse.
This does not certify the full proposer, iterative deflation, interpreter or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section StoredResponse

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- Construction for source Returned Root Product in the native source stored response model. -/
def sourceReturnedRootProduct {m : ℕ} (f : Fin m → RootIntegerFactorData) (eta : ℚ) (z : ℂ) : ℂ :=
  (rootCompletionListPolynomial (rootCompletionMonicCoefficients (rootDecodedReturnList f eta))).eval z

/-- Construction for source Actual G1 Norm2 in the native source stored response model. -/
def sourceActualG1Norm2 {m : ℕ} (f : Fin m → RootIntegerFactorData) (eta : ℚ) : ℚ :=
  let g := rootCompletionCoefficientSum (rootCompletionMonicCoefficients (rootDecodedReturnList f eta))
  g.1^2+g.2^2

/-- Construction for source Actual Completion Alpha in the native source stored response model. -/
def sourceActualCompletionAlpha {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ) (f : Fin m → RootIntegerFactorData) : ℚ :=
  sourceActualH1 cs N E/sourceActualG1Norm2 f (sourceInputEta cs N E)

/-- Construction for source Stored Completion Scale in the native source stored response model. -/
def sourceStoredCompletionScale {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ) (f : Fin m → RootIntegerFactorData) : ℚ :=
  sourceSqrtLower (sourceActualCompletionAlpha cs N E f)
    (sourceCompletionSqrtBits (sourceDegree cs N E) (sourceInputEta cs N E))

/-- Construction for source Ideal Scaled Response in the native source stored response model. -/
def sourceIdealScaledResponse (cs : List ℚ) (N : ℕ) (E : ℚ) (z : ℂ) : ℂ :=
  (Real.sqrt (sourceActualH1 cs N E : ℝ) : ℂ)*sourceIdealProduct cs N E z/
    (‖sourceIdealProduct cs N E 1‖ : ℂ)

/-- Construction for source Stored Scaled Response in the native source stored response model. -/
def sourceStoredScaledResponse {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ)
    (f : Fin m → RootIntegerFactorData) (z : ℂ) : ℂ :=
  (sourceStoredCompletionScale cs N E f : ℂ)*sourceReturnedRootProduct f (sourceInputEta cs N E) z

/-- The finite construction in `NativeSourceStoredResponse` satisfies `sourceActualG1Norm2_eq` under the displayed hypotheses. -/
theorem sourceActualG1Norm2_eq {m : ℕ} (f : Fin m → RootIntegerFactorData) (eta : ℚ) :
    (sourceActualG1Norm2 f eta : ℝ)=‖sourceReturnedRootProduct f eta 1‖^2 := by
  rw [sourceReturnedRootProduct,← rootCompletionCoefficientSum_decode,rootRationalCoordinate_sq_norm]
  rfl

/-- The finite construction in `NativeSourceStoredResponse` satisfies `pair_inside` under the displayed hypotheses. -/
private theorem pair_inside {qs : List (ℚ×ℚ)} {zs : List ℂ} {eta : ℚ}
    (h : List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖<1 ∧
      ‖rootRationalCoordinate q-z‖≤(eta : ℝ)) qs zs) :
    ∀ q∈qs,‖rootRationalCoordinate q‖<1 := by
  induction h with
  | nil => simp
  | cons hhead htail ih =>
    intro q hq
    rcases List.mem_cons.mp hq with he|he
    · subst q; exact hhead.1
    · exact ih q he

/-- The estimate `unit_product_bound` retains the actual parameter, input-error and normalization budgets. -/
private theorem unit_product_bound (qs : List (ℚ×ℚ)) (z : ℂ) (hz : ‖z‖=1) :
    (∀ q∈qs,‖rootRationalCoordinate q‖<1) →
      ‖(qs.map (fun q => z-rootRationalCoordinate q)).prod‖ ≤ (2 : ℝ)^qs.length := by
  induction qs with
  | nil => intro _; simp
  | cons q qs ih =>
    intro h
    have hq : ‖z-rootRationalCoordinate q‖ ≤ 2 := by
      have ht := norm_sub_le z (rootRationalCoordinate q)
      rw [hz] at ht
      have hn := h q (by simp)
      linarith
    have htail := ih (fun r hr => h r (List.mem_cons_of_mem q hr))
    rw [List.map_cons,List.prod_cons,norm_mul,List.length_cons,pow_succ]
    calc
      _ ≤ 2*(2 : ℝ)^qs.length := mul_le_mul hq htail (norm_nonneg _) (by norm_num)
      _ = _ := by ring

/-- The finite construction in `NativeSourceStoredResponse` satisfies `alpha_sqrt` under the displayed hypotheses. -/
private theorem alpha_sqrt {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ)
    (f : Fin m → RootIntegerFactorData) (hh : 0<sourceActualH1 cs N E) :
    Real.sqrt (sourceActualCompletionAlpha cs N E f : ℝ)=Real.sqrt (sourceActualH1 cs N E : ℝ)/
      ‖sourceReturnedRootProduct f (sourceInputEta cs N E) 1‖ := by
  have hhR : (0 : ℝ) ≤ (sourceActualH1 cs N E : ℝ) := by exact_mod_cast hh.le
  rw [sourceActualCompletionAlpha,Rat.cast_div,sourceActualG1Norm2_eq,Real.sqrt_div hhR,
    Real.sqrt_sq (norm_nonneg _)]

/-- The finite construction in `NativeSourceStoredResponse` satisfies `idealScaled_norm` under the displayed hypotheses. -/
private theorem idealScaled_norm (cs : List ℚ) (N : ℕ) (E : ℚ) (z : ℂ) :
    ‖sourceIdealScaledResponse cs N E z‖=Real.sqrt (sourceActualH1 cs N E : ℝ)*
      ‖sourceIdealProduct cs N E z/sourceIdealProduct cs N E 1‖ := by
  unfold sourceIdealScaledResponse
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _),norm_div,mul_div_assoc]

/-- The finite construction in `NativeSourceStoredResponse` satisfies `normalized_difference` under the displayed hypotheses. -/
private theorem normalized_difference (H : ℝ) (Iz I1 Az A1 : ℂ)
    (hIz : Iz≠0) (hI1 : I1≠0) (hA1 : A1≠0) :
    (H : ℂ)*Az/(‖A1‖ : ℂ)-(H : ℂ)*Iz/(‖I1‖ : ℂ)=
      ((H : ℂ)*Iz/(‖I1‖ : ℂ))*((Az/Iz)/(‖A1/I1‖ : ℂ)-1) := by
  have hi : (‖I1‖ : ℂ)≠0 := by exact_mod_cast (norm_pos_iff.mpr hI1).ne'
  have ha : (‖A1‖ : ℂ)≠0 := by exact_mod_cast (norm_pos_iff.mpr hA1).ne'
  rw [norm_div,Complex.ofReal_div]
  field_simp [hIz,hi,ha]

/-- The estimate `sourceStoredScaled_error` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceStoredScaled_error (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
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
    0<sourceActualG1Norm2 f (sourceInputEta cs N E) ∧
      ∀ z : ℂ,‖z‖=1 →
        ‖sourceStoredScaledResponse cs N E f z-sourceIdealScaledResponse cs N E z‖ ≤
          8*(((rootDecodedReturnList f (sourceInputEta cs N E)).length : ℝ)*
            (sourceInputEta cs N E : ℝ)/(rootDecodedCertificateGap f : ℝ))+
          (sourceInputEta cs N E : ℝ)/2 := by
  obtain ⟨zs,hm,hpair,_hlen,hbound⟩ := source_completion_accuracy_without_count
    cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted
  have hideal (z : ℂ) : (zs.map (fun r => z-r)).prod=sourceIdealProduct cs N E z := by
    unfold sourceIdealProduct sourceInsideRoots
    rw [← hm]
    simp only [Multiset.map_coe,Multiset.prod_coe]
  have hA1 : sourceReturnedRootProduct f (sourceInputEta cs N E) 1≠0 := by
    have h := (hbound 1 (norm_one : ‖(1 : ℂ)‖=1)).2.1
    dsimp only at h
    rw [hideal] at h
    exact (div_ne_zero_iff.mp h).1
  have hn2 : 0<sourceActualG1Norm2 f (sourceInputEta cs N E) := by
    have hr : (0 : ℝ)<(sourceActualG1Norm2 f (sourceInputEta cs N E) : ℝ) := by
      rw [sourceActualG1Norm2_eq]
      exact pow_pos (norm_pos_iff.mpr hA1) 2
    exact_mod_cast hr
  refine ⟨hn2,?_⟩
  intro z hz
  let eta := sourceInputEta cs N E
  let d := sourceDegree cs N E
  let alpha := sourceActualCompletionAlpha cs N E f
  let q := sourceCompletionSqrtBits d eta
  let exact := (Real.sqrt (alpha : ℝ) : ℂ)*sourceReturnedRootProduct f eta z
  have hh := sourceActualH1_pos cs N E hE htail hnorm
  have heta : 0<eta := by dsimp [eta,sourceInputEta]; positivity
  have halpha : 0 ≤ alpha := (div_pos hh hn2).le
  have hsqrt := sourceSqrtLower_error alpha halpha q
  have hbudget : 1/(2 : ℝ)^q ≤ (eta : ℝ)/(2*(3 : ℝ)^d) := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr (sourceCompletionSqrtBits_envelope d eta heta)
  have hscalar : ‖(sourceSqrtLower alpha q : ℂ)-(Real.sqrt (alpha : ℝ) : ℂ)‖ ≤
      (eta : ℝ)/(2*(3 : ℝ)^d) := by
    rw [← Complex.ofReal_ratCast,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hsqrt.1)]
    linarith [hsqrt.2.le.trans hbudget]
  have hinside := pair_inside hpair
  have hcount := source_returned_length cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted
  have hprod : ‖sourceReturnedRootProduct f eta z‖ ≤ (3 : ℝ)^d := by
    unfold sourceReturnedRootProduct
    rw [rootCompletionMonicCoefficients_eval]
    exact (unit_product_bound _ z hz hinside).trans
      (by rw [hcount]; exact pow_le_pow_left₀ (by norm_num) (by norm_num : (2 : ℝ) ≤ 3) _)
  have hstore : ‖sourceStoredScaledResponse cs N E f z-exact‖ ≤ (eta : ℝ)/2 := by
    change ‖(sourceSqrtLower alpha q : ℂ)*sourceReturnedRootProduct f eta z-
      (Real.sqrt (alpha : ℝ) : ℂ)*sourceReturnedRootProduct f eta z‖ ≤ _
    rw [← sub_mul,norm_mul]
    calc
      _ ≤ ((eta : ℝ)/(2*(3 : ℝ)^d))*(3 : ℝ)^d :=
        mul_le_mul hscalar hprod (norm_nonneg _) (by positivity)
      _ = (eta : ℝ)/2 := by field_simp
  have he : exact=(Real.sqrt (sourceActualH1 cs N E : ℝ) : ℂ)*sourceReturnedRootProduct f eta z/
      (‖sourceReturnedRootProduct f eta 1‖ : ℂ) := by
    dsimp [exact,alpha]
    rw [alpha_sqrt cs N E f hh,Complex.ofReal_div]
    ring
  have herr := (hbound z hz).2.2
  simp only [hideal] at herr
  have hnormI : ‖sourceIdealScaledResponse cs N E z‖ ≤ 1 := by
    rw [idealScaled_norm]
    exact sourceIdealNormalized_norm_le_one cs N E hE htail hparity hd hnorm z hz
  have hnormalized : ‖exact-sourceIdealScaledResponse cs N E z‖ ≤
      8*(((rootDecodedReturnList f eta).length : ℝ)*(eta : ℝ)/(rootDecodedCertificateGap f : ℝ)) := by
    rw [he,sourceIdealScaledResponse,normalized_difference _ _ _ _ _
      (sourceIdealProduct_ne_zero cs N E z hz)
      (sourceIdealProduct_ne_zero cs N E 1 (norm_one : ‖(1 : ℂ)‖=1)) hA1,norm_mul]
    exact (mul_le_mul_of_nonneg_right hnormI (norm_nonneg _)).trans
      (by simpa only [one_mul, sourceReturnedRootProduct, eta] using herr)
  calc
    _ = ‖(sourceStoredScaledResponse cs N E f z-exact)+(exact-sourceIdealScaledResponse cs N E z)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ (eta : ℝ)/2+8*(((rootDecodedReturnList f eta).length : ℝ)*(eta : ℝ)/
        (rootDecodedCertificateGap f : ℝ)) := add_le_add hstore hnormalized
    _ = _ := by ring

end StoredResponse

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
