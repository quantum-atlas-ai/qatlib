/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceInitialPivot
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceIdealExtremes
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceDeflationStep
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Same original-input Gaussian Gram normalization and first deflation: FirstDeflation.
This does not certify subsequent ideal preservation, the whole loop, interpreter or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section InitialErrorBudget

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- The estimate `coefficient_factor_bound` retains the actual parameter, input-error and normalization budgets. -/
private theorem coefficient_factor_bound (d M u g : ℝ) (hd : 0<d) (hdM : d ≤ M)
    (hM : 1 ≤ M) (hu : 0<u) (hu1 : u ≤ 1/2) (hg : 3*u/(1024*d^2) ≤ g) :
    16*d/g+2 ≤ 2^20*M^6/u^2 := by
  let S := M^6/u^2
  have hM0 : 0 ≤ M := by linarith
  have hM3 : (1 : ℝ) ≤ M^3 := one_le_pow₀ hM
  have hp : d^3 ≤ M^6 := (pow_le_pow_left₀ hd.le hdM 3).trans (by nlinarith [sq_nonneg (M^3-1)])
  have hS : 1 ≤ S := by
    dsimp [S]
    apply (le_div_iff₀ (sq_pos_of_pos hu)).mpr
    have h6 : (1 : ℝ) ≤ M^6 := one_le_pow₀ hM
    nlinarith
  have hdu : d^3/u ≤ S := by
    apply (div_le_div_iff₀ hu (sq_pos_of_pos hu)).mpr
    have hsq : u^2 ≤ u := by nlinarith
    exact (mul_le_mul_of_nonneg_left hsq (pow_nonneg hd.le 3)).trans
      (mul_le_mul_of_nonneg_right hp hu.le)
  have hg0 : 0<3*u/(1024*d^2) := by positivity
  have h16 : 16*d/g ≤ 16384*S := by
    calc
      _ ≤ 16*d/(3*u/(1024*d^2)) := div_le_div_of_nonneg_left (by positivity) hg0 hg
      _ = 16384*d^3/(3*u) := by field_simp [hu.ne',hd.ne']; ring
      _ ≤ 16384*d^3/u := div_le_div_of_nonneg_left (by positivity) hu (by linarith)
      _ = 16384*(d^3/u) := by ring
      _ ≤ 16384*S := mul_le_mul_of_nonneg_left hdu (by norm_num)
  calc
    _ ≤ 16386*S := by linarith
    _ ≤ 1048576*S := by nlinarith
    _ = _ := by norm_num [S]; ring

/-- The estimate `source_initial_error_budget` retains the actual parameter, input-error and normalization budgets. -/
theorem source_initial_error_budget (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
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
 :
    let u := sourceInputU cs N E
    let K := sourceK N u
    let eta := sourceInputEta cs N E
    let h := sourceGrid N u
    (eta : ℝ) ≤ (K : ℝ)*(eta : ℝ) ∧ (K : ℝ)*(eta : ℝ) ≤ (h : ℝ)/16 ∧
      ∀ j,‖sourceDecodeCompletionMatrix (sourceRoundedMatrix cs N E f j)-sourceIdealMatrixArray cs N E j‖ ≤
        (K : ℝ)*(eta : ℝ) := by
  let u := sourceInputU cs N E
  let K := sourceK N u
  let eta := sourceInputEta cs N E
  let h := sourceGrid N u
  have hu : (0 : ℝ)<(u : ℝ) := by exact_mod_cast sourceInputU_pos cs N E hE
  have hu1 : (u : ℝ) ≤ 1/2 := by
    have hq : u ≤ (1/2 : ℚ) := sourceInputU_le_half cs N E
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq
  have he : (0 : ℝ)<(eta : ℝ) := by dsimp [eta,sourceInputEta]; positivity
  have hdR : (0 : ℝ)<(sourceDegree cs N E : ℝ) := by exact_mod_cast hd
  have hM : (1 : ℝ) ≤ N+1 := by have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
  have hdM : (sourceDegree cs N E : ℝ) ≤ N+1 := by exact_mod_cast (Nat.le_succ_of_le (sourceDegree_le cs N E))
  have hg := sourceCertificateGap_lower cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted
  have hgR : (3*(u : ℝ)/(1024*(sourceDegree cs N E : ℝ)^2)) ≤ (rootDecodedCertificateGap f : ℝ) := by
    have hc : ((sourceGamma0 cs N E/8 : ℚ) : ℝ) ≤ (rootDecodedCertificateGap f : ℝ) := by exact_mod_cast hg
    convert hc using 1
    simp only [sourceGamma0,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast]
    dsimp [u]
    field_simp
    ring
  have hgpos : (0 : ℝ)<(rootDecodedCertificateGap f : ℝ) :=
    lt_of_lt_of_le (by positivity) hgR
  have hf := coefficient_factor_bound (sourceDegree cs N E : ℝ) (N+1 : ℝ) (u : ℝ)
    (rootDecodedCertificateGap f : ℝ) hdR hdM hM hu hu1 hgR
  have hKr : 16*(sourceDegree cs N E : ℝ)/(rootDecodedCertificateGap f : ℝ)+2 ≤ (K : ℝ) := by
    simpa only [K,sourceK,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one] using hf
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by
    have hnon : 0 ≤ 16*(sourceDegree cs N E : ℝ)/(rootDecodedCertificateGap f : ℝ) := by positivity
    linarith
  have hh : (0 : ℝ)<(h : ℝ) := by exact_mod_cast sourceGrid_pos N u
  have hh1 : (h : ℝ) ≤ 1 := by
    dsimp [h,sourceGrid]
    push_cast
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hL : (1 : ℝ) ≤ (128/(h : ℝ))^(N+1) := one_le_pow₀ ((le_div_iff₀ hh).mpr (by linarith))
  have hb : (K : ℝ)*(eta : ℝ)*(128/(h : ℝ))^(N+1) ≤ (h : ℝ)/16 := by
    exact_mod_cast (source_input_budget cs N E hE).1
  have hbudget : (K : ℝ)*(eta : ℝ) ≤ (h : ℝ)/16 :=
    (le_mul_of_one_le_right (by positivity) hL).trans hb
  refine ⟨by nlinarith,hbudget,?_⟩
  intro j
  have h := sourceRoundedMatrix_error_to_ideal_array cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted j
  rw [source_returned_length cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted] at h
  have hm := mul_le_mul_of_nonneg_right hKr he.le
  have heq : 16*((sourceDegree cs N E : ℝ)*(eta : ℝ)/(rootDecodedCertificateGap f : ℝ))+2*(eta : ℝ)=
      (16*(sourceDegree cs N E : ℝ)/(rootDecodedCertificateGap f : ℝ)+2)*(eta : ℝ) := by ring
  exact h.trans (heq.trans_le hm)

end InitialErrorBudget

section FirstDeflation

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- Construction for source First Deflation Array in the native source first deflation model. -/
def sourceFirstDeflationArray {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ)
    (f : Fin m → RootIntegerFactorData) {k : ℕ} (hk : sourceDegree cs N E=k+1) :
    Fin (k+2) → Matrix Bool Bool (ℚ×ℚ) :=
  fun j => sourceRoundedMatrix cs N E f ⟨j.val,by omega⟩

/-- Construction for source First Ideal Deflation Array in the native source first deflation model. -/
def sourceFirstIdealDeflationArray (cs : List ℚ) (N : ℕ) (E : ℚ) {k : ℕ} (hk : sourceDegree cs N E=k+1) :
    Fin (k+2) → Matrix Bool Bool ℂ :=
  fun j => sourceIdealMatrixArray cs N E ⟨j.val,by omega⟩

/-- The finite construction in `NativeSourceFirstDeflation` satisfies `source_first_deflation` under the displayed hypotheses. -/
theorem source_first_deflation (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
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
 :
    ∃ k : ℕ,∃ hk : sourceDegree cs N E=k+1,
      let F := sourceFirstDeflationArray cs N E f hk
      let G := sourceFirstIdealDeflationArray cs N E hk
      let eta := sourceInputEta cs N E
      let h := sourceGrid N (sourceInputU cs N E)
      let K := sourceK N (sourceInputU cs N E)
      ((sourceGaussianGramTrace (F 0)).2=0 ∧ 0<(sourceGaussianGramTrace (F 0)).1) ∧
        ((sourceGaussianGramTrace (F (Fin.last (k+1)))).2=0 ∧ 0<(sourceGaussianGramTrace (F (Fin.last (k+1)))).1) ∧
        ∀ j,‖sourceDecodeCompletionMatrix (sourceDeflationStep F eta j)-sourceIdealDeflationStep G j‖ ≤
          30*(K : ℝ)*(eta : ℝ)/(h : ℝ) := by
  let k := sourceDegree cs N E-1
  have hk : sourceDegree cs N E=k+1 := by dsimp [k]; omega
  refine ⟨k,hk,?_⟩
  let F := sourceFirstDeflationArray cs N E f hk
  let G := sourceFirstIdealDeflationArray cs N E hk
  let eta := sourceInputEta cs N E
  let h := sourceGrid N (sourceInputU cs N E)
  let K := sourceK N (sourceInputU cs N E)
  let delta : ℝ := (K : ℝ)*(eta : ℝ)
  have hb := source_initial_error_budget cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted
  have hh : (0 : ℝ)<(h : ℝ) := by exact_mod_cast sourceGrid_pos N (sourceInputU cs N E)
  have hh1 : (h : ℝ) ≤ 1 := by
    dsimp [h,sourceGrid]
    push_cast
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have he : ∀ j,‖sourceDecodeCompletionMatrix (F j)-G j‖ ≤ delta := by
    intro j
    exact hb.2.2 ⟨j.val,by omega⟩
  have hGn : ∀ j,‖G j‖ ≤ 1 := by
    intro j
    exact source_ideal_coefficient_norm cs N E hE htail hparity hd hnorm ⟨j.val,by omega⟩
  have hleft := source_ideal_extreme_rank_one cs N E hE htail hparity hd hnorm
    (⟨0,by omega⟩ : Fin (sourceDegree cs N E+1)) (Or.inl rfl)
  have hright := source_ideal_extreme_rank_one cs N E hE htail hparity hd hnorm
    (⟨k+1,by omega⟩ : Fin (sourceDegree cs N E+1)) (Or.inr hk.symm)
  have hs := sourceDeflationStep_error F G eta (by unfold eta sourceInputEta; positivity)
    delta (h : ℝ) hh hh1 (by have ht := hb.2.1; change delta ≤ (h : ℝ)/16 at ht; linarith)
    hb.1 he hGn hleft.1 hright.1 hleft.2 hright.2
  simpa only [delta,mul_assoc] using hs

end FirstDeflation

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
