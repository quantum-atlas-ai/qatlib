/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeRootCompletionProductBound
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeRootCertificateGap
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Uniform accuracy for the actual monic array from the SAME original integer
root target and raw disk guards. The positive rational gap is computed from
those disks. The ideal full inside catalogue and matching errors are outputs,
not extra input answers. This does not yet bind original cs/n/E to H, prove
the source cap from R, complete spectral factorization/deflation, or charge fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords

open scoped BigOperators

/-- Scalar accuracy helper for the same product ratios at z and1; the actual
raw-input consumer must derive these two hypotheses, not receive final errors. -/
private theorem rootCompletion_normalizedRatioError (Rz R1 : ℂ) (s : ℝ) (hs : 0 ≤ s) (hcap : s ≤ 1/4)
    (hz : ‖Rz-1‖ ≤ 2*s) (h1 : ‖R1-1‖ ≤ 2*s) :
    R1≠0 ∧ ‖Rz/(‖R1‖ : ℂ)-1‖ ≤ 8*s := by
  have hd : |‖R1‖-1| ≤ 2*s := by
    have h := abs_norm_sub_norm_le R1 1
    rw [norm_one] at h
    exact h.trans h1
  have hl : 1-2*s ≤ ‖R1‖ := by linarith [(abs_le.mp hd).1]
  have hh : (1/2 : ℝ) ≤ ‖R1‖ := by linarith
  have hp : 0<‖R1‖ := by linarith
  refine ⟨norm_pos_iff.mp hp,?_⟩
  have hc : (‖R1‖ : ℂ)≠0 := by exact_mod_cast ne_of_gt hp
  have he : Rz/(‖R1‖ : ℂ)-1=(Rz-(‖R1‖ : ℂ))/(‖R1‖ : ℂ) := by
    field_simp [hc]
  have ha : ‖(1 : ℂ)-(‖R1‖ : ℂ)‖ ≤ 2*s := by
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_sub_comm]
    exact hd
  have hb : ‖Rz-(‖R1‖ : ℂ)‖ ≤ 4*s := by
    calc
      _=‖(Rz-1)+(1-(‖R1‖ : ℂ))‖ := by congr 1; ring
      _ ≤ ‖Rz-1‖+‖(1 : ℂ)-(‖R1‖ : ℂ)‖ := norm_add_le _ _
      _ ≤ 2*s+2*s := add_le_add hz ha
      _=4*s := by ring
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  have hm := mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ 8*s)
  nlinarith


/-- The estimate `rootCompletionList_relative_bound` retains the actual parameter, input-error and normalization budgets. -/
private theorem rootCompletionList_relative_bound (qs : List (ℚ×ℚ)) (zs : List ℂ)
    (eta gamma : ℝ) (heta : 0 ≤ eta) (hgamma : 0<gamma)
    (hpair : List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖<1 ∧
      ‖rootRationalCoordinate q-z‖ ≤ eta) qs zs)
    (z : ℂ) (hgap : ∀ rho∈zs,gamma ≤ ‖z-rho‖)
    (hcap : (qs.length : ℝ)*eta/gamma ≤ 1) :
    ‖(rootCompletionListPolynomial (rootCompletionMonicCoefficients qs)).eval z/
      (zs.map (fun rho => z-rho)).prod-1‖ ≤ 2*((qs.length : ℝ)*eta/gamma) := by
  let r : Fin qs.length → ℂ := fun i => zs.get (Fin.cast hpair.length_eq i)
  have hrlist : List.ofFn r=zs := by
    exact (List.ofFn_congr hpair.length_eq.symm zs.get).symm.trans (List.ofFn_get zs)
  have herr (i : Fin qs.length) : ‖rootRationalCoordinate (qs.get i)-r i‖ ≤ eta :=
    (hpair.get i.isLt (by simpa only [← hpair.length_eq] using i.isLt)).2
  have hg (i : Fin qs.length) : gamma ≤ ‖z-r i‖ :=
    hgap (r i) (List.get_mem _ _)
  have h := rootCompletionMonic_relative_bound qs.get r z eta gamma heta hgamma hg herr hcap
  have hp : (∏ i : Fin qs.length,(z-r i))=(zs.map (fun rho => z-rho)).prod := by
    rw [← Fin.prod_ofFn,List.ofFn_comp' r (fun rho => z-rho),hrlist]
  rw [List.ofFn_get,hp] at h
  exact h

/-- The same complete original inside root list controls the actual array at
EVERY unit-circle point, using only raw guards and a computed numeric cap.
No supplied ideal roots, root gaps, or final errors occur in the input. -/
theorem rootDecodedCertificate_completion_accuracy (m : ℕ) (target : List ℤ)
    (content : ℤ) (f : Fin m → RootIntegerFactorData) (eta : ℚ)
    (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients target)
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) eta)
    (heta : 0 ≤ eta)
    (hcapQ : ((rootDecodedReturnList f eta).length : ℚ)*eta/
      rootDecodedCertificateGap f ≤ 1/4) :
    ∃ zs : List ℂ,
      (zs : Multiset ℂ)=(rootIntegerListPolynomial target).roots.filter (fun z => ‖z‖<1) ∧
      List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖<1 ∧
        ‖rootRationalCoordinate q-z‖ ≤ (eta : ℝ)) (rootDecodedReturnList f eta) zs ∧
      (rootCompletionMonicCoefficients (rootDecodedReturnList f eta)).length=zs.length+1 ∧
      (∀ z : ℂ,‖z‖=1 →
        let actual := (rootCompletionListPolynomial
          (rootCompletionMonicCoefficients (rootDecodedReturnList f eta))).eval
        let ideal := fun w : ℂ => (zs.map (fun rho => w-rho)).prod
        let s := ((rootDecodedReturnList f eta).length : ℝ)*(eta : ℝ)/
          (rootDecodedCertificateGap f : ℝ)
        ‖actual z/ideal z-1‖ ≤ 2*s ∧
        actual 1/ideal 1≠0 ∧
        ‖(actual z/ideal z)/(‖actual 1/ideal 1‖ : ℂ)-1‖ ≤ 8*s) := by
  have hcap : ((rootDecodedReturnList f eta).length : ℝ)*(eta : ℝ)/
      (rootDecodedCertificateGap f : ℝ) ≤ 1/4 := by
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_one,Rat.cast_ofNat]
      using (Rat.cast_le (K := ℝ)).mpr hcapQ
  obtain ⟨zs,hm,hpair,hlen,hpos⟩ :=
    rootDecodedCertificate_completion_normalizer m target content f eta hcontent hguard haccepted
  have hgamma : 0<(rootDecodedCertificateGap f : ℝ) := by
    exact_mod_cast rootDecodedCertificateGap_pos f eta haccepted
  have hetaR : (0 : ℝ) ≤ eta := by exact_mod_cast heta
  have hrad (rho : ℂ) (hrho : rho∈zs) : ‖rho‖ ≤ 1-(rootDecodedCertificateGap f : ℝ) := by
    have hmem : rho∈(zs : Multiset ℂ) := hrho
    rw [hm] at hmem
    obtain ⟨hroot,hi⟩ := Multiset.mem_filter.mp hmem
    exact rootDecodedCertificate_inside_gap m target content f eta hcontent hguard haccepted
      rho hroot hi
  have hbound (z : ℂ) (hz : ‖z‖=1) :
      ‖(rootCompletionListPolynomial
        (rootCompletionMonicCoefficients (rootDecodedReturnList f eta))).eval z/
        (zs.map (fun rho => z-rho)).prod-1‖ ≤
        2*(((rootDecodedReturnList f eta).length : ℝ)*(eta : ℝ)/
          (rootDecodedCertificateGap f : ℝ)) := by
    apply rootCompletionList_relative_bound _ zs (eta : ℝ)
      (rootDecodedCertificateGap f : ℝ) hetaR hgamma hpair z
    · intro rho hrho
      have hn := norm_sub_norm_le z rho
      rw [hz] at hn
      linarith [hrad rho hrho]
    · linarith
  refine ⟨zs,hm,hpair,hlen,?_⟩
  intro z hz
  dsimp only
  have hs : 0 ≤ ((rootDecodedReturnList f eta).length : ℝ)*(eta : ℝ)/
      (rootDecodedCertificateGap f : ℝ) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hetaR) hgamma.le
  exact ⟨hbound z hz,rootCompletion_normalizedRatioError _ _ _ hs hcap
    (hbound z hz) (hbound 1 (norm_one : ‖(1 : ℂ)‖=1))⟩

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
