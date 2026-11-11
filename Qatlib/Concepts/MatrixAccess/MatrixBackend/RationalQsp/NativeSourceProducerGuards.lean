/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceRootCount
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Actual original-input H: reciprocal roots, multiplicity and source guards.
This does not certify the full proposer, interpreter, spectral deflation or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- The finite construction in `NativeSourceProducerGuards` satisfies `source_proposer_root_prerequisites` under the displayed hypotheses. -/
theorem source_proposer_root_prerequisites (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    (rootIntegerListPolynomial (sourceIntegerComplement cs N E)).roots.card=2*sourceDegree cs N E ∧
      ((rootIntegerListPolynomial (sourceIntegerComplement cs N E)).roots.filter
        (fun z => ‖z‖<1)).card=sourceDegree cs N E ∧
      (∀ rho : ℂ,(rootIntegerListPolynomial (sourceIntegerComplement cs N E)).eval rho=0 →
        (sourceGamma0 cs N E : ℝ) ≤ |‖rho‖-1|) := by
  refine ⟨?_,sourceIntegerComplement_inside_count cs N E hE htail hparity hd hnorm,?_⟩
  · rw [sourceIntegerComplement_roots cs N E hparity hd,IsAlgClosed.card_roots_eq_natDegree,
      sourceF_natDegree_eq cs N E hd]
  · exact sourceIntegerComplement_all_roots_gap cs N E hE htail hparity hd hnorm

/-- The same emitted instruction list satisfies `source_returned_length` with the displayed gate and query accounting. -/
theorem source_returned_length (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
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
    (rootDecodedReturnList f (sourceInputEta cs N E)).length=sourceDegree cs N E := by
  obtain ⟨zs,hm,hpair⟩ := rootDecodedCertificate_returned m (sourceIntegerComplement cs N E)
    content f (sourceInputEta cs N E) hcontent hguard haccepted
  have hc := congrArg Multiset.card hm
  have hlen : zs.length=((rootIntegerListPolynomial (sourceIntegerComplement cs N E)).roots.filter
      (fun z => ‖z‖<1)).card := by simpa only [Multiset.coe_card] using hc
  rw [hpair.length_eq,hlen]
  exact sourceIntegerComplement_inside_count cs N E hE htail hparity hd hnorm

/-- The same emitted instruction list satisfies `source_completion_accuracy_without_count` with the displayed gate and query accounting. -/
theorem source_completion_accuracy_without_count (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
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
    ∃ zs : List ℂ,
      (zs : Multiset ℂ)=(rootIntegerListPolynomial (sourceIntegerComplement cs N E)).roots.filter
        (fun z => ‖z‖<1) ∧
      List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖<1 ∧
        ‖rootRationalCoordinate q-z‖ ≤ (sourceInputEta cs N E : ℝ))
        (rootDecodedReturnList f (sourceInputEta cs N E)) zs ∧
      (rootCompletionMonicCoefficients (rootDecodedReturnList f (sourceInputEta cs N E))).length=
        zs.length+1 ∧
      (∀ z : ℂ,‖z‖=1 →
        let actual := (rootCompletionListPolynomial
          (rootCompletionMonicCoefficients (rootDecodedReturnList f (sourceInputEta cs N E)))).eval
        let ideal := fun w : ℂ => (zs.map (fun rho => w-rho)).prod
        let s := ((rootDecodedReturnList f (sourceInputEta cs N E)).length : ℝ)*
          (sourceInputEta cs N E : ℝ)/(rootDecodedCertificateGap f : ℝ)
        ‖actual z/ideal z-1‖ ≤ 2*s ∧
        actual 1/ideal 1≠0 ∧
        ‖(actual z/ideal z)/(‖actual 1/ideal 1‖ : ℂ)-1‖ ≤ 8*s) := by
  exact source_completion_accuracy cs N E hE htail hparity hd hnorm
    m content f hcontent hguard haccepted
    (source_returned_length cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
