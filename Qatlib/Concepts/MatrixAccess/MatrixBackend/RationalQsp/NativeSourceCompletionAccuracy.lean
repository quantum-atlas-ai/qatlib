/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceCertificateCap
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Original-input CFD source bridge: CompletionAccuracy.
The nonconstant branch uses the computed surviving degree.
This module does not certify spectral completion, deflation, interpreter refinement or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data

/-- The finite construction in `NativeSourceCompletionAccuracy` satisfies `source_completion_accuracy` under the displayed hypotheses. -/
theorem source_completion_accuracy (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
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
  exact rootDecodedCertificate_completion_accuracy m (sourceIntegerComplement cs N E)
    content f (sourceInputEta cs N E) hcontent hguard haccepted
    (by unfold sourceInputEta; positivity)
    (sourceCertificate_numeric_cap cs N E hE htail hparity hd hnorm
      m content f hcontent hguard haccepted hcount)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
