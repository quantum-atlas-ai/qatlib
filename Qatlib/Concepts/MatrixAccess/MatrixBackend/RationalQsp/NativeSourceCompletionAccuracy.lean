/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceCertificateCap
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Original-input CFD source bridge: CompletionAccuracy.
The nonconstant branch uses the computed surviving degree.
This module does not certify spectral completion, deflation, interpreter refinement or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data

/-- Assume positive `E` and source degree, with a Chebyshev target of degree at most `N`, parity
`N`, and absolute value at most one on `[-1, 1]`. If guarded factors with nonzero content
reconstruct the integer complement and return as many roots as the source degree, the returned
coordinates lie inside the unit circle and match all interior roots with multiplicity to within
the root tolerance. The monic list has one more entry than roots. The actual-to-ideal product
ratio on the unit circle differs from one by at most `2 * s`, where `s` is the returned root
count times the tolerance divided by the decoded gap. The ratio at `1` is nonzero, and dividing
the ratio at each unit-circle point by the norm of the ratio at `1` gives error at most `8 * s`.
-/
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
