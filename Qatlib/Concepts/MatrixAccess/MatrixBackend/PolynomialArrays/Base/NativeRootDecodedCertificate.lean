/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootFactorProduct
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootClassifiedCatalogue

set_option backward.isDefEq.respectTransparency false

/-! One same-input typed certificate: integer factor-product equality, all
integer root tests, complete multiplicities, computed sides and actual grid.
The parser, returned list and fee are not asserted by this theorem. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Polynomial
open scoped BigOperators

/-- Decoded factor data contain no roots, side flags or polynomial identities. -/
structure RootIntegerFactorData where
  n : ℕ
  coefficients : Fin (n+2) → ℤ
  exponent : ℕ
  centers : Fin (n+1) → ℚ×ℚ
  radii : Fin (n+1) → ℚ

/-- Only canonical and actual source arithmetic acceptance predicates. -/
structure RootIntegerFactorGuards (f : RootIntegerFactorData) (eta : ℚ) : Prop where
  leading : f.coefficients (Fin.last (f.n+1))≠0
  exponent_pos : 0<f.exponent
  radius_pos : ∀ i,0<f.radii i
  inclusion : ∀ i,
    (rootCompactHorner (rootSharedNumerator (f.centers i))
      (rootSharedDenominator (f.centers i)) (List.ofFn f.coefficients)).numerator=(0,0) ∨
    rootIntegerCoordinateBound (f.n+1)
      (rootCompactHorner (rootSharedNumerator (f.centers i))
        (rootSharedDenominator (f.centers i)) (List.ofFn f.coefficients))
      (rootCompactHorner (rootSharedNumerator (f.centers i))
        (rootSharedDenominator (f.centers i))
        (List.ofFn (rootIntegerDerivative f.n f.coefficients))) (f.radii i)
  separation : ∀ i j,i≠j → (f.radii i+f.radii j)^2<
    ((f.centers i).1-(f.centers j).1)^2+((f.centers i).2-(f.centers j).2)^2
  classified : ∀ i,rootRationalDiskClassify (f.centers i) (f.radii i)≠none
  eta_pos : ∀ i,rootRationalDiskComputedTag (f.centers i) (f.radii i)=true → 0<eta
  budget : ∀ i,rootRationalDiskComputedTag (f.centers i) (f.radii i)=true →
    f.radii i+|(rootGridPoint (f.centers i) (eta/16)).1-(f.centers i).1|+
      |(rootGridPoint (f.centers i) (eta/16)).2-(f.centers i).2|≤eta

/-- The actual coefficient-list guard, rather than an assumed product of
polynomials, determines the ORIGINAL target's entire root multiset. Shared
roots of different factors add multiplicities; coprimality is not assumed. -/
theorem rootDecodedCertificate_sound (m : ℕ) (target : List ℤ) (content : ℤ)
    (f : Fin m → RootIntegerFactorData) (eta : ℚ) (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients target)
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) eta) :
    ∃ w : (j : Fin m) → Fin ((f j).n+1) → ℂ,
      (∀ j i,(rootIntegerPolynomial (f j).coefficients).eval (w j i)=0 ∧
        ‖w j i-rootRationalCoordinate ((f j).centers i)‖≤((f j).radii i : ℝ)) ∧
      (∀ j,Function.Injective (w j)) ∧
      (rootIntegerListPolynomial target).roots=(Finset.univ : Finset (Fin m)).val.bind
        (fun j => (f j).exponent • (Finset.univ.image (w j)).val) ∧
      (∀ j i,‖w j i‖<1 ↔
        rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i)=true) ∧
      (∀ j i,rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i)=true →
        ‖rootRationalCoordinate (rootGridPoint ((f j).centers i) (eta/16))‖<1 ∧
        ‖rootRationalCoordinate (rootGridPoint ((f j).centers i) (eta/16))-w j i‖≤(eta : ℝ)) := by
  classical
  choose w hw hinj hroots hside hreturn using fun j => rootIntegerArray_classified_catalogue
    (f j).n (f j).coefficients (haccepted j).leading
    (f j).centers (f j).radii (haccepted j).radius_pos
    (haccepted j).inclusion (haccepted j).separation (haccepted j).classified eta
    (haccepted j).eta_pos (haccepted j).budget
  refine ⟨w,hw,hinj,?_,hside,hreturn⟩
  have hp : rootIntegerListPolynomial target=C (content : ℂ)*
      ∏ j,(rootIntegerPolynomial (f j).coefficients)^(f j).exponent := by
    have h := rootIntegerFactorProduct_guard target content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent))) hguard
    simpa only [List.map_ofFn,Function.comp_def,rootIntegerListPolynomial_ofFn,Fin.prod_ofFn] using h
  have hnz : ∀ j∈(Finset.univ : Finset (Fin m)),
      rootIntegerPolynomial (f j).coefficients≠0 := by
    intro j _ hz
    have hd := rootIntegerPolynomial_natDegree (f j).coefficients (haccepted j).leading
    rw [hz,Polynomial.natDegree_zero] at hd
    omega
  have hwhole := polynomial_factor_certificate_root_multiset Finset.univ
    (rootIntegerListPolynomial target) (content : ℂ)
    (fun j => rootIntegerPolynomial (f j).coefficients) (fun j => (f j).exponent)
    (by exact_mod_cast hcontent) hnz hp
  simpa only [hroots] using hwhole

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
