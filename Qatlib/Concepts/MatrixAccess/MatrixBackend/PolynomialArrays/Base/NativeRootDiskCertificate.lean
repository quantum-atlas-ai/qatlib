/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootDiskCompleteness

set_option backward.isDefEq.respectTransparency false

/-! One mathematical certificate consumer matching factor product, actual
coordinate acceptance, complete multiplicities, side and forward precision.
The supplied algebraic/rational predicates still need executable decoding and
integer-Horner transport; no Python execution or cost theorem is asserted. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Polynomial
open scoped BigOperators

/-- The factor-family certificate determines H's ENTIRE root multiset. Raw
returned coordinates need not be distinct. Factors need not be coprime. -/
theorem polynomial_root_coordinate_certificate (m : ℕ) (H : ℂ[X]) (content : ℂ)
    (f : Fin m → ℂ[X]) (e : Fin m → ℕ)
    (c q : (j : Fin m) → Fin (f j).natDegree → ℂ)
    (r : (j : Fin m) → Fin (f j).natDegree → ℝ)
    (inside : (j : Fin m) → Fin (f j).natDegree → Bool) (eta : ℝ)
    (hcontent : content≠0) (hf : ∀ j,0<(f j).natDegree)
    (hproduct : H=C content*∏ j,(f j)^e j)
    (hr : ∀ j i,0<r j i)
    (htest : ∀ j i,((f j).natDegree : ℝ)*
        (|((f j).eval (c j i)).re|+|((f j).eval (c j i)).im|)≤
      r j i*max |((f j).derivative.eval (c j i)).re|
        |((f j).derivative.eval (c j i)).im|)
    (hsep : ∀ j i k,i≠k → (r j i+r j k)^2<
      (c j i-c j k).re^2+(c j i-c j k).im^2)
    (hbudget : ∀ j i,inside j i=true →
      r j i+|(q j i-c j i).re|+|(q j i-c j i).im|≤eta)
    (hside : ∀ j i,if inside j i then
        r j i<1 ∧ (c j i).re^2+(c j i).im^2<(1-r j i)^2
      else (1+r j i)^2<(c j i).re^2+(c j i).im^2) :
    ∃ w : (j : Fin m) → Fin (f j).natDegree → ℂ,
      (∀ j i,(f j).eval (w j i)=0 ∧ ‖w j i-c j i‖≤r j i) ∧
      (∀ j,Function.Injective (w j)) ∧
      H.roots=(Finset.univ : Finset (Fin m)).val.bind
        (fun j => e j • (Finset.univ.image (w j)).val) ∧
      (∀ j i,inside j i=true → ‖q j i-w j i‖≤eta) ∧
      (∀ j i,‖w j i‖<1 ↔ inside j i=true) := by
  classical
  choose w hw hinj hcatalog using fun j => polynomial_disjoint_coordinate_disks_complete
    (f j) (hf j) (c j) (r j) (hr j) (htest j) (hsep j)
  refine ⟨w,hw,hinj,?_,?_,?_⟩
  · have hnonzero : ∀ j∈(Finset.univ : Finset (Fin m)),f j≠0 := by
      intro j _ hz
      have h := hf j
      simp [hz] at h
    have hroots := polynomial_factor_certificate_root_multiset
      Finset.univ H content f e hcontent hnonzero hproduct
    simpa only [hcatalog] using hroots
  · intro j i hinside
    exact root_disk_returned_coordinate_error (c j i) (w j i) (q j i)
      (r j i) eta (hw j i).2 (hbudget j i hinside)
  · intro j i
    cases hflag : inside j i with
    | false =>
      have houtside := hside j i
      simp only [hflag,Bool.false_eq_true,ite_false] at houtside
      have hsquared : (1+r j i)^2<‖c j i‖^2 := by
        rw [Complex.sq_norm,Complex.normSq_apply]
        nlinarith [houtside]
      have hz := root_disk_outside_of_squared_test (c j i) (w j i) (r j i)
        (hr j i).le hsquared (hw j i).2
      simp only [Bool.false_eq_true,iff_false]
      exact not_lt_of_ge hz.le
    | true =>
      have hinside := hside j i
      simp only [hflag,ite_true] at hinside
      have hsquared : ‖c j i‖^2<(1-r j i)^2 := by
        rw [Complex.sq_norm,Complex.normSq_apply]
        nlinarith [hinside.2]
      have hz := root_disk_inside_of_squared_test (c j i) (w j i) (r j i)
        hinside.1 hsquared (hw j i).2
      simp only [iff_true]
      exact hz

/-- Coordinate truncation towards zero cannot enlarge the norm. This is the
extra property used by the actual checker to keep every returned inside point
strictly inside; arbitrary approximants satisfying only eta need not have it. -/
theorem truncated_root_coordinate_norm_le (q c : ℂ)
    (hre : |q.re|≤|c.re|) (him : |q.im|≤|c.im|) : ‖q‖≤‖c‖ := by
  apply (sq_le_sq₀ (norm_nonneg q) (norm_nonneg c)).mp
  rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
  nlinarith [sq_le_sq.mpr hre,sq_le_sq.mpr him]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
