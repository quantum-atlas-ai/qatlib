/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerCatalogue
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootDiskClassification

set_option backward.isDefEq.respectTransparency false

/-! One same-factor consumer for integer inclusion, completeness, computed
side tags and the actual returned inside grid. No caller-supplied side flags.
The fallback tag is used only under a successful non-none classification. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Polynomial
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Gaussian
open scoped BigOperators

/-- Read a computed side result only after the caller has checked non-none. -/
def rootRationalDiskComputedTag (c : ℚ×ℚ) (r : ℚ) : Bool :=
  (rootRationalDiskClassify c r).getD false

/-- The finite construction in `NativeRootClassifiedCatalogue` satisfies `rootRationalDiskClassify_computed_tag` under the displayed hypotheses. -/
theorem rootRationalDiskClassify_computed_tag (c : ℚ×ℚ) (r : ℚ)
    (h : rootRationalDiskClassify c r≠none) :
    rootRationalDiskClassify c r=some (rootRationalDiskComputedTag c r) := by
  unfold rootRationalDiskComputedTag
  cases he : rootRationalDiskClassify c r with
  | none => exact (h he).elim
  | some b => rfl

/-- The original factor data determine all roots and exactly their inside
indices; only inside indices require a positive eta and a returned-point
budget. Outside-only data may use a dummy eta=0 without constructing a grid. -/
theorem rootIntegerArray_classified_catalogue (n : ℕ) (a : Fin (n+2) → ℤ)
    (ha : a (Fin.last (n+1))≠0)
    (c : Fin (n+1) → ℚ×ℚ) (r : Fin (n+1) → ℚ) (hr : ∀ i,0<r i)
    (hcheck : ∀ i,
      (rootCompactHorner (rootSharedNumerator (c i)) (rootSharedDenominator (c i))
        (List.ofFn a)).numerator=(0,0) ∨
      rootIntegerCoordinateBound (n+1)
        (rootCompactHorner (rootSharedNumerator (c i)) (rootSharedDenominator (c i)) (List.ofFn a))
        (rootCompactHorner (rootSharedNumerator (c i)) (rootSharedDenominator (c i))
          (List.ofFn (rootIntegerDerivative n a))) (r i))
    (hsep : ∀ i j,i≠j → (r i+r j)^2<
      ((c i).1-(c j).1)^2+((c i).2-(c j).2)^2)
    (hclass : ∀ i,rootRationalDiskClassify (c i) (r i)≠none) (eta : ℚ)
    (heta : ∀ i,rootRationalDiskComputedTag (c i) (r i)=true → 0<eta)
    (hbudget : ∀ i,rootRationalDiskComputedTag (c i) (r i)=true →
      r i+|(rootGridPoint (c i) (eta/16)).1-(c i).1|+
        |(rootGridPoint (c i) (eta/16)).2-(c i).2|≤eta) :
    ∃ w : Fin (n+1) → ℂ,
      (∀ i,(rootIntegerPolynomial a).eval (w i)=0 ∧
        ‖w i-rootRationalCoordinate (c i)‖≤(r i : ℝ)) ∧
      Function.Injective w ∧
      (rootIntegerPolynomial a).roots=(Finset.univ.image w).val ∧
      (∀ i,‖w i‖<1 ↔ rootRationalDiskComputedTag (c i) (r i)=true) ∧
      (∀ i,rootRationalDiskComputedTag (c i) (r i)=true →
        ‖rootRationalCoordinate (rootGridPoint (c i) (eta/16))‖<1 ∧
        ‖rootRationalCoordinate (rootGridPoint (c i) (eta/16))-w i‖≤(eta : ℝ)) := by
  obtain ⟨w,hw,hinj,hroots⟩ := rootIntegerArray_disks_complete n a ha c r hr hcheck hsep
  refine ⟨w,hw,hinj,hroots,?_,?_⟩
  · intro i
    have hc := rootRationalDiskClassify_computed_tag (c i) (r i) (hclass i)
    cases hb : rootRationalDiskComputedTag (c i) (r i) with
    | false =>
      have hc' : rootRationalDiskClassify (c i) (r i)=some false := by
        simpa only [hb] using hc
      have ho : 1<‖w i‖ := rootRationalDiskClassify_root_side (c i) (r i) (hr i)
        (w i) (hw i).2 false hc'
      constructor
      · intro hi
        exact ((not_lt_of_ge ho.le) hi).elim
      · intro hfalse
        cases hfalse
    | true =>
      have hc' : rootRationalDiskClassify (c i) (r i)=some true := by
        simpa only [hb] using hc
      have hi : ‖w i‖<1 := rootRationalDiskClassify_root_side (c i) (r i) (hr i)
        (w i) (hw i).2 true hc'
      exact ⟨fun _ => rfl,fun _ => hi⟩
  · intro i hi
    have hc := rootRationalDiskClassify_computed_tag (c i) (r i) (hclass i)
    have hc' : rootRationalDiskClassify (c i) (r i)=some true := by
      simpa only [hi] using hc
    exact rootClassified_inside_return (c i) (r i) eta (hr i) (heta i hi) hc'
      (w i) (hw i).2 (hbudget i hi)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
