/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootDiskCompleteness

set_option backward.isDefEq.respectTransparency false

/-! Complete single-factor catalogue from actual integer-array disk predicates.
The zero shortcut is preserved and no squarefree/root catalogue is supplied.
This does not yet combine factor products, side/truncation or parser control. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Polynomial
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Gaussian
open scoped BigOperators

/-- A sound envelope of the source's two acceptance branches: zero value, or
its actual integer comparison. The source additionally checks the derivative
numerator is nonzero in the latter branch; that is unnecessary for soundness. -/
theorem rootIntegerArray_disks_complete (n : ℕ) (a : Fin (n+2) → ℤ)
    (ha : a (Fin.last (n+1))≠0)
    (c : Fin (n+1) → ℚ×ℚ) (r : Fin (n+1) → ℚ)
    (hr : ∀ i,0<r i)
    (hcheck : ∀ i,
      (rootCompactHorner (rootSharedNumerator (c i)) (rootSharedDenominator (c i))
        (List.ofFn a)).numerator=(0,0) ∨
      rootIntegerCoordinateBound (n+1)
        (rootCompactHorner (rootSharedNumerator (c i)) (rootSharedDenominator (c i)) (List.ofFn a))
        (rootCompactHorner (rootSharedNumerator (c i)) (rootSharedDenominator (c i))
          (List.ofFn (rootIntegerDerivative n a))) (r i))
    (hsep : ∀ i j,i≠j → (r i+r j)^2<
      ((c i).1-(c j).1)^2+((c i).2-(c j).2)^2) :
    ∃ w : Fin (n+1) → ℂ,
      (∀ i,(rootIntegerPolynomial a).eval (w i)=0 ∧
        ‖w i-rootRationalCoordinate (c i)‖≤(r i : ℝ)) ∧
      Function.Injective w ∧
      (rootIntegerPolynomial a).roots=(Finset.univ.image w).val := by
  classical
  have hone : ∀ i,∃ z : ℂ,(rootIntegerPolynomial a).eval z=0 ∧
      ‖z-rootRationalCoordinate (c i)‖≤(r i : ℝ) := by
    intro i
    rcases hcheck i with hz | hb
    · exact rootIntegerArray_zero_disk a (c i) (r i) (hr i).le hz
    · exact rootIntegerArray_disk n a ha (c i) (r i) (hr i) hb
  choose w hw using hone
  have hinj : Function.Injective w := by
    intro i j hij
    by_contra hne
    have hi : (0 : ℝ)<r i := by exact_mod_cast hr i
    have hj : (0 : ℝ)<r j := by exact_mod_cast hr j
    have hclose : ‖rootRationalCoordinate (c i)-rootRationalCoordinate (c j)‖≤
        (r i : ℝ)+(r j : ℝ) := by
      calc
        _≤‖rootRationalCoordinate (c i)-w i‖+‖w i-rootRationalCoordinate (c j)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _≤(r i : ℝ)+(r j : ℝ) := add_le_add
          (by simpa only [norm_sub_rev] using (hw i).2)
          (by rw [hij]; exact (hw j).2)
    have hsq : ((r i : ℝ)+(r j : ℝ))^2<
        ‖rootRationalCoordinate (c i)-rootRationalCoordinate (c j)‖^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      have hs : ((r i : ℝ)+(r j : ℝ))^2<
          ((↑((c i).1) : ℝ)-↑((c j).1))^2+((↑((c i).2) : ℝ)-↑((c j).2))^2 := by
        exact_mod_cast hsep i j hne
      simpa only [rootRationalCoordinate,Complex.sub_re,Complex.sub_im,pow_two] using hs
    have hfar := (sq_lt_sq₀ (add_nonneg hi.le hj.le)
      (norm_nonneg (rootRationalCoordinate (c i)-rootRationalCoordinate (c j)))).mp hsq
    exact (not_lt_of_ge hclose) hfar
  have hd := rootIntegerPolynomial_natDegree a ha
  have hf0 : rootIntegerPolynomial a≠0 := by
    intro hz
    have h := hd
    rw [hz,Polynomial.natDegree_zero] at h
    omega
  let e : Fin (rootIntegerPolynomial a).natDegree ≃ Fin (n+1) :=
    { toFun := fun i => ⟨i.val,by have hi := i.isLt; omega⟩
      invFun := fun i => ⟨i.val,by have hi := i.isLt; omega⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  have hroots := polynomial_roots_eq_degree_many_image (rootIntegerPolynomial a) hf0
    (fun i => w (e i)) (fun i => (hw (e i)).1) (hinj.comp e.injective)
  have himage : (Finset.univ.image (fun i : Fin (rootIntegerPolynomial a).natDegree => w (e i)))=
      (Finset.univ.image w) := by
    ext z
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨e i,hi⟩
    · rintro ⟨i,hi⟩
      exact ⟨e.symm i,by simpa only [Equiv.apply_symm_apply] using hi⟩
  exact ⟨w,hw,hinj,by simpa only [himage] using hroots⟩

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
