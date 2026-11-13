/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.Entanglement.BellWitness.Native

/-!
# Bell-state overlaps with product vectors

This module defines the two-qubit Bell vector `phi` and proves that its squared overlap with any
normalized product vector is at most one half. The argument uses `two_term_cauchy` and an
explicit formula for the product amplitude.

The identity `projector_trace` expresses overlaps as traces of outer products, supporting the
mixed-state witness developed in the companion module. For Bell states and bipartite
entanglement, see [NielsenChuang2010].

## Main statements

* `phi`: The Bell vector `( |00⟩ + |11⟩ ) / √2` in the two-qubit coordinate space.
* `product_overlap_le`: The squared overlap of the Bell vector with any normalized two-qubit
  product vector is at most one half.
* `projector_trace`: The trace of the product of two outer products is the squared modulus of
  the inner product of their defining vectors.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Foundations.Entanglement.BellWitness
noncomputable section

/-- The Bell vector `( |00⟩ + |11⟩ ) / √2` in the two-qubit coordinate space. -/
def phi : QState (Fin 2 × Fin 2) := fun p=>
  ((Real.sqrt 2)⁻¹ : ℂ)*((if p=(0,0) then 1 else 0)+(if p=(1,1) then 1 else 0))

/-- The Bell vector `phi` is normalized. -/
theorem phi_normalized : Normalized phi := by
  have hs : ‖((Real.sqrt 2)⁻¹ : ℂ)‖^2=1/2 := by
    rw [← Complex.normSq_eq_norm_sq,map_inv₀,Complex.normSq_ofReal,← sq,Real.sq_sqrt (by norm_num)]
    norm_num
  norm_num [Normalized,phi,Fintype.sum_prod_type,Fin.sum_univ_two,hs]

/-- The squared modulus of `a*c + b*d` is bounded by the product of the sums of squared moduli
of the two pairs. -/
theorem two_term_cauchy (a b c d : ℂ) :
    Complex.normSq (a*c+b*d) ≤
      (Complex.normSq a+Complex.normSq b)*(Complex.normSq c+Complex.normSq d) := by
  have he : Complex.normSq (a*c+b*d) + Complex.normSq (a*star d-b*star c) =
      (Complex.normSq a+Complex.normSq b)*(Complex.normSq c+Complex.normSq d) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    ring
  linarith [Complex.normSq_nonneg (a*star d-b*star c)]

/-- The overlap of `phi` with a product vector is `(a 0 * b 0 + a 1 * b 1) / √2`. -/
theorem phi_product_amplitude (a b : QState (Fin 2)) :
    Inner phi (TensorState a b) = ((Real.sqrt 2)⁻¹ : ℂ) * (a 0*b 0+a 1*b 1) := by
  simp [Inner, phi, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two,TensorState,Complex.conj_ofReal]
  ring

/-- The squared overlap of the Bell vector with any normalized two-qubit product vector is at
most one half. -/
theorem product_overlap_le (a b : QState (Fin 2)) (ha : Normalized a) (hb : Normalized b) :
    Complex.normSq (Inner phi (TensorState a b)) ≤ 1/2 := by
  have ha' : Complex.normSq (a 0)+Complex.normSq (a 1) = 1 := by
    simpa only [Normalized, Fin.sum_univ_two, Complex.normSq_eq_norm_sq] using ha
  have hb' : Complex.normSq (b 0)+Complex.normSq (b 1) = 1 := by
    simpa only [Normalized, Fin.sum_univ_two, Complex.normSq_eq_norm_sq] using hb
  have hc := two_term_cauchy (a 0) (a 1) (b 0) (b 1)
  rw [ha',hb',one_mul] at hc
  rw [phi_product_amplitude, Complex.normSq_mul]
  have hs : Complex.normSq ((Real.sqrt 2 : ℂ)⁻¹) = 1/2 := by
    rw [map_inv₀, Complex.normSq_ofReal, ← sq, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [hs]
  linarith

/-- The trace of the product of two outer products is the squared modulus of the inner product
of their defining vectors. -/
theorem projector_trace {I : Type*} [Fintype I] [DecidableEq I] (z v : QState I) :
    (outerProduct z * outerProduct v).trace = (Complex.normSq (Inner z v) : ℂ) := by
  rw [trace_outerProduct_mul_eq_quadratic, outerProduct_mulVec, dotProduct_smul, smul_eq_mul]
  change Inner v z * Inner z v = _
  rw [← star_inner z v]
  exact Complex.normSq_eq_conj_mul_self.symm

end
end Qatlib.Foundations.Entanglement.BellWitness
