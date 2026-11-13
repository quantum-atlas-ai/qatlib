/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HHLManyBody22.HomOverlap.TensorCircuit

/-!
# Born probability readout of the HOM overlap circuit

`homPairEquiv` identifies a string of bit pairs with a pair of bit strings, and `homJoint` forms
the corresponding product state. The tensor Bell circuit conjugates the parity observable to the
swap operator.

`hom_actual_born_overlap` evaluates the parity weighted sum of actual output Born masses as the
squared norm of the input inner product. The identity is stated for arbitrary input vectors
without normalization hypotheses. See [BaskaranEtAl2023].

## Main statements

* `homTensor_parity_operator`: Conjugating the diagonal parity observable by `homTensor n` gives
  the swap matrix.
* `hom_actual_born_overlap`: The parity weighted Born masses of the HOM circuit on the joint
  input equal the squared norm of the input inner product.

## References

* [Baskaran et al., 2023][BaskaranEtAl2023]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Papers.HHLManyBody22.HomOverlap
open Matrix

/-- The equivalence between strings of bit pairs and pairs of bit strings. -/
def homPairEquiv (n : ℕ) : HomBits n ≃ ((Fin n→Bool)×(Fin n→Bool)) where
  toFun x := (fun i => (x i).1,fun i => (x i).2)
  invFun x := fun i => (x.1 i,x.2 i)
  left_inv x := by funext i; exact Prod.eta (x i)
  right_inv x := by cases x; rfl

/-- The product state on bit pairs obtained from `u` and `v` through `homPairEquiv`. -/
def homJoint (n : ℕ) (u v : (Fin n→Bool)→ℂ) : HomBits n→ℂ :=
  fun x => u (homPairEquiv n x).1*v (homPairEquiv n x).2

/-- Conjugating the diagonal parity observable by `homTensor n` gives the swap matrix. -/
theorem homTensor_parity_operator (n : ℕ) :
    (homTensor n)ᴴ * diagonal (fun z => (homParity n z:ℂ)) * homTensor n =
      (fun x y => if x=homSwap n y then 1 else 0) := by
  ext x y
  simp only [mul_apply,conjTranspose_apply,homTensor,Complex.star_def,
    Complex.conj_ofReal,diagonal_apply]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simpa only [← Complex.ofReal_mul,← Complex.ofReal_sum,apply_ite,Complex.ofReal_one,
    Complex.ofReal_zero] using congrArg Complex.ofReal (homTensorReal_parity_swap n x y)

/-- The parity weighted output Born sum, cast to a complex number, equals the input quadratic
form of the conjugated parity observable. -/
theorem hom_actual_born_quadratic (n : ℕ) (ψ : HomBits n→ℂ) :
    ((∑z,homParity n z*Complex.normSq ((homTensor n*ᵥψ) z):ℝ):ℂ) =
      star ψ ⬝ᵥ (((homTensor n)ᴴ * diagonal (fun z => (homParity n z:ℂ)) * homTensor n) *ᵥ ψ) := by
  rw [← mulVec_mulVec,← mulVec_mulVec,dotProduct_mulVec,← star_mulVec]
  simp only [dotProduct,mulVec_diagonal,Pi.star_apply,Complex.star_def,
    Complex.ofReal_sum,Complex.ofReal_mul,Complex.normSq_eq_conj_mul_self]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- The parity weighted output Born sum equals the input pairing with its bitwise swapped
vector. -/
theorem hom_actual_born_swap (n : ℕ) (ψ : HomBits n→ℂ) :
    ((∑z,homParity n z*Complex.normSq ((homTensor n*ᵥψ) z):ℝ):ℂ) =
      ∑y,star (ψ (homSwap n y))*ψ y := by
  rw [hom_actual_born_quadratic,homTensor_parity_operator]
  simp only [dotProduct,mulVec,ite_mul,one_mul,zero_mul,Pi.star_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp

/-- The swap pairing of the joint product state equals the squared norm of `star u ⬝ᵥ v`. -/
theorem homJoint_swap_overlap (n : ℕ) (u v : (Fin n→Bool)→ℂ) :
    (∑y,star (homJoint n u v (homSwap n y))*homJoint n u v y) =
      (Complex.normSq (star u ⬝ᵥ v):ℂ) := by
  classical
  change (∑y, (fun p : ((Fin n→Bool)×(Fin n→Bool)) =>
    star (u p.2*v p.1)*(u p.1*v p.2)) (homPairEquiv n y)) = _
  rw [Equiv.sum_comp (homPairEquiv n) (fun p : ((Fin n→Bool)×(Fin n→Bool)) => star (u p.2*v p.1)*(u p.1*v p.2))]
  rw [Fintype.sum_prod_type]
  simp only [star_mul,Complex.normSq_eq_conj_mul_self,dotProduct,map_sum,
    map_mul,Pi.star_apply,Complex.star_def,Complex.conj_conj,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The parity weighted Born masses of the HOM circuit on the joint input equal the squared norm
of the input inner product. See [BaskaranEtAl2023]. -/
theorem hom_actual_born_overlap (n : ℕ) (u v : (Fin n→Bool)→ℂ) :
    (∑z,homParity n z*Complex.normSq ((homTensor n*ᵥhomJoint n u v) z)) =
      Complex.normSq (star u ⬝ᵥ v) := by
  apply Complex.ofReal_injective
  rw [hom_actual_born_swap,homJoint_swap_overlap]

end Qatlib.Papers.HHLManyBody22.HomOverlap
