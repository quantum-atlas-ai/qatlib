/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorHyper20.PhysicalTHC.PhysicalModes
import Qatlib.Papers.TensorHyper20.MainResults.LambdaTHC
import Qatlib.Concepts.LcuPostselect.ScaledLCU.OrientedSelect

/-!
# Physical SELECT terms and compression identities

Defines the term index `Term`, real coefficients `coefficient`, and physical SELECT matrices
`termSelect` for the tensor hypercontraction construction of [LeeEtAl2021]. Normalization of the
orbital vectors ensures that each SELECT term is a unitary involution.

Compression through `plusEmbedding` gives a single reflection for one-body terms and the
symmetrized product of two reflections for two-body terms. The coefficient mass equals
`LambdaTHC.lambdaTHC`, and `actual_lcu_compression` sums these compression identities.

## Main statements

* `actual_term_unitary`: proves unitarity of the physical SELECT terms.
* `actual_two_compression`: computes compression of a two-body term.
* `actual_coefficient_mass`: identifies the absolute coefficient sum.
* `actual_lcu_compression`: computes compression of the weighted SELECT sum.

## References

* [Lee et al., 2021][LeeEtAl2021]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.TensorHyper20.PhysicalTHC.PhysicalSelect
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner.WeightedModes
open Qatlib.Concepts.LcuPostselect.ScaledLCU.OrientedSelect
open PhysicalModes
open Qatlib.Papers.TensorHyper20.MainResults

/-- The disjoint union indexing one-body orbital-spin terms and two-body pairs of auxiliary
indices and spins. -/
abbrev Term (N M : ℕ) := Sum (Fin N×Fin 2) ((Fin M×Fin M)×(Fin 2×Fin 2))

/-- The real coefficient `-t k / 2` for a one-body term and `zeta μ ν / 8` for a two-body term. -/
def coefficient {N M : ℕ} (t : Fin N→ℝ) (zeta : Fin M→Fin M→ℝ) : Term N M→ℝ
  | .inl x => -(t x.1)/2
  | .inr x => zeta x.1.1 x.1.2/8

/-- The SELECT matrix built from one orbital reflection and the identity for a one-body term, or
from two auxiliary-mode reflections for a two-body term. -/
def termSelect {N M : ℕ} (tau : Fin N→Fin N→ℝ) (chi : Fin M→Fin N→ℝ) :
    Term N M→Matrix (Sum (Reg (N*2)) (Reg (N*2))) (Sum (Reg (N*2)) (Reg (N*2))) ℂ
  | .inl x => select (reflection (spinVector (tau x.1) x.2)) 1
  | .inr x => select (reflection (spinVector (chi x.1.1) x.2.1))
      (reflection (spinVector (chi x.1.2) x.2.2))

/-- If all rows of `tau` and `chi` have squared coefficients summing to one, every physical
SELECT term is unitary. See [LeeEtAl2021]. -/
theorem actual_term_unitary {N M : ℕ} (tau : Fin N→Fin N→ℝ) (chi : Fin M→Fin N→ℝ)
    (ht : ∀k,∑p,tau k p^2=1) (hc : ∀mu,∑p,chi mu p^2=1) (j : Term N M) :
    termSelect tau chi j∈Matrix.unitaryGroup (Sum (Reg (N*2)) (Reg (N*2))) ℂ := by
  cases j with
  | inl x =>
    apply select_unitary _ _ (reflection_hermitian _) Matrix.isHermitian_one
      (physical_reflection _ _ (ht x.1)).2
    simp
  | inr x =>
    exact select_unitary _ _ (reflection_hermitian _) (reflection_hermitian _)
      (physical_reflection _ _ (hc x.1.1)).2 (physical_reflection _ _ (hc x.1.2)).2

/-- Under normalization of all orbital and auxiliary-mode vectors, every physical SELECT term
squares to the identity. See [LeeEtAl2021]. -/
theorem actual_term_square {N M : ℕ} (tau : Fin N→Fin N→ℝ) (chi : Fin M→Fin N→ℝ)
    (ht : ∀k,∑p,tau k p^2=1) (hc : ∀mu,∑p,chi mu p^2=1) (j : Term N M) :
    termSelect tau chi j*termSelect tau chi j=1 := by
  cases j with
  | inl x => exact select_square _ _ (physical_reflection _ _ (ht x.1)).2 (by simp)
  | inr x =>
    exact select_square _ _ (physical_reflection _ _ (hc x.1.1)).2
      (physical_reflection _ _ (hc x.1.2)).2

/-- Compressing a one-body SELECT term through `plusEmbedding` yields the corresponding
spin-sector orbital reflection. -/
theorem actual_one_compression {N M : ℕ} (tau : Fin N→Fin N→ℝ) (chi : Fin M→Fin N→ℝ)
    (k : Fin N) (spin : Fin 2) :
    (plusEmbedding (I:=Reg (N*2)))ᴴ*termSelect tau chi (.inl (k,spin))*
      plusEmbedding (I:=Reg (N*2))=reflection (spinVector (tau k) spin) :=
  plus_select_one _

/-- Compressing a two-body SELECT term through `plusEmbedding` yields one half of the sum of the
two ordered products of its reflections. See [LeeEtAl2021]. -/
theorem actual_two_compression {N M : ℕ} (tau : Fin N→Fin N→ℝ) (chi : Fin M→Fin N→ℝ)
    (mu nu : Fin M) (spin spin' : Fin 2) :
    (plusEmbedding (I:=Reg (N*2)))ᴴ*termSelect tau chi (.inr ((mu,nu),(spin,spin')))*
      plusEmbedding (I:=Reg (N*2))=(1/2:ℂ) •
      (reflection (spinVector (chi mu) spin)*reflection (spinVector (chi nu) spin')+
       reflection (spinVector (chi nu) spin')*reflection (spinVector (chi mu) spin)) :=
  plus_select_compression _ _

/-- The sum of the absolute values of all physical term coefficients equals `LambdaTHC.lambdaTHC
t zeta`. See [LeeEtAl2021]. -/
theorem actual_coefficient_mass {N M : ℕ} (t : Fin N→ℝ) (zeta : Fin M→Fin M→ℝ) :
    (∑j : Term N M,|coefficient t zeta j|)=LambdaTHC.lambdaTHC t zeta := by
  simp only [Term,Fintype.sum_sum_type,Fintype.sum_prod_type,coefficient,
    abs_div,abs_neg,LambdaTHC.lambdaTHC,LambdaTHC.lambdaZeta]
  simp only [Fin.sum_univ_two]
  norm_num only [abs_of_nonneg (show (0:ℝ)≤2 by norm_num),abs_of_nonneg (show (0:ℝ)≤8 by norm_num)]
  simp only [Finset.sum_add_distrib,div_eq_mul_inv,← Finset.sum_mul]
  ring

/-- If the absolute one-body coefficient sum is at most `C * lambdaZeta`, then the physical term
coefficient mass is at most `(C + 1) * lambdaZeta`. See [LeeEtAl2021]. -/
theorem actual_coefficient_domination {N M : ℕ} (t : Fin N→ℝ) (zeta : Fin M→Fin M→ℝ)
    (C : ℝ) (h : ∑k,|t k|≤C*LambdaTHC.lambdaZeta zeta) :
    (∑j : Term N M,|coefficient t zeta j|)≤(C+1)*LambdaTHC.lambdaZeta zeta := by
  rw [actual_coefficient_mass]
  exact LambdaTHC.lambdaTHC_asymptotic t zeta C h

/-- Compressing the coefficient-weighted SELECT sum gives the sum of the weighted one-body
reflections and weighted symmetrized two-body reflection products. See [LeeEtAl2021]. -/
theorem actual_lcu_compression {N M : ℕ} (tau : Fin N→Fin N→ℝ)
    (chi : Fin M→Fin N→ℝ) (t : Fin N→ℝ) (zeta : Fin M→Fin M→ℝ) :
    (plusEmbedding (I:=Reg (N*2)))ᴴ*
      (∑j : Term N M,coefficient t zeta j • termSelect tau chi j)*
      plusEmbedding (I:=Reg (N*2))=
    (∑k : Fin N,∑spin : Fin 2,(-(t k)/2) • reflection (spinVector (tau k) spin))+
    ∑mu : Fin M,∑nu : Fin M,∑spin : Fin 2,∑spin' : Fin 2,
      (zeta mu nu/8) • ((1/2:ℂ) •
        (reflection (spinVector (chi mu) spin)*reflection (spinVector (chi nu) spin')+
         reflection (spinVector (chi nu) spin')*reflection (spinVector (chi mu) spin))) := by
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,
    Fintype.sum_sum_type,Fintype.sum_prod_type,coefficient,
    actual_one_compression,actual_two_compression]

end Qatlib.Papers.TensorHyper20.PhysicalTHC.PhysicalSelect
