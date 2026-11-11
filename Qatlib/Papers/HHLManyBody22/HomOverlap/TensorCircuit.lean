/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HHLManyBody22.HomOverlap.BellCircuit
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Tensor Bell circuits and the parity swap identity

`homTensorReal` is the entrywise tensor product of the two qubit Bell circuit, and `homTensor`
is its complex matrix form. The module proves orthogonality and unitarity and extends the local
parity swap identity to all bit pairs.

The outcome space `HomBits n` has cardinality `2^(2*n)`. `homGateWord` records two labeled
positions for each qubit pair and has length `2*n`. See [BaskaranEtAl2023].

## Main statements

* `homTensor_unitary`: The complex tensor Bell circuit matrix is unitary.
* `homTensorReal_parity_swap`: The parity weighted column pairing of the tensor Bell circuit
  equals the matrix entry of bitwise swap.
* `homGateWord_length`: The list `homGateWord n` has length `2*n`.

## References

* [Baskaran et al., 2023][BaskaranEtAl2023]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Papers.HHLManyBody22.HomOverlap
open Matrix

/-- Strings of `n` Boolean pairs indexing the joint register. -/
abbrev HomBits (n : ℕ) := Fin n→Bool×Bool

/-- The real matrix whose entries are products of the local Bell circuit entries over all `n`
pairs. -/
def homTensorReal (n : ℕ) : Matrix (HomBits n) (HomBits n) ℝ :=
  fun z x => ∏i,homBell (z i) (x i)

/-- The complex matrix obtained from `homTensorReal n`. -/
def homTensor (n : ℕ) : Matrix (HomBits n) (HomBits n) ℂ :=
  fun z x => (homTensorReal n z x:ℂ)

/-- The product of the local outcome signs over all bit pairs. -/
def homParity (n : ℕ) (z : HomBits n) : ℝ := ∏i,homPairSign (z i)

/-- The bitwise swap exchanging the two components of every pair. -/
def homSwap (n : ℕ) (x : HomBits n) : HomBits n := fun i => ((x i).2,(x i).1)

/-- A finite product of equality indicators is one exactly when the two functions are equal, and
zero otherwise. -/
theorem hom_prod_delta {I B : Type} [Fintype I] [DecidableEq B] (x y : I→B) :
    (∏i,if x i=y i then (1:ℝ) else 0)=if x=y then 1 else 0 := by
  by_cases h : x=y
  · subst y
    simp
  · rw [if_neg h]
    have hn : ¬∀i,x i=y i := fun heq => h (funext heq)
    obtain ⟨i,hi⟩ := not_forall.mp hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The columns of the tensor real Bell circuit matrix are orthonormal. -/
theorem homTensorReal_orthogonal (n : ℕ) (x y : HomBits n) :
    (∑z,homTensorReal n z x*homTensorReal n z y)=if x=y then 1 else 0 := by
  calc
    _ = ∑z : HomBits n,∏i,homBell (z i) (x i)*homBell (z i) (y i) := by
      simp only [homTensorReal,Finset.prod_mul_distrib]
    _ = ∏i,∑z,homBell z (x i)*homBell z (y i) := (Fintype.prod_sum (fun (i : Fin n) (z : Bool×Bool) => homBell z (x i)*homBell z (y i))).symm
    _ = _ := by simp only [homBell_orthogonal,hom_prod_delta]

/-- The complex tensor Bell circuit matrix is unitary. -/
theorem homTensor_unitary (n : ℕ) : homTensor n∈Matrix.unitaryGroup (HomBits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext x y
  simp only [Matrix.star_eq_conjTranspose,Matrix.mul_apply,Matrix.conjTranspose_apply,
    homTensor,Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,← Complex.ofReal_sum,
    homTensorReal_orthogonal,Matrix.one_apply]
  split_ifs <;> rfl

/-- The parity weighted column pairing of the tensor Bell circuit equals the matrix entry of
bitwise swap. -/
theorem homTensorReal_parity_swap (n : ℕ) (x y : HomBits n) :
    (∑z,homTensorReal n z x*homParity n z*homTensorReal n z y)=
      if x=homSwap n y then 1 else 0 := by
  calc
    _ = ∑z : HomBits n,∏i,homBell (z i) (x i)*homPairSign (z i)*homBell (z i) (y i) := by
      simp only [homTensorReal,homParity,Finset.prod_mul_distrib]
    _ = ∏i,∑z,homBell z (x i)*homPairSign z*homBell z (y i) := (Fintype.prod_sum (fun (i : Fin n) (z : Bool×Bool) => homBell z (x i)*homPairSign z*homBell z (y i))).symm
    _ = ∏i,if x i=(homSwap n y) i then 1 else 0 := by simpa only [homSwap] using! (Finset.prod_congr rfl (fun i _ => homBell_parity_swap (x i) (y i)))
    _ = _ := hom_prod_delta x (homSwap n y)

/-- The square of every tensor parity sign is one. -/
theorem homParity_sq (n : ℕ) (z : HomBits n) : homParity n z^2=1 := by
  rw [homParity,← Finset.prod_pow]
  have hs (i : Fin n) : homPairSign (z i)^2=1 := by unfold homPairSign; split_ifs <;> norm_num
  simp_rw [hs]
  simp

/-- The joint bit pair register has cardinality `2^(2*n)`. See [BaskaranEtAl2023]. -/
theorem hom_measured_card (n : ℕ) : Fintype.card (HomBits n)=2^(2*n) := by
  simp only [HomBits,Fintype.card_fun,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
  rw [show 2*2=2^2 by norm_num,← pow_mul]

/-- The list containing `(i,false)` followed by `(i,true)` for each index `i`. -/
def homGateWord (n : ℕ) : List (Fin n×Bool) :=
  (List.ofFn fun i : Fin n => [(i,false),(i,true)]).flatten

/-- The list `homGateWord n` has length `2*n`. -/
theorem homGateWord_length (n : ℕ) : (homGateWord n).length=2*n := by
  simp [homGateWord,List.length_flatten,List.sum_ofFn]
  omega

end Qatlib.Papers.HHLManyBody22.HomOverlap
