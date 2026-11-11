/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs

/-!
# Hermiticity and sparsity of the Markov Hamiltonian

Expands the square-root-weight matrix `HM` and uses positive detailed balance to prove
Hermiticity. Under `StronglySamplable`, the square-root weight vector lies in its kernel, and
its row support contains at most the original matrix support plus a diagonal entry. See
[AharonovTaShma2007].

## Main statements

* `hm_isHermitian`: Positive detailed balance makes the associated Hamiltonian Hermitian.
* `hm_mulVec_sqrt`: The square-root weight vector is annihilated.
* `hm_rowSparse`: The row-sparsity bound increases by at most one.

## References

* [Aharonov and Ta‐Shma, 2007][AharonovTaShma2007]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.MarkovCorollary

open Qatlib.Papers.AdiabStateGen03.MainResults

variable {n : ℕ}

/-- For positive weights satisfying `a * pi = b * pj`, the square-root-weighted coefficients
`sqrt pi / sqrt pj * a` and `sqrt pj / sqrt pi * b` are equal. -/
lemma sqrt_ratio_mul_symm {pi pj a b : ℝ} (hi : 0 < pi) (hj : 0 < pj)
    (hab : a * pi = b * pj) :
    Real.sqrt pi / Real.sqrt pj * a = Real.sqrt pj / Real.sqrt pi * b := by
  have hsi : 0 < Real.sqrt pi := Real.sqrt_pos.mpr hi
  have hsj : 0 < Real.sqrt pj := Real.sqrt_pos.mpr hj
  have hb : b = a * pi / pj := by
    rw [eq_div_iff hj.ne']
    linarith [hab]
  rw [hb]
  field_simp
  rw [Real.sq_sqrt hi.le, Real.sq_sqrt hj.le]
  ring

/-- An entry of `HM M π` is the identity entry minus the complex coercion of `sqrt (π i) / sqrt
(π j) * M i j` [AharonovTaShma2007]. -/
lemma HM_apply (M : MC n) (π : Dim n → ℝ) (i j : Dim n) :
    HM M π i j = (if i = j then (1 : ℂ) else 0) -
      ((Real.sqrt (π i) / Real.sqrt (π j) * M i j : ℝ) : ℂ) := by
  simp only [HM, Matrix.sub_apply, Matrix.one_apply]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
  push_cast
  rw [div_eq_mul_inv]
  have h : (algebraMap ℝ ℂ) (M i j) = (M i j : ℂ) := rfl
  rw [h]
  ring

/-- The Hamiltonian associated with a `StronglySamplable` matrix and its weight function is
Hermitian [AharonovTaShma2007]. -/
theorem hm_isHermitian (M : MC n) (π : Dim n → ℝ) (h : StronglySamplable M π) :
    IsHermitian (HM M π) := by
  refine IsHermitian.ext ?_
  intro i j
  have hsymm : Real.sqrt (π i) / Real.sqrt (π j) * M i j =
      Real.sqrt (π j) / Real.sqrt (π i) * M j i :=
    sqrt_ratio_mul_symm (h.reversible.1 i) (h.reversible.1 j) (h.reversible.2 i j)
  rw [HM_apply M π j i, HM_apply M π i j]
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : j ≠ i := fun h' => hij h'.symm
    rw [if_neg hij, if_neg hji]
    simp only [star_sub, star_zero]
    rw [Complex.star_def, Complex.conj_ofReal]
    rw [hsymm]

/-- Under `StronglySamplable`, the vector with coordinates `sqrt (π i)` lies in the kernel of
`HM M π` [AharonovTaShma2007]. -/
theorem hm_mulVec_sqrt (M : MC n) (π : Dim n → ℝ) (h : StronglySamplable M π) :
    (HM M π).mulVec (fun i => (Real.sqrt (π i) : ℂ)) = 0 := by
  have hπ : ∀ i, 0 < π i := h.positive
  have hM : IsStochastic M := h.stochastic
  funext i
  rw [Pi.zero_apply]
  have hterm : ∀ j, HM M π i j * (Real.sqrt (π j) : ℂ)
      = (if i = j then (Real.sqrt (π i) : ℂ) else 0) - (Real.sqrt (π i) : ℂ) * (M i j : ℂ) := by
    intro j
    rw [HM_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl]
      have hs : Real.sqrt (π i) ≠ 0 := (Real.sqrt_pos.mpr (hπ i)).ne'
      push_cast
      field_simp
    · rw [if_neg hij, if_neg hij]
      have hs : Real.sqrt (π j) ≠ 0 := (Real.sqrt_pos.mpr (hπ j)).ne'
      push_cast
      field_simp
      ring
  calc (HM M π).mulVec (fun i => (Real.sqrt (π i) : ℂ)) i
      = ∑ j, HM M π i j * (Real.sqrt (π j) : ℂ) := by
        simp only [Matrix.mulVec, dotProduct]
    _ = ∑ j, ((if i = j then (Real.sqrt (π i) : ℂ) else 0)
          - (Real.sqrt (π i) : ℂ) * (M i j : ℂ)) :=
        Finset.sum_congr rfl (fun j _ => hterm j)
    _ = (Real.sqrt (π i) : ℂ) - (Real.sqrt (π i) : ℂ) * ∑ j, (M i j : ℂ) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        congr 1
        rw [Finset.sum_ite_eq]
        simp
    _ = 0 := by
        have hcast : (∑ j, (M i j : ℂ)) = ((∑ j, M i j : ℝ) : ℂ) := by
          push_cast
          rfl
        rw [hcast, hM i]
        norm_num

/-- A nonzero entry of `HM M π` is either supported by a nonzero entry of `M` or lies on the
diagonal [AharonovTaShma2007]. -/
theorem hm_support (M : MC n) (π : Dim n → ℝ) (i j : Dim n)
    (hij : HM M π i j ≠ 0) : M i j ≠ 0 ∨ i = j := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hM, hne⟩ := hcon
  have hM0 : M i j = 0 := by simpa using hM
  have hne0 : ¬ i = j := by simpa using hne
  apply hij
  rw [HM_apply, if_neg hne0, hM0]
  simp

/-- The Hamiltonian associated with a `StronglySamplable` matrix with row bound `D` has at most
`D + 1` nonzero entries per row [AharonovTaShma2007]. -/
theorem hm_rowSparse (M : MC n) (π : Dim n → ℝ) (h : StronglySamplable M π) :
    RowSparse (HM M π) (h.D + 1) := by
  intro i
  have hsub : (Finset.univ.filter (fun j : Dim n => HM M π i j ≠ 0)) ⊆
      (Finset.univ.filter (fun j : Dim n => M i j ≠ 0)) ∪ {i} := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    rcases hm_support M π i j hj with hM | hij
    · exact Or.inl hM
    · exact Or.inr hij.symm
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le (Finset.univ.filter (fun j : Dim n => M i j ≠ 0)) {i}
  have hsingle : ({i} : Finset (Dim n)).card = 1 := Finset.card_singleton i
  have hMcard : (Finset.univ.filter (fun j : Dim n => M i j ≠ 0)).card ≤ h.D :=
    h.rowSparse i
  omega

end Qatlib.Papers.AdiabStateGen03.MainResults.MarkovCorollary
