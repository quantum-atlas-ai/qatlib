/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.ZMod.Basic
import Qatlib.Papers.HiddenTransl02.MainResults.LineLemma
import Mathlib.Tactic

/-!
# The line lemma for multivariate polynomials

The map `lin` sends a vector over `ZMod p` to its associated linear polynomial. The module
establishes its algebraic and evaluation properties and proves the multivariate polynomial form
of the Line Lemma from [FriedlEtAl2014].

## Main statements

* `lineLemma_poly_span`: places mixed products of two linear forms in the span of powers along
  an affine line.
* `line_pow_mem_of_all_mem`: recovers the direction power from membership of all line powers.

## References

* [Friedl et al., 2014][FriedlEtAl2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false
noncomputable section

namespace Qatlib.Papers.HiddenTransl02.MainResults.Section3

open MvPolynomial Finset
open Qatlib.Papers.HiddenTransl02.MainResults.LineLemma

variable {n p : ℕ}

/-- The linear polynomial `∑ i, C (y i) * X i` associated with the coefficient vector `y`. -/
def lin (y : Fin n → ZMod p) : MvPolynomial (Fin n) (ZMod p) :=
  ∑ i, C (y i) * X i

/-- The linear polynomial associated with a sum of vectors is the sum of their linear
polynomials. -/
@[simp]
theorem lin_add (a b : Fin n → ZMod p) : lin (a + b) = lin a + lin b := by
  simp only [lin, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/-- Scaling a coefficient vector by `c` multiplies its associated linear polynomial by `C c`. -/
theorem lin_smul (c : ZMod p) (a : Fin n → ZMod p) : lin (c • a) = C c * lin a := by
  simp only [lin, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

/-- The linear polynomial associated with the `i`th standard basis vector is `X i`. -/
@[simp]
theorem lin_single (i : Fin n) : lin (Pi.single i (1 : ZMod p)) = X i := by
  rw [lin, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The linear polynomial associated with the zero vector is zero. -/
@[simp]
theorem lin_zero : lin (0 : Fin n → ZMod p) = 0 := by
  simp [lin]

/-- Expands the linear polynomial of `z + a • y` as `lin z + C a * lin y`. -/
theorem lin_add_smul (z y : Fin n → ZMod p) (a : ZMod p) :
    lin (z + a • y) = lin z + C a * lin y := by
  rw [lin_add, lin_smul]

/-- For prime `p`, `1 ≤ k ≤ p - 1`, and `l ≤ k`, the mixed product `lin z ^ l * lin y ^ (k - l)`
lies in the span of the first `k + 1` affine-line powers. This is [Friedl et al., Lemma
3.2][FriedlEtAl2014]. -/
theorem lineLemma_poly_span (hp : p.Prime) {k l : ℕ}
    (hk1 : 1 ≤ k) (hkp : k ≤ p - 1) (hl : l ≤ k) (z y : Fin n → ZMod p) :
    lin z ^ l * lin y ^ (k - l) ∈
      Submodule.span (ZMod p)
        (Set.range (fun a : Fin (k + 1) => (lin (z + (a.val : ZMod p) • y)) ^ k)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hklt : k < p := by omega
  obtain ⟨c0, hc0⟩ :=
    exists_coeffs (K := ZMod p) k l hl
      (fun i hi => zmod_choose_ne_zero hp hklt hi)
      (zmod_natCast_injective_on_fin hp hklt)
  have hc : ∀ i : Fin (k + 1),
      ∑ a : Fin (k + 1),
          MvPolynomial.C (c0 a) *
            (Nat.choose k i.val : MvPolynomial (Fin n) (ZMod p)) *
            (a.val : MvPolynomial (Fin n) (ZMod p)) ^ (k - i.val) =
        if i.val = l then 1 else 0 := by
    intro i
    have h0 := hc0 i
    by_cases hil : i.val = l
    · rw [if_pos hil] at h0
      have hC := congrArg (MvPolynomial.C (σ := Fin n)) h0
      simpa [hil] using hC
    · rw [if_neg hil] at h0
      have hC := congrArg (MvPolynomial.C (σ := Fin n)) h0
      simpa [hil] using hC
  have hcomb :=
    line_combination_of_coeffs (R := MvPolynomial (Fin n) (ZMod p))
      (lin z) (lin y) k l hl (fun a => MvPolynomial.C (c0 a)) hc
  have hcomb' :
      (∑ a : Fin (k + 1),
        MvPolynomial.C (c0 a) *
          (lin z + (a.val : MvPolynomial (Fin n) (ZMod p)) * lin y) ^ k)
        = lin z ^ l * lin y ^ (k - l) := by
    simpa using hcomb
  have hmem :
      (∑ a : Fin (k + 1),
          MvPolynomial.C (c0 a) *
            (lin z + (a.val : MvPolynomial (Fin n) (ZMod p)) * lin y) ^ k) ∈
        Submodule.span (ZMod p)
          (Set.range (fun a : Fin (k + 1) => (lin (z + (a.val : ZMod p) • y)) ^ k)) := by
    refine Submodule.sum_mem _ ?_
    intro a _
    have hlin : (lin z + (a.val : MvPolynomial (Fin n) (ZMod p)) * lin y)
        = lin (z + (a.val : ZMod p) • y) := by
      rw [lin_add_smul z y (a.val : ZMod p)]
      simp
    have hsmul : (c0 a) • (lin (z + (a.val : ZMod p) • y)) ^ k ∈
        Submodule.span (ZMod p)
          (Set.range (fun a : Fin (k + 1) => (lin (z + (a.val : ZMod p) • y)) ^ k)) :=
      Submodule.smul_mem _ (c0 a) (Submodule.subset_span (Set.mem_range_self a))
    simpa [hlin, MvPolynomial.smul_eq_C_mul] using hsmul
  rw [hcomb'] at hmem
  exact hmem

/-- Over a prime field, if all `(p - 1)`st powers along the line `z + a • y` lie in `W`, then
`lin y ^ (p - 1)` lies in `W` as well, by the Line Lemma in [FriedlEtAl2014]. -/
theorem line_pow_mem_of_all_mem (hp : p.Prime)
    (W : Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p)))
    (z y : Fin n → ZMod p)
    (h : ∀ a : Fin p, lin (z + (a.val : ZMod p) • y) ^ (p - 1) ∈ W) :
    lin y ^ (p - 1) ∈ W := by
  have hk1 : 1 ≤ p - 1 := by have := hp.two_le; omega
  have hline := lineLemma_poly_span (p := p) (n := n) hp (k := p - 1) (l := 0)
    hk1 le_rfl (Nat.zero_le _) z y
  have hidx : ((p - 1) + 1) = p := Nat.sub_add_cancel (by have := hp.two_le; omega)
  rw [hidx] at hline
  have hle : Submodule.span (ZMod p)
      (Set.range (fun a : Fin p => (lin (z + (a.val : ZMod p) • y)) ^ (p - 1))) ≤ W := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    exact h a
  have := hle hline
  simpa using this

/-- Evaluating `lin u` at `y` gives the coordinate sum `∑ i, y i * u i`. -/
theorem eval₂_lin (y u : Fin n → ZMod p) :
    MvPolynomial.eval₂Hom (RingHom.id (ZMod p)) y (lin u) = ∑ i, y i * u i := by
  simp only [lin, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X', RingHom.id_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  exact mul_comm (u i) (y i)

/-- Evaluating the `k`th power of `lin u` at `y` gives the `k`th power of their coordinate
pairing. -/
theorem eval₂_lin_pow (y u : Fin n → ZMod p) (k : ℕ) :
    MvPolynomial.eval₂Hom (RingHom.id (ZMod p)) y (lin u ^ k) = (∑ i, y i * u i) ^ k := by
  rw [map_pow, eval₂_lin]

/-- Over a prime field, evaluating `lin u ^ (p - 1)` at a vector pairing nontrivially with `u`
gives one. -/
theorem eval₂_lin_pow_card_sub_one (hp : p.Prime) {y u : Fin n → ZMod p}
    (h : ∑ i, y i * u i ≠ 0) :
    MvPolynomial.eval₂Hom (RingHom.id (ZMod p)) y (lin u ^ (p - 1)) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [eval₂_lin_pow]
  exact ZMod.pow_card_sub_one_eq_one h

/-- The polynomial `lin y` vanishes exactly when its coefficient vector `y` is zero. -/
theorem lin_eq_zero_iff {y : Fin n → ZMod p} : lin y = 0 ↔ y = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  funext j
  have he := eval₂_lin (y := Pi.single j (1 : ZMod p)) (u := y)
  rw [h] at he
  have hj : ∑ i, (Pi.single j (1 : ZMod p) : Fin n → ZMod p) i * y i = y j := by
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, one_mul]
    · intro i _ hij
      rw [Pi.single_eq_of_ne hij, zero_mul]
    · intro hh
      exact absurd (Finset.mem_univ j) hh
  rw [hj] at he
  simpa using he.symm

/-- Over a prime field, multiplying a vector by a nonzero scalar does not change the `(p - 1)`st
power of its associated linear polynomial. -/
theorem lin_smul_pow_card_sub_one (hp : p.Prime) (c : ZMod p) (hc : c ≠ 0)
    (y : Fin n → ZMod p) :
    lin (c • y) ^ (p - 1) = lin y ^ (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hC : (MvPolynomial.C c : MvPolynomial (Fin n) (ZMod p)) ^ (p - 1) = 1 := by
    rw [← map_pow, ZMod.pow_card_sub_one_eq_one hc, map_one]
  rw [lin_smul, mul_pow, hC, one_mul]

end Qatlib.Papers.HiddenTransl02.MainResults.Section3
