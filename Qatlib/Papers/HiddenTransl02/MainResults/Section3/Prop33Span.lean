/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finsupp.Weight
import Qatlib.Papers.HiddenTransl02.MainResults.Section3.LineLemmaPoly
import Mathlib.Tactic

/-!
# Powers of linear forms span homogeneous polynomials

This module proves Proposition 3.3 of [FriedlEtAl2014]: for `1 ≤ k ≤ p - 1`, the `k`th powers of
linear forms over the prime field span the homogeneous polynomials of degree `k`. The induction
uses multiplication by coordinate variables through the linear map `mulXi`.

## Main statements

* `span_lin_pow_one`: proves the degree-one spanning identity.
* `span_lin_pow_eq_homogeneous`: proves the spanning identity in all degrees from one to `p -
  1`.

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

variable {n p : ℕ}

/-- The polynomial `lin y` is homogeneous of degree one. -/
theorem lin_isHomogeneous (y : Fin n → ZMod p) : (lin y).IsHomogeneous 1 := by
  rw [lin]
  refine MvPolynomial.IsHomogeneous.sum univ
    (fun i => MvPolynomial.C (y i) * (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod p))) 1 ?_
  intro i _
  exact (MvPolynomial.isHomogeneous_X (R := ZMod p) i).C_mul (y i)

/-- The `k`th power of `lin y` is homogeneous of degree `k`. -/
theorem lin_pow_isHomogeneous (y : Fin n → ZMod p) (k : ℕ) :
    (lin y ^ k).IsHomogeneous k := by
  have h := (lin_isHomogeneous (p := p) y).pow k
  simpa using h

/-- The span of the first powers of all `lin y` is the degree-one homogeneous subspace. -/
theorem span_lin_pow_one :
    Submodule.span (ZMod p) (Set.range (fun y : Fin n → ZMod p => lin y ^ 1))
      = MvPolynomial.homogeneousSubmodule (Fin n) (ZMod p) 1 := by
  rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨y, rfl⟩
    change lin y ^ 1 ∈ Submodule.span (ZMod p)
      (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod p))))
    rw [pow_one, lin]
    refine Submodule.sum_mem _ ?_
    intro i _
    have hmem : (y i) • (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod p)) ∈
        Submodule.span (ZMod p)
          (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod p)))) :=
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
    simpa [MvPolynomial.smul_eq_C_mul] using hmem
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ⟨Pi.single i (1 : ZMod p), ?_⟩
    change lin (Pi.single i (1 : ZMod p)) ^ 1 = MvPolynomial.X i
    rw [pow_one, lin_single]

/-- For prime `p` and `m + 1 ≤ p - 1`, the product `X i * lin z ^ m` lies in the span of `(m +
1)`st powers of linear forms. -/
theorem Xi_mul_lin_pow_mem (hp : p.Prime) {m : ℕ} (hmp : m + 1 ≤ p - 1)
    (i : Fin n) (z : Fin n → ZMod p) :
    (MvPolynomial.X i) * lin z ^ m ∈
      Submodule.span (ZMod p) (Set.range (fun y : Fin n → ZMod p => lin y ^ (m + 1))) := by
  have h := lineLemma_poly_span (p := p) (n := n) hp (k := m + 1) (l := 1)
    (by omega) hmp (by omega) (Pi.single i (1 : ZMod p)) z
  have hspan_le : Submodule.span (ZMod p)
      (Set.range (fun a : Fin ((m + 1) + 1) =>
        lin (Pi.single i (1 : ZMod p) + (a.val : ZMod p) • z) ^ (m + 1)))
      ≤ Submodule.span (ZMod p) (Set.range (fun y : Fin n → ZMod p => lin y ^ (m + 1))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self _)
  have h' := hspan_le h
  simpa [lin_single, pow_one] using h'

/-- The `ZMod p`-linear map given by multiplication by the coordinate variable `X i`. -/
def mulXi (i : Fin n) :
    MvPolynomial (Fin n) (ZMod p) →ₗ[ZMod p] MvPolynomial (Fin n) (ZMod p) where
  toFun x := MvPolynomial.X i * x
  map_add' x y := mul_add _ x y
  map_smul' c x := by
    simp only [MvPolynomial.smul_eq_C_mul, RingHom.id_apply]
    ring

/-- For prime `p` and `m + 1 ≤ p - 1`, multiplication by `X i` sends the span of `m`th powers of
linear forms into the span of `(m + 1)`st powers. -/
theorem Xi_mul_span_le (hp : p.Prime) {m : ℕ} (hmp : m + 1 ≤ p - 1) (i : Fin n) :
    ∀ M' ∈ Submodule.span (ZMod p) (Set.range (fun z : Fin n → ZMod p => lin z ^ m)),
      (MvPolynomial.X i) * M' ∈
        Submodule.span (ZMod p) (Set.range (fun y : Fin n → ZMod p => lin y ^ (m + 1))) := by
  intro M' hM'
  have hcomap : Submodule.span (ZMod p) (Set.range (fun z : Fin n → ZMod p => lin z ^ m)) ≤
      Submodule.comap (mulXi (p := p) i)
        (Submodule.span (ZMod p) (Set.range (fun y : Fin n → ZMod p => lin y ^ (m + 1)))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    exact Xi_mul_lin_pow_mem hp hmp i z
  exact hcomap hM'

/-- For prime `p`, assuming the degree-`m` spanning identity, every monomial of degree `m + 1 ≤
p - 1` belongs to the span of `(m + 1)`st powers of linear forms. -/
theorem monomial_mem_span_succ (hp : p.Prime) {m : ℕ}
    (hmp : m + 1 ≤ p - 1)
    (hIH : Submodule.span (ZMod p) (Set.range (fun z : Fin n → ZMod p => lin z ^ m))
      = MvPolynomial.homogeneousSubmodule (Fin n) (ZMod p) m)
    (d : Fin n →₀ ℕ) (hd : d.degree = m + 1) :
    (MvPolynomial.monomial d (1 : ZMod p) : MvPolynomial (Fin n) (ZMod p)) ∈
      Submodule.span (ZMod p) (Set.range (fun y : Fin n → ZMod p => lin y ^ (m + 1))) := by
  have hne : d ≠ 0 := by
    intro h0
    rw [h0] at hd
    simp at hd
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hdi : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hle : Finsupp.single i (1 : ℕ) ≤ d :=
    Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hdi)
  set g : Fin n →₀ ℕ := d - Finsupp.single i (1 : ℕ) with hgdef
  have hdec : Finsupp.single i (1 : ℕ) + g = d := by
    rw [hgdef]
    exact add_tsub_cancel_of_le hle
  have hgdeg : g.degree = m := by
    have hsum : d.degree = (Finsupp.single i (1 : ℕ)).degree + g.degree := by
      rw [← hdec]
      exact map_add Finsupp.degree (Finsupp.single i 1) g
    rw [Finsupp.degree_single] at hsum
    omega
  have hg_mem : (MvPolynomial.monomial g (1 : ZMod p) : MvPolynomial (Fin n) (ZMod p)) ∈
      Submodule.span (ZMod p) (Set.range (fun z : Fin n → ZMod p => lin z ^ m)) := by
    rw [hIH]
    exact (MvPolynomial.mem_homogeneousSubmodule m
      (MvPolynomial.monomial g (1 : ZMod p))).mpr
      (MvPolynomial.isHomogeneous_monomial (1 : ZMod p) hgdeg)
  have hXi : (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod p))
      = MvPolynomial.monomial (Finsupp.single i (1 : ℕ)) 1 := rfl
  have hsplit : (MvPolynomial.monomial d (1 : ZMod p) : MvPolynomial (Fin n) (ZMod p))
      = (MvPolynomial.X i) * MvPolynomial.monomial g (1 : ZMod p) := by
    rw [hXi, MvPolynomial.monomial_mul, hdec, mul_one]
  rw [hsplit]
  exact Xi_mul_span_le hp hmp i _ hg_mem

/-- Over a prime field, the degree-`m` spanning identity implies the degree-`(m + 1)` identity
whenever `m + 1 ≤ p - 1`. -/
theorem span_lin_pow_succ (hp : p.Prime) {m : ℕ} (hmp : m + 1 ≤ p - 1)
    (hIH : Submodule.span (ZMod p) (Set.range (fun z : Fin n → ZMod p => lin z ^ m))
      = MvPolynomial.homogeneousSubmodule (Fin n) (ZMod p) m) :
    Submodule.span (ZMod p) (Set.range (fun y : Fin n → ZMod p => lin y ^ (m + 1)))
      = MvPolynomial.homogeneousSubmodule (Fin n) (ZMod p) (m + 1) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨y, rfl⟩
    exact lin_pow_isHomogeneous y (m + 1)
  · rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin n) (ZMod p) (m + 1)]
    erw [AddMonoidAlgebra.supported_eq_span_single (R := ZMod p)]
    apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, rfl⟩
    change MvPolynomial.monomial d (1 : ZMod p) ∈
      Submodule.span (ZMod p) (Set.range (fun y : Fin n → ZMod p => lin y ^ (m + 1)))
    exact monomial_mem_span_succ hp hmp hIH d (by simpa using hd)

/-- For prime `p` and `1 ≤ k ≤ p - 1`, the `k`th powers of all linear forms span the degree-`k`
homogeneous subspace. This is [Friedl et al., Proposition 3.3][FriedlEtAl2014]. -/
theorem span_lin_pow_eq_homogeneous (hp : p.Prime) :
    ∀ (k : ℕ), 1 ≤ k → k ≤ p - 1 →
      Submodule.span (ZMod p) (Set.range (fun y : Fin n → ZMod p => lin y ^ k))
        = MvPolynomial.homogeneousSubmodule (Fin n) (ZMod p) k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1 hkp
    rcases Nat.eq_or_lt_of_le hk1 with h1 | h2
    · subst h1
      exact span_lin_pow_one
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hmp : m + 1 ≤ p - 1 := by omega
      exact span_lin_pow_succ hp hmp (ih m (by omega) (by omega) (by omega))

end Qatlib.Papers.HiddenTransl02.MainResults.Section3
