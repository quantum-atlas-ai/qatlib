/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Squarefree coefficients on disjoint variable blocks

`SupportedIn` tracks the variables occurring in nonzero monomials of a multivariate polynomial.
For disjoint variable supports, coefficients of products factor uniquely into coefficients of
the factors.

The exponent functions `squarefree` and `blockDegree` specialize this factorization to products
of powers of variable sums. Matching block sizes give products of factorials, providing the
polarization normalization used in [AftabAnTrivisa2026].

## Main statements

* `coeff_prod_disjoint`: factors coefficients across disjoint variable blocks.
* `coeff_position_power`: computes the squarefree coefficient of a power of a variable sum.
* `coeff_matching_blocks`: gives the product of block factorials.
* `normalized_coeff_matching_blocks`: normalizes the matching rational coefficient to one.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHPolarCoeff

open scoped BigOperators Classical
open MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- Every monomial with nonzero coefficient uses only variables in the specified finite set. -/
def SupportedIn (p : MvPolynomial σ R) (s : Finset σ) : Prop :=
  ∀ d : σ →₀ ℕ, p.coeff d ≠ 0 → d.support ⊆ s

/-- A polynomial is supported in a finite variable set exactly when its variable set is
contained in that set. -/
theorem supportedIn_iff_vars (p : MvPolynomial σ R) (s : Finset σ) :
    SupportedIn p s ↔ p.vars ⊆ s := by
  constructor
  · intro h j hj
    obtain ⟨d, hd, hjd⟩ := (mem_vars_iff_mem_support j).mp hj
    exact h d (mem_support_iff.mp hd) hjd
  · intro h d hd
    exact (support_subset_vars_of_mem_support (mem_support_iff.mpr hd)).trans h

/-- A finite product of polynomials supported in specified variable sets is supported in their
union. -/
theorem supportedIn_prod {ι : Type*} (I : Finset ι) (p : ι → MvPolynomial σ R)
    (s : ι → Finset σ) (hp : ∀ i ∈ I, SupportedIn (p i) (s i)) :
    SupportedIn (∏ i ∈ I, p i) (I.biUnion s) := by
  classical
  rw [supportedIn_iff_vars]
  apply (vars_prod p).trans
  exact Finset.biUnion_mono fun i hi => (supportedIn_iff_vars _ _).mp (hp i hi)

/-- A coefficient vanishes if its exponent support is not contained in a variable set supporting
the polynomial. -/
theorem coeff_zero_of_not_supported {p : MvPolynomial σ R} {s : Finset σ}
    (hp : SupportedIn p s) {d : σ →₀ ℕ} (hd : ¬d.support ⊆ s) : p.coeff d = 0 := by
  by_contra h
  exact hd (hp d h)

/-- Decompositions of equal exponent sums into two disjoint support sets have equal
corresponding components. -/
theorem exponents_unique {s t : Finset σ} (hst : Disjoint s t)
    {a b c d : σ →₀ ℕ} (ha : a.support ⊆ s) (hb : b.support ⊆ t)
    (hc : c.support ⊆ s) (hd : d.support ⊆ t) (h : a + b = c + d) : a = c ∧ b = d := by
  have hz (e : σ →₀ ℕ) (u : Finset σ) (he : e.support ⊆ u) (i : σ) (hi : i ∉ u) :
      e i = 0 := Finsupp.notMem_support_iff.mp (fun hm => hi (he hm))
  have hac : a = c := by
    ext i
    have hi := DFunLike.congr_fun h i
    simp only [Finsupp.add_apply] at hi
    by_cases his : i ∈ s
    · have hit : i ∉ t := fun hit => Finset.disjoint_left.mp hst his hit
      simpa only [hz b t hb i hit, hz d t hd i hit, add_zero] using hi
    · rw [hz a s ha i his, hz c s hc i his]
  exact ⟨hac, add_left_cancel (by simpa only [hac] using h)⟩

/-- For polynomials supported in disjoint variable sets, the coefficient at a sum of compatible
exponents is the product of their individual coefficients. -/
theorem coeff_mul_disjoint {p q : MvPolynomial σ R} {s t : Finset σ}
    (hp : SupportedIn p s) (hq : SupportedIn q t) (hst : Disjoint s t)
    (a b : σ →₀ ℕ) (ha : a.support ⊆ s) (hb : b.support ⊆ t) :
    (p * q).coeff (a + b) = p.coeff a * q.coeff b := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_single (a, b)
  · intro u hu hne
    by_cases hp0 : p.coeff u.1 = 0
    · rw [hp0, zero_mul]
    by_cases hq0 : q.coeff u.2 = 0
    · rw [hq0, mul_zero]
    obtain ⟨h1, h2⟩ := exponents_unique hst (hp u.1 hp0) (hq u.2 hq0) ha hb
      (Finset.mem_antidiagonal.mp hu)
    exact (hne (Prod.ext h1 h2)).elim
  · intro hnot
    exact (hnot (Finset.mem_antidiagonal.mpr rfl)).elim

/-- For finitely many polynomials supported in pairwise disjoint variable sets, the coefficient
at a sum of compatible exponents factors into the product of the coefficients. -/
theorem coeff_prod_disjoint {ι : Type*} (I : Finset ι) (p : ι → MvPolynomial σ R)
    (s : ι → Finset σ) (d : ι → σ →₀ ℕ)
    (hs : (↑I : Set ι).Pairwise (fun i j => Disjoint (s i) (s j)))
    (hp : ∀ i ∈ I, SupportedIn (p i) (s i)) (hd : ∀ i ∈ I, (d i).support ⊆ s i) :
    (∏ i ∈ I, p i).coeff (∑ i ∈ I, d i) = ∏ i ∈ I, (p i).coeff (d i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [coeff_one]
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    have hI : (↑I : Set ι).Pairwise (fun a b => Disjoint (s a) (s b)) :=
      hs.mono (Finset.subset_insert _ _)
    have hdis : Disjoint (s i) (I.biUnion s) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hs (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj)
        (ne_of_mem_of_not_mem hj hi).symm
    have htail : (∑ j ∈ I, d j).support ⊆ I.biUnion s := by
      intro j hj
      obtain ⟨a, ha, hja⟩ := Finsupp.mem_support_finsetSum j hj
      exact Finset.mem_biUnion.mpr ⟨a, ha, hd a (Finset.mem_insert_of_mem ha) hja⟩
    rw [coeff_mul_disjoint (hp i (Finset.mem_insert_self _ _))
      (supportedIn_prod I p s (fun j hj => hp j (Finset.mem_insert_of_mem hj))) hdis
      (d i) (∑ j ∈ I, d j) (hd i (Finset.mem_insert_self _ _)) htail]
    rw [ih hI (fun j hj => hp j (Finset.mem_insert_of_mem hj))
      (fun j hj => hd j (Finset.mem_insert_of_mem hj))]

/-- The finitely supported exponent function equal to one on a finite variable set and zero
elsewhere. -/
def squarefree (s : Finset σ) : σ →₀ ℕ := Finsupp.indicator s (fun _ _ => 1)

/-- The squarefree exponent function on the union of a finite family of variable blocks. -/
def blockDegree {ι : Type*} (I : Finset ι) (s : ι → Finset σ) : σ →₀ ℕ :=
  squarefree (I.biUnion s)

/-- The support of the squarefree exponent function is contained in its defining variable set. -/
theorem squarefree_support (s : Finset σ) : (squarefree s).support ⊆ s :=
  Finsupp.support_indicator_subset _ _

/-- The total degree of the squarefree exponent function equals the cardinality of its defining
set. -/
theorem squarefree_degree (s : Finset σ) : (squarefree s).sum (fun _ n => n) = s.card := by
  classical
  rw [Finsupp.sum_of_support_subset _ (squarefree_support s) _ (by simp)]
  simp [squarefree]

/-- The multinomial coefficient of a squarefree exponent function equals the factorial of the
number of variables. -/
theorem squarefree_multinomial (s : Finset σ) : (squarefree s).multinomial = s.card.factorial := by
  classical
  rw [← Finsupp.multinomial_of_support_subset (squarefree_support s)]
  have hp : (∏ j ∈ s, ((squarefree s) j).factorial) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    simp [squarefree, Finsupp.indicator_of_mem hj]
  simp only [Nat.multinomial, hp, Nat.div_one]
  congr 1
  simp [squarefree]

/-- The full squarefree coefficient of the kth power of a sum of distinct variables is the
number of variables factorial when `k` equals that number, and zero otherwise. -/
theorem coeff_position_power (s : Finset σ) (k : ℕ) :
    ((∑ j ∈ s, X j : MvPolynomial σ R) ^ k).coeff (squarefree s) =
      if s.card = k then (s.card.factorial : R) else 0 := by
  classical
  have hsum : (∑ j ∈ s, X j : MvPolynomial σ R) =
      (Finsupp.indicator s (fun _ _ => (1 : R))).linearCombination R X := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _
      (Finsupp.support_indicator_subset _ _) _ (by simp)]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finsupp.indicator_of_mem hj]
  rw [hsum, coeff_linearCombination_X_pow, squarefree_degree, squarefree_multinomial]
  have hprod : (squarefree s).prod (fun j n =>
      (Finsupp.indicator s (fun _ _ => (1 : R))) j ^ n) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    simp [Finsupp.indicator_of_mem (squarefree_support s hj)]
  rw [hprod, mul_one]

/-- Every power of a sum of variables is supported in that variable set. -/
theorem position_power_supported [Nontrivial R] (s : Finset σ) (k : ℕ) :
    SupportedIn ((∑ j ∈ s, X j : MvPolynomial σ R) ^ k) s := by
  classical
  rw [supportedIn_iff_vars]
  apply (vars_pow _ k).trans
  apply (vars_sum_subset s (fun j => (X j : MvPolynomial σ R))).trans
  simp

/-- For disjoint variable sets, the squarefree exponent function of their union is the sum of
their squarefree exponent functions. -/
theorem squarefree_union {s t : Finset σ} (h : Disjoint s t) :
    squarefree (s ∪ t) = squarefree s + squarefree t := by
  classical
  ext j
  by_cases hs : j ∈ s <;> by_cases ht : j ∈ t
  · exact (Finset.disjoint_left.mp h hs ht).elim
  all_goals simp [squarefree, Finsupp.indicator_apply, hs, ht]

/-- For pairwise disjoint variable blocks, the squarefree exponent function of their union is
the sum of the block exponent functions. -/
theorem squarefree_biUnion {ι : Type*} (I : Finset ι) (s : ι → Finset σ)
    (hs : (↑I : Set ι).Pairwise (fun i j => Disjoint (s i) (s j))) :
    squarefree (I.biUnion s) = ∑ i ∈ I, squarefree (s i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.biUnion_empty, Finset.sum_empty]
    ext j
    simp [squarefree, Finsupp.indicator_apply]
  | @insert i I hi ih =>
    have hdis : Disjoint (s i) (I.biUnion s) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hs (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj)
        (ne_of_mem_of_not_mem hj hi).symm
    rw [Finset.biUnion_insert, squarefree_union hdis, Finset.sum_insert hi,
      ih (hs.mono (Finset.subset_insert _ _))]

/-- For disjoint variable blocks, the full squarefree coefficient of the product of block sum
powers is the product of block factorials when all powers match their block sizes, and zero
otherwise. -/
theorem coeff_position_blocks [Nontrivial R] {ι : Type*} (I : Finset ι)
    (s : ι → Finset σ) (k : ι → ℕ)
    (hs : (↑I : Set ι).Pairwise (fun i j => Disjoint (s i) (s j))) :
    (∏ i ∈ I, (∑ j ∈ s i, X j : MvPolynomial σ R) ^ k i).coeff (blockDegree I s) =
        ∏ i ∈ I, if (s i).card = k i then ((s i).card.factorial : R) else 0 := by
  rw [blockDegree, squarefree_biUnion I s hs,
    coeff_prod_disjoint I (fun i => (∑ j ∈ s i, X j : MvPolynomial σ R) ^ k i)
      s (fun i => squarefree (s i)) hs (fun i _ => position_power_supported (s i) (k i))
      (fun i _ => squarefree_support (s i))]
  exact Finset.prod_congr rfl fun i _ => coeff_position_power (s i) (k i)

/-- For disjoint variable blocks with powers equal to their sizes, the full squarefree
coefficient is the product of the block factorials. -/
theorem coeff_matching_blocks [Nontrivial R] {ι : Type*} (I : Finset ι)
    (s : ι → Finset σ)
    (hs : (↑I : Set ι).Pairwise (fun i j => Disjoint (s i) (s j))) :
    (∏ i ∈ I, (∑ j ∈ s i, X j : MvPolynomial σ R) ^ (s i).card).coeff (blockDegree I s) =
        ∏ i ∈ I, ((s i).card.factorial : R) := by
  simp only [coeff_position_blocks I s (fun i => (s i).card) hs, ite_true]

/-- For disjoint variable blocks, the full squarefree coefficient vanishes if any block power
differs from its size. -/
theorem coeff_mismatched_blocks [Nontrivial R] {ι : Type*} (I : Finset ι)
    (s : ι → Finset σ) (k : ι → ℕ)
    (hs : (↑I : Set ι).Pairwise (fun i j => Disjoint (s i) (s j)))
    (i : ι) (hi : i ∈ I) (hk : (s i).card ≠ k i) :
    (∏ a ∈ I, (∑ j ∈ s a, X j : MvPolynomial σ R) ^ k a).coeff (blockDegree I s) = 0 := by
  rw [coeff_position_blocks I s k hs]
  exact Finset.prod_eq_zero hi (if_neg hk)

/-- Dividing the full squarefree coefficient of matching disjoint rational variable blocks by
the product of their factorials gives one. -/
theorem normalized_coeff_matching_blocks {ι : Type*} (I : Finset ι) (s : ι → Finset σ)
    (hs : (↑I : Set ι).Pairwise (fun i j => Disjoint (s i) (s j))) :
    (∏ i ∈ I, ((s i).card.factorial : ℚ))⁻¹ *
      (∏ i ∈ I, (∑ j ∈ s i, X j : MvPolynomial σ ℚ) ^ (s i).card).coeff (blockDegree I s) = 1 := by
  rw [coeff_matching_blocks I s hs, inv_mul_cancel₀]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact_mod_cast Nat.factorial_ne_zero (s i).card

end Qatlib.Papers.CommutLCHS26.MainResults.BCHPolarCoeff
