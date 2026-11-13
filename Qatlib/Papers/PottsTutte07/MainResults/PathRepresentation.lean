/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PottsTutte07.MainResults.Definitions

/-!
# Path-coefficient normalization identities

The module derives local normalization identities from reciprocal coefficient relations and a
weighted adjacency eigenvector equation. Its real-coefficient existence statements characterize
when every ratio of eigenvector entries has a real square root [AharonovEtAl2007].

## Main statements

* `lemma5_1`: The adjacency eigenvector relation gives normalized sums of squared path
  coefficients.
* `corollary5_1_hermitian_iff`: Real square-root coefficients exist exactly when all entry
  ratios are nonnegative.

## References

* [Aharonov et al., 2007][AharonovEtAl2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PottsTutte07.MainResults

open scoped BigOperators

/-- The reciprocal coefficient and column-sum hypotheses imply the local cancellation and scalar
extension identities [AharonovEtAl2007]. -/
theorem claim5_1_representation_conditions
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (a b : ι → ι → R) (d : R)
    (h22 : ∀ ℓ k, b ℓ k * a ℓ k = 1)
    (h23 : ∀ k, (∑ ℓ : ι, a ℓ k * b k ℓ) = d) :
    (∀ (old : R) (ℓ k : ι), old * (b ℓ k * a ℓ k) = old) ∧
    (∀ (k : ι) (ext : R), (∑ ℓ : ι, (a ℓ k * b k ℓ) * ext) = d * ext) := by
  refine ⟨?_, ?_⟩
  · intro old ℓ k
    rw [h22 ℓ k, mul_one]
  · intro k ext
    rw [← Finset.sum_mul, h23 k]

/-- The stated branch relation and adjacency eigenvector equation imply reciprocal coefficients
and normalized adjacency sums of their squares [AharonovEtAl2007]. -/
theorem lemma5_1
    {ι : Type*} [Fintype ι]
    (adj : ι → ι → Bool) (π : ι → ℂ) (a : ι → ι → ℂ) (d : ℂ)
    (hπ : ∀ i, π i ≠ 0)
    (ha : ∀ l k, a l k ^ 2 = π l / π k)
    (hbranch : ∀ l k, a k l * a l k = 1)
    (heigen : ∀ k, (∑ l : ι, (if adj l k then π l else 0)) = d * π k) :
    (∀ l k, a k l * a l k = 1) ∧
    (∀ k, (∑ l : ι, (if adj l k then a l k * a l k else 0)) = d) := by
  refine ⟨hbranch, ?_⟩
  intro k
  have step : ∀ l : ι, (if adj l k then a l k * a l k else 0)
      = (if adj l k then π l else 0) / π k := by
    intro l
    by_cases h : adj l k
    · simp only [h, if_true]
      have hs : a l k * a l k = a l k ^ 2 := by ring
      rw [hs, ha l k]
    · simp [h]
  calc (∑ l : ι, (if adj l k then a l k * a l k else 0))
      = ∑ l : ι, (if adj l k then π l else 0) / π k := Finset.sum_congr rfl (fun l _ => step l)
    _ = (∑ l : ι, (if adj l k then π l else 0)) / π k := by rw [Finset.sum_div]
    _ = d * π k / π k := by rw [heigen k]
    _ = d := by field_simp [hπ k]

/-- A real coefficient family whose squares are the ratios `π l / π k` exists if and only if all
those ratios are nonnegative [AharonovEtAl2007]. -/
theorem corollary5_1_hermitian_iff
    {ι : Type*} (π : ι → ℝ) :
    (∃ a : ι → ι → ℝ, ∀ l k, a l k ^ 2 = π l / π k)
      ↔ ∀ l k, 0 ≤ π l / π k := by
  constructor
  · rintro ⟨a, ha⟩ l k
    have hsq : 0 ≤ a l k ^ 2 := sq_nonneg _
    rwa [ha l k] at hsq
  · intro h
    exact ⟨fun l k => Real.sqrt (π l / π k), fun l k => Real.sq_sqrt (h l k)⟩

/-- A strictly positive real family `π` possesses real coefficients whose squares are every
ratio `π l / π k` [AharonovEtAl2007]. -/
theorem corollary5_1_of_pos
    {ι : Type*} (π : ι → ℝ) (hpos : ∀ i, 0 < π i) :
    ∃ a : ι → ι → ℝ, ∀ l k, a l k ^ 2 = π l / π k := by
  refine corollary5_1_hermitian_iff π |>.2 ?_
  intro l k
  exact le_of_lt (div_pos (hpos l) (hpos k))

end Qatlib.Papers.PottsTutte07.MainResults
