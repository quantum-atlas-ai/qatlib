/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic

/-!
# Equivalence of classical and diagonal quantum witnesses

`basisVec` embeds each Boolean witness as a normalized complex basis vector. Bounds on the
weighted average `qAccept` show that allowing arbitrary normalized vectors does not change the
completeness and soundness conditions, yielding `lemma2_MA_eq_MAq`. See
[BravyiEtAl2008Stoquastic].

## Main statements

* `qAccept_le_max`: some classical witness bounds the quantum acceptance value from above.
* `MA_iff_MAq_pointwise`: classical and normalized-vector acceptance conditions are equivalent.
* `lemma2_MA_eq_MAq`: `InMA` and `InMAq` coincide in the stated verifier model.

## References

* [Bravyi et al., 2008][BravyiEtAl2008Stoquastic]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs

namespace Qatlib.Papers.StoquasticHam06.MainResults.Lemma2

/-- The complex coordinate vector equal to one at `z` and zero at every other Boolean string. -/
def basisVec {n : ℕ} (z : Sigma n) : Sigma n → ℂ :=
  fun z' => if z' = z then 1 else 0

/-- A computational basis vector is normalized. -/
lemma normalized_basis {n : ℕ} (z : Sigma n) : Normalized (basisVec z) := by
  simp [Normalized, basisVec]

/-- The quantum acceptance average of a computational basis vector is its corresponding
classical acceptance value. -/
lemma qAccept_basis {n : ℕ} (a : Sigma n → ℝ) (z : Sigma n) :
    qAccept a (basisVec z) = a z := by
  simp [qAccept, basisVec]

/-- For a normalized complex vector, some basis acceptance value is at least its quantum
acceptance average. -/
lemma qAccept_le_max {n : ℕ} (a : Sigma n → ℝ) (ξ : Sigma n → ℂ)
    (hξ : Normalized ξ) : ∃ z, qAccept a ξ ≤ a z := by
  obtain ⟨z, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Sigma n)) a Finset.univ_nonempty
  refine ⟨z, ?_⟩
  calc qAccept a ξ = ∑ z', a z' * Complex.normSq (ξ z') := rfl
    _ ≤ ∑ z', a z * Complex.normSq (ξ z') := by
      refine Finset.sum_le_sum ?_
      intro z' _
      exact mul_le_mul_of_nonneg_right (hmax z' (Finset.mem_univ z'))
        (Complex.normSq_nonneg _)
    _ = a z * ∑ z', Complex.normSq (ξ z') := by rw [Finset.mul_sum]
    _ = a z := by rw [hξ]; ring

/-- For a normalized complex vector, some basis acceptance value is at most its quantum
acceptance average. -/
lemma qAccept_ge_min {n : ℕ} (a : Sigma n → ℝ) (ξ : Sigma n → ℂ)
    (hξ : Normalized ξ) : ∃ z, a z ≤ qAccept a ξ := by
  obtain ⟨z, -, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Sigma n)) a Finset.univ_nonempty
  refine ⟨z, ?_⟩
  calc a z = a z * ∑ z', Complex.normSq (ξ z') := by rw [hξ]; ring
    _ = ∑ z', a z * Complex.normSq (ξ z') := by rw [Finset.mul_sum]
    _ ≤ ∑ z', a z' * Complex.normSq (ξ z') := by
      refine Finset.sum_le_sum ?_
      intro z' _
      exact mul_le_mul_of_nonneg_right (hmin z' (Finset.mem_univ z'))
        (Complex.normSq_nonneg _)

/-- The pointwise completeness and soundness conditions using classical witnesses are equivalent
to those using normalized complex vectors and the diagonal average `qAccept`. See
[BravyiEtAl2008Stoquastic]. -/
lemma MA_iff_MAq_pointwise {n : ℕ} (a : Sigma n → ℝ) (py pn : Prop) :
    ((py → ∃ z : Sigma n, (2 : ℝ) / 3 ≤ a z) ∧
      (pn → ∀ z : Sigma n, a z ≤ (1 : ℝ) / 3)) ↔
    ((py → ∃ ξ : Sigma n → ℂ,
        Normalized ξ ∧ (2 : ℝ) / 3 ≤ qAccept a ξ) ∧
      (pn → ∀ ξ : Sigma n → ℂ, Normalized ξ → qAccept a ξ ≤ (1 : ℝ) / 3)) := by
  constructor
  · rintro ⟨hyes, hno⟩
    refine ⟨?_, ?_⟩
    · intro hp
      obtain ⟨z, hz⟩ := hyes hp
      exact ⟨basisVec z, normalized_basis z, by rwa [qAccept_basis]⟩
    · intro hn ξ hξ
      calc qAccept a ξ = ∑ z', a z' * Complex.normSq (ξ z') := rfl
        _ ≤ ∑ z', (1 : ℝ) / 3 * Complex.normSq (ξ z') := by
          refine Finset.sum_le_sum ?_
          intro z' _
          exact mul_le_mul_of_nonneg_right (hno hn z') (Complex.normSq_nonneg _)
        _ = (1 : ℝ) / 3 * ∑ z', Complex.normSq (ξ z') := by rw [Finset.mul_sum]
        _ = (1 : ℝ) / 3 := by rw [hξ]; ring
  · rintro ⟨hyes, hno⟩
    refine ⟨?_, ?_⟩
    · intro hp
      obtain ⟨ξ, hξ, hq⟩ := hyes hp
      obtain ⟨z, hz⟩ := qAccept_le_max a ξ hξ
      exact ⟨z, le_trans hq hz⟩
    · intro hn z
      have h := hno hn (basisVec z) (normalized_basis z)
      rwa [qAccept_basis] at h

/-- For every encoding and promise problem, membership in `InMA` is equivalent to membership in
`InMAq`. See [BravyiEtAl2008Stoquastic]. -/
theorem lemma2_MA_eq_MAq {α : Type*} (E : Encoding α) (L : PromiseProblem α) :
    InMA E L ↔ InMAq E L := by
  constructor
  · rintro ⟨W, hW⟩
    exact ⟨W, fun x =>
      (MA_iff_MAq_pointwise (fun z => W.accept E x (List.ofFn z)) (L.yes x) (L.no x)).1
        (hW x)⟩
  · rintro ⟨W, hW⟩
    exact ⟨W, fun x =>
      (MA_iff_MAq_pointwise (fun z => W.accept E x (List.ofFn z)) (L.yes x) (L.no x)).2
        (hW x)⟩

end Qatlib.Papers.StoquasticHam06.MainResults.Lemma2
