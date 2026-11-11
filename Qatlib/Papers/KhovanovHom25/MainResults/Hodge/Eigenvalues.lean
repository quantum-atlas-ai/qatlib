/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KhovanovHom25.MainResults.Hodge.Decomposition

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 10: eigenvalues of the Hodge Laplacian

Source: arXiv:2501.12378v2, Proposition 10, pp. 33-34 (proof at eq. (6.4)).

Two assertions are formalized (degree `i+1` in the `ℕ` grading):

1. every non-zero eigenvalue of `Δᵢ₊₁` on `ℋᵢ₊₁⊥` also occurs as an eigenvalue
   of `Δᵢ₊₂` on `ℋᵢ₊₂⊥` or of `Δᵢ` on `ℋᵢ⊥` (the paper cites
   [79, Proposition 2.2]);
2. every eigenvalue of `Δᵢ₊₁` is an eigenvalue of `dᵢ₊₁†dᵢ₊₁` or of
   `dᵢdᵢ†`.

The proof of (2) is the algebraic computation displayed in eq. (6.4): with
`A = dᵢ₊₁†dᵢ₊₁`, `B = dᵢdᵢ†`, one has `AB = 0` and `A(A+B) = A²`, so applying `A`
to `Δx = λx` yields `A(Ax) = λ·Ax`.  Either `Ax ≠ 0` and `Ax` is an
`A`-eigenvector, or `Ax = 0` and `Bx = λx`.  Part (1) then transports the
eigenvector through `dᵢ₊₁` (respectively `dᵢ†`) into the neighbouring cochain
space, using `Δ ∘ d = d ∘ Δ` and `Δ ∘ d† = d† ∘ Δ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators ComplexInnerProductSpace

namespace Qatlib.Papers.KhovanovHom25.MainResults

open CochainComplex

variable (K : CochainComplex)

/-- **Proposition 10, second bullet (eq. (6.4)).**  A non-zero eigenvalue `λ` of
`Δᵢ` is an eigenvalue of `dᵢ†dᵢ` or of `dᵢ₋₁dᵢ₋₁†` (here `lapDown`/`lapUp`). -/
theorem proposition10_eigenvalue_factors (i : ℕ) {lam : ℂ} (hne : lam ≠ 0)
    {x : K.C i} (hx : x ≠ 0) (h : K.lap i x = lam • x) :
    (∃ y : K.C i, y ≠ 0 ∧ K.lapDown i y = lam • y) ∨
      (∃ y : K.C i, y ≠ 0 ∧ K.lapUp i y = lam • y) := by
  have hABx : K.lapDown i (K.lapUp i x) = 0 := by
    have hAB := K.lapDown_comp_lapUp i
    have hval := congrArg (fun f : K.C i →ₗ[ℂ] K.C i => f x) hAB
    simpa using hval
  have hΔ : K.lap i x = K.lapDown i x + K.lapUp i x := rfl
  have hAΔ : K.lapDown i (K.lap i x) =
      K.lapDown i (K.lapDown i x) + K.lapDown i (K.lapUp i x) := by
    rw [hΔ, map_add]
  have hAA : K.lapDown i (K.lapDown i x) = lam • (K.lapDown i x) := by
    rw [h, map_smul] at hAΔ
    rw [hABx, add_zero] at hAΔ
    exact hAΔ.symm
  by_cases hA0 : K.lapDown i x = 0
  · right
    refine ⟨x, hx, ?_⟩
    have hB : K.lapUp i x = lam • x := by
      rw [hΔ, hA0, zero_add] at h
      exact h
    exact hB
  · left
    exact ⟨K.lapDown i x, hA0, hAA⟩

/-- **Proposition 10, first bullet.**  A non-zero eigenvalue of `Δᵢ₊₁` on the
orthogonal complement of the harmonic chains is an eigenvalue of the Laplacian
one degree up or one degree down, on the corresponding orthogonal complement. -/
theorem proposition10_neighbor_eigenvalue (i : ℕ) {lam : ℂ} (hne : lam ≠ 0)
    {x : K.C (i + 1)} (hx : x ≠ 0) (_hxorth : x ∈ (K.harmonic (i + 1))ᗮ)
    (h : K.lap (i + 1) x = lam • x) :
    (∃ y : K.C ((i + 1) + 1), y ≠ 0 ∧ y ∈ (K.harmonic ((i + 1) + 1))ᗮ ∧
        K.lap ((i + 1) + 1) y = lam • y) ∨
      (∃ y : K.C i, y ≠ 0 ∧ y ∈ (K.harmonic i)ᗮ ∧
        K.lap i y = lam • y) := by
  by_cases hd : K.d (i + 1) x = 0
  · -- `d x = 0`: transport `d†x` down.
    right
    have hlapup : K.lapUp (i + 1) x = lam • x := by
      have h' := h
      rw [K.lap_apply, hd] at h'
      simpa using h'
    have hdadj_ne : K.dAdj i x ≠ 0 := by
      intro hz
      have hzero : lam • x = 0 := by
        rw [← hlapup]
        simp [lapUp_succ, hz]
      rcases smul_eq_zero.mp hzero with h0 | h0
      · exact hne h0
      · exact hx h0
    refine ⟨K.dAdj i x, hdadj_ne, ?_, ?_⟩
    · exact K.orthogonal_of_le_orthogonal (K.harmonic_le_orthogonal_range_dAdj i)
        ⟨x, rfl⟩
    · rw [K.lap_dAdj i x, h, map_smul]
  · -- `d x ≠ 0`: transport `d x` up.
    left
    refine ⟨K.d (i + 1) x, hd, ?_, ?_⟩
    · exact K.orthogonal_of_le_orthogonal
        (K.harmonic_le_orthogonal_range_left (i + 1)) ⟨x, rfl⟩
    · rw [K.lap_d (i + 1) x, h, map_smul]

/-- **Proposition 10.**  Both bullets of the proposition, in the paper's form,
at degree `i+1`. -/
theorem proposition10 (i : ℕ) :
    (∀ (lam : ℂ), lam ≠ 0 → ∀ x : K.C (i + 1), x ≠ 0 →
      x ∈ (K.harmonic (i + 1))ᗮ → K.lap (i + 1) x = lam • x →
      (∃ y : K.C ((i + 1) + 1), y ≠ 0 ∧ y ∈ (K.harmonic ((i + 1) + 1))ᗮ ∧
          K.lap ((i + 1) + 1) y = lam • y) ∨
        (∃ y : K.C i, y ≠ 0 ∧ y ∈ (K.harmonic i)ᗮ ∧
          K.lap i y = lam • y)) ∧
      (∀ (lam : ℂ), lam ≠ 0 → ∀ x : K.C (i + 1), x ≠ 0 →
        K.lap (i + 1) x = lam • x →
        (∃ y : K.C (i + 1), y ≠ 0 ∧ K.lapDown (i + 1) y = lam • y) ∨
          (∃ y : K.C (i + 1), y ≠ 0 ∧ K.lapUp (i + 1) y = lam • y)) :=
  ⟨fun lam hne x hx hxorth h => proposition10_neighbor_eigenvalue K i hne hx hxorth h,
    fun lam hne x hx h => proposition10_eigenvalue_factors K (i + 1) hne hx h⟩

end Qatlib.Papers.KhovanovHom25.MainResults
