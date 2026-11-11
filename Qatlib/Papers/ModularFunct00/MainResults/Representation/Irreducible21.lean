/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ModularFunct00.MainResults.Setup
import Qatlib.Papers.ModularFunct00.MainResults.Examples
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# Irreducibility of the two-dimensional Jones example

This module proves irreducibility of the explicit pair `sig1_21`, `sig2_21` under the nontrivial
fifth-root and parameter equations. It first rules out a common nonzero eigenvector, then shows
that a subspace invariant under both matrices is zero or the whole space.

These calculations supply the two-dimensional irreducibility argument used in
[FreedmanLarsenWang2000].

## Main statements

* `sig21_no_common_eigenvector`: The generator pair has no common nonzero eigenvector.
* `sig21_irreducible`: A common invariant subspace is trivial.

## References

* [Freedman et al., 2000][FreedmanLarsenWang2000]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Representation

open Matrix
open Qatlib.Papers.ModularFunct00.MainResults.Examples

variable {q : ℂ}

/-- A subspace of `ℂ²` is invariant when multiplication by each of the two given matrices
preserves it. -/
def IsInvariant (A B : CM 2) (W : Submodule ℂ (Fin 2 → ℂ)) : Prop :=
  (∀ x ∈ W, A.mulVec x ∈ W) ∧ (∀ x ∈ W, B.mulVec x ∈ W)

/-- For a nontrivial fifth root of unity `q`, the quantity `q^2 + q + 1` is nonzero. -/
lemma fiveRoot_quantum_three_ne_zero {q : ℂ} (hq5 : q ^ 5 = 1) (hq1 : q ≠ 1) :
    q ^ 2 + q + 1 ≠ 0 := by
  intro h
  have hq3 : q ^ 3 = 1 := by
    have h3 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by ring
    have hfac : (q - 1) * (q ^ 2 + q + 1) = 0 := by rw [h]; ring
    have hzero : q ^ 3 - 1 = 0 := by rw [h3, hfac]
    linear_combination hzero
  have hq6 : q ^ 6 = 1 := by
    have h1 : q ^ 6 = (q ^ 3) ^ 2 := by ring
    rw [h1, hq3]; norm_num
  have hq6' : q ^ 6 = q := by
    have h6 : (6 : ℕ) = 5 + 1 := rfl
    rw [h6, pow_succ, hq5, one_mul]
  exact hq1 (hq6'.symm.trans hq6)

/-- Under the stated fifth-root and parameter equations, `sig1_21` and `sig2_21 s` have no
common nonzero eigenvector; see [FreedmanLarsenWang2000]. -/
theorem sig21_no_common_eigenvector {q s : ℂ} (hq5 : q ^ 5 = 1) (hq1 : q ≠ 1)
    (hs : s ^ 2 * q = q ^ 2 + q + 1) :
    ¬ ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ ∃ α β : ℂ,
      (sig1_21 (q := q)).mulVec v = α • v ∧
      (sig2_21 (q := q) s).mulVec v = β • v := by
  rintro ⟨v, hv0, α, β, hA, hB⟩
  have hq0 : q ≠ 0 := fiveRoot_ne_zero hq5
  have hq1' : q + 1 ≠ 0 := fiveRoot_add_one_ne_zero hq5
  have hq1'' : 1 + q ≠ 0 := by simpa [add_comm] using hq1'
  have hq2 : q ^ 2 + q + 1 ≠ 0 := fiveRoot_quantum_three_ne_zero hq5 hq1
  have hs0 : s ≠ 0 := by
    intro h
    have hz : s ^ 2 * q = 0 := by rw [h]; ring
    rw [hs] at hz
    exact hq2 hz
  have hb01 : -(q * s) / (q + 1) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hq0 hs0)) hq1'

  have hA0 : -(v 0) = α * v 0 := by
    have h := congrFun hA 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, sig1_21, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul] using h
  have hA1 : q * v 1 = α * v 1 := by
    have h := congrFun hA 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, sig1_21, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul] using h
  by_cases hv1 : v 1 = 0
  · have hv0' : v 0 ≠ 0 := by
      intro h0
      apply hv0
      funext i
      fin_cases i <;> simp [h0, hv1]
    have hB1 : (sig2_21 (q := q) s).mulVec v 1 = β * v 1 := by
      have h := congrFun hB 1
      simpa [Pi.smul_apply, smul_eq_mul] using h
    have hBcoord : (sig2_21 (q := q) s).mulVec v 1
        = (-(q * s) / (q + 1)) * v 0 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, sig2_21, Matrix.of_apply, hv1]
    rw [hBcoord, hv1, mul_zero] at hB1
    exact (mul_ne_zero hb01 hv0') hB1
  · have hα : α = q := by
      have := mul_right_cancel₀ hv1 hA1
      exact this.symm
    have hv0z : v 0 = 0 := by
      have h := hA0
      rw [hα] at h
      have h' : (1 + q) * v 0 = 0 := by linear_combination -h
      exact (mul_eq_zero.mp h').resolve_left hq1''
    have hB0 : (sig2_21 (q := q) s).mulVec v 0 = β * v 0 := by
      have h := congrFun hB 0
      simpa [Pi.smul_apply, smul_eq_mul] using h
    have hBcoord : (sig2_21 (q := q) s).mulVec v 0
        = (-(q * s) / (q + 1)) * v 1 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, sig2_21, Matrix.of_apply, hv0z]
    rw [hBcoord, hv0z, mul_zero] at hB0
    exact (mul_ne_zero hb01 hv1) hB0

/-- Under the stated fifth-root and parameter equations, any subspace invariant under both
explicit generators is either zero or the whole space; see [FreedmanLarsenWang2000]. -/
theorem sig21_irreducible {q s : ℂ} (hq5 : q ^ 5 = 1) (hq1 : q ≠ 1)
    (hs : s ^ 2 * q = q ^ 2 + q + 1)
    (W : Submodule ℂ (Fin 2 → ℂ))
    (hW : IsInvariant (sig1_21 (q := q)) (sig2_21 (q := q) s) W) :
    W = ⊥ ∨ W = ⊤ := by
  rcases eq_or_ne W ⊥ with hbot | hbot
  · exact Or.inl hbot
  right
  have hfr_le : Module.finrank ℂ W ≤ 2 := by
    have := Submodule.finrank_le (R := ℂ) W
    simpa [Module.finrank_fin_fun] using this
  have hfr_ne0 : Module.finrank ℂ W ≠ 0 := by
    intro h
    exact hbot (Submodule.finrank_eq_zero.mp h)
  have hfr_ne1 : Module.finrank ℂ W ≠ 1 := by
    intro h1
    obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hspan_le : Submodule.span ℂ ({v} : Set (Fin 2 → ℂ)) ≤ W := by
      rw [Submodule.span_le]
      simpa using hvW
    have hfin : Module.finrank ℂ (Submodule.span ℂ ({v} : Set (Fin 2 → ℂ))) = 1 := by
      simpa using finrank_span_singleton (K := ℂ) hv0
    have hWeq : W = Submodule.span ℂ ({v} : Set (Fin 2 → ℂ)) :=
      (Submodule.eq_of_le_of_finrank_eq hspan_le (by rw [hfin, h1])).symm
    have hAv : (sig1_21 (q := q)).mulVec v ∈
        Submodule.span ℂ ({v} : Set (Fin 2 → ℂ)) := hWeq ▸ hW.1 v hvW
    have hBv : (sig2_21 (q := q) s).mulVec v ∈
        Submodule.span ℂ ({v} : Set (Fin 2 → ℂ)) := hWeq ▸ hW.2 v hvW
    obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp hAv
    obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp hBv
    exact sig21_no_common_eigenvector hq5 hq1 hs
      ⟨v, hv0, α, β, hα.symm, hβ.symm⟩
  have hfr : Module.finrank ℂ W = 2 := by omega
  exact Submodule.eq_top_of_finrank_eq (by simpa [Module.finrank_fin_fun] using hfr)

end Qatlib.Papers.ModularFunct00.MainResults.Representation
