/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Value

/-!
# Filter absorption and evaluation adversary bounds

This module shows that a Schur factor fixing the target matrix can be absorbed into all filters
without increasing the certificate budget or filtered gamma-two value. It also proves an
adversary lower bound for evaluation-filtered gamma-two, in the comparison framework of
[LeeEtAl2011].

## Main statements

* `filteredGamma2_le_of_filter_absorb`: absorption gives a monotonicity inequality.
* `adversary_le_filteredGamma2_evalRelaxed`: the norm of a feasible adversary is bounded by the
  relaxed evaluation-filtered value.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GramQueryCore.GammaDuality

namespace Qatlib.Concepts.GramQueryCore.FilteredCert
open Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator
set_option autoImplicit false

/-- If the Schur product of `A` with `B` equals `A`, multiplying every filter by `B` preserves
any certificate and its budget. This is a filter-absorption step in the comparison
associated with [Lee et al., Theorem 3.4][LeeEtAl2011]. -/
theorem gramFilteredCert_of_filter_absorb {X : Type} {n : ℕ} {A : Matrix X X ℂ}
    {Z : Fin n → Matrix X X ℂ} {B : Matrix X X ℂ} {W : ℝ}
    (h : gramFilteredCert A Z W) (hidem : ∀ x y, A x y * B x y = A x y) :
    gramFilteredCert A (fun j x y => Z j x y * B x y) W := by
  obtain ⟨Q,hQ,u,v,hu,hv,hrep⟩ := h
  refine ⟨Q,hQ,u,v,hu,hv,?_⟩
  intro x y
  calc
    A x y = A x y * B x y := (hidem x y).symm
    _ = (∑ j, Z j x y * (star (u j x) ⬝ᵥ v j y))*B x y := by rw [hrep]
    _ = ∑ j, (Z j x y * B x y)*(star (u j x) ⬝ᵥ v j y) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- If the Schur product of `A` with `B` equals `A`, multiplying every filter by `B` cannot
increase `filteredGamma2 A`. See [Lee et al., Theorem 3.4][LeeEtAl2011]. -/
theorem filteredGamma2_le_of_filter_absorb {X : Type} {n : ℕ} {A : Matrix X X ℂ}
    {Z : Fin n → Matrix X X ℂ} {B : Matrix X X ℂ}
    (hidem : ∀ x y, A x y * B x y = A x y) :
    filteredGamma2 A (fun j x y => Z j x y * B x y) ≤ filteredGamma2 A Z := by
  unfold filteredGamma2
  refine le_sInf fun W hW => ?_
  obtain ⟨w,rfl,hcert⟩ := hW
  exact sInf_le ⟨w,rfl,gramFilteredCert_of_filter_absorb hcert hidem⟩

/-- A matrix vanishing on equal-output pairs and satisfying the coordinate-filter norm
constraints has norm bounded by the evaluation-filtered gamma-two value. See [Lee et al.,
Theorem 3.4][LeeEtAl2011]. -/
theorem adversary_le_filteredGamma2_evalRelaxed {X : Type} [Fintype X] [DecidableEq X]
    {E : Type} [Fintype E] [DecidableEq E] {n : ℕ} (input : X → Fin n → Bool) (f : X → E)
    (Γ : Matrix X X ℂ) (hzero : ∀ x y, f x = f y → Γ x y = 0)
    (hfeas : ∀ j, ‖gramFilterDelta input j ⊙ Γ‖ ≤ 1) :
    ENNReal.ofReal ‖Γ‖ ≤ filteredGamma2 (gramFunctionEvaluationMatrix f)
      (fun j x y => gramFilterDelta input j x y * gramFunctionEvaluationMatrix f x y) := by
  have he : gramFunctionEvaluationMatrix f ⊙ Γ = Γ := by
    ext x y
    by_cases hxy : f x = f y
    · simp [gramFunctionEvaluationMatrix, hxy, hzero x y hxy]
    · simp [gramFunctionEvaluationMatrix, hxy]
  have hb := filteredGamma2_dual_ge (gramFunctionEvaluationMatrix f)
    (fun j x y => gramFilterDelta input j x y * gramFunctionEvaluationMatrix f x y) Γ
    (fun j => by
      change ‖(gramFilterDelta input j ⊙ gramFunctionEvaluationMatrix f) ⊙ Γ‖ ≤ 1
      rw [Matrix.hadamard_assoc, he]
      exact hfeas j)
  rwa [he] at hb
end Qatlib.Concepts.GramQueryCore.FilteredCert
