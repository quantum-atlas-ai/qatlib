/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Complex.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 2 (telescoping product inequality)

Childs--Gosset--Webb, *Universal computation by multi-particle quantum walk*,
fixed arXiv:1205.3782v2, Appendix H, Proposition 2 / equation (57), p.68.

For unitary operators `U_1, …, U_n` and `V_1, …, V_n` and any `|ψ⟩`:

`‖(∏_{i=n}^{1} U_i − ∏_{i=n}^{1} V_i)|ψ⟩‖ ≤ ∑_{j=1}^{n} ‖(U_j − V_j) ∏_{i=j-1}^{1} U_i |ψ⟩‖`.

We model a unitary operator over a complex (semi)normed space as a
`LinearIsometryEquiv ℂ E E`, and `∏_{i=k}^{1} U_i` as the iterated composition
`orderedProduct U k` that applies `U 0`, then `U 1`, …, then `U (k-1)`.  The proof is the
paper's induction on `n` (its equations (58)–(60)).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UniversalWalk12.MainResults.Product

open scoped BigOperators

variable {E : Type*} [SeminormedAddCommGroup E] [Module ℂ E]

/-- `orderedProduct U k` is the ordered product `U_{k-1} ⋯ U_1 U_0` (apply `U 0` first),
the Lean form of the paper's `∏_{i=k}^{1} U_i` under the index shift `i ↦ i+1`. -/
def orderedProduct (U : ℕ → E ≃ₗᵢ[ℂ] E) : ℕ → E ≃ₗᵢ[ℂ] E
  | 0 => LinearIsometryEquiv.refl ℂ E
  | k + 1 => (orderedProduct U k).trans (U k)

/-- Unfolding of `orderedProduct` at a successor index: `orderedProduct U (k + 1) ψ = U k (orderedProduct U k ψ)`. -/
theorem prefix_succ_apply (U : ℕ → E ≃ₗᵢ[ℂ] E) (k : ℕ) (ψ : E) :
    orderedProduct U (k + 1) ψ = U k (orderedProduct U k ψ) := by
  simp only [orderedProduct, LinearIsometryEquiv.trans_apply]

/-- **Proposition 2** (arXiv:1205.3782v2, eq. (57), p.68), fixed version.

Telescoping bound for the difference of two ordered products of unitary
operators applied to a state, by induction on `n` (paper's eqs. (58)–(60)). -/
theorem source_prop2_telescoping
    (U V : ℕ → E ≃ₗᵢ[ℂ] E) (ψ : E) (n : ℕ) :
    ‖orderedProduct U n ψ - orderedProduct V n ψ‖ ≤
      ∑ j ∈ Finset.range n, ‖U j (orderedProduct U j ψ) - V j (orderedProduct U j ψ)‖ := by
  induction n with
  | zero =>
      simp [orderedProduct]
  | succ n ih =>
      rw [prefix_succ_apply, prefix_succ_apply, Finset.sum_range_succ]
      set a : E := orderedProduct U n ψ
      set b : E := orderedProduct V n ψ
      have hsplit : U n a - V n b = (U n a - V n a) + (V n a - V n b) := by abel
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      have hv : ‖V n a - V n b‖ = ‖a - b‖ := by
        rw [← map_sub, LinearIsometryEquiv.norm_map]
      rw [hv]
      have hstep := add_le_add_left ih (‖U n a - V n a‖)
      linarith

end Qatlib.Papers.UniversalWalk12.MainResults.Product
