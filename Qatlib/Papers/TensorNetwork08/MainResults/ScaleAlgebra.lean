/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Algebra of tensor-network scales and Potts weights

Collects the finite-product algebra behind the general-model, difference-model, and homogeneous
Potts scale expressions in [AradLandau2010]. Vertex factors taking values `√q` or one reduce to
a power determined by the number of `√q` factors.

The definition `pottsW` and its sum and maximum identities yield the Potts factors, with
separate simplifications for positive and negative `β * J`.

## Main statements

* `scale_lattice`: simplifies the general product when exactly two vertex factors equal `√q`.
* `scale_difference`: absorbs the color factor into the square-root power.
* `potts_sum`: evaluates the sum of homogeneous Potts weights.
* `potts_max`: identifies the maximum for at least two colors.

## References

* [Arad and Landau, 2010][AradLandau2010]
-/

set_option autoImplicit false

noncomputable section

open Finset BigOperators
open Classical

namespace Qatlib.Papers.TensorNetwork08.MainResults.ScaleAlgebra

/-- If every vertex factor equals `√q` or one, their product is `√q` raised to the number of
factors equal to `√q`. See [AradLandau2010]. -/
theorem prod_vertex_norms (q : ℕ) {V : Type*} [Fintype V]
    (nv : V → ℝ) (hv : ∀ v, nv v = Real.sqrt q ∨ nv v = 1) :
    ∏ v, nv v
      = (Real.sqrt q) ^ ((univ.filter (fun v => nv v = Real.sqrt q)).card) := by
  have hpt : ∀ v, nv v = if nv v = Real.sqrt q then Real.sqrt q else 1 := by
    intro v
    rcases hv v with h | h
    · rw [h]; simp
    · rw [h]; simp
  calc ∏ v, nv v
      = ∏ v, (if nv v = Real.sqrt q then Real.sqrt q else 1) := by
        exact Finset.prod_congr rfl (fun v _ => hpt v)
    _ = (Real.sqrt q) ^ ((univ.filter (fun v => nv v = Real.sqrt q)).card) := by
        rw [← Finset.prod_filter_mul_prod_filter_not (s := (univ : Finset V))
          (p := fun v => nv v = Real.sqrt q) (f := fun v => if nv v = Real.sqrt q then Real.sqrt q else 1)]
        have h1 : (univ.filter (fun v => ¬ nv v = Real.sqrt q)).prod
            (fun v => if nv v = Real.sqrt q then Real.sqrt q else 1) = 1 := by
          apply Finset.prod_eq_one
          intro v hv'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv'
          simp [hv']
        have h2 : (univ.filter (fun v => nv v = Real.sqrt q)).prod
            (fun v => if nv v = Real.sqrt q then Real.sqrt q else 1)
            = (Real.sqrt q) ^ ((univ.filter (fun v => nv v = Real.sqrt q)).card) := by
          rw [Finset.prod_congr rfl (fun v hv' => ?_), Finset.prod_const]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv'
          simp [hv']
        rw [h1, h2, mul_one]

/-- Rewrites the vertex-norm product in the general scale as a power of `√q`, leaving the
edge-norm product unchanged. -/
theorem scale_general (q : ℕ) {V E : Type*} [Fintype V] [Fintype E]
    (nv : V → ℝ) (ne : E → ℝ)
    (hv : ∀ v, nv v = Real.sqrt q ∨ nv v = 1) :
    (∏ v, nv v) * (∏ e, ne e)
      = (Real.sqrt q) ^ ((univ.filter (fun v => nv v = Real.sqrt q)).card)
          * ∏ e, ne e := by
  rw [prod_vertex_norms q nv hv]

/-- If exactly two vertex factors equal `√q` and all others equal one, the total scale is `q`
times the edge-factor product. See [AradLandau2010]. -/
theorem scale_lattice (q : ℕ) (hq : 0 ≤ (q : ℝ)) {V E : Type*} [Fintype V] [Fintype E]
    (nv : V → ℝ) (ne : E → ℝ)
    (hv : ∀ v, nv v = Real.sqrt q ∨ nv v = 1)
    (hb : (univ.filter (fun v => nv v = Real.sqrt q)).card = 2) :
    (∏ v, nv v) * (∏ e, ne e) = (q : ℝ) * ∏ e, ne e := by
  rw [scale_general q nv ne hv, hb]
  have hsq : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt hq
  rw [hsq]

/-- For `nV ≥ 1`, multiplying `(√q)^(nV - 1)` by `q` changes the exponent to `nV + 1`, including
the common factor `P`. See [AradLandau2010]. -/
theorem scale_difference (q nV : ℕ) (P : ℝ) (hq : 0 ≤ (q : ℝ)) (hn : 1 ≤ nV) :
    (Real.sqrt (q : ℝ)) ^ (nV - 1) * (q : ℝ) * P
      = (Real.sqrt (q : ℝ)) ^ (nV + 1) * P := by
  have hsq : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt hq
  have harith : nV - 1 + 2 = nV + 1 := by omega
  calc (Real.sqrt (q : ℝ)) ^ (nV - 1) * (q : ℝ) * P
      = (Real.sqrt (q : ℝ)) ^ (nV - 1) * (Real.sqrt (q : ℝ)) ^ 2 * P := by rw [hsq]
    _ = (Real.sqrt (q : ℝ)) ^ (nV - 1 + 2) * P := by
        rw [← pow_add]
    _ = (Real.sqrt (q : ℝ)) ^ (nV + 1) * P := by rw [harith]

/-- The homogeneous Potts edge weight `exp (β * J)` at label zero and one at every other label. -/
def pottsW (q : ℕ) [NeZero q] (β J : ℝ) (j : Fin q) : ℝ :=
  if j = 0 then Real.exp (β * J) else 1

/-- For nonzero `q`, the sum of the `q` Potts edge weights is `exp (β * J) + q - 1`. See
[AradLandau2010]. -/
theorem potts_sum (q : ℕ) [NeZero q] (β J : ℝ) :
    ∑ j : Fin q, pottsW q β J j = Real.exp (β * J) + ((q : ℝ) - 1) := by
  have h0 : (0 : Fin q) ∈ (univ : Finset (Fin q)) := Finset.mem_univ _
  have hsingle : (∑ j : Fin q, (if j = 0 then (Real.exp (β * J) - 1) else 0))
      = Real.exp (β * J) - 1 := by
    rw [Finset.sum_ite_eq' (univ : Finset (Fin q)) 0 (fun _ => Real.exp (β * J) - 1)]
    simp
  have hconst : (∑ _j : Fin q, (1 : ℝ)) = (q : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
  calc ∑ j : Fin q, pottsW q β J j
      = ∑ j : Fin q, (1 + (if j = 0 then (Real.exp (β * J) - 1) else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        unfold pottsW
        by_cases hj : j = 0
        · simp [hj]
        · simp [hj]
    _ = (∑ _j : Fin q, (1 : ℝ))
          + ∑ j : Fin q, (if j = 0 then (Real.exp (β * J) - 1) else 0) := by
        rw [Finset.sum_add_distrib]
    _ = (q : ℝ) + (Real.exp (β * J) - 1) := by rw [hconst, hsingle]
    _ = Real.exp (β * J) + ((q : ℝ) - 1) := by ring

/-- For `q ≥ 2`, every Potts edge weight is at most `max (exp (β * J)) 1`, and some label
attains this value. See [AradLandau2010]. -/
theorem potts_max (q : ℕ) [NeZero q] (hq : 2 ≤ q) (β J : ℝ) :
    (∀ j : Fin q, pottsW q β J j ≤ max (Real.exp (β * J)) 1)
      ∧ (∃ j : Fin q, pottsW q β J j = max (Real.exp (β * J)) 1) := by
  refine ⟨?_, ?_⟩
  · intro j
    unfold pottsW
    split_ifs with hj
    · exact le_max_left _ _
    · exact le_max_right _ _
  · rcases le_total (Real.exp (β * J)) 1 with h | h
    · refine ⟨⟨1, by omega⟩, ?_⟩
      unfold pottsW
      have hv : (⟨1, by omega⟩ : Fin q) ≠ 0 := by
        intro hh
        have hv1 := congrArg Fin.val hh
        simp at hv1
      rw [if_neg hv, max_eq_right h]
    · refine ⟨0, ?_⟩
      unfold pottsW
      rw [if_pos rfl, max_eq_left h]

/-- When `β * J > 0`, the maximum of `exp (β * J)` and one is the exponential. -/
theorem potts_ferro (q : ℕ) [NeZero q] (β J : ℝ) (hJ : 0 < β * J) :
    (max (Real.exp (β * J)) 1) = Real.exp (β * J) := by
  apply max_eq_left
  exact le_of_lt (Real.one_lt_exp_iff.mpr hJ)

/-- When `β * J < 0`, the maximum of `exp (β * J)` and one is one. -/
theorem potts_antiferro (q : ℕ) [NeZero q] (β J : ℝ) (hJ : β * J < 0) :
    (max (Real.exp (β * J)) 1) = 1 := by
  apply max_eq_right
  exact le_of_lt (Real.exp_lt_one_iff.mpr hJ)

/-- For positive `β * J`, replaces the maximum factor in the Potts scale by `exp (β * J)`. See
[AradLandau2010]. -/
theorem potts_scale_ferro (q nV nE : ℕ) [NeZero q] (β J : ℝ) (hJ : 0 < β * J) :
    (q : ℝ) * (Real.exp (β * J) + ((q : ℝ) - 1)) ^ (nV - 1)
        * (max (Real.exp (β * J)) 1) ^ (nE - nV + 1)
      = (q : ℝ) * (Real.exp (β * J) + ((q : ℝ) - 1)) ^ (nV - 1)
        * (Real.exp (β * J)) ^ (nE - nV + 1) := by
  rw [potts_ferro q β J hJ]

/-- For negative `β * J`, the maximum factor in the Potts scale is one and its power drops out.
See [AradLandau2010]. -/
theorem potts_scale_antiferro (q nV nE : ℕ) [NeZero q] (β J : ℝ)
    (hJ : β * J < 0) :
    (q : ℝ) * (Real.exp (β * J) + ((q : ℝ) - 1)) ^ (nV - 1)
        * (max (Real.exp (β * J)) 1) ^ (nE - nV + 1)
      = (q : ℝ) * (Real.exp (β * J) + ((q : ℝ) - 1)) ^ (nV - 1) := by
  rw [potts_antiferro q β J hJ, one_pow, mul_one]

end Qatlib.Papers.TensorNetwork08.MainResults.ScaleAlgebra
