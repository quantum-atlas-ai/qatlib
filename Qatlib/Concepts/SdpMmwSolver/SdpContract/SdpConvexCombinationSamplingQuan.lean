/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.SdpContract.SdpConvexCombinationSamplingStat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Convex sampling of a dual certificate

`sdpConvexCombinationSampling` decomposes the normalized dual certificate into a convex mixture
of the distinguished-coordinate correction and round contributions. It also proves positivity of
the scale and normalization of the resulting distribution.

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `sdpConvexCombinationSampling`: For positive parameters and nonnegative responses of positive
  round mass, the normalized dual certificate is a probability distribution with the stated
  convex mixture weights and exact scale factorization. See [BrandaoSvore2017].

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.SdpDuality.ConeSeparation

namespace Qatlib.Concepts.SdpMmwSolver.SdpContract
open scoped Classical BigOperators

/-- For positive parameters and nonnegative responses of positive round mass, the normalized
dual certificate is a probability distribution with the stated convex mixture weights and
exact scale factorization. See [BrandaoSvore2017]. -/
theorem sdpConvexCombinationSampling : SdpConvexCombinationSampling := by
  intro m T y j₀ α R δ hT hα hR hδ hy _hround
  (try dsimp only)
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hnonneg (i : Fin m) : 0 ≤ sdpDualCertificate m δ α R j₀ y T i := by
    unfold sdpDualCertificate
    apply add_nonneg
    · split_ifs <;> positivity
    · exact div_nonneg (Finset.sum_nonneg fun t _ => hy t i) hTr.le
  have hscale : 0 < sdpDualSampleScale m δ α R j₀ y T := by
    have he := Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ j₀)
    have hpos : 0 < sdpDualCertificate m δ α R j₀ y T j₀ := by
      unfold sdpDualCertificate
      rw [if_pos rfl]
      exact add_pos_of_pos_of_nonneg (by positivity)
        (div_nonneg (Finset.sum_nonneg fun t _ => hy t j₀) hTr.le)
    exact hpos.trans_le he
  have htotal : sdpDualSampleScale m δ α R j₀ y T = δ * α / (2 * R) +
      (∑ t ∈ Finset.range T, ∑ i, y t i) / (T : ℝ) := by
    unfold sdpDualSampleScale sdpDualCertificate
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_div, Finset.sum_comm]
  refine ⟨hscale, ?_, ?_, ?_⟩
  · intro i
    exact div_nonneg (hnonneg i) hscale.le
  · unfold sdpDualSampleDist
    rw [← Finset.sum_div]
    exact div_self hscale.ne'
  · let w : Fin (T + 1) → ℝ := Fin.cons
      ((δ * α / (2 * R)) / sdpDualSampleScale m δ α R j₀ y T)
      (fun t => (∑ i, y t i) / (T : ℝ) / sdpDualSampleScale m δ α R j₀ y T)
    refine ⟨w, ?_, ?_, rfl, (fun _ => rfl), ?_⟩
    · intro u
      cases u using Fin.cases with
      | zero =>
        dsimp [w]
        exact div_nonneg (by positivity) hscale.le
      | succ t =>
        dsimp [w]
        exact div_nonneg (div_nonneg (Finset.sum_nonneg fun i _ => hy t i) hTr.le) hscale.le
    · dsimp [w]
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← Finset.sum_div, ← Finset.sum_div]
      have hsum : (∑ t : Fin T, ∑ i, y t i) =
          ∑ t ∈ Finset.range T, ∑ i, y t i := by
        exact Fin.sum_univ_eq_sum_range (fun t => ∑ i, y t i) T
      rw [hsum, ← add_div, ← htotal]
      exact div_self hscale.ne'
    · intro i
      unfold sdpDualSampleDist
      rw [mul_comm, div_mul_cancel₀ _ hscale.ne']

end Qatlib.Concepts.SdpMmwSolver.SdpContract
