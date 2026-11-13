/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseNetwork13.MainResults.ElectricalFlow.KernelFlowCharacterization

set_option backward.isDefEq.respectTransparency false

/-!
# Projection onto the Modified Network Kernel and the Electrical Flow State

This module formalizes Lemma 9 (Section 4.1, Eq. (112)) of Wang on quantum
algorithms for analyzing large sparse electrical networks. Given the electrical
flow `i = W_G B_Gᵀ v` induced by potential `v` solving `L_G v = i_ext`, any
kernel vector `Ψ = β₀ |e₀⟩ + ∑_e β_e |e⟩` of the modified incidence operator
`C_{G'}` that is orthogonal to the flow state
`|Φ⟩ = (1 / √(2 λ)) |e₀⟩ + ∑_e (i(e) / √(w_e)) |e⟩` has vanishing `|e₀⟩`
amplitude (`β₀ = 0`), establishing that the orthogonal projection of `|e₀⟩`
onto `ker(C_{G'})` lies along `|Φ⟩`.

## Main statements

* `lemma9_projection`: any vector `(beta0, be)` in the kernel of
  `modifiedCAction G lam iext` orthogonal to the normalized electrical flow
  state satisfies `beta0 = 0`.

## References

* [Wang, 2017][Wang2017Networks], Section 4.1, Lemma 9, Eq. (112).
-/

set_option autoImplicit false
noncomputable section

open Matrix BigOperators

namespace Qatlib.Papers.SparseNetwork13.MainResults.ElectricalFlow

open Qatlib.Papers.SparseNetwork13.MainResults.Model

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **Lemma 9** (Eq. (112)): for the electrical flow `flowFromPotential G v`
associated with potential `v` satisfying `laplacian G *ᵥ v = iext` and
parameter `lam > 0`, any kernel vector `(beta0, be)` of
`modifiedCAction G lam iext` that is orthogonal to the flow state
`(1 / √(2 * lam)) |e₀⟩ + ∑_e (flowFromPotential G v e / √(G.w e)) |e⟩`
satisfies `beta0 = 0`. -/
theorem lemma9_projection (G : ElecNetwork V E) (lam : ℝ) (iext : V → ℝ) (v : V → ℝ)
    (hlam : 0 < lam) (hL : laplacian G *ᵥ v = iext) :
    ∀ (beta0 : ℝ) (be : E → ℝ),
      (∀ u, modifiedCAction G lam iext beta0 be u = 0) →
      ((1 / Real.sqrt (2 * lam)) * beta0
        + ∑ e, be e * (flowFromPotential G v e / Real.sqrt (G.w e))) = 0 →
      beta0 = 0 := by
  intro beta0 be hker hortho
  have hflow (e : E) : flowFromPotential G v e / Real.sqrt (G.w e) =
      Real.sqrt (G.w e) * ((incident G)ᵀ *ᵥ v) e := by
    have hs : Real.sqrt (G.w e) ≠ 0 := (Real.sqrt_pos_of_pos (G.w_pos e)).ne'
    simp only [flowFromPotential, weightMatrix, Matrix.mulVec_diagonal]
    rw [div_eq_iff hs]
    calc
      _ = (Real.sqrt (G.w e) * Real.sqrt (G.w e)) * ((incident G)ᵀ *ᵥ v) e := by
        rw [Real.mul_self_sqrt (G.w_pos e).le]
      _ = _ := by ring
  have henergy : v ⬝ᵥ iext = ∑ e, G.w e * (((incident G)ᵀ *ᵥ v) e) ^ 2 := by
    rw [← hL, laplacian, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    simp only [weightMatrix, dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun e _ => by ring
  have henergy_nonneg : 0 ≤ v ⬝ᵥ iext := by
    rw [henergy]
    exact Finset.sum_nonneg fun e _ => mul_nonneg (G.w_pos e).le (sq_nonneg _)
  have hkernel := (lemma8_kernel_characterization G lam iext hlam beta0 be).mp hker
  have hpair : (∑ e, be e * (flowFromPotential G v e / Real.sqrt (G.w e))) =
      Real.sqrt (2 * lam) * beta0 * (v ⬝ᵥ iext) := by
    calc
      _ = v ⬝ᵥ (incident G *ᵥ (fun e => Real.sqrt (G.w e) * be e)) := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
        simp only [dotProduct, hflow]
        exact Finset.sum_congr rfl fun e _ => by ring
      _ = Real.sqrt (2 * lam) * beta0 * (v ⬝ᵥ iext) := by
        rw [hkernel]
        simp only [dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by ring
  rw [hpair] at hortho
  have hs : 0 < Real.sqrt (2 * lam) := Real.sqrt_pos_of_pos (by positivity)
  have hpos : 0 < 1 / Real.sqrt (2 * lam) + Real.sqrt (2 * lam) * (v ⬝ᵥ iext) :=
    add_pos_of_pos_of_nonneg (one_div_pos.mpr hs) (mul_nonneg hs.le henergy_nonneg)
  have hzero : beta0 *
      (1 / Real.sqrt (2 * lam) + Real.sqrt (2 * lam) * (v ⬝ᵥ iext)) = 0 := by
    nlinarith [hortho]
  exact (mul_eq_zero.mp hzero).resolve_right hpos.ne'

end Qatlib.Papers.SparseNetwork13.MainResults.ElectricalFlow
