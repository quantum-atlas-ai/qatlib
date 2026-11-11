/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseNetwork13.MainResults.ElectricalFlow.EnergyMinimality

set_option backward.isDefEq.respectTransparency false

/-!
# SparseNetwork13 — Lemma 6: the block pseudo-inverse identifies the electrical flow

Fixed source: Guoming Wang, *Efficient Quantum Algorithms for Analyzing Large Sparse
Electrical Networks*, arXiv:1311.1851 **v10 (24 Jul 2017)**.

**Lemma 6** (§3.2, p.16, Eq. (69)).  For `C_G = B_G W_G^{1/2}` and the electrical flow
`i = W_G B_Gᵀ L_G⁺ i_ext`,

  `[[0, C_G], [C_Gᵀ, 0]]⁺ (i_ext, 0) = (0, W_G^{-1/2} i)`.

The pseudo-inverse solution is characterised (Moore–Penrose) by the two conditions:
(1) it solves the block system `M x = b`; and (2) it is orthogonal to `ker M` (minimal
norm).  We formalise exactly these two conditions for `x = (0, W_G^{-1/2} i)`, without
introducing a general matrix pseudo-inverse:

* `C_G · W_G^{-1/2} i = B_G i = i_ext` (Kirchhoff's current law, Eq. (21));
* for any kernel vector `(u, v) ∈ ker M` (so `C_G v = 0`), one has
  `⟨W_G^{-1/2} i, v⟩ = ∑_e (i_e/√w_e) v_e = 0`, because `i_e/√w_e = √w_e·(B_Gᵀ v_pot)_e`
  and `C_G v = B_G(√w_e v_e) = 0` (the orthogonality computation of §2.3 applied to `v`).

Everything here is proved; the file carries no `sorry`.
-/

set_option autoImplicit false
noncomputable section

open Matrix BigOperators

namespace Qatlib.Papers.SparseNetwork13.MainResults.ElectricalFlow

open Qatlib.Papers.SparseNetwork13.MainResults.Model

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- `W_G^{-1/2} i`, the second block of the pseudo-inverse solution: componentwise
`i(e)/√(w_e)`. -/
def invSqrtFlow (G : ElecNetwork V E) (i : E → ℝ) : E → ℝ :=
  fun e => i e / Real.sqrt (G.w e)

/-- Ohm's law in `W^{-1/2}` form: `i(e)/√(w_e) = √(w_e)·(B_Gᵀ v)(e)` for the flow
`i = W_G B_Gᵀ v` induced by a potential `v`. -/
theorem invSqrtFlow_flowFromPotential (G : ElecNetwork V E) (v : V → ℝ) (e : E) :
    invSqrtFlow G (flowFromPotential G v) e
      = Real.sqrt (G.w e) * (((incident G)ᵀ *ᵥ v) e) := by
  unfold invSqrtFlow
  have hwpos : 0 < Real.sqrt (G.w e) := Real.sqrt_pos.mpr (G.w_pos e)
  have hw2 : Real.sqrt (G.w e) * Real.sqrt (G.w e) = G.w e :=
    Real.mul_self_sqrt (le_of_lt (G.w_pos e))
  rw [flowFromPotential_apply, incident_transpose_mulVec_apply,
    div_eq_iff (ne_of_gt hwpos)]
  have hD : G.w e * (v (G.tail e) - v (G.head e))
      = (Real.sqrt (G.w e) * Real.sqrt (G.w e)) * (v (G.tail e) - v (G.head e)) := by
    conv_lhs => rw [← hw2]
  rw [hD]
  ring

/-- **Lemma 6 (arXiv:1311.1851v10, §3.2, p.16, Eq. (69)).**  With `i = W_G B_Gᵀ v` and
`L_G v = i_ext`, the vector `x = (0, W_G^{-1/2} i)` satisfies the two Moore–Penrose
conditions for `M = [[0, C_G], [C_Gᵀ, 0]]` and `b = (i_ext, 0)`:

1. the first block equation `C_G · W_G^{-1/2} i = i_ext`;
2. orthogonality of `x` to the kernel of `M`: `⟨W_G^{-1/2} i, v⟩ = 0` for every `v` with
   `C_G v = 0`, i.e. `B_G (√w_e v_e) = 0`. -/
theorem lemma6_block_pseudoinverse (G : ElecNetwork V E) (iext : V → ℝ) (v : V → ℝ)
    (hL : laplacian G *ᵥ v = iext) :
    (incident G *ᵥ (fun e =>
        Real.sqrt (G.w e) * (flowFromPotential G v e / Real.sqrt (G.w e))) = iext) ∧
    (∀ wv : E → ℝ, incident G *ᵥ (fun e => Real.sqrt (G.w e) * wv e) = 0 →
      ∑ e, (flowFromPotential G v e / Real.sqrt (G.w e)) * wv e = 0) := by
  refine ⟨?_, ?_⟩
  · -- Block 1: `B (√w · (i/√w)) = B i = i_ext`.
    have hvec : (fun e =>
        Real.sqrt (G.w e) * (flowFromPotential G v e / Real.sqrt (G.w e)))
        = flowFromPotential G v := by
      funext e
      have hwpos : 0 < Real.sqrt (G.w e) := Real.sqrt_pos.mpr (G.w_pos e)
      field_simp
    rw [hvec, incident_mulVec_flow_of_laplacian G v hL]
  · -- Block 2: orthogonality to `ker M`.
    intro wv hwv
    -- `i(e)/√w_e = √w_e · (Bᵀ v)(e)`.
    have hdiv : ∀ e, flowFromPotential G v e / Real.sqrt (G.w e)
        = Real.sqrt (G.w e) * (((incident G)ᵀ *ᵥ v) e) :=
      fun e => invSqrtFlow_flowFromPotential G v e
    calc
      ∑ e, (flowFromPotential G v e / Real.sqrt (G.w e)) * wv e
          = ∑ e, (Real.sqrt (G.w e) * (((incident G)ᵀ *ᵥ v) e)) * wv e := by
            refine Finset.sum_congr rfl (fun e _ => ?_)
            rw [hdiv e]
      _ = ∑ e, (((incident G)ᵀ *ᵥ v) e) * (Real.sqrt (G.w e) * wv e) := by
            refine Finset.sum_congr rfl (fun e _ => ?_)
            ring
      _ = ∑ e, (∑ x, incident G x e * v x) * (Real.sqrt (G.w e) * wv e) := by
            refine Finset.sum_congr rfl (fun e _ => ?_)
            rw [show ((incident G)ᵀ *ᵥ v) e = ∑ x, incident G x e * v x by
              simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]]
      _ = ∑ e, ∑ x, (incident G x e * v x) * (Real.sqrt (G.w e) * wv e) := by
            simp only [Finset.sum_mul]
      _ = ∑ x, ∑ e, (incident G x e * v x) * (Real.sqrt (G.w e) * wv e) := Finset.sum_comm
      _ = ∑ x, v x * (∑ e, incident G x e * (Real.sqrt (G.w e) * wv e)) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun e _ => ?_)
            ring
      _ = ∑ x, v x * (0 : ℝ) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            have hrow : (∑ e, incident G x e * (Real.sqrt (G.w e) * wv e))
                = (incident G *ᵥ (fun e => Real.sqrt (G.w e) * wv e)) x := by
              rw [incident_mulVec_apply]
            rw [hrow, congrFun hwv x]
            simp
      _ = 0 := by simp

end Qatlib.Papers.SparseNetwork13.MainResults.ElectricalFlow
