/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseNetwork13.MainResults.Model.ElectricalNetwork

set_option backward.isDefEq.respectTransparency false

/-!
# SparseNetwork13 — Lemma 2: the electrical flow minimises dissipated power

Fixed source: Guoming Wang, *Efficient Quantum Algorithms for Analyzing Large Sparse
Electrical Networks*, arXiv:1311.1851 **v10 (24 Jul 2017)**.

Lemma 2 (§2.3, p.7).  Let `i = W_G B_Gᵀ L_G⁺ i_ext` be the electrical flow induced
by `i_ext`.  Then any flow `f` consistent with `i_ext` satisfies
`E(f) ≥ E(i)`, where `E(f) = ∑_e f(e)² / w_e` is the dissipated power (Eq. (27)).

The paper's proof (p.7) works through an SVD `C_G = ∑_j s_j u_j v_jᵀ` and shows
`W_G^{-1/2} f = W_G^{-1/2} i + Φ⊥` with `Φ⊥` orthogonal to the electrical flow.
Here we run the same orthogonal-decomposition argument without the SVD: since
`i = W_G B_Gᵀ v` for a potential `v` with `L_G v = i_ext`, we have
`i(e)/w_e = (B_Gᵀ v)(e)`, and the cross term
`∑_e (i(e)/w_e)(f(e) − i(e)) = ∑_x v(x)·(B_G(f − i))(x) = 0`
because both `f` and `i` satisfy `B_G · = i_ext` (Kirchhoff's current law).  Hence
`E(f) = E(i) + ∑_e (f(e) − i(e))²/w_e ≥ E(i)`, the energy analogue of Eq. (31).
-/

set_option autoImplicit false
noncomputable section

open Matrix BigOperators

namespace Qatlib.Papers.SparseNetwork13.MainResults.ElectricalFlow

open Qatlib.Papers.SparseNetwork13.MainResults.Model

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **Lemma 2 (arXiv:1311.1851v10, §2.3, p.7).**  Let `v` be a potential solving
`L_G v = i_ext`, so that `i = W_G B_Gᵀ v` is the electrical flow induced by
`i_ext` (the paper's `v = L_G⁺ i_ext`).  Then every flow `f` consistent with
`i_ext` (i.e. `B_G f = i_ext`) has dissipated power at least that of `i`:
`E(f) ≥ E(i)`. -/
theorem lemma2_energy_minimal (G : ElecNetwork V E) (iext : V → ℝ) (v : V → ℝ)
    (hL : laplacian G *ᵥ v = iext) (f : E → ℝ)
    (hf : incident G *ᵥ f = iext) :
    energy G (flowFromPotential G v) ≤ energy G f := by
  set i := flowFromPotential G v with hi
  -- `i` is consistent with `i_ext` (Kirchhoff's current law).
  have hBi : incident G *ᵥ i = iext := by
    rw [hi, incident_mulVec_flow_of_laplacian G v hL]
  -- Componentwise consistency of `f` and `i`.
  have hBf : ∀ x, ∑ e, incident G x e * f e = iext x := fun x => by
    have h := congrFun hf x
    rwa [incident_mulVec_apply] at h
  have hBi' : ∀ x, ∑ e, incident G x e * i e = iext x := fun x => by
    have h := congrFun hBi x
    rwa [incident_mulVec_apply] at h
  -- The cross term vanishes.
  have hC : ∑ e, (i e / G.w e) * (f e - i e) = 0 := by
    have hiw : ∀ e, i e / G.w e = ((incident G)ᵀ *ᵥ v) e := by
      intro e; rw [hi]; exact flowFromPotential_div_weight G v e
    calc
      ∑ e, (i e / G.w e) * (f e - i e)
          = ∑ e, (∑ x, incident G x e * v x) * (f e - i e) := by
            refine Finset.sum_congr rfl (fun e _ => ?_)
            rw [hiw e]
            simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      _ = ∑ e, ∑ x, incident G x e * v x * (f e - i e) := by
            simp only [Finset.sum_mul]
      _ = ∑ x, ∑ e, incident G x e * v x * (f e - i e) := Finset.sum_comm
      _ = ∑ x, v x * (∑ e, incident G x e * (f e - i e)) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun e _ => ?_)
            ring
      _ = ∑ x, v x * 0 := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            have hzero : ∑ e, incident G x e * (f e - i e) = 0 := by
              rw [Finset.sum_congr rfl (fun e _ => mul_sub (incident G x e) (f e) (i e)),
                Finset.sum_sub_distrib, hBf x, hBi' x]
              ring
            rw [hzero]
      _ = 0 := by simp
  -- Energy split.
  have hD : 0 ≤ ∑ e, (f e - i e) ^ 2 / G.w e :=
    Finset.sum_nonneg (fun e _ => div_nonneg (sq_nonneg _) (le_of_lt (G.w_pos e)))
  have hsplit :
      energy G f = energy G i + 2 * (∑ e, (i e / G.w e) * (f e - i e))
        + ∑ e, (f e - i e) ^ 2 / G.w e := by
    simp only [energy]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    have hw : G.w e ≠ 0 := ne_of_gt (G.w_pos e)
    field_simp
    ring
  rw [show energy G (flowFromPotential G v) = energy G i from by rw [hi]]
  rw [hsplit, hC]
  nlinarith [hD]

end Qatlib.Papers.SparseNetwork13.MainResults.ElectricalFlow
