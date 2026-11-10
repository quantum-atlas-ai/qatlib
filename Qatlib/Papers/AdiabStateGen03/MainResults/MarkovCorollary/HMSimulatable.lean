/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Qatlib.Papers.AdiabStateGen03.MainResults.MarkovCorollary.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.MarkovCorollary

open Qatlib.Papers.AdiabStateGen03.MainResults
open WithLp

variable {n : ℕ}

def SparseHamiltonianLemma (n : ℕ) : Prop :=
  ∀ (H : Ham n) (D : ℕ), RowSparse H D → RowComputable H →
    PolyBoundedAt n ‖H‖ → Simulatable H

theorem hm_simulatable (M : MC n) (π : Dim n → ℝ) (h : StronglySamplable M π)
    (hrow : RowComputable (HM M π)) (hnorm : PolyBoundedAt n ‖HM M π‖)
    (hlemma : SparseHamiltonianLemma n) : Simulatable (HM M π) :=
  hlemma (HM M π) (h.D + 1) (hm_rowSparse M π h) hrow hnorm

theorem hm_rayleigh_sqrt (M : MC n) (π : Dim n → ℝ) (h : StronglySamplable M π) :
    rayleigh (HM M π) (ketOfDist π) = 0 := by
  unfold rayleigh
  have hzero : toOp (HM M π) (ketOfDist π) = 0 := by
    have hk : ketOfDist π = toLp 2 (fun i : Dim n => (Real.sqrt (π i) : ℂ)) := rfl
    rw [hk]
    unfold toOp
    rw [Matrix.toEuclideanCLM_toLp]
    rw [show (HM M π) *ᵥ (fun i : Dim n => (Real.sqrt (π i) : ℂ)) = 0 from
      hm_mulVec_sqrt M π h]
    simp
  rw [hzero, inner_zero_right]
  simp

theorem hm_ground_rayleigh (M : MC n) (π : Dim n → ℝ) (h : StronglySamplable M π) :
    (⟪ketOfDist π, toOp (HM M π) (ketOfDist π)⟫_ℂ).re = 0 :=
  hm_rayleigh_sqrt M π h

end Qatlib.Papers.AdiabStateGen03.MainResults.MarkovCorollary
