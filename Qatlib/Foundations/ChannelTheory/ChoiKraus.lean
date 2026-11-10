/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.Channels.CPTP
set_option warningAsError false

namespace Qatlib.Foundations.ChannelTheory.ChoiKraus

noncomputable section

open scoped ComplexOrder MatrixOrder

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def matrix (f : MatrixMap A B ℂ) : Matrix (A × B) (A × B) ℂ :=
  fun ij kl => f (Matrix.single ij.1 kl.1 1) ij.2 kl.2

omit [Fintype A] [Fintype B] [DecidableEq B] in

theorem matrix_eq_swapped (f : MatrixMap A B ℂ) :
    matrix f = f.choi_matrix.submatrix Prod.swap Prod.swap := rfl

omit [DecidableEq B] in

theorem posSemidef_iff (f : MatrixMap A B ℂ) :
    (matrix f).PosSemidef ↔ f.IsCompletelyPositive := by
  rw [MatrixMap.choi_PSD_iff_CP_map]
  constructor
  · intro h
    have hs := h.submatrix (Prod.swap : B × A → A × B)
    simpa [matrix, MatrixMap.choi_matrix, Matrix.submatrix] using! hs
  · intro h
    exact h.submatrix Prod.swap

omit [DecidableEq B] in

theorem traceRight_eq_one_iff (f : MatrixMap A B ℂ) :
    (matrix f).traceRight = 1 ↔ f.IsTracePreserving := by
  rw [MatrixMap.IsTracePreserving_iff_trace_choi]
  rfl

def linearMap (J : Matrix (A × B) (A × B) ℂ) : MatrixMap A B ℂ :=
  MatrixMap.of_choi_matrix (J.submatrix Prod.swap Prod.swap)

omit [DecidableEq A] [Fintype B] [DecidableEq B] in

theorem linearMap_apply (J : Matrix (A × B) (A × B) ℂ) (X : Matrix A A ℂ)
    (b b' : B) :
    linearMap J X b b' = ∑ a : A, ∑ a' : A, X a a' * J (a, b) (a', b') := rfl

omit [Fintype B] [DecidableEq B] in

theorem linearMap_matrix (f : MatrixMap A B ℂ) : linearMap (matrix f) = f := by
  change MatrixMap.of_choi_matrix f.choi_matrix = f
  exact MatrixMap.choi_map_inv f

omit [Fintype B] [DecidableEq B] in

theorem matrix_linearMap (J : Matrix (A × B) (A × B) ℂ) :
    matrix (linearMap J) = J := by
  rw [matrix_eq_swapped]
  simp only [linearMap, MatrixMap.map_choi_inv]
  rfl

def channel (J : Matrix (A × B) (A × B) ℂ)
    (hpos : J.PosSemidef) (htrace : J.traceRight = 1) : CPTPMap A B where
  toLinearMap := linearMap J
  cp := (posSemidef_iff _).mp ((matrix_linearMap J).symm ▸ hpos)
  TP := (traceRight_eq_one_iff _).mp (by rw [matrix_linearMap]; exact htrace)

omit [DecidableEq B] in

theorem channel_map (J : Matrix (A × B) (A × B) ℂ)
    (hpos : J.PosSemidef) (htrace : J.traceRight = 1) :
    (channel J hpos htrace).map = linearMap J := rfl

omit [DecidableEq B] in

theorem channel_matrix (f : CPTPMap A B) :
    channel (matrix f.map) ((posSemidef_iff _).mpr f.cp)
      ((traceRight_eq_one_iff _).mpr f.TP) = f := by
  apply CPTPMap.ext
  exact linearMap_matrix f.map

end

end Qatlib.Foundations.ChannelTheory.ChoiKraus
