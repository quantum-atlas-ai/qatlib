/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.Channels.CPTP

/-!
# Choi matrices with input-output index order

This module uses indices `(input, output)` for the Choi matrix of a linear map
and relates this convention to the upstream output-input ordering. It transports
complete positivity, trace preservation, and the inverse Choi correspondence
across that permutation, then constructs a channel from a positive Choi matrix
whose output partial trace is the identity.

The correspondence is due to [Choi1975] and [Jamiolkowski1972]; see also
[Nielsen & Chuang, Chapter 8][NielsenChuang2010].
-/

namespace Qatlib.Foundations.ChannelTheory.ChoiKraus

noncomputable section

open scoped ComplexOrder MatrixOrder

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The unnormalized Choi matrix in input-output order; compare
[Choi, completely positive maps][Choi1975]. -/
def matrix (f : MatrixMap A B ℂ) : Matrix (A × B) (A × B) ℂ :=
  fun ij kl => f (Matrix.single ij.1 kl.1 1) ij.2 kl.2

omit [Fintype A] [Fintype B] [DecidableEq B] in

/-- The input-output Choi matrix is obtained from the upstream Choi matrix by swapping both
product indices. -/
theorem matrix_eq_swapped (f : MatrixMap A B ℂ) :
    matrix f = f.choi_matrix.submatrix Prod.swap Prod.swap := rfl

omit [DecidableEq B] in

/-- The input-output Choi matrix is positive semidefinite exactly when the matrix map is
completely positive. -/
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

/-- The output partial trace of the input-output Choi matrix is the identity exactly when the
map is trace preserving. -/
theorem traceRight_eq_one_iff (f : MatrixMap A B ℂ) :
    (matrix f).traceRight = 1 ↔ f.IsTracePreserving := by
  rw [MatrixMap.IsTracePreserving_iff_trace_choi]
  rfl

/-- The matrix map corresponding to an input-output indexed Choi matrix, constructed by swapping
indices before applying the upstream inverse correspondence. -/
def linearMap (J : Matrix (A × B) (A × B) ℂ) : MatrixMap A B ℂ :=
  MatrixMap.of_choi_matrix (J.submatrix Prod.swap Prod.swap)

omit [DecidableEq A] [Fintype B] [DecidableEq B] in

/-- Evaluates the matrix map associated with a Choi matrix by summing its entries against the
input matrix entries. -/
theorem linearMap_apply (J : Matrix (A × B) (A × B) ℂ) (X : Matrix A A ℂ)
    (b b' : B) :
    linearMap J X b b' = ∑ a : A, ∑ a' : A, X a a' * J (a, b) (a', b') := rfl

omit [Fintype B] [DecidableEq B] in

/-- Recovering a linear map from its input-output Choi matrix returns the original map. -/
theorem linearMap_matrix (f : MatrixMap A B ℂ) : linearMap (matrix f) = f := by
  change MatrixMap.of_choi_matrix f.choi_matrix = f
  exact MatrixMap.choi_map_inv f

omit [Fintype B] [DecidableEq B] in

/-- Taking the input-output Choi matrix of the associated linear map returns the original
matrix. -/
theorem matrix_linearMap (J : Matrix (A × B) (A × B) ℂ) :
    matrix (linearMap J) = J := by
  rw [matrix_eq_swapped]
  simp only [linearMap, MatrixMap.map_choi_inv]
  rfl

/-- Construct a trace-preserving completely positive map from a positive Choi
matrix with output partial trace equal to the identity [Choi1975]. -/
def channel (J : Matrix (A × B) (A × B) ℂ)
    (hpos : J.PosSemidef) (htrace : J.traceRight = 1) : CPTPMap A B where
  toLinearMap := linearMap J
  cp := (posSemidef_iff _).mp ((matrix_linearMap J).symm ▸ hpos)
  TP := (traceRight_eq_one_iff _).mp (by rw [matrix_linearMap]; exact htrace)

omit [DecidableEq B] in

/-- The map underlying the channel constructed from a positive Choi matrix with identity output
partial trace is `linearMap J`. -/
theorem channel_map (J : Matrix (A × B) (A × B) ℂ)
    (hpos : J.PosSemidef) (htrace : J.traceRight = 1) :
    (channel J hpos htrace).map = linearMap J := rfl

omit [DecidableEq B] in

/-- Reconstructing a channel from the input-output Choi matrix of its map returns the original
channel. -/
theorem channel_matrix (f : CPTPMap A B) :
    channel (matrix f.map) ((posSemidef_iff _).mpr f.cp)
      ((traceRight_eq_one_iff _).mpr f.TP) = f := by
  apply CPTPMap.ext
  exact linearMap_matrix f.map

end

end Qatlib.Foundations.ChannelTheory.ChoiKraus
