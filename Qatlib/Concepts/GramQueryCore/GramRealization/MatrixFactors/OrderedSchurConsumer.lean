/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.GramRealization.MatrixFactors.RationalLDL

/-!
# Ordered Schur complement traces

This module records the complete sequence of leading-pivot Schur reductions of a rational square
matrix in `trace`. Positive semidefiniteness is preserved throughout the sequence, and `consume`
extracts a successful LDL factorization reconstructing the original matrix with nonnegative
diagonal weights; see [Bhatia2007] for matrix positivity background.

## Main statements

* `trace_length`: The ordered Schur trace of a matrix of size `n` contains exactly `n + 1`
  states.

* `trace_posSemidef`: Every rational matrix in the ordered Schur trace is positive semidefinite
  after real coercion if the initial matrix is.

* `consume`: A rational matrix that is positive semidefinite over the reals has a successful
  computed LDL factorization reconstructing the matrix with nonnegative diagonal weights.

## References

* [Bhatia, 2007][Bhatia2007]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.GramQueryCore.GramRealization.OrderedSchurConsumer

open Qatlib.Concepts.GramQueryCore.GramRealization.RationalLDL
open Matrix

/-- A rational square matrix together with its finite dimension. -/
abbrev State := Sigma (fun n : ℕ => Matrix (Fin n) (Fin n) ℚ)

/-- The list of successive leading-pivot Schur complements, including the original rational
matrix and the final matrix of size zero. -/
def trace : (n : ℕ) → Matrix (Fin n) (Fin n) ℚ → List State
  | 0, K => [⟨0, K⟩]
  | n + 1, K => ⟨n + 1, K⟩ :: trace n (RationalLDL.schur K)

/-- The ordered Schur trace of a matrix of size `n` contains exactly `n + 1` states. -/
theorem trace_length (n : ℕ) (K : Matrix (Fin n) (Fin n) ℚ) :
    (trace n K).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [trace, List.length_cons, ih]

/-- The first state in the ordered Schur trace is the original matrix with its dimension. -/
theorem trace_head (n : ℕ) (K : Matrix (Fin n) (Fin n) ℚ) :
    (trace n K).head? = some ⟨n, K⟩ := by
  cases n with
  | zero => rfl
  | succ n => simp only [trace, List.head?_cons]

/-- Every rational matrix in the ordered Schur trace is positive semidefinite after real
coercion if the initial matrix is. -/
theorem trace_posSemidef {n : ℕ} (K : Matrix (Fin n) (Fin n) ℚ)
    (hK : (RationalLDL.realMatrix K).PosSemidef) :
    ∀ s ∈ trace n K, (RationalLDL.realMatrix s.2).PosSemidef := by
  induction n with
  | zero =>
      intro s hs
      simp only [trace, List.mem_singleton] at hs
      subst s
      exact hK
  | succ n ih =>
      intro s hs
      simp only [trace, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact hK
      · exact ih (RationalLDL.schur K) (RationalLDL.schur_psd K hK) s hs

/-- A rational matrix that is positive semidefinite over the reals has a successful computed LDL
factorization reconstructing the matrix with nonnegative diagonal weights. -/
theorem consume {n : ℕ} (K : Matrix (Fin n) (Fin n) ℚ)
    (hK : (RationalLDL.realMatrix K).PosSemidef) :
    ∃ F, RationalLDL.compute n K = some F ∧
      RationalLDL.factor F = K ∧ ∀ i, 0 ≤ F.diagonal i := by
  obtain ⟨F, hF⟩ := RationalLDL.compute_complete n K hK
  exact ⟨F, hF, (RationalLDL.compute_sound n K F hF).1,
    (RationalLDL.compute_sound n K F hF).2⟩

end Qatlib.Concepts.GramQueryCore.GramRealization.OrderedSchurConsumer
