/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3: stability of the smallest eigenvalue

Source: arXiv:1605.03590v2, Appendix D, Lemma 3 (p.13, Eqs. (D1)--(D5)).
If `A` and `B` are Hermitian matrices on a finite-dimensional space with
`‖A - B‖₂ ≤ ε`, then their smallest eigenvalues differ by at most `ε`.

The paper proves this variationally (Rayleigh quotient plus the operator-norm
bound).  Here we reuse the frozen ordered Weyl bound
`ordered_hermitian_weyl_and_hoffman_wielandt`: the ordered `eigenvalues₀` are
decreasing, so the last index carries the smallest eigenvalue of each operator,
and the frozen Weyl inequality applies at that common index.

Boundary: finite-dimensional complex matrices, L2 operator norm, and `Nonempty`
index type so that a smallest eigenvalue exists.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder BigOperators

namespace Qatlib.Papers.ReactionMech16.MainResults.Source

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

/-- arXiv:1605.03590v2, Lemma 3 (p.13): for Hermitian `A B` on a finite-dimensional
space, the smallest eigenvalues of `A` and `B` satisfy `|E_A - E_B| ≤ ‖A - B‖₂`.
The index of the smallest eigenvalue is the last position of the decreasing
ordered spectrum; the conclusion is stated both as the `IsLeast` characterization
("`E_A` and `E_B` are the smallest eigenvalues") and as the norm bound. -/
theorem lemma3_smallest_eigenvalue_stability
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    let i : Fin (Fintype.card I) :=
      ⟨Fintype.card I - 1, by
        have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr inferInstance
        omega⟩
    IsLeast (Set.range hA.eigenvalues₀) (hA.eigenvalues₀ i) ∧
    IsLeast (Set.range hB.eigenvalues₀) (hB.eigenvalues₀ i) ∧
    |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ ‖A - B‖ := by
  intro i
  have hle : ∀ j : Fin (Fintype.card I), j ≤ i := by
    intro j
    simp only [Fin.le_def, i]
    have := j.isLt
    omega
  have hlastA : IsLeast (Set.range hA.eigenvalues₀) (hA.eigenvalues₀ i) := by
    refine ⟨⟨i, rfl⟩, ?_⟩
    rintro y ⟨j, rfl⟩
    exact hA.eigenvalues₀_antitone (hle j)
  have hlastB : IsLeast (Set.range hB.eigenvalues₀) (hB.eigenvalues₀ i) := by
    refine ⟨⟨i, rfl⟩, ?_⟩
    rintro y ⟨j, rfl⟩
    exact hB.eigenvalues₀_antitone (hle j)
  have hweyl :=
    (ordered_hermitian_weyl_and_hoffman_wielandt I A B hA hB).1 i
  exact ⟨hlastA, hlastB, hweyl⟩

/-- arXiv:1605.03590v2, Lemma 3 (p.13), numerical form: under the hypothesis
`‖A - B‖₂ ≤ ε` from the paper, the smallest eigenvalues differ by at most `ε`. -/
theorem lemma3_smallest_eigenvalue_gap_le
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (ε : ℝ) (hε : ‖A - B‖ ≤ ε) :
    let i : Fin (Fintype.card I) :=
      ⟨Fintype.card I - 1, by
        have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr inferInstance
        omega⟩
    |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ ε := by
  intro i
  exact le_trans (lemma3_smallest_eigenvalue_stability A B hA hB).2.2 hε

end Qatlib.Papers.ReactionMech16.MainResults.Source
