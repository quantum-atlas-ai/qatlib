/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ApproxSpan15.MainResults.Source.SpanProgramModel
public import Qatlib.Papers.ApproxSpan15.MainResults.Source.AlgorithmModels

@[expose] public section


/-!
# Appendix B — time and space complexity (Lemma B.2)

Ito--Jeffery, *Approximate Span Programs*, arXiv:1507.00432v1, Lemma B.2
(p. 28).

* Lemma B.2 : the `+1`-eigenspace of the reflection
  `2Π_Z − I` restricted to `Y` is `Y ∩ Z` and its `−1`-eigenspace restricted
  to `Y` is `Y ∩ Z⊥`.

Theorems B.1 and B.3 are outside this module's scope: their legacy statements quantify
over the paper-level `SpaceBoundedAlgorithm` interface, which carries no
operational semantics (a record of an estimate, a query count and a space
count), so the stated bounds are trivially satisfiable by the zero-cost
record; the source content (sparse `O(log n)` implementations of `M_Y`,
`R_Z`, `R_Y` and `U′(P^β, x)` from the graph's incidence structure) needs a
quantum time/space model with sparse oracles.  These operational bounds are not asserted by the interface.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace Qatlib.Papers.ApproxSpan15.MainResults.TimeComplexity

open Qatlib.Papers.ApproxSpan15.MainResults

variable {q n : ℕ} {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Fixed arXiv:1507.00432v1, Lemma B.2 (p. 28).**  The `+1`-eigenspace of
the reflection `reflectionAbout Z = 2Π_Z − I` restricted to `Y` is
`Y ∩ Z`, and its `−1`-eigenspace restricted to `Y` is `Y ∩ Z⊥`.

Proof: `reflectionAbout Z v = v` reads `2Π_Z v − v = v`, i.e. `Π_Z v = v`,
which holds exactly on `Z` (`Submodule.starProjection_eq_self_iff`);
similarly `reflectionAbout Z v = −v` reads `Π_Z v = 0`, which holds exactly
on `Zᗮ`.  The ambient restriction to `Y` is as in the source. -/
theorem source_lemma_B_2 (Y Z : Submodule ℝ H) :
    (∀ v : H, v ∈ Y → (SpanProgram.reflectionAbout Z v = v ↔ v ∈ Z)) ∧
      ∀ v : H, v ∈ Y → (SpanProgram.reflectionAbout Z v = -v ↔ v ∈ Zᗮ) := by
  constructor
  · intro v _
    show (2 : ℝ) • Z.starProjection v - v = v ↔ v ∈ Z
    have hp : Z.starProjection v = v ↔ v ∈ Z := Submodule.starProjection_eq_self_iff
    constructor
    · intro h
      have e1 : (2 : ℝ) • Z.starProjection v - v + v = v + v := by rw [h]
      rw [sub_add_cancel] at e1
      have e2 : (2 : ℝ) • Z.starProjection v = (2 : ℝ) • v :=
        e1.trans (two_smul ℝ v).symm
      exact hp.mp (smul_right_injective H (by norm_num : (2 : ℝ) ≠ 0) e2)
    · intro hv
      show (2 : ℝ) • Z.starProjection v - v = v
      rw [hp.mpr hv, two_smul]
      abel
  · intro v _
    show (2 : ℝ) • Z.starProjection v - v = -v ↔ v ∈ Zᗮ
    have hp : Z.starProjection v = 0 ↔ v ∈ Zᗮ :=
      Submodule.starProjection_apply_eq_zero_iff Z
    constructor
    · intro h
      have e1 : (2 : ℝ) • Z.starProjection v - v + v = -v + v := by rw [h]
      rw [sub_add_cancel, neg_add_cancel] at e1
      exact hp.mp ((smul_eq_zero.mp e1).resolve_left two_ne_zero)
    · intro hv
      show (2 : ℝ) • Z.starProjection v - v = -v
      rw [hp.mpr hv, smul_zero, zero_sub]

end Qatlib.Papers.ApproxSpan15.MainResults.TimeComplexity
