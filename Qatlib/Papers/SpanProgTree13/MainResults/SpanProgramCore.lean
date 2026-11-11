/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
# Span-program semantics used by the tree-detection construction

Guoming Wang, *Span-program-based quantum algorithm for tree detection*,
fixed arXiv:1309.7713v3 (5 Mar 2014).

Section 2.3, Definition 1 (span program) and Definition 2 (witness size), with
Eqs. (1)-(4).

A span program is a target vector together with a family of input vectors. On a
given input only the vectors labelled by the input bits (plus the free ones) are
available, the program accepts exactly when the target vector lies in the span
of the available vectors, and the two witness sizes are the squared norms of
positive and negative witnesses normalised by the projections `Π(x)` and `Π̄(x)`.
-/

import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-!
# SpanProgramCore

Paper-specific span program core constructions and proofs for SpanProgTree13.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset
open Classical

namespace Qatlib.Papers.SpanProgTree13.MainResults

/-- Definition 1 of arXiv:1309.7713v3: a span program over the coordinate type
`I` whose input vectors are indexed by `J`. The set `freeIdx` collects the free
input vectors; every other index is labelled by an input bit, which is why the
set of available indices is supplied separately for each input. -/
structure SpanProgram (I J : Type*) where
  /-- The target vector `|τ⟩` of Eq. (1). -/
  target : I → ℝ
  /-- The input vectors `|v_j⟩` of Eq. (1). -/
  inp : J → I → ℝ
  /-- The free input vectors `I_free`. -/
  freeIdx : Set J

namespace SpanProgram

variable {I J : Type*} [Fintype J]

/-- Eq. (1): `P` accepts the input whose available set is `avail` exactly when the
target vector lies in the span of the available input vectors. -/
def accepts (P : SpanProgram I J) (avail : Set J) : Prop :=
  P.target ∈ Submodule.span ℝ (P.inp '' avail)

/-- Definition 2, positive case: a witness is a coefficient vector `w` supported
on the available indices with `A Π(x) w = |τ⟩`. -/
def IsPositiveWitness (P : SpanProgram I J) (avail : Set J) (w : J → ℝ) : Prop :=
  (∀ j, j ∉ avail → w j = 0) ∧ ∑ j, w j • P.inp j = P.target

/-- Definition 2, positive witness size `‖Π̄(x) w‖²`: only the non-free
available coordinates are counted. -/
def positiveSize (P : SpanProgram I J) (avail : Set J) (w : J → ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => j ∈ avail ∧ j ∉ P.freeIdx), (w j) ^ 2

/-- The positive witness size of `P` on this input is at most `W`. -/
def HasPositiveWitnessOfSizeAtMost (P : SpanProgram I J) (avail : Set J) (W : ℝ) : Prop :=
  ∃ w, P.IsPositiveWitness avail w ∧ P.positiveSize avail w ≤ W

/-- Definition 2, negative case: `w` is orthogonal to every available input
vector and pairs to `1` with the target vector. -/
def IsNegativeWitness (P : SpanProgram I J) [Fintype I] (avail : Set J) (w : I → ℝ) : Prop :=
  (∑ i, w i * P.target i = 1) ∧ (∀ j, j ∈ avail → ∑ i, w i * P.inp j i = 0)

/-- Definition 2, negative witness size `‖w‖²`. -/
def negativeSize [Fintype I] (w : I → ℝ) : ℝ :=
  ∑ i, (w i) ^ 2

/-- The negative witness size of `P` on this input is at most `W`. -/
def HasNegativeWitnessOfSizeAtMost (P : SpanProgram I J) [Fintype I]
    (avail : Set J) (W : ℝ) : Prop :=
  ∃ w, P.IsNegativeWitness avail w ∧ negativeSize w ≤ W

variable {P : SpanProgram I J}

/-- A positive witness certifies acceptance: Eq. (1) holds by exhibiting the
target vector as the available linear combination. -/
theorem accepts_of_positiveWitness {avail : Set J} {W : ℝ}
    (h : P.HasPositiveWitnessOfSizeAtMost avail W) : P.accepts avail := by
  obtain ⟨w, ⟨hw0, hsum⟩, _⟩ := h
  rw [accepts, ← hsum]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases hj : j ∈ avail
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_image_of_mem _ hj))
  · rw [hw0 j hj, zero_smul]
    exact Submodule.zero_mem _

/-- The linear functional `y ↦ ⟨w, y⟩` used to turn a negative witness into a
certificate of rejection. -/
def bracket [Fintype I] (w : I → ℝ) : (I → ℝ) →ₗ[ℝ] ℝ := ∑ i, w i • LinearMap.proj i

/-- The bracket is the coordinate pairing `⟨w, y⟩`. -/
theorem bracket_apply [Fintype I] (w : I → ℝ) (y : I → ℝ) :
    bracket w y = ∑ i, w i * y i := by
  simp [bracket, smul_eq_mul]

omit [Fintype J] in
/-- A negative witness certifies rejection: a linear functional that pairs to `1`
with the target and annihilates every available input vector vanishes on the whole
span, so the target cannot lie in it. -/
theorem not_accepts_of_negativeWitness [Fintype I] {avail : Set J}
    (h : P.HasNegativeWitnessOfSizeAtMost avail (0 : ℝ)) : ¬ P.accepts avail := by
  obtain ⟨w, ⟨htau, horth⟩, _⟩ := h
  intro hacc
  have hspan : ∀ y ∈ Submodule.span ℝ (P.inp '' avail), bracket w y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, hj, rfl⟩ := hy
        rw [bracket_apply, horth j hj]
    | zero => simp [bracket]
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  have h1 : bracket w P.target = 0 := hspan _ hacc
  rw [bracket_apply, htau] at h1
  exact one_ne_zero h1

end SpanProgram

end Qatlib.Papers.SpanProgTree13.MainResults
