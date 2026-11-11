/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Multiplicity accounting for saved replacements (Lemma C.1)

Shen--Wu--Yuan--Zhang, fixed arXiv:2610.05362v1, Lemma C.1, page 55.
Rotation type `ℓ` appears `n_ℓ` times in the expanded circuit, including inverse
occurrences.  One saved replacement of type `ℓ` has operator-norm error `η_ℓ`
and gate length `s_ℓ`.  The expanded circuit then satisfies

`‖Ĉ - C‖ ≤ ∑_ℓ n_ℓ η_ℓ`,   `G = ∑_ℓ n_ℓ s_ℓ + G_exact`.

The source proof expands the acyclic description in chronological order and
uses that a saved replacement and its adjoint have the same norm error and the
same gate length; the operator-norm bound is then the usual telescoping product
bound, and the gate count is direct counting.

We formalize both halves.  The operator-norm half is stated for an arbitrary
chronological list of occurrence types, with unitaries `C ℓ` and their saved
replacements `A ℓ`.  The gate count half is pure list arithmetic; `n_ℓ` is
represented by `List.count`.
-/

open scoped BigOperators

namespace Qatlib.Papers.ShallowLind26.ShallowSim.MultiplicityAccounting

set_option autoImplicit false

variable {σ : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Chronological product of the saved replacements of a list of occurrences. -/
noncomputable def actualProd (A : σ → E →L[ℂ] E) : List σ → E →L[ℂ] E
  | [] => 1
  | l :: ls => (actualProd A ls).comp (A l)

/-- Chronological product of the ideal rotations of a list of occurrences. -/
noncomputable def idealProd (C : σ → E →L[ℂ] E) : List σ → E →L[ℂ] E
  | [] => 1
  | l :: ls => (idealProd C ls).comp (C l)

/-- A chronological product of norm-preserving operators preserves norms. -/
theorem norm_actualProd (A : σ → E →L[ℂ] E)
    (hA : ∀ (l : σ) (v : E), ‖A l v‖ = ‖v‖) :
    ∀ (L : List σ) (v : E), ‖actualProd A L v‖ = ‖v‖ := by
  intro L
  induction L with
  | nil => intro v; simp [actualProd]
  | cons l ls ih =>
      intro v
      rw [actualProd, ContinuousLinearMap.comp_apply, ih, hA]

/-- A chronological product of ideal norm-preserving rotations preserves norms. -/
theorem norm_idealProd (C : σ → E →L[ℂ] E)
    (hC : ∀ (l : σ) (v : E), ‖C l v‖ = ‖v‖) :
    ∀ (L : List σ) (v : E), ‖idealProd C L v‖ = ‖v‖ := by
  intro L
  induction L with
  | nil => intro v; simp [idealProd]
  | cons l ls ih =>
      intro v
      rw [idealProd, ContinuousLinearMap.comp_apply, ih, hC]

/-- **Lemma C.1, operator-norm half.**  If every saved replacement of type `ℓ`
has one-step error at most `η_ℓ` and all ideal rotations and replacements
preserve norms, then the expanded chronological circuit differs from the ideal
one by at most the total of the per-occurrence errors. -/
theorem expanded_error_le (A C : σ → E →L[ℂ] E) (η : σ → ℝ)
    (hA : ∀ (l : σ) (v : E), ‖A l v‖ = ‖v‖)
    (hC : ∀ (l : σ) (v : E), ‖C l v‖ = ‖v‖)
    (herror : ∀ (l : σ) (v : E), ‖A l v - C l v‖ ≤ η l * ‖v‖) :
    ∀ (L : List σ) (v : E),
      ‖actualProd A L v - idealProd C L v‖ ≤ (L.map η).sum * ‖v‖ := by
  intro L
  induction L with
  | nil => intro v; simp [actualProd, idealProd]
  | cons l ls ih =>
      intro v
      have hsplit : actualProd A (l :: ls) v - idealProd C (l :: ls) v
          = (actualProd A ls (A l v) - actualProd A ls (C l v))
            + (actualProd A ls (C l v) - idealProd C ls (C l v)) := by
        rw [actualProd, idealProd]
        simp only [ContinuousLinearMap.comp_apply]
        abel
      have hfirst : ‖actualProd A ls (A l v) - actualProd A ls (C l v)‖
          ≤ η l * ‖v‖ := by
        have hnorm : ‖actualProd A ls (A l v) - actualProd A ls (C l v)‖
            = ‖A l v - C l v‖ := by
          rw [← map_sub, norm_actualProd A hA]
        exact hnorm.le.trans (herror l v)
      have hsecond : ‖actualProd A ls (C l v) - idealProd C ls (C l v)‖
          ≤ (ls.map η).sum * ‖v‖ := by
        calc ‖actualProd A ls (C l v) - idealProd C ls (C l v)‖
            ≤ (ls.map η).sum * ‖C l v‖ := ih (C l v)
          _ = (ls.map η).sum * ‖v‖ := by rw [hC]
      rw [hsplit]
      calc ‖(actualProd A ls (A l v) - actualProd A ls (C l v))
            + (actualProd A ls (C l v) - idealProd C ls (C l v))‖
          ≤ ‖actualProd A ls (A l v) - actualProd A ls (C l v)‖
            + ‖actualProd A ls (C l v) - idealProd C ls (C l v)‖ := norm_add_le _ _
        _ ≤ η l * ‖v‖ + (ls.map η).sum * ‖v‖ := add_le_add hfirst hsecond
        _ = ((l :: ls).map η).sum * ‖v‖ := by
              rw [List.map_cons, List.sum_cons]
              ring

/-- **Lemma C.1, gate-count half.**  A chronological occurrence list has exactly
`∑_ℓ n_ℓ s_ℓ` saved gates, where `n_ℓ` is the number of occurrences of type
`ℓ` and `s_ℓ` is the length of one saved replacement. -/
theorem gate_count_eq [Fintype σ] [DecidableEq σ] (s : σ → ℕ) (L : List σ) :
    (L.map s).sum = ∑ l : σ, L.count l * s l := by
  induction L with
  | nil => simp
  | cons a L ih =>
      rw [List.map_cons, List.sum_cons, ih]
      have hcount : ∀ l : σ, List.count l (a :: L) * s l
          = List.count l L * s l + if l = a then s a else 0 := by
        intro l
        by_cases hl : l = a
        · subst hl
          rw [List.count_cons_self]
          simp
          ring
        · rw [List.count_cons_of_ne (a := l) (b := a) (Ne.symm hl)]
          simp [hl]
      rw [Finset.sum_congr rfl (fun l _ => hcount l), Finset.sum_add_distrib]
      simp
      ring

end Qatlib.Papers.ShallowLind26.ShallowSim.MultiplicityAccounting
