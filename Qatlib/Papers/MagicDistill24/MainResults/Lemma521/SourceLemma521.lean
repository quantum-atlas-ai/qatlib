/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalCss

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Source contract: Lemma 5.2.1 (arXiv:2408.07764v2, p.~44, Eq (263))

Recall that `(P₁, …, P_N)` are the places on which the algebraic geometry code is
defined and correspond, in order, to the columns of `G̃`. Consider the AG code
`C_short = C_L(P_{k+1} + … + P_N, A − P₁ − … − P_k)` (Eq (263)), and let `m̃_w` be
componentwise multiplication by `(w_{k+1}, …, w_N)` (so `(m̃_w x)_i = w_{k+i} x_i`).
Then `G₀` is a generator matrix for the code `m̃_w(C_short)`.

The algebraic content is: scaling every generator row of `C_short` componentwise by
the nowhere-zero weights `w` yields a generator matrix of the scaled code, i.e.
`rowspace(G₀) = m̃_w(rowspace(G_short))` whenever `(G₀)_i = m̃_w((G_short)_i)`. The
AG-specific fact that `G_short` is the generator of `C_L(…, A − P₁ − … − P_k)` is
not formalised (Mathlib has no AG codes); the lemma below proves the row-space
identity that Lemma 5.2.1 states, from that defining relation.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MagicDistill24.MainResults.Lemma521

open Matrix
open Qatlib.Papers.MagicDistill24.Triorthogonal

/-- Componentwise multiplication by the weight vector `w`: the map `m̃_w` of
Lemma 5.2.1, `(m̃_w x)_j = w_j x_j`, as a linear map. -/
noncomputable def scaleLin {n : ℕ} (w : Fin n → F1024) :
    (Fin n → F1024) →ₗ[F1024] (Fin n → F1024) where
  toFun x := fun j => w j * x j
  map_add' x y := by ext j; simp [mul_add]
  map_smul' a x := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Fixed arXiv:2408.07764v2, Lemma 5.2.1 (p.~44, Eq (263)): if the rows of `G₀`
are the rows of the short AG code's generator `G_short` componentwise scaled by
the nowhere-zero weight vector `w` (`(G₀)_i = m̃_w((G_short)_i)`), then `G₀`
generates `m̃_w(C_short)`, i.e. `rowspace(G₀) = m̃_w(rowspace(G_short))`. -/
theorem source_lemma_5_2_1 {m' n : ℕ}
    (Gshort G0 : Matrix (Fin m') (Fin n) F1024) (w : Fin n → F1024)
    (_hw : ∀ j, w j ≠ 0)
    (hG : ∀ i, G0 i = fun j => w j * Gshort i j) :
    triRowSpace G0 = Submodule.map (scaleLin w) (triRowSpace Gshort) := by
  apply le_antisymm
  · -- `span (rows G₀) ≤ m̃_w (span (rows G_short))`.
    rw [triRowSpace, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_map.mpr
      ⟨Gshort i, Submodule.subset_span ⟨i, rfl⟩, by ext j; simp [scaleLin, hG i]⟩
  · -- `m̃_w (span (rows G_short)) ≤ span (rows G₀)`.
    rw [triRowSpace, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.subset_span ⟨i, by ext j; simp [scaleLin, hG i]⟩

end Qatlib.Papers.MagicDistill24.MainResults.Lemma521
