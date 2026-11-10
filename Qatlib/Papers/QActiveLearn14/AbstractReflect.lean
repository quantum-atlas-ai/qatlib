/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QActiveLearn14.AbstractReflect

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def flaggedReflection (P : E → E) (v : E) : E := 2 • P v - v

def piTildeReflection (πtilde v : E) : E := v - (2 * ⟪v, πtilde⟫) • πtilde

theorem lemma6_reflection_identity
    (P : E → E) (π πtilde : E) (r : ℝ)
    (hPπ : P π = r • πtilde)
    (hPπt : P πtilde = πtilde)
    (hadd : ∀ α β : ℝ, P (α • π + β • πtilde) = α • P π + β • P πtilde)
    (hunit : ⟪πtilde, πtilde⟫ = 1)
    (horth : ⟪π - r • πtilde, πtilde⟫ = 0) :
    ∀ α β : ℝ, piTildeReflection πtilde (α • π + β • πtilde) =
      -flaggedReflection P (α • π + β • πtilde) := by
  intro α β
  have hinner : ⟪π, πtilde⟫ = r := by
    rw [inner_sub_left, real_inner_smul_left, hunit] at horth
    linarith
  have hinner_comb : ⟪α • π + β • πtilde, πtilde⟫ = α * r + β := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hinner, hunit]
    ring
  unfold piTildeReflection flaggedReflection
  rw [hadd α β, hPπ, hPπt, hinner_comb]
  simp only [smul_add, smul_smul]
  module

end Qatlib.Papers.QActiveLearn14.AbstractReflect
