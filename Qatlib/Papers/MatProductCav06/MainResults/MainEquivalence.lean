/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatProductCav06.MainResults.SequentialDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexConjugate

namespace Qatlib.Papers.MatProductCav06.MainResults

theorem det_sequential_to_mps {n d D : ℕ} {ψ : (Fin n → Fin d) → ℂ}
    (h : InDetSequentialClass n d D ψ) : InMpsClass n d D ψ :=
  det_subset_mps h

theorem det_sequential_to_prob {n d D : ℕ} {ψ : (Fin n → Fin d) → ℂ}
    (h : InDetSequentialClass n d D ψ) : InProbSequentialClass n d D ψ :=
  det_subset_mps h

theorem three_class_forward {n d D : ℕ} {ψ : (Fin n → Fin d) → ℂ}
    (h : InDetSequentialClass n d D ψ) :
    InMpsClass n d D ψ ∧ InProbSequentialClass n d D ψ :=
  ⟨det_sequential_to_mps h, det_sequential_to_prob h⟩

theorem three_class_equivalence_iff_constructive :
    (∀ (n d D : ℕ) (ψ : (Fin n → Fin d) → ℂ),
        InMpsClass n d D ψ → InDetSequentialClass n d D ψ) ↔
      (∀ (n d D : ℕ) (ψ : (Fin n → Fin d) → ℂ),
        InMpsClass n d D ψ ↔
          (InDetSequentialClass n d D ψ ∧ InProbSequentialClass n d D ψ)) := by
  constructor
  · intro hcon n d D ψ
    refine ⟨fun hmps => ⟨hcon n d D ψ hmps, prob_iff_mps.mpr hmps⟩, ?_⟩
    rintro ⟨hdet, -⟩
    exact det_sequential_to_mps hdet
  · intro heq n d D ψ hmps
    exact (heq n d D ψ).mp hmps |>.1

end Qatlib.Papers.MatProductCav06.MainResults
