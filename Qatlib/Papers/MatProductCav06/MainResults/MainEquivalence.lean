/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatProductCav06.MainResults.SequentialDefs

/-!
# Relations between sequential generation classes

The module relates the matrix product, deterministic sequential, and probabilistic sequential
predicates. `three_class_forward` proves the forward inclusions, while
`three_class_equivalence_iff_constructive` identifies the remaining constructive implication
needed for the stated class equivalence. See [SchoenEtAl2007] for the sequential generation
setting.

## Main statements

* `three_class_forward`: deterministic sequential membership implies both other memberships.
* `three_class_equivalence_iff_constructive`: reduces the class equivalence to a constructive
  converse.

## References

* [Schoen et al., 2007][SchoenEtAl2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexConjugate

namespace Qatlib.Papers.MatProductCav06.MainResults

/-- Every state in the deterministic sequential class belongs to the matrix product class with
the same parameters. See [SchoenEtAl2007]. -/
theorem det_sequential_to_mps {n d D : ℕ} {ψ : (Fin n → Fin d) → ℂ}
    (h : InDetSequentialClass n d D ψ) : InMpsClass n d D ψ :=
  det_subset_mps h

/-- Every state in the deterministic sequential class belongs to the probabilistic sequential
class with the same parameters. See [SchoenEtAl2007]. -/
theorem det_sequential_to_prob {n d D : ℕ} {ψ : (Fin n → Fin d) → ℂ}
    (h : InDetSequentialClass n d D ψ) : InProbSequentialClass n d D ψ :=
  det_subset_mps h

/-- Deterministic sequential membership implies both matrix product and probabilistic sequential
membership. See [SchoenEtAl2007]. -/
theorem three_class_forward {n d D : ℕ} {ψ : (Fin n → Fin d) → ℂ}
    (h : InDetSequentialClass n d D ψ) :
    InMpsClass n d D ψ ∧ InProbSequentialClass n d D ψ :=
  ⟨det_sequential_to_mps h, det_sequential_to_prob h⟩

/-- The universal implication from matrix product membership to deterministic sequential
membership is equivalent to the universal characterization of matrix product membership by
the conjunction of deterministic and probabilistic sequential membership. See
[SchoenEtAl2007]. -/
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
