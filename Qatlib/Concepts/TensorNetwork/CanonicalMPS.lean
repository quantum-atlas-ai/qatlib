/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorNetwork.GaugeInvariance
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Concepts.TensorNetwork.GaugeInvariance

namespace Qatlib.Concepts.TensorNetwork.CanonicalMPS
open scoped BigOperators ComplexConjugate

theorem g2 :
∀ (n d : ℕ) (ψ : (Fin n → Fin d) → ℂ),

  (∑ x, Complex.normSq (ψ x) = 1) →

  (∀ (D : ℕ) (hD : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      @IsMpsRepresentation n d D hD A ψ → ∀ c : ℕ, c < n → cutRank n d ψ c ≤ D)

  ∧ (1 ≤ n → ∃ (D : ℕ) (hD : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      @IsMpsRepresentation n d D hD A ψ ∧ LeftCanonical A ∧
        D = max 1 ((Finset.range n).sup fun c => cutRank n d ψ c))

  ∧ (1 ≤ n → ∀ D : ℕ, 0 < D →
      ∃ (hD : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
        ∑ x, Complex.normSq (@mpsAmplitude n d D hD A x - ψ x)
          ≤ 2 * ∑ c ∈ Finset.range n, schmidtTailSq n d ψ c D) := by
  intro n d ψ hnorm
  exact ⟨clause2_clause1 n d ψ hnorm, clause2_clause2 n d ψ hnorm,
    clause2_clause3 n d ψ hnorm⟩

end Qatlib.Concepts.TensorNetwork.CanonicalMPS
