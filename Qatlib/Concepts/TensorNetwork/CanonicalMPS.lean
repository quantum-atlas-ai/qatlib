/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorNetwork.GaugeInvariance

/-!
# Canonical matrix product states

This module packages three matrix product state results for a normalized amplitude function in
`g2`. Every exact MPS representation has bond dimension at least the rank `cutRank` at each cut.
For a nonempty chain, an exact `LeftCanonical` representation exists with bond dimension equal
to the maximum of one and the cut ranks.

For every positive bond dimension on a nonempty chain, `g2` also supplies an MPS approximation
whose squared amplitude error is bounded by twice the sum of the squared Schmidt tails
`schmidtTailSq` over all cuts. Background on MPS representations and canonical forms is given in
[PerezGarciaEtAl2007].

## Main statements

* `g2`: the cut-rank lower bound, existence of an exact left-canonical representation, and the
  Schmidt-tail approximation bound for normalized states.

## References

* [Perez-Garcia et al., 2007][PerezGarciaEtAl2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Concepts.TensorNetwork.GaugeInvariance

namespace Qatlib.Concepts.TensorNetwork.CanonicalMPS
open scoped BigOperators ComplexConjugate

/-- For a normalized amplitude function, every exact MPS representation has bond dimension at
least `cutRank n d ψ c` at each cut `c < n`. If `1 ≤ n`, there exists an exact
`LeftCanonical` representation with bond dimension equal to the maximum of one and the cut
ranks, and for every positive `D` there exists an MPS of bond dimension `D` whose squared
amplitude error is at most twice the sum of `schmidtTailSq n d ψ c D` over `c < n`
[PerezGarciaEtAl2007]. -/
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
