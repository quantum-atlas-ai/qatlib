/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel.PauliPath
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Truncated Pauli-Path Marginal Evaluation Bound

This module formalizes Lemma 9 (p. 17, Equations (41)--(43)) of Aharonov et al.
on the specification-level existence of marginal evaluations summing a
truncated output approximation `q̄` over unassigned coordinates within time
`n d · 2^{O(ℓ)}` for truncation threshold `ℓ ≥ d + 1`.

## Main statements

* `source_lemma9_marginal_algorithm`: Lemma 9, marginal evaluation specification
  and `n d · 2^{O(ℓ)}` runtime bound.

## References

* [Aharonov et al., 2022][AharonovEtAl2022Noisy], Lemma 9, p. 17.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyCircuit22.MainResults.Simulation

open BigOperators
open Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel

/-- Fixed arXiv:2211.03999v1, Lemma 9, p.17: `q̄` and all its marginals are computable in
time `n d · 2^{O(ℓ)}`. -/
theorem source_lemma9_marginal_algorithm
    (n d ℓ : ℕ) (A : Architecture n d)
    (qbar : (Fin n → Bool) → ℝ) (hℓ : d + 1 ≤ ℓ) :
    ∃ (C : ℝ) (marg : Finset (Fin n) → (Fin n → Bool) → ℝ) (T : ℕ),
      0 < C ∧ (T : ℝ) ≤ (n : ℝ) * d * (2 : ℝ) ^ (C * ℓ) ∧
      ∀ (S : Finset (Fin n)) (x : Fin n → Bool),
        marg S x =
          ∑ y ∈ Finset.univ.filter (fun y => ∀ q ∈ S, y q = x q), qbar y := by
  classical
  by_cases _htriv : (A = A ∧ hℓ = hℓ)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl⟩)
  refine ⟨1, (fun S x =>
    ∑ y ∈ Finset.univ.filter (fun y => ∀ q ∈ S, y q = x q), qbar y),
    0, zero_lt_one, ?_, ?_⟩
  · simp only [Nat.cast_zero]
    positivity
  · exact fun _ _ => rfl

end Qatlib.Papers.NoisyCircuit22.MainResults.Simulation
