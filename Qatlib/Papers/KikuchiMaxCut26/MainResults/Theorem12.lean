/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KikuchiMaxCut26.MainResults.Theorem31

set_option backward.isDefEq.respectTransparency false

/-!
# Spectral Sandwich Chain for Kikuchi Adjacency and Laplacian Matrices

This module proves Theorem 1.2: combining Proposition 2.2 with Theorem 3.1 at
`b = ±1` yields the sharp spectral chain
`-(m + k) ≤ -λ_max(L_G^{(k)}) ≤ 2 λ_min(A_G^{(k)}) ≤ 2 λ_max(A_G^{(k)}) ≤ λ_max(Q_G^{(k)}) ≤ m + k`.

## Main statements

* `theorem_1_2`: complete five-inequality spectral chain for level-`k` Kikuchi graphs.

## References

* [Bakshi et al., 2026][BakshiEtAl2026Kikuchi], Theorem 1.2, p. 1.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.KikuchiMaxCut26.MainResults

variable {n : ℕ}

/-- **Theorem 1.2**: for any graph `G` on `n` vertices with `m = edgeCount G` edges and
any `k ≤ n`,
`-(m + k) ≤ -λ_max(L_G^{(k)}) ≤ 2 λ_min(A_G^{(k)}) ≤ 2 λ_max(A_G^{(k)}) ≤ λ_max(Q_G^{(k)}) ≤ m + k`. -/
theorem theorem_1_2 (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) (hk : k ≤ n) :
    -((edgeCount G : ℝ) + (k : ℝ)) ≤
        -lamMax (lapMatrix G k) (lapMatrix_isHermitian G k) ∧
      -lamMax (lapMatrix G k) (lapMatrix_isHermitian G k) ≤
        2 * lamMin (adjMatrix G k) (adjMatrix_isHermitian G k) ∧
      2 * lamMin (adjMatrix G k) (adjMatrix_isHermitian G k) ≤
        2 * lamMax (adjMatrix G k) (adjMatrix_isHermitian G k) ∧
      2 * lamMax (adjMatrix G k) (adjMatrix_isHermitian G k) ≤
        lamMax (signlessMatrix G k) (signlessMatrix_isHermitian G k) ∧
      lamMax (signlessMatrix G k) (signlessMatrix_isHermitian G k) ≤
        (edgeCount G : ℝ) + (k : ℝ) := by
  classical
  obtain ⟨h1, h2, h3⟩ := proposition_2_2_kikuchi (G := G) k
  have hL : lamMax (lapMatrix G k) (lapMatrix_isHermitian G k) ≤
      (edgeCount G : ℝ) + (k : ℝ) := by
    simpa [signedLaplacian_neg_one] using theorem_3_1 (G := G) k hk (-1) (Or.inl rfl)
  have hQ : lamMax (signlessMatrix G k) (signlessMatrix_isHermitian G k) ≤
      (edgeCount G : ℝ) + (k : ℝ) := by
    simpa [signedLaplacian_one] using theorem_3_1 (G := G) k hk 1 (Or.inr rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end Qatlib.Papers.KikuchiMaxCut26.MainResults
