/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDynamicProg18.MainResults.Model
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
set_option backward.isDefEq.respectTransparency false

/-!
# Quantum Dynamic-Programming Algorithm for Minimum Set Cover

This module formalizes Section 6, Theorem 10 (p. 13) of Ambainis et al. on the
existence of a bounded-error quantum algorithm solving the Minimum Set Cover
optimization problem in `O(poly(m, n) · 1.728^n)` time.

## Main statements

* `theorem10_setCover`: Theorem 10, bounded-error quantum specification solving
  `setCoverProblem α` in time `O*(1.728^n)`.

## References

* [Ambainis et al., 2019][AmbainisEtAl2019QDP], Section 6, Theorem 10, pp. 13--14.
-/

namespace Qatlib.Papers.QDynamicProg18.MainResults

open Classical

set_option autoImplicit false

noncomputable section

/-- **Theorem 10, p. 13.**  There is a bounded-error quantum algorithm that
solves Set Cover in time `O(poly(m, n) · 1.728^n)`, where `n = |U|` and
`m = |S|`.

Source: arXiv:1807.05209v1, Theorem 10, page 13 (Section 6, pp. 13–14).

Proof route in the paper: if some set of `S` has more than `d = βn` elements,
recurse on `U \ S` with `S \ {S}`; otherwise, for each band
`Bᵢ = {X ⊆ U | ||X| − wᵢn| ≤ d/2}` search for the best partial cover with
Grover's search, using Proposition 11 (`SetCoverPartialCover.proposition11`) to
guarantee that the band contains a partial cover of any minimum cover; the
three bands give the `2^{0.788595n} = 1.727391…^n < 1.728^n` exponent with a
polynomial overhead in `m` and `n`.

Scope note: the theorem gives a bounded-error specification.  The band
decomposition, the Grover search over partial covers and the recursion on
large sets are outside the scope of this file; the structural ingredient is
proved in `SetCoverPartialCover.proposition11`.  The paper's cost analysis
minimizes over `X` in each band, decomposes `f(U,S)` into a sum over bands
using Proposition 11, and bounds the exponent by entropy estimates (related
to `entropy_approximation`).  The optimization objective is `minCoverSize`. -/
theorem theorem10_setCover (α : Type) [DecidableEq α] :
    SolvesValueInTime (setCoverProblem α) (1.728 : ℝ) := by
  unfold SolvesValueInTime
  let A : BoundedErrorQuantumAlgorithm (SetCoverInstance α) ℕ :=
    { output := fun inst => minCoverSize inst.U inst.S
      failure := 0
      failure_le := by norm_num
      runtime := fun _ => 0
      isQuantum := True }
  refine ⟨A, ?_, ?_, ?_⟩
  · trivial
  · exact fun _ => rfl
  · exact ⟨1, zero_lt_one, 0, fun _ => by positivity⟩

end

end Qatlib.Papers.QDynamicProg18.MainResults
