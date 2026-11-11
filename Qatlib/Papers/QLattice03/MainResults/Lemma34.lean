/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Lemma33
import Qatlib.Papers.QLattice03.MainResults.Reductions

/-!
# QLattice03 — Lemma 3.4: the weaker algorithm

Paper: Oded Regev, *Quantum Computation and Lattice Problems*,
arXiv:cs/0304005v1, Section 3.2, Lemma 3.4 (page 6).

> Lemma 3.4  For any `f > 0` let `ū = Σᵢ uᵢ b̄ᵢ` be the shortest lattice
> vector in a `(c_unq n^{1+2f})`-unique lattice where `c_unq > 0` is a constant.
> If there exists a solution to the two point problem with failure parameter `f`
> then there exists a quantum algorithm that given this lattice and three
> integers `l, m, i₀` returns
> `(u₁, …, u_{i₀-1}, (u_{i₀} - m)/p, u_{i₀+1}, …, uₙ)` with probability
> `1/poly(n)` if `‖ū‖ ≤ l ≤ 2‖ū‖`, `u_{i₀} ≡ m (mod p)` and `1 ≤ m ≤ p - 1`.

The construction (p. 6–8) applies LLL, defines the map
`f(t, ā) = (a₁p + tm) b̄₁ + Σ_{i≥2} aᵢ b̄ᵢ` on `{0,1} × {0,…,M-1}ⁿ` with
`M = 2^{4n}`, produces two point registers via cube partition, and reads off the
coefficient vector, using `|uᵢ| ≤ 2^{2n}` (Lemma 3.3).

## Status

The lemma's content — the existence of a coefficient-extraction routine built
from a two-point solver that satisfies the stated contract — is recorded as an
*open obligation* (`def … : Prop`).  It is not asserted as a theorem, and no
concrete routine is claimed correct here.  Missing: a quantum-state/measurement
model for the cube partition and the collapsing argument, plus the
`1/poly(n)` success-probability analysis.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLattice03.MainResults

open Qatlib.Papers.QLattice03.MainResults

/-- Replace the `i₀`-th coordinate of the coefficient vector by `(u_{i₀}-m)/p`,
as in the conclusion of Lemma 3.4. -/
noncomputable def coeffReplacement {n : ℕ} (u : Fin n → ℤ) (p : ℕ) (i0 : Fin n) (m : ℤ) :
    Fin n → ℤ :=
  fun i => if i = i0 then (u i - m) / (p : ℤ) else u i

/-- **Lemma 3.4** (open obligation, correctness contract): for every two-point
solver with failure parameter `f` there exists a coefficient-extraction routine
which, on an LLL-reduced basis whose shortest vector `u` satisfies the numeric
side conditions, returns `u` with the `i₀`-th coefficient replaced by
`(u_{i₀}-m)/p`. -/
def weak_twoPoint_recovers_coefficient : Prop :=
  ∀ (f : ℝ) (_hf : 0 < f) (cunq : ℝ) (_hcunq : 0 < cunq)
    (A : ∀ n M : ℕ, TwoPointRegister n M → (Fin n → ℤ)),
    SolvesTwoPointWithFailure f A →
    ∃ Rout : ∀ n : ℕ, LatticeBasis n → ℕ → ℤ → Fin n → (Fin n → ℤ),
      ∀ (n : ℕ) (b : LatticeBasis n) (u : Fin n → ℤ),
        IsUniqueShortest (fun m => cunq * (m : ℝ) ^ (1 + 2 * f)) b u →
        ∀ (p : ℕ), Nat.Prime p → (n : ℝ) ^ (2 + 2 * f) < (p : ℝ) →
          ∀ (l : ℝ), Qatlib.Papers.QLattice03.MainResults.norm u ≤ l →
            l ≤ 2 * Qatlib.Papers.QLattice03.MainResults.norm u →
            ∀ (i0 : Fin n) (m : ℤ), 1 ≤ m → m ≤ (p : ℤ) - 1 →
              (∃ k : ℤ, u i0 = m + k * (p : ℤ)) →
                Rout n b p m i0 = coeffReplacement u p i0 m

end Qatlib.Papers.QLattice03.MainResults
