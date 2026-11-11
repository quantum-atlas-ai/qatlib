/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# IsingFormat — Corollary 3 (arXiv:2303.01471v1, Appendix F.3)

Source: *Quantum Hamiltonian Descent*, Leng–Hickman–Li–Wu, arXiv:2303.01471v1,
PDF page 56, equations (F.43)–(F.47).
-/

open scoped Matrix BigOperators
open Matrix

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QHamDescent23.MainResults.IsingFormat

/-!
### Corollary 3 (F.43)–(F.47)

Source: arXiv:2303.01471v1, Corollary 3, p.56.

Any quadratic program (QUBO) in binary variables `x_i ∈ {0,1}` can be written
in Ising form in spin variables `s_i ∈ {−1,+1}` via `x_i = (1 − s_i)/2`:

`Σ_{ij} Q_{ij} x_i x_j
  = ¼ Σ_{ij} Q_{ij} s_i s_j − ¼ Σ_i (Σ_j (Q_{ij}+Q_{ji})) s_i
    + ¼ Σ_{ij} Q_{ij}`,

so the Ising couplings are `J_{ij} = Q_{ij}/4` and the fields are
`h_i = −¼ Σ_j (Q_{ij} + Q_{ji})` (F.43)–(F.47).

Paper proof route: substitute `x_i = (1−s_i)/2` and expand; the quadratic term
produces `s_i s_j/4`, the linear term arises from the two cross terms, and the
constant is `Σ Q_{ij}/4`.

Proof: expand each summand and distribute the sums with
`Finset.sum_add_distrib`/`Finset.sum_sub_distrib`/`Finset.mul_sum`; the two
cross terms are identified after `Finset.sum_comm`, and `ring` closes the
resulting scalar identity.  No `sorry`.
-/
/-- Corollary 3, Eqs. (F.43)–(F.47): substituting `x_i = (1 − s_i)/2` turns a
QUBO with matrix `Q` into the stated Ising quadratic, linear and constant
terms. [arXiv:2303.01471v1, Corollary 3, p.56.] -/
theorem source_corollary3_ising_format
    (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ) :
    (∑ i, ∑ j, Q i j * ((1 - s i) / 2) * ((1 - s j) / 2))
      = (1 / 4) * (∑ i, ∑ j, Q i j * s i * s j)
        - (1 / 4) * (∑ i, (∑ j, (Q i j + Q j i)) * s i)
        + (1 / 4) * (∑ i, ∑ j, Q i j) := by
  have hterm : ∀ i j : Fin n, Q i j * ((1 - s i) / 2) * ((1 - s j) / 2)
      = (1/4) * (Q i j * s i * s j) - (1/4) * (Q i j * s i)
        - (1/4) * (Q i j * s j) + (1/4) * Q i j := by
    intro i j; ring
  simp only [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have hA : ∑ x, ∑ y, (1/4 : ℝ) * (Q x y * s x)
      = ∑ x, (1/4) * ((∑ y, Q x y) * s x) := by
    apply Finset.sum_congr rfl; intro x hx
    rw [← Finset.mul_sum, Finset.sum_mul]
  have hB : ∑ x, ∑ y, (1/4 : ℝ) * (Q x y * s y)
      = ∑ x, (1/4) * ((∑ y, Q y x) * s x) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x hx
    rw [← Finset.mul_sum, Finset.sum_mul]
  have hcomb : ∑ x, (1/4 : ℝ) * (((∑ y, Q x y) + (∑ y, Q y x)) * s x)
      = ∑ x, (1/4) * ((∑ y, Q x y) * s x)
        + ∑ x, (1/4) * ((∑ y, Q y x) * s x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x hx; ring
  rw [hA, hB, hcomb]
  ring

end Qatlib.Papers.QHamDescent23.MainResults.IsingFormat
