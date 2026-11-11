/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 1: the swap-test output observable equals `K0(x, x0)`

Fixed version: arXiv:2608.15545v1 (2026-08-16), Proposition 1, p.15, with
Eqs. (F7)-(F9) and the definition of `K0` in Eq. (E5).  Paper: *Quantum
Advantage with Adaptive Shallow Circuits*.

The paper's classical-hardness argument observes a fixed single-qubit
readout `Z_{q_out}` of an adaptive shallow circuit.  The circuit prepares a
state on two registers whose amplitudes are `x` and `x0`, applies a
Hadamard-controlled swap, and measures the ancilla in the `Z` basis.  The
expectation of the readout is

```
Z_{q_out} = K0(x, x0) = ⟨x|x0⟩²                                       (E5)
```

(`h`- and `c`-type contributions cancel by the Hadamard on the control), so
the hardness of `K0` is exactly the hardness of a one-qubit observable of a
CRAS circuit.  This is the real-amplitude shadow of the complex statement;
the complex case follows by splitting the amplitudes into real and imaginary
parts.

We formalize the arithmetic core for real amplitudes `u, v : Fin N → ℝ`.
The post-selected amplitudes on outcome `0` and `1` of the ancilla are
`(u_i v_j ± v_i u_j)/2`, so the `Z`-expectation is the difference of the
squared norms; the cross terms sum to `⟨u, v⟩²`:

```
∑_{i,j} ((u_i v_j + v_i u_j)/2)² - ((u_i v_j - v_i u_j)/2)²
  = (∑_i u_i v_i)².
```

This is proved below (`swapTestZ_eq_overlap_sq`), with no `sorry`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.ShallowAdvWu26.ShallowPower.SwapTest

/-- Real inner product `⟨u, v⟩ = ∑_i u_i v_i`, the real analogue of the
overlap `K0(x, x0)` of Eq. (E5). -/
noncomputable def overlap {N : ℕ} (u v : Fin N → ℝ) : ℝ :=
  ∑ i, u i * v i

/-- Amplitude of the `0` ancilla outcome in the swap test: the symmetric
combination `(u_i v_j + v_i u_j)/2` on the pair `(i, j)`. -/
noncomputable def ampZero {N : ℕ} (u v : Fin N → ℝ) (p : Fin N × Fin N) : ℝ :=
  (u p.1 * v p.2 + v p.1 * u p.2) / 2

/-- Amplitude of the `1` ancilla outcome in the swap test: the antisymmetric
combination `(u_i v_j - v_i u_j)/2`. -/
noncomputable def ampOne {N : ℕ} (u v : Fin N → ℝ) (p : Fin N × Fin N) : ℝ :=
  (u p.1 * v p.2 - v p.1 * u p.2) / 2

/-- Expectation of the swap-test readout: `∑_{i,j} (ampZero² - ampOne²)`,
i.e. `P(0) - P(1)` for the ancilla measurement. -/
noncomputable def swapTestZ {N : ℕ} (u v : Fin N → ℝ) : ℝ :=
  (∑ p : Fin N × Fin N, ampZero u v p ^ 2) -
    ∑ p : Fin N × Fin N, ampOne u v p ^ 2

/-- **Proposition 1, Eq. (E5), real-amplitude form.**  The swap-test `Z`
expectation equals the squared overlap `K0(x, x0) = ⟨x|x0⟩²`. -/
theorem swapTestZ_eq_overlap_sq {N : ℕ} (u v : Fin N → ℝ) :
    swapTestZ u v = overlap u v ^ 2 := by
  unfold swapTestZ overlap ampZero ampOne
  rw [← Finset.sum_sub_distrib]
  trans ∑ p : Fin N × Fin N, (u p.1 * v p.2) * (v p.1 * u p.2)
  · apply Finset.sum_congr rfl
    intro p _
    ring
  · rw [pow_two, Fintype.sum_prod_type, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- **Proposition 1, quantitative form.**  Since the identity is exact, the
readout approximates `K0` within any additive error; in particular within
`n^{-c}` for every `c > 0`.  This records the statement of Proposition 1
with `K0` read off as the overlap of Eq. (E5). -/
theorem swap_test_approx_K0 {N : ℕ} (u v : Fin N → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    |swapTestZ u v - overlap u v ^ 2| ≤ ε := by
  rw [swapTestZ_eq_overlap_sq]
  simp only [sub_self, abs_zero]
  exact hε

end Qatlib.Papers.ShallowAdvWu26.ShallowPower.SwapTest
