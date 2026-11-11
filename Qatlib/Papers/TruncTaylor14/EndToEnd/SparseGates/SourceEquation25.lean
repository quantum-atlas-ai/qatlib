/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorSimulation

set_option backward.isDefEq.respectTransparency false

/-!
# Source Eq. (25) — sparse-oracle gate cost

arXiv:1412.4687v1, p. 4, Eq. (25).  When `H` is given by a sparse oracle the
controlled-`select(H)` work collapses: with all `α_ℓ = γ` equal, each index
register is prepared in `log L` gates and multiplied by `K` registers, while
the `1`-sparse self-inverse terms cost `O(n)` apiece and need no explicit
`L`-term decomposition.  With `L = O(T/ε)`, so `log₂L = O(m)` for the
precision parameter `m = Θ(log(T/ε))`, the per-segment cost is

`K·(n + O(m)) = O( n · log²(T/ε) / loglog(T/ε) )`.

We model the sparse-select cost per segment as
`K·(n + m)` (`m` bounds `log₂L`), and derive the Eq. (25) shape from the
frozen native-cutoff rate `K·log₂ m ≤ C m` and `n + m ≤ n·m` (`n,m ≥ 2`).

Frozen FQNs reused: `factorialTaylorCutoff`,
`factorial_taylor_native_cutoff_and_rate` (restated locally
as `cutoff_rate`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TruncTaylor14.EndToEnd.SparseGates

open Qatlib.Concepts.CoherentSim.FactorialTaylor

/-- Per-segment gate cost of the sparse-oracle variant: `K` sparse-select
operations, each costing `n` oracle queries plus `O(log L) ≤ m` synthesis
gates. -/
def sparseSegmentGates (K n m : ℕ) : ℕ := K * (n + m)


/-- The frozen native-cutoff rate, restated in divided form: the least `K`
with `(K+1)! ≥ 2^m` satisfies `K ≤ C m / log₂ m`. -/
private theorem cutoff_rate :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ m ≥ m₀,
      (factorialTaylorCutoff m : ℝ) ≤
        C * (m : ℝ) / (Nat.log 2 m : ℝ) := by
  obtain ⟨C, m₀, hC, hm₀, hrate⟩ :=
    factorial_taylor_native_cutoff_and_rate.2
  refine ⟨C, max m₀ 2, hC, le_max_right _ _, ?_⟩
  intro m hm
  have hm0 : m₀ ≤ m := (le_max_left _ _).trans hm
  have hm2 : 2 ≤ m := (le_max_right _ _).trans hm
  have hlogpos : 0 < Nat.log 2 m := Nat.log_pos (by norm_num) hm2
  have hcast : (factorialTaylorCutoff m : ℝ) * (Nat.log 2 m : ℝ) ≤ C * (m : ℝ) := by
    exact_mod_cast hrate m hm0
  rw [le_div_iff₀ (by exact_mod_cast hlogpos)]
  exact hcast

/-- arXiv:1412.4687v1 Eq. (25), p. 4: with a sparse Hamiltonian oracle the
per-segment gate cost is `O(n·log²(T/ε)/loglog(T/ε))`. -/
theorem source_equation25 :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ (n m : ℕ), 2 ≤ n → m₀ ≤ m →
      (sparseSegmentGates (factorialTaylorCutoff m) n m : ℝ) ≤
        C * (n : ℝ) * (m : ℝ) ^ 2 / (Nat.log 2 m : ℝ) := by
  obtain ⟨D, n₀, hD, hn₀, hrate⟩ :=
    cutoff_rate
  refine ⟨D, max n₀ 2, hD, le_max_right _ _, ?_⟩
  intro n m hn hm
  have hm0 : n₀ ≤ m := (le_max_left _ _).trans hm
  have hm2 : 2 ≤ m := (le_max_right _ _).trans hm
  have hK := hrate m hm0
  have hcast : (sparseSegmentGates (factorialTaylorCutoff m) n m : ℝ) =
      (factorialTaylorCutoff m : ℝ) * ((n : ℝ) + (m : ℝ)) := by
    unfold sparseSegmentGates
    push_cast
    ring
  rw [hcast]
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hm2r : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hnm : (n : ℝ) + (m : ℝ) ≤ (n : ℝ) * (m : ℝ) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith
    have hm1 : (1 : ℝ) ≤ (m : ℝ) - 1 := by linarith
    have hprod : (1 : ℝ) ≤ ((n : ℝ) - 1) * ((m : ℝ) - 1) := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ ((n : ℝ) - 1) * ((m : ℝ) - 1) :=
            mul_le_mul hn1 hm1 (by norm_num) (by linarith)
    nlinarith [hprod]
  have hc : (0 : ℝ) ≤ (n : ℝ) + (m : ℝ) := by positivity
  calc (factorialTaylorCutoff m : ℝ) * ((n : ℝ) + (m : ℝ))
      ≤ (D * (m : ℝ) / (Nat.log 2 m : ℝ)) * ((n : ℝ) + (m : ℝ)) :=
        mul_le_mul_of_nonneg_right hK hc
    _ ≤ (D * (m : ℝ) / (Nat.log 2 m : ℝ)) * ((n : ℝ) * (m : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hnm (by positivity)
    _ = D * (n : ℝ) * (m : ℝ) ^ 2 / (Nat.log 2 m : ℝ) := by ring

end Qatlib.Papers.TruncTaylor14.EndToEnd.SparseGates
