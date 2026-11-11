/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatticeSVP13.MainResults.ExponentCore.PaperConstants

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4: quantum complexity of the Nguyen--Vidick sieve

Laarhoven--Mosca--van de Pol, *Solving the Shortest Vector Problem in Lattices Faster
Using Quantum Search*, fixed arXiv:1301.6176v1 (25 Jan 2013), Appendix A, p. 16.

The classical analysis (Lemma 3) bounds the two sieve lists by `|S|, |C| ≤ 2 ^ (c_h n + o(n))`
with `c_h` the exponent of Equation (1).  The space cost is `O(|S| + |C|)` and the time
cost is `Õ(|S| · |C|)` classically, or `Õ(|S| · √|C|)` after replacing the search over
`C` by Grover's quantum search.  Lemma 4 is exactly this statement:

> **Lemma 4.** On a quantum computer, assuming that Heuristic 1 holds, Algorithm 1 will
> return a shortest vector of a lattice in time `2 ^ (3 c_h / 2 · n + o(n))` and space
> `2 ^ (c_h · n + o(n))`.

The output guarantee `return a shortest vector` is the paper's Heuristic 1
(p. 6) inherited from Nguyen--Vidick [41, Lemma 1]; it is an assumption about the
distribution of the sieve lists that the quantum search does not alter, so it is carried
verbatim here rather than re-derived.  What is proved is the *complexity* content: the
leading exponent of `|S| · √|C|` is `(3/2) c_h` and of `|S| + |C|` is `c_h`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.LatticeSVP13.MainResults.SieveQuantum

open Qatlib.Papers.LatticeSVP13.MainResults.ExponentCore

/-- **Lemma 4** (arXiv:1301.6176v1, p. 16).  If the sieve lists have size exponent
`c_h(γ)` from Equation (1), then the quantum time cost `|S| · √|C|` has exponent
`(3/2) c_h(γ)` and the space cost `|S| + |C|` has exponent `c_h(γ)`.

`hT` fixes the time cost to the paper's `|S| · √|C|` (the Grover-accelerated search
over `C`); `hSp`, `hCp` are the strict positivity of the list sizes needed to take
base-two logarithms of the product and the sum. -/
theorem lemma4_quantum_sieve
    (S C T : ℕ → ℝ) (γ : ℝ)
    (hS : HasLog2Exponent (fun n => Real.logb 2 (S n)) (cH γ))
    (hC : HasLog2Exponent (fun n => Real.logb 2 (C n)) (cH γ))
    (hSp : ∀ n, 0 < S n) (hCp : ∀ n, 0 < C n)
    (hT : ∀ n, T n = S n * Real.sqrt (C n)) :
    HasLog2Exponent (fun n => Real.logb 2 (T n)) ((3 / 2) * cH γ) ∧
    HasLog2Exponent (fun n => Real.logb 2 (S n + C n)) (cH γ) := by
  constructor
  · -- Time: `log₂ (|S| · √|C|) = log₂ |S| + ½ log₂ |C|`, so the exponent is `c_h + ½ c_h`.
    have hhalf : HasLog2Exponent (fun n => (1 / 2) * Real.logb 2 (C n)) ((1 / 2) * cH γ) :=
      hC.const_mul (by norm_num)
    have hsum := hS.add hhalf
    have hprod : HasLog2Exponent
        (fun n => Real.logb 2 (S n * Real.sqrt (C n))) (cH γ + (1 / 2) * cH γ) :=
      hsum.congr (fun n => by
        have hSpos : (0 : ℝ) < S n := hSp n
        have hCpos : (0 : ℝ) < C n := hCp n
        have hsqrtpos : (0 : ℝ) < Real.sqrt (C n) := Real.sqrt_pos.mpr hCpos
        rw [Real.logb_mul (ne_of_gt hSpos) (ne_of_gt hsqrtpos)]
        rw [show Real.sqrt (C n) = (C n) ^ (1 / 2 : ℝ) from Real.sqrt_eq_rpow (C n)]
        rw [Real.logb_rpow_eq_mul_logb_of_pos hCpos])
    have hcoef : cH γ + (1 / 2) * cH γ = (3 / 2) * cH γ := by ring
    rw [hcoef] at hprod
    exact hprod.congr (fun n => by rw [hT n])
  · -- Space: `O(|S| + |C|)`, bounded by `2 · max |S| |C|`, so exponent `c_h`.
    have hmax := hS.max_exp hC
    have hshift := hmax.add_const 1
    refine hshift.of_le (fun n => ?_)
    have h := logb_two_sum_le (hSp n) (hCp n)
    linarith

end Qatlib.Papers.LatticeSVP13.MainResults.SieveQuantum
