/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup.SourceNLFTModel
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Theorem 3: smoothness implies decay (c004)

Fixed source: arXiv:2603.02021v1 (2026-03-02), Theorem 3, (1.7)–(1.8), p.4.

If `(a, b)` is the NLFT image of `F ∈ ℓ²(ℤ)`, `a*` is outer in `𝔻`,
`a b* ∈ H^s(𝕋)` with `s ≥ 1` and `(a b*)' ∈ L∞(𝕋)`, then

`|F_n| ≲_s a*(0)/|n|^s · (1 + ‖b/a*‖_{H^s}) · max(1, ‖(b/a*)'‖^{⌈s⌉}_{L∞})`,

with the improved `L²` bound `|F_n| ≤ 2a*(0)/|n| · ‖(b/a*)'‖_{L²}` when `s = 1`.

The paper's proof (pp.13–15) has three ingredients:
1. the *layer-stripping* formula `F_n = (z^{-n} b_n)(∞)/a_n(∞)` (p.13), reducing
   `|F_n|` to a single Fourier coefficient `|b̂_n(n)|` of the truncated data;
2. the *linear Fourier decay* bound `|b̂_n(n)| ≤ |n|^{-s} ‖b_n‖_{H^s}` (p.13,
   (4.2)), which is purely about the Sobolev norm;
3. the *Kato–Ponce fractional Leibniz rule* (4.1) bounding `‖b_n‖_{H^s}` by the
   NLFT data.

Here we formalize ingredient 2 in its sharpest algebraic form: the `H^s` norm
dominates each individual (weighted) Fourier coefficient term.  The layer-stripping
formula, the Kato–Ponce estimate and the NLFT-specific assembly are not
formalized.

The full statement is recorded for reference:

```
theorem decay_estimate (W : StrongBeurlingWeight) (F : ℤ → ℂ) (a b : CircleT → ℂ)
    (hF : MemL2 F) (himg : IsNLFTImage F a b) (hout : IsOuterInD W (starFun a))
    {s : ℝ} (hs : 1 ≤ s) (hab : MemHS s (fun x => a x * starFun b x)) ... :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℤ, n ≠ 0 → ‖F n‖ ≤ C * ...
```
-/

open scoped BigOperators
open MeasureTheory Filter Topology

set_option autoImplicit false

open Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup

namespace Qatlib.Papers.SU2Fourier26.MainResults

noncomputable section

/-- The `H^s` norm dominates each weighted Fourier coefficient (the linear
Fourier-decay estimate used at arXiv:2603.02021v1, p.13, (4.2)): for a circle
function `f ∈ H^s(𝕋)` and any `n : ℤ`,
`(1 + n²)^s · |f̂(n)|² ≤ ‖f‖²_{H^s}`.  This is the single-term bound that,
after the rearrangement `(1 + n²)^s ≥ |n|^{2s}`, yields the paper's
`|f̂(n)| ≤ |n|^{-s} ‖f‖_{H^s}`. -/
theorem sobolevNorm_term_bound (s : ℝ) (f : CircleT → ℂ) (h : MemHS s f) (n : ℤ) :
    (1 + (n : ℝ) ^ 2) ^ s * ‖fourierCoeff f n‖ ^ 2 ≤ sobolevNorm s f ^ 2 := by
  have hnonneg : ∀ m : ℤ,
      0 ≤ (1 + (m : ℝ) ^ 2) ^ s * ‖fourierCoeff f m‖ ^ 2 :=
    fun m => mul_nonneg (Real.rpow_nonneg (by positivity) s) (sq_nonneg _)
  have hS : 0 ≤ ∑' m : ℤ, (1 + (m : ℝ) ^ 2) ^ s * ‖fourierCoeff f m‖ ^ 2 :=
    tsum_nonneg hnonneg
  have hterm : (1 + (n : ℝ) ^ 2) ^ s * ‖fourierCoeff f n‖ ^ 2 ≤
      ∑' m : ℤ, (1 + (m : ℝ) ^ 2) ^ s * ‖fourierCoeff f m‖ ^ 2 :=
    h.le_tsum n (fun j _ => hnonneg j)
  rw [sobolevNorm, Real.sq_sqrt hS]
  exact hterm

end

end Qatlib.Papers.SU2Fourier26.MainResults
