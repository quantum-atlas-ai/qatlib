/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.OracleError.SdpAlphaRescaleLemma2Quan

set_option backward.isDefEq.respectTransparency false

/-!
# Source Lemma 2 — reduction to `b_i ≥ 1` (Brandão–Svore 2016)

Fixed source: arXiv:1609.05537v5, printed Lemma 2, page 6, and its proof in
Appendix A (Lemma 18, printed pp. 21–23, Eqs. (98)–(108)).

The reduction has three independent algebraic parts:

1. **coefficient lift** (Appendix A, below Eq. (98)): given `b_i ≥ 1` and
   `R ≥ 0`, the lifted cost vector `(b_1,…,b_m, R+1)` has every entry `≥ 1`.
   The theorem used here is:
   `Qatlib.Concepts.SdpMmwSolver.OracleError.sdpAlphaRescaleLemma2`
   (coverage `partial_support`, `OracleError/SdpAlphaRescaleLemma2Quan`);
2. **sampling conversion** (Eqs. (102)–(108)): if `(y_1,…,y_{m+1})` is a
   δ-optimal solution of the lifted SDP (98), and the lifted
   `(n+1,n+1)` constraint gives `∑_{i≤m+1} y_i ≥ r` (Eq. (103)/(106)), then
   the truncation `(y_1,…,y_m)` satisfies `∑ b_i y_i ≤ opt + δ` — the
   `(R+1)∑ y_i` terms cancel exactly (Eq. (108));
3. **`C`-rescale** (last paragraph of Appendix A): solving the `C/r`-rescaled
   SDP to additive error `δ/r` delivers additive error `δ` for the original.

The operational sampling procedure itself is not modelled; what is formalised
is the exact arithmetic that carries a sampled lifted solution to a δ-optimal
original solution.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SDPBrandao16.MainResults.SourceClaims

open Qatlib.Concepts.SdpMmwSolver.OracleError
open scoped BigOperators

/-! ## §1 Coefficient lift (reuse of the α-rescale contract) -/

/-- **Source Lemma 2 / Lemma 18, coefficient-lift clause (Appendix A, after
Eq. (98)).**

For `b_i ≥ 1`, `R ≥ 0`, `n, m > 0`, `0 < α ≤ R`, `r α ≤ R`, there is a lifted
cost vector `liftedB : Fin (m+1) → ℝ` with `liftedB i ≥ 1` for every `i`,
`liftedB (Fin.last m) = R + 1`, and `liftedB i.castSucc = b_i`; moreover every
nonnegative `bsol` whose scaled objective `∑ bsol_i (b_i/α) ≤ 1 + δ` has
original objective `∑ bsol_i b_i ≤ (1+δ) α`.

The theorem used here is:
`Qatlib.Concepts.SdpMmwSolver.OracleError.sdpAlphaRescaleLemma2`. -/
theorem lemma2_alphaRescale (n m : ℕ) (b : Fin m → ℝ) (R r α δ : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hR : 0 < R) (hr : 0 < r) (hα : 0 < α) (hδ : 0 < δ)
    (hb : ∀ i, 1 ≤ b i) (hαR : α ≤ R) (hrαR : r * α ≤ R) :
    (∃ liftedB : Fin (m + 1) → ℝ,
        (∀ i, 1 ≤ liftedB i) ∧
        liftedB (Fin.last m) = R + 1 ∧
        (∀ i : Fin m, liftedB i.castSucc = b i)) ∧
      (∀ bsol : Fin m → ℝ,
        (∀ i, 0 ≤ bsol i) →
        (∑ i, bsol i * (b i / α)) ≤ 1 + δ →
        (∑ i, bsol i * b i) ≤ (1 + δ) * α) :=
  sdpAlphaRescaleLemma2 n m b R r α δ hn hm hR hr hα hδ hb hαR hrαR

/-! ## §2 Sampling conversion (Eqs. (102)–(108)) -/

/-- **Source Lemma 2 / Lemma 18, sampling-conversion clause (Eqs. (102)–(108)).**

Let `opt` be the optimal objective of the original SDP and let `y` be a
solution of the lifted SDP (98) with last coordinate `ylast`.  Assume:

* `opt = ∑ i, b i * z i` for an optimal original solution `z`
  (so the lifted optimum is at most `opt + (R+1) * (ylast + ∑ y)`, realised by
  the constructed solution `(z_1,…,z_m, ylast + ∑y − ∑z)` of Eqs. (102)/(107));
* the lifted `(n+1,n+1)` constraint gives `r ≤ ylast + ∑ i, y i`
  (Eq. (103)/(106));
* `y` is δ-optimal for the lifted SDP (98), i.e. its lifted objective is at
  most the lifted optimum plus `δ` (Eq. (108) contradiction premise).

Then the truncated vector `(y_1,…,y_m)` satisfies `∑ i, b i * y i ≤ opt + δ`.

The `(R+1) * (ylast + ∑ y)` terms cancel exactly, which is the content of
Eq. (108). -/
theorem lemma2_samplingConversion (m : ℕ) (b z y : Fin m → ℝ) (ylast opt R δ r : ℝ)
    (hopt : opt = ∑ i, b i * z i)
    (hconstraint : r ≤ ylast + ∑ i, y i)
    (hδopt : (∑ i, b i * y i) + (R + 1) * (ylast + ∑ i, y i) ≤
      opt + (R + 1) * (ylast + ∑ i, y i) + δ) :
    ∑ i, b i * y i ≤ opt + δ := by
  -- The lifted `(R+1) * ∑ y` term appears on both sides and cancels (Eq. (108)).
  linarith

/-! ## §3 `C`-rescale (Appendix A, last paragraph) -/

/-- **Source Lemma 2 / Lemma 18, `C`-rescale clause.**

`C` has norm `r > 0`; rescaling it by `1/r` divides both the objective and the
optimal value by `r`.  Hence an additive error `δ/r` on the rescaled problem
yields an additive error `δ` on the original. -/
theorem lemma2_rescale (r δ origObj origOpt : ℝ) (hr : 0 < r)
    (hδ : origObj / r - origOpt / r ≤ δ / r) :
    origObj - origOpt ≤ δ := by
  rw [← sub_div] at hδ
  exact (div_le_div_iff_of_pos_right hr).mp hδ

/-! ## §4 The assembled Lemma 2 reduction -/

/-- **Source Lemma 2 (printed p. 6) / Lemma 18 (printed p. 21): assembled sampling
reduction.**

Given the coefficient lift (`hb`, `hR`), the lifted-constraint reading
`r ≤ ylast + ∑ y` (Eq. (103)) and the sampled lifted solution `y` satisfying the
`δ/r`-rescaled δ-optimality inequality, the truncated vector `(y_1,…,y_m)` is
`δ`-optimal for the original SDP: `∑ i, b i * y i ≤ opt + δ`.

This chains the rescale (cancelling the `C/r`) and the sampling conversion
(cancelling the lifted `(R+1)∑y` term).  The two cancellation steps are exactly
Eq. (108) and the final `C/r` paragraph of Appendix A. -/
theorem lemma2_source (m : ℕ) (b z y : Fin m → ℝ) (ylast opt R r δ : ℝ)
    (hr : 0 < r)
    (hopt : opt = ∑ i, b i * z i)
    (hconstraint : r ≤ ylast + ∑ i, y i)
    (hδoptScaled :
      (((∑ i, b i * y i) + (R + 1) * (ylast + ∑ i, y i)) / r) -
        ((opt + (R + 1) * (ylast + ∑ i, y i)) / r) ≤ δ / r) :
    ∑ i, b i * y i ≤ opt + δ := by
  have h := lemma2_rescale r δ
    ((∑ i, b i * y i) + (R + 1) * (ylast + ∑ i, y i))
    (opt + (R + 1) * (ylast + ∑ i, y i)) hr hδoptScaled
  linarith

end Qatlib.Papers.SDPBrandao16.MainResults.SourceClaims
