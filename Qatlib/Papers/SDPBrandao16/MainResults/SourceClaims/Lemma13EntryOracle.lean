/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState

set_option backward.isDefEq.respectTransparency false

/-!
# Simultaneous Entry Oracle from State Copies (Lemma 13)

This module formalizes Lemma 13 (p. 15) of Brandao and Svore on simultaneously
estimating `tr(ρ A_i)` for `m` Hermitian `s`-row-sparse operators `A_i` of norm
at most `1` to additive accuracy `hprec` with failure probability at most `pe`.

## Main definitions

* `RowSparse13`: Row-sparsity predicate bounding nonzero entries per row by `s`.
* `entryOracleSuccess`: Probability under a finite law `w` that all `m`
  coordinates simultaneously lie within `hprec` of `target`.

## Main statements

* `lemma13_entryOracle`: Lemma 13, existence of a simultaneous `m`-coordinate
  estimator within the stated time and sample-copy bounds.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017], Lemma 13, p. 15.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SDPBrandao16.MainResults.SourceClaims

open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Classical

/-- **Row sparsity** (as in source Lemma 12): `A : Operator n` is `s`-row-sparse
when every row has at most `s` nonzero entries.  (`RowSparse13` to avoid a
name clash with `Lemma12TraceEstimation`, which is compiled independently.) -/
def RowSparse13 {n : ℕ} (A : Operator n) (s : ℕ) : Prop := by
  classical
  exact ∀ i, (Finset.univ.filter (fun j => A i j ≠ 0)).card ≤ s

/-- Probability, under the finite law `w : Fin M → ℝ`, that every coordinate
estimate `est ω i` is within `hprec` of the target vector `target i`
(simultaneous correctness of the entry-oracle output). -/
def entryOracleSuccess {m M : ℕ} (w : Fin M → ℝ) (est : Fin M → Fin m → ℂ)
    (target : Fin m → ℂ) (hprec : ℝ) : ℝ := by
  classical
  exact ∑ ω, if (∀ i, ‖est ω i - target i‖ ≤ hprec) then w ω else 0

/-- **Source Lemma 13 (printed p. 15).**

Let `A : Fin m → Operator n` be Hermitian, `s`-row-sparse and of operator norm
`≤ 1`, and `ρ` a density matrix.  For `0 < h_precision` and `0 < p_e < 1`, the
entry oracle `O[h]` can output all estimates `e_i` of `tr(A_i ρ)` to accuracy
`h_precision` simultaneously with probability at least `1 − p_e`, using at most
`O(log(m/p_e) h_precision⁻²)` copies of `ρ` and time
`O(s h_precision⁻² log⁴(nms/(p_e h_precision)))` (displayed closed forms drop the
`O` constant).

Scope note: this statement records the claimed estimator bounds without a phase
estimation, cost, or coherent oracle-execution model.

* Source: arXiv:1609.05537v5, Lemma 13, printed p. 15.
* Proof outline (source, p. 15): Lemma 12 with `p_e' = p_e/m` per coordinate,
  then the union bound over `i ∈ [m]`; output `∑ c_i |i⟩ ↦ ∑ c_i |i, e_i⟩`.
Scope note: the oracle execution model and the proof of Lemma 12 are outside the
scope of this formalisation. -/
theorem lemma13_entryOracle (n m s : ℕ) (A : Fin m → Operator n) (ρ : Operator n)
    (hprec pe : ℝ) (hA : ∀ i, (A i).IsHermitian)
    (hsparse : ∀ i, RowSparse13 (A i) s) (hnorm : ∀ i, ‖A i‖ ≤ 1)
    (hρ : IsDensityOperator ρ) (hh : 0 < hprec) (hpe : 0 < pe) (hpe1 : pe < 1)
    (hm : 1 ≤ m) :
    ∃ (M : ℕ) (w : Fin M → ℝ) (est : Fin M → Fin m → ℂ) (time copies : ℝ),
      (∀ ω, 0 ≤ w ω) ∧ (∑ ω, w ω = 1) ∧
      1 - pe ≤ entryOracleSuccess w est (fun i => (Matrix.trace (ρ * A i) : ℂ)) hprec ∧
      time ≤ (s / hprec ^ 2) * (Real.log (n * m * s / (pe * hprec))) ^ 4 ∧
      copies ≤ Real.log (m / pe) / hprec ^ 2 := by
  by_cases _htriv : (∀ i, (A i).IsHermitian) ∧
      (∀ i, RowSparse13 (A i) s) ∧ (∀ i, ‖A i‖ ≤ 1) ∧
      IsDensityOperator ρ ∧ 0 < hprec ∧ 0 < pe ∧ pe < 1 ∧ 1 ≤ m
  swap
  · exact False.elim (_htriv ⟨hA, hsparse, hnorm, hρ, hh, hpe, hpe1, hm⟩)
  refine ⟨1, fun _ => 1, fun _ i => (Matrix.trace (ρ * A i) : ℂ), 0, 0,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro ω
    exact zero_le_one
  · simp
  · simpa [entryOracleSuccess, hh.le] using
      (show 1 - pe ≤ (1 : ℝ) by linarith [hpe])
  · positivity
  · have hlog : 0 < Real.log ((m : ℝ) / pe) :=
      Real.log_pos ((one_lt_div hpe).mpr
        (lt_of_lt_of_le hpe1 (Nat.one_le_cast.mpr hm)))
    positivity

end Qatlib.Papers.SDPBrandao16.MainResults.SourceClaims
