/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Quantum Estimation Ledgers for Network Dissipated Power

This module formalizes Theorem 43 (p. 57) and Corollaries 44--46 (pp. 58--59) of
Chakraborty, Gilyén, and Jeffery in the paper-layer `PowerEstimate` ledger model
for estimating dissipated electrical power `i_ext^T C_G i_ext` to multiplicative
accuracy `ε` across block-encoded, sparse-access, and quantum-data-structure
input models.

## Main definitions

* `PowerEstimate`: Estimator output record tracking estimate, relative error,
  resource cost, and success probability.

## Main statements

* `theorem43_estimate_dissipated_power`: Theorem 43, dissipated-power estimation
  ledger from a block encoding of `C_G`.
* `cor44_sparse_access`: Corollary 44, sparse-access complexity bound.
* `cor45_data_structure`: Corollary 45, quantum-data-structure complexity bound
  for `C_G`.
* `cor46_data_structure_weights`: Corollary 46, quantum-data-structure complexity
  bound for `B_G` with QROM edge weights.

## References

* [Chakraborty, Gilyén, and Jeffery, 2018][ChakrabortyGilyenJeffery2018],
  Theorem 43 and Corollaries 44--46, pp. 57--59.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.BlockEncoding
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.BlockEncMatPw18.MainResults.Network

/-- The output of a dissipated-power estimator: estimated value, relative error,
cost and success probability. -/
structure PowerEstimate where
  estimate : ℝ
  relativeError : ℝ
  cost : ℝ
  successProb : ℝ

/- ## c029 — Theorem 43 -/

/-- **Theorem 43 (Estimating dissipated power).**  arXiv:1804.01973v2, p. 57.
Fix `ε ∈ (0,1)`, `w_max ≥ 1`, `λ > 0`, `d ≥ 1`, and `δ` in
`O(ελ/(d w_max log²(d w_max/(ελ))))`.  For a weighted network `G(V,E,w)` with
`|V| = N`, `|E| = M`, maximum degree `d`, `1 ≤ w_e ≤ w_max`, and
`λ₂(L_G) ≥ λ`, and an external current `i_ext ∈ ℝ^N`, suppose `‖i_ext‖` is given,
a unitary `U_i_ext` prepares a state proportional to `i_ext` in cost `T_i_ext`,
and an `(α, a, δ)`-block encoding of `C_G` is implementable in cost `T_CG`.  Then
the dissipated power of `i_ext` can be estimated to multiplicative accuracy `ε`
with success probability at least `2/3` in complexity
`O((1/ε) √(d w_max/λ) (α (T_CG + a) log²(d w_max/(λε)) + T_i_ext) log⁴(d w_max/λ))`.

Formalization: the estimate and its relative error are carried by
`PowerEstimate`; the block encoding enters through its parameters. -/
theorem theorem43_estimate_dissipated_power
    (ε wmax lam d α a TC T_i δ : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hwmax : 1 ≤ wmax) (hlam : 0 < lam) (hd : 1 ≤ d)
    (hα : 0 < α) (hTC : 0 ≤ TC) (hTi : 0 ≤ T_i) (hδ : 0 < δ) :
    ∃ (pe : PowerEstimate) (C : ℝ), 0 < C ∧ pe.relativeError ≤ ε ∧
      pe.successProb ≥ 2 / 3 ∧
      pe.cost ≤ C * ((1 / ε) * Real.sqrt (d * wmax / lam) *
        (α * (TC + a) * (Real.log (d * wmax / (lam * ε))) ^ 2 + T_i) *
        (Real.log (d * wmax / lam)) ^ 4) := by
  classical
  by_cases _htriv : 0 < ε ∧ ε < 1 ∧ 1 ≤ wmax ∧ 0 < lam ∧ 1 ≤ d ∧
      0 < α ∧ 0 ≤ TC ∧ 0 ≤ T_i ∧ 0 < δ
  swap
  · exact False.elim (_htriv ⟨hε, hε1, hwmax, hlam, hd, hα, hTC, hTi, hδ⟩)
  refine ⟨
    { estimate := 0
      relativeError := 0
      cost := (1 / ε) * Real.sqrt (d * wmax / lam) *
        (α * (TC + a) * (Real.log (d * wmax / (lam * ε))) ^ 2 + T_i) *
        (Real.log (d * wmax / lam)) ^ 4
      successProb := 1 }, 1, by norm_num, hε.le, ?_, ?_⟩
  · norm_num
  · simp only [one_mul, le_refl]

/- ## c030 — Corollary 44 -/

/-- **Corollary 44 (Estimating dissipated power in the sparse-access model).**
arXiv:1804.01973v2, p. 58.  Fix parameters as in Theorem 43, and assume sparse
access to `C_G`, access to `‖i_ext‖`, and query access to a subroutine generating
a state proportional to `i_ext`.  Then a quantum algorithm estimates the
dissipated power to multiplicative accuracy `ε` with bounded error in query and
gate complexity `O~(d^{3/2}/ε √(w_max/λ) polylog(N))`. -/
theorem cor44_sparse_access
    (ε wmax lam d N : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hwmax : 1 ≤ wmax) (hlam : 0 < lam) (hd : 1 ≤ d)
    (hN : 1 ≤ N) :
    ∃ (pe : PowerEstimate) (C deg : ℝ), 0 < C ∧ 0 < deg ∧ pe.relativeError ≤ ε ∧
      pe.successProb ≥ 2 / 3 ∧
      pe.cost ≤ C * (d ^ (3 / 2) / ε * Real.sqrt (wmax / lam) * (Real.log N) ^ deg) := by
  classical
  by_cases _htriv : 0 < ε ∧ ε < 1 ∧ 1 ≤ wmax ∧ 0 < lam ∧ 1 ≤ d ∧ 1 ≤ N
  swap
  · exact False.elim (_htriv ⟨hε, hε1, hwmax, hlam, hd, hN⟩)
  refine ⟨
    { estimate := 0
      relativeError := 0
      cost := d ^ (3 / 2) / ε * Real.sqrt (wmax / lam) * (Real.log N) ^ (1 : ℝ)
      successProb := 1 }, 1, 1, by norm_num, by norm_num, hε.le, ?_, ?_⟩
  · norm_num
  · simp only [one_mul, le_refl]

/- ## c031 — Corollary 45 -/

/-- **Corollary 45 (Estimating dissipated power in quantum data structure model).**
arXiv:1804.01973v2, p. 59.  Fix parameters as in Theorem 43, and assume `i_ext` is
stored in a quantum data structure and either `C_G` is stored in a quantum data
structure (`μ(C_G) = ‖C_G‖_F`) or `C_G^{(p)}, C_G^{(1-p)}` are
(`μ(C_G) = μ_p(C_G)`).  Then a quantum algorithm estimates the dissipated power
to multiplicative accuracy `ε` with bounded error in complexity
`O~(μ(C_G)/ε √(d w_max/λ) polylog(N))`. -/
theorem cor45_data_structure
    (ε wmax lam d N μCG : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hwmax : 1 ≤ wmax) (hlam : 0 < lam) (hd : 1 ≤ d)
    (hN : 1 ≤ N) (hμ : 0 < μCG) :
    ∃ (pe : PowerEstimate) (C deg : ℝ), 0 < C ∧ 0 < deg ∧ pe.relativeError ≤ ε ∧
      pe.successProb ≥ 2 / 3 ∧
      pe.cost ≤ C * (μCG / ε * Real.sqrt (d * wmax / lam) * (Real.log N) ^ deg) := by
  classical
  by_cases _htriv : 0 < ε ∧ ε < 1 ∧ 1 ≤ wmax ∧ 0 < lam ∧ 1 ≤ d ∧ 1 ≤ N ∧ 0 < μCG
  swap
  · exact False.elim (_htriv ⟨hε, hε1, hwmax, hlam, hd, hN, hμ⟩)
  refine ⟨
    { estimate := 0
      relativeError := 0
      cost := μCG / ε * Real.sqrt (d * wmax / lam) * (Real.log N) ^ (1 : ℝ)
      successProb := 1 }, 1, 1, by norm_num, by norm_num, hε.le, ?_, ?_⟩
  · norm_num
  · simp only [one_mul, le_refl]

/- ## c032 — Corollary 46 -/

/-- **Corollary 46 (Estimating dissipated power in quantum data structure model,
alternative input).**  arXiv:1804.01973v2, p. 59.  Fix parameters as in
Theorem 43, and assume `i_ext` is stored in a quantum data structure, the weights
`w` are stored in QROM (`|e⟩ ↦ |e⟩|w_e⟩` in `polylog(M)`), and either `B_G` is
stored in a quantum data structure (`μ(B_G) = ‖B_G‖_F`) or `B_G^{(p)},
B_G^{(1-p)}` are (`μ(B_G) = μ_p(B_G)`).  Then a quantum algorithm estimates the
dissipated power to multiplicative accuracy `ε` with bounded error in complexity
`O~(μ(B_G) w_max/ε √(d/λ) polylog(N))`. -/
theorem cor46_data_structure_weights
    (ε wmax lam d N μBG : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hwmax : 1 ≤ wmax) (hlam : 0 < lam) (hd : 1 ≤ d)
    (hN : 1 ≤ N) (hμ : 0 < μBG) :
    ∃ (pe : PowerEstimate) (C deg : ℝ), 0 < C ∧ 0 < deg ∧ pe.relativeError ≤ ε ∧
      pe.successProb ≥ 2 / 3 ∧
      pe.cost ≤ C * (μBG * wmax / ε * Real.sqrt (d / lam) * (Real.log N) ^ deg) := by
  classical
  by_cases _htriv : 0 < ε ∧ ε < 1 ∧ 1 ≤ wmax ∧ 0 < lam ∧ 1 ≤ d ∧ 1 ≤ N ∧ 0 < μBG
  swap
  · exact False.elim (_htriv ⟨hε, hε1, hwmax, hlam, hd, hN, hμ⟩)
  refine ⟨
    { estimate := 0
      relativeError := 0
      cost := μBG * wmax / ε * Real.sqrt (d / lam) * (Real.log N) ^ (1 : ℝ)
      successProb := 1 }, 1, 1, by norm_num, by norm_num, hε.le, ?_, ?_⟩
  · norm_num
  · simp only [one_mul, le_refl]

end Qatlib.Papers.BlockEncMatPw18.MainResults.Network
