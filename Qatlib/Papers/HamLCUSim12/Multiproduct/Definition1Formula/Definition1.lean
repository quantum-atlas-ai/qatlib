/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductMomentHami
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoeffClosedFormHami

set_option backward.isDefEq.respectTransparency false

/-!
# Definition 1 — the multi-product formula `M_{k,chi}`

Fixed source: arXiv:1202.5822v1, Definition 1, p.5, Eqs. (15)-(17):

`M_{k,chi}(t) := sum_{q=1}^{k+1} C_q S_chi(t/ell_q)^{ell_q}`,
with `ell_q = q` for `q <= k`, `ell_{k+1} = e^{gamma(k+1)}`, and the explicit
coefficients `C_q` of Eq. (17).

This module records the definition in the frozen coefficient system
(`mNode`/`mCoeff`, which encode Eqs. (16)/(17) verbatim) and proves the two defining
properties used everywhere downstream: normalization `sum_q C_q = 1` and the moment
annihilations `sum_q C_q / ell_q^{2m} = 0` (`m = 1, ..., k`) of Eq. (19), plus the
closed form of the coefficients.  Reuses frozen
`MultiproductMoment.multiproductMoment` and
`MultiproductCoeffClosedForm.multiproductCoeffClosedForm`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HamLCUSim12.Multiproduct.Definition1Formula

open Qatlib.Papers.HamLCUSim12.Multiproduct

/-- The generic linear combination `M(t) = sum_q C_q U_q` of Eq. (15), with the
paper's coefficients of Eq. (17); `S q` is the term `S_chi(t/ell_q)^{ell_q}`. -/
def multiproductFormula {I : Type} (k : ℕ) (N : ℝ)
    (S : Fin (k + 1) → Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ q, (mCoeff k N q : ℂ) • S q

/-- Fixed arXiv:1202.5822v1, Eq. (16): the repetition nodes are `ell_q = q+1`
(paper index `q <= k`) and `ell_{k+1} = N = e^{gamma(k+1)}`. -/
theorem definition1_nodes (k : ℕ) (N : ℝ) :
    (∀ q : Fin (k + 1), (q : ℕ) < k → mNode k N q = ((q : ℕ) + 1 : ℝ)) ∧
      mNode k N (Fin.last k) = N := by
  refine ⟨?_, ?_⟩
  · intro q hq
    simp [mNode, hq]
  · simp [mNode]

/-- Fixed arXiv:1202.5822v1, Definition 1 Eqs. (15)-(17) and Eq. (19): for distinct
nodes `N > 0`, `N notin {1,...,k}`, the coefficients satisfy `sum_q C_q = 1` and
`sum_q C_q / ell_q^{2m} = 0` for `m = 1, ..., k`. -/
theorem definition1_moments (k : ℕ) (N : ℝ) (hN : 0 < N) (hd : NodesDistinct k N) :
    (∑ q : Fin (k + 1), mCoeff k N q = 1) ∧
      (∀ m : ℕ, 1 ≤ m → m ≤ k →
        (∑ q : Fin (k + 1), mCoeff k N q / mNode k N q ^ (2 * m)) = 0) :=
  multiproductMoment k N hN hd

/-- Fixed arXiv:1202.5822v1, Eq. (17) closed form: for `q < k`,
`C_q ((q+1)^2 - N^2) (k+q+1)! (k-q-1)! = (-1)^{k-q-1} 2 (q+1)^{2(k+1)}`. -/
theorem definition1_coeff_closed_form (k : ℕ) (hk : 1 ≤ k) (N : ℝ)
    (hN : 0 < N) (hd : NodesDistinct k N) (q : Fin (k + 1)) (hq : (q : ℕ) < k) :
    mCoeff k N q * (((q : ℕ) + 1 : ℝ) ^ 2 - N ^ 2)
        * (((k + (q : ℕ) + 1).factorial : ℝ) * (((k : ℕ) - (q : ℕ) - 1).factorial : ℝ))
      = (-(1 : ℝ)) ^ ((k - (q : ℕ) - 1 : ℕ)) * 2 * (((q : ℕ) + 1 : ℝ) ^ (2 * (k + 1))) :=
  multiproductCoeffClosedForm k hk N hN hd q hq

end Qatlib.Papers.HamLCUSim12.Multiproduct.Definition1Formula
