/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Obstruction to a universal greedy entropy certificate

This module proves `fGGS99GreedyCertificate_obstruction` by evaluating the entropy of the
uniform distribution on 2^23 points. Its entropy is 23 bits, which exceeds the universal upper
bound required by `FGGS99GreedyCertificateContract`. The certificate is associated with the
ordered search discussion in [BenOrHassidim2007] and the invariant algorithms of
[FarhiEtAl1999].

## Main statements

* `fGGS99GreedyCertificate_obstruction`: the specified certificate contract is false.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
* [Farhi et al., 1999][FarhiEtAl1999]
-/

set_option autoImplicit false
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- The universal entropy requirement in `FGGS99GreedyCertificateContract` fails for the uniform
distribution on 2^23 points. This refutes the specified certificate associated with the
ordered search discussion in [BenOrHassidim2007]. -/
theorem fGGS99GreedyCertificate_obstruction : ¬ FGGS99GreedyCertificateContract := by
  intro h
  let Q : Fin (2 ^ 23) → ℝ := fun _ => 1 / ((2 : ℝ) ^ 23)
  have hpos : ∀ i, 0 < Q i := by intro i; norm_num [Q]
  have hsum : (∑ i, Q i) = 1 := by
    simp only [Q, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
  have he := h.2.2.2.2 Q hpos hsum
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hlog : Real.log (1 / ((2 : ℝ) ^ 23)) / Real.log 2 = -23 := by
    rw [one_div, Real.log_inv, Real.log_pow]
    field_simp
    norm_num
  simp only [Q, hlog, fggsInfo, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at he
  norm_num at he

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
