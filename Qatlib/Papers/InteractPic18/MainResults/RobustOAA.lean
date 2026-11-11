/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.RobustCoherentImplementation

/-!
# RobustOAA — Lemma 14 of InteractPic18

Low--Wiebe, *Hamiltonian Simulation in the Interaction Picture*,
fixed arXiv:1805.00675v2.

* Lemma 14 (Appendix B p. 27, quoted from [8]): robust oblivious amplitude
  amplification. Around a `(2, ε)` block encoding `U` of a unitary `V`, the
  compressed cubic response `3A - 4AA†A` (`A = ⟨0|U|0⟩`) is within
  `(3 + 3ε/2 + ε²/2)·ε` of `V`; consequently the amplified operator
  `coherentOAAOperator U R` is a `(1, (3 + 3ε/2 + ε²/2)ε)` block encoding of
  `V`. For `ε ≤ 1` this error is at most `5ε`, the form used in the paper's
  proof of Theorem 3.

Formalized content: the compressed cubic error bound of Lemma 14, the
`(1, error)` amplified encoding it yields, the `≤ 5ε` small-error form, and
the three-query/four-macro cost of the cubic amplification word.

Boundary: the amplification is stated for a single cubic application; the
paper's `n`-fold repetition with accumulated `n·√(2·error)` is the frozen
`coherent_oaa_clean_workspace_error` and is not restated here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.CoherentSim.CoherentOAA
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.InteractPic18.MainResults.RobustOAA

/-- **Lemma 14, cubic error** (fixed arXiv:1805.00675v2, Appendix B p. 27): if
`U` is a `(2, ε)` block encoding of the unitary `V` in the frame `R`, then one
cubic amplification step is within the paper's explicit error
`(3 + 3ε/2 + ε²/2)·ε` of `V`. -/
theorem lemma14_robust_oaa_error {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (V : Matrix I I ℂ) (U : Matrix H H ℂ)
    (R : Matrix H I ℂ) (ε : ℝ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (h : BlockEncoding V U R R 2 ε) :
    ‖compress R (coherentOAAOperator U R) R - V‖ ≤
      (3 + 3 * ε / 2 + ε ^ 2 / 2) * ε := by
  have herr := (coherent_oaa_compressed_error V U R ε hV h).2
  have heq : coherentOAAError ε = (3 + 3 * ε / 2 + ε ^ 2 / 2) * ε := by
    unfold coherentOAAError
    ring
  rwa [heq] at herr

/-- **Lemma 14, amplified block encoding** (fixed arXiv:1805.00675v2, Appendix
B p. 27): the amplified operator `coherentOAAOperator U R` is a `(1, ε')`
block encoding of `V` with `ε' = (3 + 3ε/2 + ε²/2)·ε`. -/
theorem lemma14_amplified_block_encoding {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (V : Matrix I I ℂ) (U : Matrix H H ℂ)
    (R : Matrix H I ℂ) (ε : ℝ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (h : BlockEncoding V U R R 2 ε) :
    BlockEncoding V (coherentOAAOperator U R) R R 1 (coherentOAAError ε) := by
  have hR : IsIsometry R := h.right_isometry
  have hW : coherentOAAOperator U R ∈ Matrix.unitaryGroup H ℂ :=
    (coherent_oaa_word_correct U R hR h.unitary).2.2.2.1
  obtain ⟨heta, herr⟩ := coherent_oaa_compressed_error V U R ε hV h
  refine ⟨hW, hR, hR, by norm_num, heta, ?_⟩
  simpa only [one_smul, norm_sub_rev] using herr

/-- **Lemma 14, small-error form** (fixed arXiv:1805.00675v2, Appendix B):
for `0 ≤ ε ≤ 1` the cubic error `(3 + 3ε/2 + ε²/2)·ε` is at most `5ε`, the
form used in the proof of Theorem 3 and in Eq. (B7). -/
theorem lemma14_error_le_five (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    coherentOAAError ε ≤ 5 * ε := by
  have hsq : ε * ε ≤ ε := by
    have := mul_le_mul_of_nonneg_left h1 h0
    simpa using this
  unfold coherentOAAError
  nlinarith [hsq, h0, h1]

/-- **Lemma 14, cubic word cost** (fixed arXiv:1805.00675v2, Appendix B): one
amplification step is the compiled cubic word, using exactly three queries and
four phase macros. -/
theorem lemma14_cubic_word_cost {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (U : Matrix H H ℂ) (R : Matrix H I ℂ)
    (hR : IsIsometry R) (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    adjointQueryCount (coherentOAAWord R) = 3 ∧
      adjointGateCount (coherentOAAWord R) = 4 := by
  obtain ⟨-, hq, hg, -⟩ := coherent_oaa_word_correct U R hR hU
  exact ⟨hq, hg⟩

end Qatlib.Papers.InteractPic18.MainResults.RobustOAA
