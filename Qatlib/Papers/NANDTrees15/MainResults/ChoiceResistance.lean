/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NANDTrees15.MainResults.Model.NandTreeModel
/-!
# Average Choice Complexity, Effective Resistance, and Fault Complexity (Lemma 3)

This module formalizes Lemma 3 (Section 4.1, Equations (8)--(14), pp. 11--13)
of Jeffery and Kimmel equating player-A and player-B average choice complexity
on depth-`2d` NAND-tree instances with effective resistances of the primal and
dual series-parallel networks, and bounding choice complexity above by fault
complexity.

## Main statements

* `lemma3_choiceA_eq_resistance`: `avgChoiceA x = resA x`.
* `lemma3_choiceB_eq_resistance`: `avgChoiceB x = resB x`.
* `lemma3_choice_le_fault`: `choiceComplexity x <= faultComplexity x`.
* `lemma3`: Combined three-clause statement of Lemma 3.

## References

* [Jeffery and Kimmel, 2015][JefferyKimmel2015NANDTrees], Section 4.1, Lemma 3,
  pp. 11--13.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NANDTrees15.MainResults

open Instance
open scoped ENNReal BigOperators

/-- **Lemma 3, first equality** (arXiv:1511.02235v1, p.11–12, eqs. (8)–(14)):
`C_A(x) = R_{s,t}(G_d(x))` for every depth-`2d` instance `x`, by the induction of
the paper's proof of Lemma 3. -/
theorem lemma3_choiceA_eq_resistance {d : ℕ} (x : Instance d) :
    avgChoiceA x = resA x := by
  induction x with
  | leaf b => cases b <;> simp [avgChoiceA, resA]
  | node4 a b c e ih0 ih1 ih2 ih3 =>
      simp only [avgChoiceA, resA, ih0, ih1, ih2, ih3]

/-- **Lemma 3, second equality** (arXiv:1511.02235v1, p.11–12): the player-B version
`C_B(x) = R_{s',t'}(G'_d(x))`, by the "similar analysis for `C_B`" in the proof. -/
theorem lemma3_choiceB_eq_resistance {d : ℕ} (x : Instance d) :
    avgChoiceB x = resB x := by
  induction x with
  | leaf b => cases b <;> simp [avgChoiceB, resB]
  | node4 a b c e ih0 ih1 ih2 ih3 =>
      simp only [avgChoiceB, resB, ih0, ih1, ih2, ih3]

private theorem faultA_dichotomy {d : ℕ} (x : Instance d) :
    (faultA x = 1 ∧ resA x = 1) ∨ faultA x = ⊤ := by
  induction x with
  | leaf b => cases b <;> simp [faultA, resA]
  | node4 a b c e iha ihb ihc ihe =>
      rcases iha with ⟨ha, hra⟩ | ha <;>
        rcases ihb with ⟨hb, hrb⟩ | hb <;>
        rcases ihc with ⟨hc, hrc⟩ | hc <;>
        rcases ihe with ⟨he, hre⟩ | he
      · left
        simp [faultA, resA, parallelRes, ha, hb, hc, he, hra, hrb, hrc, hre,
          one_add_one_eq_two, ENNReal.inv_two_add_inv_two]
      all_goals
        right
        simp only [faultA, ha, hb, hc, he]
        split <;> simp

private theorem faultB_dichotomy {d : ℕ} (x : Instance d) :
    (faultB x = 1 ∧ resB x = 1) ∨ faultB x = ⊤ := by
  induction x with
  | leaf b => cases b <;> simp [faultB, resB]
  | node4 a b c e iha ihb ihc ihe =>
      rcases iha with ⟨ha, hra⟩ | ha <;>
        rcases ihb with ⟨hb, hrb⟩ | hb <;>
        rcases ihc with ⟨hc, hrc⟩ | hc <;>
        rcases ihe with ⟨he, hre⟩ | he
      · left
        simp [faultB, resB, parallelRes, ha, hb, hc, he, hra, hrb, hrc, hre,
          one_add_one_eq_two, ENNReal.inv_two_add_inv_two]
      all_goals
        right
        simp only [faultB, ha, hb, hc, he]
        split <;> simp

/-- **Lemma 3, fault clause** (arXiv:1511.02235v1, p.11, eqs. (9), (12)):
`C(x) ≤ F(x)`, where `F(x) = min{F_A(x), F_B(x)}` is the fault complexity of eq. (6).

Fixed source: arXiv:1511.02235v1.
Paper location: Lemma 3, p.11; inequality proofs at eqs. (9) (fault root) and
(12) (non-fault root), p.12–13.
Key steps of the paper's proof: at a fault root `c(r) = 2` and
`C_A ≤ min_b {F_A(x^{b0}) + F_A(x^{b1})} ≤ min_b max_{b'} 2 F_A(x^{bb'}) ≤ F(x)`
(eq. (9)); at a non-fault root `C_A ≤ (1/2) max_b {F_A(x^{b0}) + F_A(x^{b1})} ≤ F(x)`
(eq. (12)), using the induction hypothesis `C_A(x^τ) ≤ F(x^τ)`.
For the model's recursions, each player's fault complexity is either `1`, with
resistance also `1`, or `⊤`.  The two dichotomy invariants yield the playerwise
bounds, and monotonicity of `min` gives the conclusion. -/
theorem lemma3_choice_le_fault {d : ℕ} (x : Instance d) :
    choiceComplexity x ≤ faultComplexity x := by
  have hA : avgChoiceA x ≤ faultA x := by
    rw [lemma3_choiceA_eq_resistance x]
    rcases faultA_dichotomy x with ⟨hf, hr⟩ | hf
    · simp [hf, hr]
    · simp [hf]
  have hB : avgChoiceB x ≤ faultB x := by
    rw [lemma3_choiceB_eq_resistance x]
    rcases faultB_dichotomy x with ⟨hf, hr⟩ | hf
    · simp [hf, hr]
    · simp [hf]
  exact min_le_min hA hB

/-- **Lemma 3** (arXiv:1511.02235v1, p.11).  For every depth-`2d` nand-tree instance
`x`, the average choice complexity for Player A equals the effective resistance of
`G_d(x)`, the average choice complexity for Player B equals the effective resistance
of the dual graph `G'_d(x)`, and `C(x) ≤ F(x)` where `F` is the fault complexity. -/
theorem lemma3 {d : ℕ} (x : Instance d) :
    avgChoiceA x = resA x ∧ avgChoiceB x = resB x ∧
      choiceComplexity x ≤ faultComplexity x :=
  ⟨lemma3_choiceA_eq_resistance x, lemma3_choiceB_eq_resistance x,
    lemma3_choice_le_fault x⟩

end Qatlib.Papers.NANDTrees15.MainResults
