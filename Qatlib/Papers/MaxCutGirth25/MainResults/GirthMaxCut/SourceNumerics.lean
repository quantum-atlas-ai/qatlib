/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut.SourceMainBound
public import Mathlib.Tactic

@[expose] public section


/-!
# Numerical values of Table 1 and the comparison with previous bounds
(Sec. 1 p. 2, Sec. 5.1 p. 6, Sec. 6 p. 8)

Fixed version: arXiv:2503.12789v2 (2026-01-27), Farhi--Gutmann--Ranard--Villalonga.

This module records the numerical side of the paper's main claim:

* Table 1 (p. 6) gives `c̃_edge(p)` for `p = 1, …, 17`, quoted to four digits;
  the values are encoded in `table1Value`, and the entry at `p = 17` is
  `0.8971` (`table1_value_17`), the value quoted in Sec. 1, p. 2;
* combining the main claim with the `p = 17` value yields the guaranteed cut fraction
  `0.8971` for every 3-regular graph of girth at least `36`
  (`paper_cut_guarantee_at_17`) and the lower bound `M_36 ≥ 0.8971`
  (`M36_ge_08971`);
* the Thompson--Parekh--Marwaha bound of [4] has limiting value `0.8918`, which
  the QAOA values at `p = 15, 17` exceed (`paper_exceeds_TPM_limit`); because
  `2·15 + 2 = 32`, this proves the paper's statement that it is exceeded at
  girth `32` (`paper_exceeds_TPM_at_girth_32`);
* the remaining literature claims — that the QAOA bounds are the best known for
  `g ≥ 16` and that `lim_{g→∞} M_g ≥ 0.912` follows from [5], [6] — are
  external results.  The latter (`lim_{g→∞} M_g ≥ 0.912`, cited from Csóka
  et al. [5] and Gamarnik–Li [6]) is a deferred obligation of this development:
  neither reference has a Lean development, and the claim concerns a limit of
  infima over all 3-regular high-girth graphs.

No new axiom and no `native_decide` is used; every statement in this module is
proved.  The external limit bound is recorded as a deferred obligation of this
development.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open scoped BigOperators
open Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut

namespace Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut


/-- Table 1, p. 6: the per-edge QAOA value `c̃_edge(p) = c_edge(γ̃, β̃)` at the
near-optimal angles, for `p = 1, …, 17` (quoted to four digits), and `0` outside
the tabulated range. -/
noncomputable def table1Value : ℕ → ℝ
  | 1 => 6924 / 10000
  | 2 => 7559 / 10000
  | 3 => 7923 / 10000
  | 4 => 8168 / 10000
  | 5 => 8363 / 10000
  | 6 => 8498 / 10000
  | 7 => 8597 / 10000
  | 8 => 8673 / 10000
  | 9 => 8734 / 10000
  | 10 => 8784 / 10000
  | 11 => 8825 / 10000
  | 12 => 8859 / 10000
  | 13 => 8888 / 10000
  | 14 => 8913 / 10000
  | 15 => 8935 / 10000
  | 16 => 8954 / 10000
  | 17 => 8971 / 10000
  | _ => 0

/-- Table 1, p. 6: `c̃_edge(17) = 0.8971`, the value singled out in Sec. 1, p. 2
and used for the girth-36 guarantee. -/
theorem table1_value_17 : table1Value 17 = (8971 : ℝ) / 10000 := rfl

/-- Table 1, p. 6: `c̃_edge(1) = 0.6924`. -/
theorem table1_value_one : table1Value 1 = (6924 : ℝ) / 10000 := rfl

/-- Table 1 is nondecreasing and attains its maximum at `p = 17`: every tabulated
value is at most `0.8971`. -/
theorem table1_le_value17 : ∀ p : ℕ, 1 ≤ p → p ≤ 17 → table1Value p ≤ (8971 : ℝ) / 10000 := by
  intro p hp1 hp17
  interval_cases p <;> norm_num [table1Value]

/-- The Thompson--Parekh--Marwaha limiting guarantee is `0.8918` (Sec. 6, p. 8).
The QAOA values at `p = 15` and `p = 17` exceed it. -/
theorem paper_exceeds_TPM_limit :
    (8918 : ℝ) / 10000 < table1Value 15 ∧ (8918 : ℝ) / 10000 < table1Value 17 := by
  constructor <;> norm_num [table1Value]

/-- Sec. 6, p. 8: "the limit as `g` goes to infinity of their bound is `0.8918`
which we exceed at girth `32`".  Since `p = 15` is admissible at girth `32`
(`2·15 + 2 = 32`) and `c̃_edge(15) = 0.8935 > 0.8918`, the QAOA guarantee exceeds
the TPM limiting guarantee for every girth at least `32`. -/
theorem paper_exceeds_TPM_at_girth_32 :
    ∀ g : ℕ, 32 ≤ g → ∃ p : ℕ, 2 * p + 2 ≤ g ∧ (8918 : ℝ) / 10000 < table1Value p := by
  intro g hg
  exact ⟨15, by omega, (paper_exceeds_TPM_limit).1⟩

/-- The main claim at `p = 17`: every 3-regular graph of girth at least `36` whose depth-17
QAOA cut law has expected fraction `0.8971` has maximum cut fraction at least
`0.8971`.  This is the "guaranteed cut fraction of 0.8971" of Sec. 1, p. 2. -/
theorem paper_cut_guarantee_at_17 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 3) (hgirth : 36 ≤ G.girth) (hE : 0 < edgeCount G)
    (hQAOA : HasExpectedCutFraction G ((8971 : ℝ) / 10000)) :
    (8971 : ℝ) / 10000 ≤ maxCutFraction G := by
  have hg : 2 * 17 + 2 ≤ G.girth := by norm_num; exact hgirth
  exact paper_eq11_per_graph G hreg hg hE hQAOA

/-- Sec. 1 p. 2 combined with the main claim: `M_36 ≥ 0.8971`.  Nonemptiness of the class
of 3-regular graphs of girth at least `36` and the QAOA cut-law input are explicit
hypotheses, matching `paper_eq11_Mg`. -/
theorem M36_ge_08971
    (hne : (regularGraphCutFractions 36).Nonempty)
    (h : ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsRegularOfDegree 3 → 36 ≤ G.girth →
        HasExpectedCutFraction G ((8971 : ℝ) / 10000)) :
    (8971 : ℝ) / 10000 ≤ Mg 36 :=
  paper_eq11_Mg hne h

/-- The limiting value of `M_g` as `g → ∞`, expressed as the supremum of the
finite-girth bounds.  The sequence `g ↦ M_g` is nondecreasing (`M_g` is an
infimum over the shrinking class of graphs of girth at least `g`), so this
supremum is the paper's `lim_{g→∞} M_g`. -/
noncomputable def limMg : ℝ := sSup (Set.range (fun g : ℕ => Mg g))


end Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut
