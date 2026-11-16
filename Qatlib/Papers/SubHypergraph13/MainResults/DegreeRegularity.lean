/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
# SubHypergraph13 — degree regularity (Lemma 8)

Fixed source: Guerreschi--Magniez--Santha, "Quantum Algorithms for Finding
Constant-sized Sub-hypergraphs", arXiv:1310.4127 (2013), **Lemma 8, page 9**.

When `Fᵢⱼ` is a uniformly random set of `fᵢⱼ` pairs from `Vᵢ × Vⱼ`, then with
probability at least

  `1 - 2 rᵢ e^(-fᵢⱼ/(8rᵢ)) - 2 rⱼ e^(-fᵢⱼ/(8rⱼ)) - rⱼ rₖ κ 2^(-11 fᵢⱼ fᵢₖ/(rᵢrⱼrₖ))`

the conditions (b), (c), (d) of the paper hold for `Fᵢⱼ`.  Here `κ` is the
(constant) number of vertices of `H`.  Conditions (b),(c) are `degreeRegular`
and condition (d) is `pairTripleBound` (`SourceModel.lean`).
-/

module

public import Qatlib.Papers.SubHypergraph13.MainResults.SourceModel

@[expose] public section


/-!
# DegreeRegularity

Paper-specific definitions and results for SubHypergraph13.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Papers.SubHypergraph13.MainResults

namespace Qatlib.Papers.SubHypergraph13.MainResults.DegreeRegularity
open Qatlib.Papers.SubHypergraph13.MainResults

/-- Condition (d) plus `|Fⱼₖ| = fⱼₖ` bounds the inner set:
`|Γᵢⱼₖ| ≤ fⱼₖ · 11 fᵢⱼ fᵢₖ/(rᵢrⱼrₖ)`.  This is the deterministic `Mᵢⱼₖ`
consequence used in §4.4 (re-exported from `SourceModel.gammaSet_card_le`). -/
theorem pairTripleBound_gammaSet_card_le {ri rj rk fij fik fjk : ℕ}
    {Fij : Finset (Fin ri × Fin rj)} {Fik : Finset (Fin ri × Fin rk)}
    {Fjk : Finset (Fin rj × Fin rk)}
    (hFjk : Fjk.card = fjk) (hd : pairTripleBound fij fik Fij Fik Fjk) :
    (gammaSet ri rj rk Fij Fik Fjk).card ≤
      (fjk : ℝ) * (11 * (fij : ℝ) * (fik : ℝ) / ((ri : ℝ) * (rj : ℝ) * (rk : ℝ))) :=
  gammaSet_card_le hFjk hd

/-- Each left degree is bounded by the total number of pairs. -/
theorem leftDegree_le_card {ri rj : ℕ} (Fij : Finset (Fin ri × Fin rj)) (u : Fin ri) :
    leftDegree Fij u ≤ Fij.card :=
  Finset.card_filter_le _ _

/-! The remaining paper theorem requires unformalized probabilistic/circuit machinery and is intentionally omitted from this verified leaf. -/

end Qatlib.Papers.SubHypergraph13.MainResults.DegreeRegularity
