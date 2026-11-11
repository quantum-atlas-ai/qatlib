/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut.SourceCutExpectation
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Main MaxCut lower bound `M_g ≥ c̃_edge(p)` (Eq. (11), p. 4)

Fixed version: arXiv:2503.12789v2 (2026-01-27), Farhi--Gutmann--Ranard--Villalonga.

The paper's main MaxCut statement is Eq. (11), p. 4:

  `M_g ≥ c̃_edge(p)` for any `p ≤ (g − 2)/2`,

where `M_g` is the infimum of `MaxCut(G)/|E(G)|` over 3-regular graphs of girth at
least `g` (Eq. (1)), and `c̃_edge(p) = c_edge(γ̃, β̃)` (Eq. (10)) is the per-edge
expected cost of the depth-`p` QAOA at the near-optimal angles, justified by the
tree-neighborhood decomposition `F_p(γ,β) = |E(G)| c_edge(γ,β)` of Eq. (7) when
`g ≥ 2p + 2`.

The Lean content splits exactly along that argument:

* `SourceCutExpectation.expectedCutFraction_le_maxCut_of_has` is the purely
  combinatorial step "a cut law with expected fraction `c` certifies a cut of
  fraction at least `c`" (Eq. (9));
* every graph of the paper's class carries such a law with `c = c̃_edge(p)`, which
  is the QAOA computation of Sec. 3 and Sec. 5 — recorded explicitly as the
  hypothesis `HasExpectedCutFraction G c`, never asserted as a theorem;
* taking the infimum over the class gives `c ≤ M_g`.

No numerical optimisation or tensor-network contraction is formalized here; that
input enters only through the hypothesis, as the paper does.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut


/-- The set of cut fractions of all 3-regular graphs of girth at least `g` with at
least one edge, i.e. the set whose infimum is the paper's `M_g` in Eq. (1), p. 2. -/
def regularGraphCutFractions (g : ℕ) : Set ℝ :=
  {x : ℝ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      G.IsRegularOfDegree 3 ∧ g ≤ G.girth ∧ 0 < edgeCount G ∧ x = maxCutFraction G}

/-- `M_g`, the smallest possible maximum cut fraction over all 3-regular graphs of
girth at least `g`.  Source Eq. (1), p. 2. -/
noncomputable def Mg (g : ℕ) : ℝ :=
  sInf (regularGraphCutFractions g)

/-- The class of cut fractions is bounded below by `0`. -/
theorem bddBelow_regularGraphCutFractions (g : ℕ) :
    BddBelow (regularGraphCutFractions g) := by
  refine ⟨0, ?_⟩
  rintro x ⟨V, instF, instD, G, instR, hreg, hg, hE, rfl⟩
  exact div_nonneg (by positivity) (by positivity)

/-- Every member of the class is at least `M_g`. -/
theorem Mg_le_member {g : ℕ} {x : ℝ} (hx : x ∈ regularGraphCutFractions g) :
    Mg g ≤ x :=
  csInf_le (bddBelow_regularGraphCutFractions g) hx

/-- **Paper Eq. (11), graph form.** For every 3-regular graph `G` of girth at least
`g` with at least one edge, if the depth-`p` QAOA at angles `(γ,β)` supplies a
cut law with expected cut fraction `c` (Eq. (7)), then `c` is a lower bound on the
cut fraction of `G`.  The paper applies this with `c = c_edge(γ,β)` (Eq. (9)) and
then with `c = c̃_edge(p)` (Eq. (11)). -/
theorem paper_eq11_per_graph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} {c : ℝ}
    (hreg : G.IsRegularOfDegree 3) (hgirth : 2 * p + 2 ≤ G.girth)
    (hE : 0 < edgeCount G) (hQAOA : HasExpectedCutFraction G c) :
    c ≤ maxCutFraction G :=
  expectedCutFraction_le_maxCut_of_has G hE hQAOA

/-- **Paper Eq. (11), `M_g` form.** If every 3-regular graph of girth at least `g`
carries a cut law with expected cut fraction at least `c` (the QAOA computation of
Sec. 3, made possible by the tree neighborhoods whenever `g ≥ 2p + 2`), then
`M_g ≥ c`.  The nonemptiness premise is the paper's implicit fact that the class
of 3-regular graphs of girth at least `g` is inhabited. -/
theorem paper_eq11_Mg {g : ℕ} {c : ℝ}
    (hne : (regularGraphCutFractions g).Nonempty)
    (h : ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsRegularOfDegree 3 → g ≤ G.girth → HasExpectedCutFraction G c) :
    c ≤ Mg g := by
  unfold Mg
  refine le_csInf hne ?_
  rintro x ⟨V, instF, instD, G, instR, hreg, hg, hE, rfl⟩
  exact expectedCutFraction_le_maxCut_of_has G hE (h V G hreg hg)

/-- **Paper Eq. (11) with its printed range.** For `p ≤ (g − 2)/2`, equivalently
`2p + 2 ≤ g`, the QAOA per-edge value `c` is a lower bound on `M_g`.  This is the
literal form of the displayed formula on p. 4. -/
theorem paper_eq11_girth_range {p g : ℕ} (hpg : 2 * p + 2 ≤ g) {c : ℝ}
    (hne : (regularGraphCutFractions g).Nonempty)
    (h : ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsRegularOfDegree 3 → g ≤ G.girth → HasExpectedCutFraction G c) :
    c ≤ Mg g :=
  paper_eq11_Mg hne h

end Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut
