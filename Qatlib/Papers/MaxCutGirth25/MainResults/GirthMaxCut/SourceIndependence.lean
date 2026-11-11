/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut.SourceCutExpectation
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# The independence-ratio bound (Sec. 7, Eq. (15)--(24), p. 9--11)

Fixed version: arXiv:2503.12789v2 (2026-01-27), Farhi--Gutmann--Ranard--Villalonga.

The paper converts its MaxCut bound into an independence-ratio bound:

* Eq. (16)--(19): for any vertex bipartition `S | Sᶜ`, the two induced subgraphs
  contain disjoint independent sets whose combined fraction `w` satisfies
  `w ≥ 1 − |E|/|V| + C(b)/|V|`, which for a 3-regular graph is
  `w ≥ (3/2) C(b)/|E| − 1/2` (Eq. (19));
* Eq. (23): since one of the two sets has at least half the combined vertices,
  `ir ≥ (3/4) C(b)/|E| − 1/4` for every cut `b`;
* Eq. (24): averaging over the QAOA cut law (the same `HasExpectedCutFraction`
  input as the main MaxCut bound) gives `ir ≥ (3/4) c̃_edge(p) − 1/4`.

The combinatorial input is the paper's greedy claim that a vertex set `S` with
`e(S)` internal edges contains an independent set of size at least `|S| − e(S)`;
it is proved here by induction on `e(S)` (`exists_indepSet_card_ge`), using only
finite counting over `Finset`.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of edges of `G` with both endpoints in `S`, the paper's internal
edge count `e(S)` implicit in Eq. (16)--(18). -/
def edgesInside (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e => e.toFinset ⊆ S)).card

/-- Inside-edge count is monotone under set inclusion. -/
theorem edgesInside_mono (G : SimpleGraph V) [DecidableRel G.Adj] {S T : Finset V}
    (hST : S ⊆ T) : edgesInside G S ≤ edgesInside G T := by
  unfold edgesInside
  exact Finset.card_le_card (fun e he => by
    rw [Finset.mem_filter] at he ⊢
    exact ⟨he.1, he.2.trans hST⟩)

/-- Erasing one endpoint of an internal edge strictly decreases the inside-edge
count, the key counting step of the paper's greedy removal. -/
theorem edgesInside_erase_lt (G : SimpleGraph V) [DecidableRel G.Adj] {S : Finset V}
    {u v : V} (huS : u ∈ S) (hvS : v ∈ S) (huv : u ≠ v) (hadj : G.Adj u v) :
    edgesInside G (S.erase u) < edgesInside G S := by
  classical
  have hsub : (G.edgeFinset.filter (fun e => e.toFinset ⊆ S.erase u)) ⊆
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ S)) := by
    intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨he.1, he.2.trans (Finset.erase_subset u S)⟩
  have hnot : s(u, v) ∉
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ S.erase u)) := by
    rw [Finset.mem_filter]
    rintro ⟨-, hsube⟩
    have hu_mem : u ∈ (s(u, v)).toFinset := by
      rw [Sym2.toFinset_mk_eq]; simp
    have := hsube hu_mem
    exact (Finset.mem_erase.mp this).1 rfl
  have hmem : s(u, v) ∈ (G.edgeFinset.filter (fun e => e.toFinset ⊆ S)) := by
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hadj
    · rw [Sym2.toFinset_mk_eq]
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact huS
      · exact hvS
  have hproper : (G.edgeFinset.filter (fun e => e.toFinset ⊆ S.erase u)) ⊂
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ S)) := by
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨hsub, fun heq => hnot (heq ▸ hmem)⟩
  exact Finset.card_lt_card hproper

/-- If `S` has no internal edge, then `S` is independent. -/
theorem isIndepSet_of_edgesInside_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} (h0 : edgesInside G S = 0) : G.IsIndepSet S := by
  classical
  intro x hx y hy hxy hadj
  have hmem : s(x, y) ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hadj
  have hsub : (s(x, y)).toFinset ⊆ S := by
    rw [Sym2.toFinset_mk_eq]
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hpos : 0 < edgesInside G S := by
    unfold edgesInside
    exact Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨hmem, hsub⟩⟩
  omega

/-- **Paper's greedy claim, Eq. (16) discussion p. 9.** A vertex set `S` with
`e(S)` internal edges contains an independent set of size at least `|S| − e(S)`.
Proved by induction on `e(S)`: if `e(S) = 0` take `S` itself; otherwise delete one
endpoint of an internal edge, apply the induction hypothesis to `S.erase u`, and
note that `|S| = |S.erase u| + 1` while `e(S.erase u) + 1 ≤ e(S)`. -/
theorem exists_indepSet_card_ge (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ∃ A ⊆ S, G.IsIndepSet A ∧ S.card ≤ A.card + edgesInside G S := by
  classical
  suffices h : ∀ n : ℕ, ∀ S : Finset V, edgesInside G S = n →
      ∃ A ⊆ S, G.IsIndepSet A ∧ S.card ≤ A.card + edgesInside G S by
    exact h (edgesInside G S) S rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hS
    by_cases hzero : edgesInside G S = 0
    · exact ⟨S, Finset.Subset.refl S, isIndepSet_of_edgesInside_eq_zero G hzero, by simp [hzero]⟩
    · have hpos : 0 < edgesInside G S := Nat.pos_of_ne_zero hzero
      -- Extract an internal edge `u -- v`.
      unfold edgesInside at hpos
      obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter] at he
      obtain ⟨he_mem, he_sub⟩ := he
      have hcard2 : e.toFinset.card = 2 :=
        SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, he_mem⟩
      obtain ⟨u, v, huv, heuv⟩ := Finset.card_eq_two.mp hcard2
      have huS : u ∈ S := by
        apply he_sub; rw [heuv]; simp
      have hvS : v ∈ S := by
        apply he_sub; rw [heuv]; simp
      have hadj : G.Adj u v := by
        have hu : u ∈ e := by
          rw [← Sym2.mem_toFinset, heuv]; simp
        have hv : v ∈ e := by
          rw [← Sym2.mem_toFinset, heuv]; simp
        have heq : e = s(u, v) := (Sym2.mem_and_mem_iff huv).mp ⟨hu, hv⟩
        have hmem : s(u, v) ∈ G.edgeSet := heq ▸ (SimpleGraph.mem_edgeFinset.mp he_mem)
        rwa [SimpleGraph.mem_edgeSet] at hmem
      have hlt0 : edgesInside G (S.erase u) < edgesInside G S :=
        edgesInside_erase_lt G huS hvS huv hadj
      have hlt : edgesInside G (S.erase u) < n := by omega
      obtain ⟨A, hAerase, hAind, hAcard⟩ := ih (edgesInside G (S.erase u)) hlt (S.erase u) rfl
      refine ⟨A, hAerase.trans (Finset.erase_subset u S), hAind, ?_⟩
      have hSadd : (S.erase u).card + 1 = S.card := Finset.card_erase_add_one huS
      have hstep : edgesInside G (S.erase u) + 1 ≤ edgesInside G S := by omega
      omega

/-- The inside-edge counts of a cut and its complement plus the crossing count
give the total edge count: every edge is internal to `S`, internal to `Sᶜ`, or
crossing (Eq. (16)--(17) rewritten, p. 9--10). -/
theorem edgesInside_add_cutNum (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    edgesInside G S + edgesInside G Sᶜ + cutNum G S = edgeCount G := by
  classical
  set s := G.edgeFinset
  set p : Sym2 V → Prop := fun e => e.toFinset ⊆ S
  set q : Sym2 V → Prop := fun e => e.toFinset ⊆ Sᶜ
  have h1 : (s.filter p).card + (s.filter (fun e => ¬ p e)).card = s.card :=
    Finset.card_filter_add_card_filter_not (s := s) (p := p)
  -- On an edge, being inside `Sᶜ` forces not being inside `S`.
  have hqimp : ∀ e ∈ s, q e → ¬ p e := by
    intro e he hq hp
    have hsub : e.toFinset ⊆ S ∩ Sᶜ := Finset.subset_inter hp hq
    have hempty : e.toFinset = ∅ := by
      have hsub' : e.toFinset ⊆ (∅ : Finset V) := by
        simpa [Finset.inter_compl] using hsub
      exact Finset.subset_empty.mp hsub'
    have hc2 : e.toFinset.card = 2 :=
      SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, he⟩
    rw [hempty] at hc2
    simp at hc2
  have hfilt : (s.filter (fun e => ¬ p e)).filter q = s.filter q := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨he, hnp⟩, hq⟩; exact ⟨he, hq⟩
    · rintro ⟨he, hq⟩; exact ⟨⟨he, hqimp e he hq⟩, hq⟩
  have h2 : (s.filter q).card +
      ((s.filter (fun e => ¬ p e)).filter (fun e => ¬ q e)).card =
      (s.filter (fun e => ¬ p e)).card := by
    rw [← hfilt]
    exact Finset.card_filter_add_card_filter_not (s := s.filter (fun e => ¬ p e)) (p := q)
  have hcut : cutNum G S = ((s.filter (fun e => ¬ p e)).filter (fun e => ¬ q e)).card := by
    unfold cutNum cutEdges isCutEdge
    rw [Finset.filter_filter]
  unfold edgesInside edgeCount
  change (s.filter p).card + (s.filter q).card + cutNum G S = s.card
  rw [hcut]
  omega

/-- **Paper Eq. (19), p. 10.** For a 3-regular graph and any cut `S`, there are
disjoint independent sets `A ⊆ S`, `B ⊆ Sᶜ` whose combined fraction is at least
`(3/2) C(S)/|E| − 1/2`. -/
theorem exists_two_indep_with_cut_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 3) (hE : 0 < edgeCount G) (hV : 0 < Fintype.card V)
    (S : Finset V) :
    ∃ A B : Finset V, A ⊆ S ∧ B ⊆ Sᶜ ∧ G.IsIndepSet A ∧ G.IsIndepSet B ∧
      (3 / 2 : ℝ) * (cutNum G S : ℝ) / (edgeCount G : ℝ) - 1 / 2 ≤
        ((A.card + B.card : ℕ) : ℝ) / (Fintype.card V : ℝ) := by
  classical
  obtain ⟨A, hAS, hAind, hAcard⟩ := exists_indepSet_card_ge G S
  obtain ⟨B, hBS, hBind, hBcard⟩ := exists_indepSet_card_ge G Sᶜ
  refine ⟨A, B, hAS, hBS, hAind, hBind, ?_⟩
  have hpart := edgesInside_add_cutNum G S
  have hC_le_E : cutNum G S ≤ edgeCount G := by omega
  have hVsplit : S.card + Sᶜ.card = Fintype.card V := by
    have hdisj : Disjoint S Sᶜ := disjoint_compl_right
    have hunion : S ∪ Sᶜ = (Finset.univ : Finset V) := Finset.union_compl S
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
  -- Natural-number rearrangement: `|V| + C ≤ |A| + |B| + |E|`.
  have hnat : Fintype.card V + cutNum G S ≤ A.card + B.card + edgeCount G := by
    have hnat0 : S.card + Sᶜ.card ≤ A.card + B.card +
        (edgesInside G S + edgesInside G Sᶜ) := by omega
    omega
  have hreg2 : 2 * edgeCount G = 3 * Fintype.card V :=
    two_mul_edgeCount_eq_three_mul_card G hreg
  have hreal : (Fintype.card V : ℝ) + (cutNum G S : ℝ) ≤
      ((A.card + B.card : ℕ) : ℝ) + (edgeCount G : ℝ) := by
    exact_mod_cast hnat
  have hEV : (2 : ℝ) * (edgeCount G : ℝ) = 3 * (Fintype.card V : ℝ) := by
    exact_mod_cast hreg2
  have hEpos : (0 : ℝ) < (edgeCount G : ℝ) := by exact_mod_cast hE
  have hVpos : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hV
  rw [le_div_iff₀ hVpos]
  field_simp
  nlinarith [hreal, hEV, hEpos, hVpos]

/-- **Paper Eq. (23), p. 11.** The independence number is at least half the
combined size of any two disjoint independent sets. -/
theorem indepNum_ge_half_combined (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hA : G.IsIndepSet A) (hB : G.IsIndepSet B) :
    ((A.card + B.card : ℕ) : ℝ) / 2 ≤ (G.indepNum : ℝ) := by
  have hAle : A.card ≤ G.indepNum := hA.card_le_indepNum
  have hBle : B.card ≤ G.indepNum := hB.card_le_indepNum
  have hmax : A.card ≤ G.indepNum ∧ B.card ≤ G.indepNum := ⟨hAle, hBle⟩
  have : ((A.card + B.card : ℕ) : ℝ) / 2 ≤ (G.indepNum : ℝ) := by
    have hcast : ((A.card + B.card : ℕ) : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by
      push_cast; ring
    have hAmax : (A.card : ℝ) ≤ (G.indepNum : ℝ) := by exact_mod_cast hAle
    have hBmax : (B.card : ℝ) ≤ (G.indepNum : ℝ) := by exact_mod_cast hBle
    rw [hcast]
    linarith
  exact this

/-- The independence ratio `ir`, the fraction of vertices in a largest
independent set (p. 11). -/
noncomputable def independenceRatio (G : SimpleGraph V) : ℝ :=
  (G.indepNum : ℝ) / (Fintype.card V : ℝ)

/-- **Paper Eq. (23), p. 11.** For every cut `S` of a 3-regular graph,
`ir ≥ (3/4) C(S)/|E| − 1/4`. -/
theorem independenceRatio_ge_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 3) (hE : 0 < edgeCount G) (hV : 0 < Fintype.card V)
    (S : Finset V) :
    (3 / 4 : ℝ) * ((cutNum G S : ℝ) / (edgeCount G : ℝ)) - 1 / 4 ≤ independenceRatio G := by
  obtain ⟨A, B, -, -, hAind, hBind, hcard⟩ :=
    exists_two_indep_with_cut_bound G hreg hE hV S
  have hVpos : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hV
  have hhalf := indepNum_ge_half_combined G hAind hBind
  have hhalf_div : (((A.card + B.card : ℕ) : ℝ) / 2) / (Fintype.card V : ℝ) ≤
      (G.indepNum : ℝ) / (Fintype.card V : ℝ) :=
    div_le_div_of_nonneg_right hhalf hVpos.le
  have hcard_div : (3 / 4 : ℝ) * ((cutNum G S : ℝ) / (edgeCount G : ℝ)) - 1 / 4 ≤
      (((A.card + B.card : ℕ) : ℝ) / 2) / (Fintype.card V : ℝ) := by
    have h2 := div_le_div_of_nonneg_right hcard (by norm_num : (0 : ℝ) ≤ 2)
    have hleft : ((3 / 2 : ℝ) * (cutNum G S : ℝ) / (edgeCount G : ℝ) - 1 / 2) / 2 =
        (3 / 4 : ℝ) * ((cutNum G S : ℝ) / (edgeCount G : ℝ)) - 1 / 4 := by ring
    rw [hleft] at h2
    calc
      (3 / 4 : ℝ) * ((cutNum G S : ℝ) / (edgeCount G : ℝ)) - 1 / 4
          ≤ (((A.card + B.card : ℕ) : ℝ) / (Fintype.card V : ℝ)) / 2 := h2
      _ = (((A.card + B.card : ℕ) : ℝ) / 2) / (Fintype.card V : ℝ) := by ring
  unfold independenceRatio
  exact hcard_div.trans hhalf_div

/-- **Paper Eq. (24), p. 11.** Taking the QAOA expectation over the cut law:
if a graph admits a cut law with expected cut fraction `c`, then
`ir ≥ (3/4) c − 1/4`. -/
theorem independenceRatio_ge_of_expected (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 3) (hE : 0 < edgeCount G) (hV : 0 < Fintype.card V)
    (μ : Finset V → ℝ) (hμ : IsProbCutLaw μ) :
    (3 / 4 : ℝ) * expectedCutFraction G μ - 1 / 4 ≤ independenceRatio G := by
  classical
  obtain ⟨hμ0, hμ1⟩ := hμ
  have hpoint : ∀ S : Finset V,
      (3 / 4 : ℝ) * ((cutNum G S : ℝ) / (edgeCount G : ℝ)) - 1 / 4 ≤
        independenceRatio G :=
    fun S => independenceRatio_ge_cut G hreg hE hV S
  have havg : ∑ S, μ S * ((3 / 4 : ℝ) * ((cutNum G S : ℝ) / (edgeCount G : ℝ)) - 1 / 4) ≤
      ∑ S, μ S * independenceRatio G :=
    Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (hpoint S) (hμ0 S)
  have hr : ∑ S, μ S * independenceRatio G = independenceRatio G := by
    rw [← Finset.sum_mul, hμ1, one_mul]
  have hl : ∑ S, μ S * ((3 / 4 : ℝ) * ((cutNum G S : ℝ) / (edgeCount G : ℝ)) - 1 / 4) =
      (3 / 4 : ℝ) * expectedCutFraction G μ - 1 / 4 := by
    unfold expectedCutFraction
    have hpt : ∀ S : Finset V,
        μ S * ((3 / 4 : ℝ) * ((cutNum G S : ℝ) / (edgeCount G : ℝ)) - 1 / 4) =
          (3 / 4 : ℝ) * (μ S * ((cutNum G S : ℝ) / (edgeCount G : ℝ))) - μ S * (1 / 4) := by
      intro S; ring
    calc
      ∑ S, μ S * ((3 / 4 : ℝ) * ((cutNum G S : ℝ) / (edgeCount G : ℝ)) - 1 / 4)
          = ∑ S, ((3 / 4 : ℝ) * (μ S * ((cutNum G S : ℝ) / (edgeCount G : ℝ))) -
              μ S * (1 / 4)) := Finset.sum_congr rfl fun S _ => hpt S
      _ = (3 / 4 : ℝ) * (∑ S, μ S * ((cutNum G S : ℝ) / (edgeCount G : ℝ))) -
            (∑ S, μ S) * (1 / 4) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      _ = (3 / 4 : ℝ) * (∑ S, μ S * ((cutNum G S : ℝ) / (edgeCount G : ℝ))) - 1 / 4 := by
              rw [hμ1]; ring
  rw [hl, hr] at havg
  exact havg

/-- **Paper Eq. (24), p. 11, stated with `c̃_edge(p)`.** For a 3-regular graph of
girth at least `2p+2` whose depth-`p` QAOA cut law has expected fraction `c`, the
independence ratio is at least `(3/4) c − 1/4`. -/
theorem paper_eq24_independence_ratio (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : ℕ} {c : ℝ} (hreg : G.IsRegularOfDegree 3) (hgirth : 2 * p + 2 ≤ G.girth)
    (hE : 0 < edgeCount G) (hV : 0 < Fintype.card V)
    (hQAOA : HasExpectedCutFraction G c) :
    (3 / 4 : ℝ) * c - 1 / 4 ≤ independenceRatio G := by
  obtain ⟨μ, hμ, hc⟩ := hQAOA
  rw [← hc]
  exact independenceRatio_ge_of_expected G hreg hE hV μ hμ

/-- **Table 1 / Eq. (24) at girth 36, p. 11.** With `c̃_edge(17) = 0.8971`
(Table 1, p. 6), the independence-ratio lower bound is
`(3/4)·0.8971 − 1/4 = 0.422825 ≥ 0.4228`, the value quoted on p. 11. -/
theorem paper_eq24_girth36 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 3) (hgirth : 36 ≤ G.girth)
    (hE : 0 < edgeCount G) (hV : 0 < Fintype.card V)
    {c : ℝ} (hc : (8971 : ℝ) / 10000 ≤ c)
    (hQAOA : HasExpectedCutFraction G c) :
    (4228 : ℝ) / 10000 ≤ independenceRatio G := by
  have hg : 2 * 17 + 2 ≤ G.girth := by norm_num; exact hgirth
  have h := paper_eq24_independence_ratio (p := 17) G hreg hg hE hV hQAOA
  nlinarith

end Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut
