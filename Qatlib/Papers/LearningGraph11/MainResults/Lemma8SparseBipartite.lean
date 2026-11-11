/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LearningGraph11.MainResults.SourceLearningGraphModel

set_option backward.isDefEq.respectTransparency false

/-!
# LearningGraph11 Lemma 8: a sparse bipartite graph counting bound

Fixed source: arXiv:1109.5135v1, Lemma 8 and its proof (p. 14).

Let `Y₁, Y₂` be disjoint `r`-element subsets of `[n]` and `(y₁,y₂) ∈ Y₁ × Y₂`. Let `K` be
a bipartite graph between `Y₁` and `Y₂` of type
`({(r/2−1, rs), (r/2+1, rs+1)}, {(r/2−1, rs), (r/2+1, rs+1)})`. Then the probability over
`σ ∈ S_n` that the edge `{y₁,y₂}` lies in `σ(K)` and both `y₁` and `y₂` have degree `rs+1`
is at least `s/4`.

The paper's proof has two counting ingredients.

* Given the degree condition (probability `≥ 1/4`), it suffices to show that for a
  bipartite graph `K'` of type `({(r,rs)}, {(r,rs)})` the probability that `σ(K')`
  contains a fixed edge is at least `s`. By symmetry this probability `p` is independent
  of the edge, and double counting the pairs `(e,h)` with `e ∈ K_h` over an enumeration
  `K₁,…,K_c` of the `c` copies of `K'` gives `p = s`:
  `χ = c·s·r²` on one hand and `χ = r²·p·c` on the other.

`double_count_edge_blocks` and `edge_probability_eq` below formalize the second
ingredient exactly (`p = q/c = s`). `source_lemma_8` formalizes the first ingredient as
the arithmetic combination of the two probability estimates on a finite uniform
probability space; the concrete uniform-`σ` model (and in particular the `≥ 1/4` degree
estimate) is the part of the paper's argument left to the probability model rather than
rebuilt from permutations.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LearningGraph11.MainResults

open Finset
open scoped BigOperators

/-- Double counting of the pairs `(e,h)` with `e ∈ h` over a family of edge sets: if
every block has `sr` edges and every edge lies in exactly `p` blocks, then
`#blocks · sr = #edges · p`. -/
theorem double_count_edge_blocks
    {Ee : Type*} [Fintype Ee] [DecidableEq Ee]
    (Copies : Finset (Finset Ee)) (sr p : ℕ)
    (hblock : ∀ h ∈ Copies, h.card = sr)
    (hmult : ∀ e : Ee, (Copies.filter (fun h => e ∈ h)).card = p) :
    Copies.card * sr = Fintype.card Ee * p := by
  classical
  have hleft : ∑ h ∈ Copies, h.card = Copies.card * sr := by
    calc ∑ h ∈ Copies, h.card = ∑ h ∈ Copies, sr :=
          Finset.sum_congr rfl (fun h hh => hblock h hh)
      _ = Copies.card * sr := by simp [Finset.sum_const, nsmul_eq_mul]
  have hstep1 : ∑ h ∈ Copies, h.card =
      ∑ e : Ee, (Copies.filter (fun h => e ∈ h)).card := by
    calc ∑ h ∈ Copies, h.card
        = ∑ h ∈ Copies, ∑ e : Ee, (if e ∈ h then (1 : ℕ) else 0) := by
          apply Finset.sum_congr rfl
          intro h _
          rw [← Finset.card_filter]
          congr 1
          ext e
          simp
      _ = ∑ e : Ee, ∑ h ∈ Copies, (if e ∈ h then (1 : ℕ) else 0) := Finset.sum_comm
      _ = ∑ e : Ee, (Copies.filter (fun h => e ∈ h)).card := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.card_filter]
  calc Copies.card * sr = ∑ h ∈ Copies, h.card := hleft.symm
    _ = ∑ e : Ee, (Copies.filter (fun h => e ∈ h)).card := hstep1
    _ = ∑ _e : Ee, p := Finset.sum_congr rfl (fun e _ => hmult e)
    _ = Fintype.card Ee * p := by simp [Finset.sum_const, nsmul_eq_mul]

/-- The double-counting identity of Lemma 8 in probability form: in a family of
`c > 0` copies of a bipartite graph of type `({(r,rs)},{(r,rs)})`, each copy having
`s·r²` edges, where every edge of the `r²`-edge ground set appears in exactly `q` copies,
the per-edge probability `q/c` equals `s`. -/
theorem edge_probability_eq
    {Ee : Type*} [Fintype Ee] [DecidableEq Ee]
    (Copies : Finset (Finset Ee)) (r s q : ℕ)
    (hr : 0 < r) (hc : 0 < Copies.card)
    (hblock : ∀ h ∈ Copies, h.card = s * r * r)
    (hmult : ∀ e : Ee, (Copies.filter (fun h => e ∈ h)).card = q)
    (hfull : Fintype.card Ee = r * r) :
    (q : ℝ) / (Copies.card : ℝ) = (s : ℝ) := by
  have hdc := double_count_edge_blocks Copies (s * r * r) q hblock hmult
  rw [hfull] at hdc
  have hR : (Copies.card : ℝ) * ((s : ℝ) * r * r) = (r : ℝ) * r * (q : ℝ) := by
    exact_mod_cast hdc
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hcR : (0 : ℝ) < (Copies.card : ℝ) := by exact_mod_cast hc
  have hrr : (0 : ℝ) < (r : ℝ) * r := mul_pos hrR hrR
  rw [div_eq_iff hcR.ne']
  have hR' : ((Copies.card : ℝ) * (s : ℝ)) * ((r : ℝ) * r) = (q : ℝ) * ((r : ℝ) * r) := by
    nlinarith [hR]
  have hqs : (q : ℝ) = (Copies.card : ℝ) * (s : ℝ) := by
    have h := mul_right_cancel₀ hrr.ne' hR'
    linarith [h]
  rw [hqs]
  ring

/-- Fixed source arXiv:1109.5135v1, Lemma 8 (p. 14), probability estimate: if the degree
condition holds with probability at least `1/4` and, conditionally on it, the fixed edge
is present with probability `s` (the double-counting identity `p = s`, proved in
`edge_probability_eq`), then the joint probability is at least `s/4`.

Formalized on a finite uniform probability space of copies (`Ω`); `degOK` is the event
"both endpoints have degree `rs+1`" and `edgeOK` the event "the fixed edge is present". -/
theorem source_lemma_8
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (degOK edgeOK : Ω → Prop) [DecidablePred degOK] [DecidablePred edgeOK]
    (s : ℝ) (hs : 0 ≤ s)
    (hdeg : (1 : ℝ) / 4 ≤
      ((Finset.univ.filter degOK).card : ℝ) / (Fintype.card Ω))
    (hcond : ((Finset.univ.filter (fun ω => degOK ω ∧ edgeOK ω)).card : ℝ) =
      s * ((Finset.univ.filter degOK).card : ℝ)) :
    s / 4 ≤ ((Finset.univ.filter (fun ω => degOK ω ∧ edgeOK ω)).card : ℝ) /
      (Fintype.card Ω) := by
  classical
  have hN : (0 : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  have h4 : (1 / 4) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter degOK).card : ℝ) :=
    (le_div_iff₀ hN).mp hdeg
  rw [hcond, le_div_iff₀ hN]
  calc (s / 4) * (Fintype.card Ω : ℝ)
      = s * ((1 / 4) * (Fintype.card Ω : ℝ)) := by ring
    _ ≤ s * ((Finset.univ.filter degOK).card : ℝ) :=
        mul_le_mul_of_nonneg_left h4 hs

end Qatlib.Papers.LearningGraph11.MainResults
