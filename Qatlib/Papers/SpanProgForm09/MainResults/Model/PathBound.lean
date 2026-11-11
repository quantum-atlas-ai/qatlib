/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgForm09.MainResults.Model.Formula

set_option backward.isDefEq.respectTransparency false

/-!
# The geometric-series core of Lemma 3.2 (Eqs. (3.7), (3.8)) of
Reichardt, *Span-program-based quantum algorithm for evaluating unbalanced formulas*
(fixed arXiv:0907.1622v1)

This module formalises the elementary half of Lemma 3.2: the passage from the
per-vertex adversary ratio (Eq. (3.7)) to the bound on the path quantity `σ₋`
(Eq. (3.8), Ref. geometric series (3.12)).

The paper's argument is:

* if at every internal vertex `v` the adversary bound satisfies
  `Adv±(φ_v) / max_j Adv±(φ_{c_j}) ≥ c` with `c = √(1 + 1/β²) > 1`, and every leaf
  has `Adv± = 1`, then along any root-to-leaf path the summands `1/Adv±` decay
  geometrically by a factor `r = 1/c < 1`;
* hence `σ₋(φ) = max_ξ ∑_{w∈ξ} 1/Adv±(φ_w)` is dominated by the geometric series
  `∑_{k≥0} r^k = 1/(1-r)`.

`geometric_path_bound` below proves exactly this implication over the *definitions*
`Formula.pathSum` and `Formula.advPlus` of `Model/Formula.lean`, and
`sigmaMinus_geometric` reads off the closed bound `σ₋ ≤ 1/(1-r)`. The final numeric
specialisation of Eq. (3.8) to the constant `(2+√2)β²` at `r = (1+1/β²)^{-1/2}`,
`β ≥ 1`, is elementary real arithmetic (`1/(1-r) = √(β²+1)·(√(β²+1)+β)` and
`√(β²+1) ≤ √2·β`) that is documented in the PR description rather than mechanised here.

Boundary: the pointwise adversary ratio (Eq. (3.7)) is taken as a hypothesis
(`Lemma32Hyp`); its derivation from the weighted-adversary minimax formulation
([HoyerLeeSpalek2007], Eq. (3.9)) is not mechanised here. The bound on the full witness size
(``Lemma 3.3``) and the operator-norm estimates (Lemmas 3.1, 3.4) are separate and
also not mechanised. Nothing here assumes or restates the conclusion `σ₋ ≤ 1/(1-r)`:
`geometric_path_bound` produces it from the ratio hypothesis alone.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpanProgForm09.MainResults

open scoped Classical BigOperators

variable {I : Type} [Fintype I] [DecidableEq I] {G : GateSet}

/-- Partial geometric sum `∑_{k=0}^{n} r^k`, defined recursively so that it needs no
topology. -/
def geomSum (r : ℝ) : ℕ → ℝ
  | 0 => 1
  | (n + 1) => geomSum r n + r ^ (n + 1)

/-- The telescoping identity `(1 - r)·∑_{k=0}^{n} r^k = 1 - r^{n+1}` for the partial
geometric sum. -/
theorem geomSum_telescope (r : ℝ) (n : ℕ) :
    (1 - r) * geomSum r n = 1 - r ^ (n + 1) := by
  induction n with
  | zero => simp [geomSum]
  | succ n ih =>
      simp only [geomSum]
      rw [mul_add, ih, pow_succ]
      ring

/-- The partial geometric sum is nonnegative for a nonnegative ratio. -/
theorem geomSum_nonneg (r : ℝ) (hr0 : 0 ≤ r) : ∀ n, 0 ≤ geomSum r n
  | 0 => by simp [geomSum]
  | (n + 1) => by
      rw [geomSum]
      exact add_nonneg (geomSum_nonneg r hr0 n) (pow_nonneg hr0 _)

/-- One step of monotonicity of the partial geometric sum in the number of terms. -/
theorem geomSum_succ_le (r : ℝ) (hr0 : 0 ≤ r) (n : ℕ) :
    geomSum r n ≤ geomSum r (n + 1) := by
  rw [geomSum]
  exact le_add_of_nonneg_right (pow_nonneg hr0 _)

/-- The partial geometric sum is monotone in the number of terms for a nonnegative
ratio. -/
theorem geomSum_mono (r : ℝ) (hr0 : 0 ≤ r) : Monotone (geomSum r) :=
  monotone_nat_of_le_succ (geomSum_succ_le r hr0)

/-- The full geometric-series bound `∑_{k=0}^{n} r^k ≤ 1/(1-r)` for `0 ≤ r < 1`.
This is the estimate (3.12) in the proof of Lemma 3.2. -/
theorem geomSum_le_inv (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    geomSum r n ≤ 1 / (1 - r) := by
  have hpos : 0 < 1 - r := by linarith
  have htel := geomSum_telescope r n
  have hrpow : 0 ≤ r ^ (n + 1) := pow_nonneg hr0 _
  have hkey : geomSum r n * (1 - r) ≤ 1 := by
    rw [mul_comm, htel]; linarith
  rw [le_div_iff₀ hpos]
  exact hkey

/-- Height of a formula tree: the largest number of internal nodes on a path from the
root to a leaf. A leaf has height `0`; an internal node has height one more than the
maximum child height. -/
def Formula.height : (φ : Formula I G) → ℕ
  | .leaf _ => 0
  | .node k _ ch => 1 + (Finset.univ : Finset (Fin k)).sup (fun j => Formula.height (ch j))
termination_by φ => φ.size
decreasing_by exact Formula.size_child_lt k _ ch j

/-- Every internal node of the formula has fan-in at least one (the paper's gates have
fan-in at least two, Lemma 3.2's hypothesis that "every gate depends on at least two
input bits"). -/
def Formula.NodeArityPos : (φ : Formula I G) → Prop
  | .leaf _ => True
  | .node k _ ch => 0 < k ∧ ∀ j, Formula.NodeArityPos (ch j)
termination_by φ => φ.size
decreasing_by exact Formula.size_child_lt k _ ch j

/-- The hypothesis packaged from Lemma 3.2, Eq. (3.7): at each leaf `Adv± = 1` (so in
particular `1 ≤ Adv±`), at each internal vertex `Adv±(φ_v) ≥ c · Adv±(φ_{c_j})` for every
child, and `1 ≤ Adv±(φ_v)` at every vertex. -/
def Lemma32Hyp (c : ℝ) : (φ : Formula I G) → Prop
  | .leaf i => 1 ≤ advPlus (Formula.leaf (G := G) i)
  | .node k g ch =>
      (∀ j, Lemma32Hyp c (ch j)) ∧
        (1 ≤ advPlus (Formula.node k g ch)) ∧
        (∀ j, c * advPlus (ch j) ≤ advPlus (Formula.node k g ch))
termination_by φ => φ.size
decreasing_by exact Formula.size_child_lt k g ch j

/-- `Lemma32Hyp c φ` implies `1 ≤ Adv±(φ)` at every vertex. -/
theorem Lemma32Hyp_one_le (c : ℝ) {φ : Formula I G} (h : Lemma32Hyp c φ) :
    1 ≤ advPlus φ := by
  induction φ with
  | leaf i => rwa [Lemma32Hyp] at h
  | node k g ch _ih =>
      rw [Lemma32Hyp] at h
      exact h.2.1

/-- A list whose elements are all `≤ M`, with `0 ≤ M`, has `foldr max 0 ≤ M`. Used to
bound the `max_j pathSum` term arising from `pathSum`. -/
theorem list_foldr_max_le {l : List ℝ} {M : ℝ} (h0 : 0 ≤ M) (h : ∀ x ∈ l, x ≤ M) :
    l.foldr max 0 ≤ M := by
  induction l with
  | nil => simpa using h0
  | cons a t ih =>
      rw [List.foldr_cons]
      apply max_le
      · exact h a (by simp)
      · apply ih
        intro x hx
        exact h x (by simp [hx])

/-- `height` of a node is one plus the supremum of its children's heights. -/
theorem height_node (k : ℕ) (g : G.gate k) (ch : Fin k → Formula I G) :
    Formula.height (Formula.node k g ch) =
      1 + (Finset.univ : Finset (Fin k)).sup (fun j => Formula.height (ch j)) := by
  rw [Formula.height]

/-- Each child of an internal node has strictly smaller height than the node, provided the
node has at least one child. -/
theorem height_child_lt (k : ℕ) (g : G.gate k) (ch : Fin k → Formula I G) (j : Fin k) :
    Formula.height (ch j) < Formula.height (Formula.node k g ch) := by
  have hle : Formula.height (ch j) ≤
      (Finset.univ : Finset (Fin k)).sup (fun j => Formula.height (ch j)) :=
    Finset.le_sup (f := fun j => Formula.height (ch j)) (Finset.mem_univ j)
  rw [height_node]
  omega

/-- The core of Lemma 3.2, Eq. (3.8): if the adversary bounds satisfy the per-vertex
ratio of Eq. (3.7) with constant `c = r⁻¹ > 1`, then for every vertex the reciprocal
adversary bound is bounded by `r ^ height` and the path quantity `pathSum` is bounded by
the partial geometric sum `geometric_sum r height`.

This is the simultaneous induction of the proof of Lemma 3.3, restricted to the part
that only uses the adversary ratio (not the full-witness-size recursion of Lemma 2.6). -/
theorem geometric_path_bound (c r : ℝ) (hc1 : 1 < c) (hrc : r = c⁻¹)
    (hr0 : 0 ≤ r) (φ : Formula I G) (hφ : Lemma32Hyp c φ) (hnz : Formula.NodeArityPos φ) :
    (advPlus φ)⁻¹ ≤ r ^ Formula.height φ ∧
      pathSum φ ≤ geomSum r (Formula.height φ) := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc1
  induction φ with
  | leaf i =>
      rw [Lemma32Hyp] at hφ
      have hone : 1 ≤ advPlus (Formula.leaf (G := G) i) := hφ
      have hpos : (0 : ℝ) < advPlus (Formula.leaf (G := G) i) := lt_of_lt_of_le one_pos hone
      constructor
      · rw [Formula.height]
        simp only [pow_zero]
        rw [← one_div]
        exact (div_le_one hpos).mpr hone
      · rw [Formula.height, pathSum]
        simp only [geomSum]
        exact (div_le_one hpos).mpr hone
  | node k g ch ih =>
      rw [Lemma32Hyp] at hφ
      rw [Formula.NodeArityPos] at hnz
      obtain ⟨hsub, hone, hratio⟩ := hφ
      obtain ⟨hkpos, hnzsub⟩ := hnz
      haveI : Nonempty (Fin k) := ⟨⟨0, hkpos⟩⟩
      have hchild : ∀ j : Fin k,
          (advPlus (ch j))⁻¹ ≤ r ^ Formula.height (ch j) ∧
            pathSum (ch j) ≤ geomSum r (Formula.height (ch j)) :=
        fun j => ih j (hsub j) (hnzsub j)
      -- pick a child of maximal height
      obtain ⟨jstar, -, hjstar⟩ :=
        Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin k)))
          (f := fun j => Formula.height (ch j)) Finset.univ_nonempty
      have hchild_pos : 0 < advPlus (ch jstar) :=
        lt_of_lt_of_le one_pos (Lemma32Hyp_one_le c (hsub jstar))
      -- P(node): reciprocal adversary bound
      have hP : (advPlus (Formula.node k g ch))⁻¹ ≤ r ^ Formula.height (Formula.node k g ch) := by
        have hle : c * advPlus (ch jstar) ≤ advPlus (Formula.node k g ch) := hratio jstar
        have hden : 0 < c * advPlus (ch jstar) := mul_pos hcpos hchild_pos
        have hstep : (advPlus (Formula.node k g ch))⁻¹ ≤
            r * (advPlus (ch jstar))⁻¹ := by
          calc (advPlus (Formula.node k g ch))⁻¹ ≤ (c * advPlus (ch jstar))⁻¹ :=
                inv_anti₀ hden hle
            _ = (advPlus (ch jstar))⁻¹ * c⁻¹ := mul_inv_rev _ _
            _ = r * (advPlus (ch jstar))⁻¹ := by rw [mul_comm, ← hrc]
        calc (advPlus (Formula.node k g ch))⁻¹ ≤ r * (advPlus (ch jstar))⁻¹ := hstep
          _ ≤ r * r ^ Formula.height (ch jstar) :=
                mul_le_mul_of_nonneg_left (hchild jstar).1 hr0
          _ = r ^ (Formula.height (ch jstar) + 1) := by rw [pow_succ']
          _ = r ^ Formula.height (Formula.node k g ch) := by
                rw [height_node, hjstar]
                rw [show 1 + Formula.height (ch jstar) = Formula.height (ch jstar) + 1 by omega]
      constructor
      · exact hP
      · -- Q(node): path sum bound
        rw [pathSum]
        have hfold : (List.ofFn (fun j : Fin k => pathSum (ch j))).foldr max 0 ≤
            geomSum r ((Finset.univ : Finset (Fin k)).sup (fun j => Formula.height (ch j))) := by
          apply list_foldr_max_le
          · exact geomSum_nonneg r hr0 _
          · intro x hx
            obtain ⟨j, hj⟩ := List.mem_ofFn.mp hx
            rw [← hj]
            exact le_trans (hchild j).2
              (geomSum_mono r hr0
                (Finset.le_sup (f := fun j => Formula.height (ch j)) (Finset.mem_univ j)))
        have hstep : (1 : ℝ) / advPlus (Formula.node k g ch) +
            (List.ofFn (fun j : Fin k => pathSum (ch j))).foldr max 0 ≤
            r ^ Formula.height (Formula.node k g ch) +
              geomSum r ((Finset.univ : Finset (Fin k)).sup (fun j => Formula.height (ch j))) := by
          have h1 : (1 : ℝ) / advPlus (Formula.node k g ch) ≤
              r ^ Formula.height (Formula.node k g ch) := by
            rw [one_div]; exact hP
          linarith
        refine le_trans hstep ?_
        rw [height_node]
        rw [show (1 + (Finset.univ : Finset (Fin k)).sup (fun j => Formula.height (ch j)))
            = (Finset.univ : Finset (Fin k)).sup (fun j => Formula.height (ch j)) + 1 by omega]
        rw [geomSum]
        linarith

/-- The path quantity `σ₋(φ)` is bounded by the geometric series value `1/(1-r)` under the
adversary ratio of Eq. (3.7). -/
theorem sigmaMinus_geometric (c r : ℝ) (hc1 : 1 < c) (hrc : r = c⁻¹) (hr0 : 0 ≤ r)
    (φ : Formula I G) (hφ : Lemma32Hyp c φ) (hnz : Formula.NodeArityPos φ) :
    sigmaMinus φ ≤ 1 / (1 - r) := by
  have hr1 : r < 1 := by
    rw [hrc]
    exact inv_lt_one_of_one_lt₀ hc1
  calc sigmaMinus φ = pathSum φ := rfl
    _ ≤ geomSum r (Formula.height φ) := (geometric_path_bound c r hc1 hrc hr0 φ hφ hnz).2
    _ ≤ 1 / (1 - r) := geomSum_le_inv r hr0 hr1 _

end Qatlib.Papers.SpanProgForm09.MainResults
