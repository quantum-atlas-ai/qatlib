/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Finset.Empty

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 9: block contribution of the fault-tolerant learning graph

Source: A. Belovs, *Learning-Graph-Based Quantum Algorithm for k-distinctness*,
fixed preprint arXiv:1205.1534v2 (`arXiv:1205.1534v2 [quant-ph] 9 Aug 2012`).

Paper statement, **Lemma 9** (p. 16):

> Let `R` and `s` be as above.  If `x` and `y` agree on
> `S = R[D₁←a₁, …, D_ℓ←a_ℓ]` then the contribution from the block on `S` is
> `(−1)^{ℓ+|D₁|+⋯+|D_ℓ|} q`.  Otherwise, it is `0`.

Paper setting (§6.1–6.2).  A vertex of the fault-tolerant learning graph is
`R[D₁←a₁, …, D_ℓ←a_ℓ]` with `∅ ⊂ D_i ⊆ [k−i]`.  For `ℓ < s`, the *block* on
`S` is

`B(S) = { R[D₁←a₁, …, D_{s−1}←a_{s−1}] | ∅ ⊂ D_i ⊆ [k−i] for ℓ < i < s }`

with contribution `C(S) = Σ_{S'∈B(S)} X^{S'}_{a_s}[[x,y]]`, where the arc matrix
entry `X^{S'}_{a_s}[[x,y]]` equals `±q` when `x` and `y` agree on `S'` (type
(13), the sign being `(−1)^{s+|D₁|+⋯+|D_{s−1}|}`) and `0` when they disagree
(the assignments they satisfy differ, §6.1).  The proof (§6.2, p. 16) is an
induction on `s−ℓ`:

* `x, y` disagree on `S` ⇒ they disagree on every vertex of the block ⇒ `0`;
* `ℓ = s−1` ⇒ `B(S) = {S}`, and (13) gives `(−1)^{ℓ+|D₁|+⋯+|D_ℓ|} q`;
* `ℓ < s−1` ⇒ `B(S)` is the disjoint union of the blocks of the children
  `R[…, D_{ℓ+1}←a_{ℓ+1}]`, one for every `∅ ⊂ D_{ℓ+1} ⊆ [k−ℓ−1]`; with
  `I ⊆ [k−ℓ−1]` the non-fault indices, `x` and `y` agree on a child exactly
  when `D_{ℓ+1} ⊆ I`, and the inductive hypothesis plus the
  inclusion–exclusion identity `Σ_{∅≠D⊆I}(−1)^{|D|} = −1` gives the claim.

Formalized content.  `blockContribution q levels` is the paper's recursion:
each remaining decomposition step picks a non-empty `D` out of the current
non-fault set `I` (`levels` is the list of the sets `I` at the successive
steps, `s−1−ℓ` of them) and contributes the relative sign `(−1)^{|D|+1}` — the
`+1` is exactly the `+1` in the exponent `ℓ+1+|D₁|+⋯+|D_{ℓ+1}|` displayed in
the paper; at the leaf (`levels = []`, i.e. `ℓ = s−1`) the value is `q` by (13).
`sourceBlockContribution` prefixes the sign `(−1)^{ℓ+|D₁|+⋯+|D_ℓ|}` of the
already-chosen subsets, giving the paper's displayed quantity.

The following results are proved here:

* `alternating_powerset_sum` and `nonempty_alternating_sum`: the
  inclusion–exclusion identity at the end of the paper's proof;
* `nonfault_card_lt`: the counting step "there are at most
  `k−1−(s−1) < k−ℓ−1` faults.  Hence, `I` is non-empty";
* `blockContribution_zero`: the "otherwise it is `0`" half;
* `blockContribution_eq_q`: the induction in the agreeing case;
* `inclusion_exclusion_step`: the paper's last displayed line;
* `source_lemma9_agree` / `source_lemma9_disagree`: the lemma as stated.

Scope note: this module formalizes the paper's induction starting from the
two leaf values supplied by §6.1: `±q` when the inputs agree (13) and `0` when
they disagree.  The construction of the concrete arc matrices `X^S_{a_s}` of
§6.1 with their assignment semantics is outside the scope of this file.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.LearnGraphDis12.MainResults.SourceLemma9

variable {R : Type*} [CommRing R]

/-! ## The block recursion -/

/-- Block contribution recursion of Lemma 9.  `levels` lists, from the root
level `ℓ` down to stage `s−1`, the non-fault index sets `I ⊆ [k−j−1]` of the
successive decomposition steps.  Each step ranges over the non-empty subsets
`∅ ⊂ D ⊆ I` (paper: `∅ ⊂ D_{ℓ+1} ⊆ [k−ℓ−1]`) and contributes the relative sign
`(−1)^{|D|+1}`.  At the leaf (`levels = []`, i.e. `ℓ = s−1`, where the block is
the single vertex `S`) the value is `q`, the entry of type (13).

The paper's decomposition `B(S) = ⊔_{∅⊂D_{ℓ+1}⊆[k−ℓ−1]} B(child)` is exactly
the first step of this recursion. -/
def blockContribution (q : R) : List (Finset ℕ) → R
  | [] => q
  | I :: rest =>
      ∑ D ∈ I.powerset.filter (fun D => D.Nonempty),
        (-1 : R) ^ (D.card + 1) * blockContribution q rest

/-- The contribution of the block on `S = R[D₁←a₁, …, D_ℓ←a_ℓ]`: the sign
`(−1)^{ℓ+|D₁|+⋯+|D_ℓ|}` of the already-fixed subsets `D₁,…,D_ℓ` times the
recursion over the remaining `s−1−ℓ` decomposition steps.  This is the
`C(S)` of §6.2. -/
def sourceBlockContribution (q : R) (ℓ : ℕ) (sD : ℕ) (levels : List (Finset ℕ)) : R :=
  (-1 : R) ^ (ℓ + sD) * blockContribution q levels

/-! ## The inclusion–exclusion identity -/

/-- Alternating sum over a powerset: for non-empty `I` the total
`Σ_{D⊆I} (−1)^{|D|}` vanishes, and for `I = ∅` it is `1`.  This is the engine
of the last line of the proof of Lemma 9. -/
theorem alternating_powerset_sum (I : Finset ℕ) :
    ∑ D ∈ I.powerset, (-1 : R) ^ D.card = if I.Nonempty then 0 else 1 := by
  induction I using Finset.induction with
  | empty => simp
  | insert a I ha _ =>
      rw [if_pos (Finset.insert_nonempty a I), Finset.sum_powerset_insert ha]
      have hneg : ∑ D ∈ I.powerset, (-1 : R) ^ (insert a D).card
          = - ∑ D ∈ I.powerset, (-1 : R) ^ D.card := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro D hD
        have haD : a ∉ D := fun h => ha (Finset.mem_powerset.mp hD h)
        rw [Finset.card_insert_of_notMem haD, pow_succ]
        ring
      rw [hneg]
      ring

/-- The inclusion–exclusion form used in the paper: for non-empty `I`,
`Σ_{∅≠D⊆I} (−1)^{|D|+1} = 1`, which turns the induction's
`(−1)^{ℓ+1+|D₁|+⋯+|D_{ℓ+1}|} q` sum into `(−1)^{ℓ+|D₁|+⋯+|D_ℓ|} q`. -/
theorem nonempty_alternating_sum (I : Finset ℕ) (hI : I.Nonempty) :
    ∑ D ∈ I.powerset.filter (fun D => D.Nonempty), (-1 : R) ^ (D.card + 1) = 1 := by
  have htotal := alternating_powerset_sum (R := R) I
  rw [if_pos hI] at htotal
  have htotal' : ∑ D ∈ I.powerset, (-1 : R) ^ (D.card + 1) = 0 := by
    have hfac : ∑ D ∈ I.powerset, (-1 : R) ^ (D.card + 1)
        = - ∑ D ∈ I.powerset, (-1 : R) ^ D.card := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro D _
      rw [pow_succ]
      ring
    rw [hfac, htotal]
    ring
  have hset : I.powerset.filter (fun D : Finset ℕ => D.Nonempty) = I.powerset.erase ∅ := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.nonempty_iff_ne_empty]
    tauto
  rw [hset]
  have hmem : (∅ : Finset ℕ) ∈ I.powerset := by simp
  have hsum : ∑ D ∈ I.powerset, (-1 : R) ^ (D.card + 1)
      = (-1 : R) + ∑ D ∈ I.powerset.erase ∅, (-1 : R) ^ (D.card + 1) := by
    rw [← Finset.insert_erase hmem,
      Finset.sum_insert (Finset.notMem_erase (∅ : Finset ℕ) I.powerset)]
    norm_num
  rw [hsum] at htotal'
  calc (∑ D ∈ I.powerset.erase ∅, (-1 : R) ^ (D.card + 1))
      = (-1 : R) + (∑ D ∈ I.powerset.erase ∅, (-1 : R) ^ (D.card + 1)) + 1 := by ring
    _ = 0 + 1 := by rw [htotal']
    _ = 1 := by ring

/-! ## The counting step ("`I` is non-empty") -/

/-- Counting step of the proof of Lemma 9 (§6.2, p. 16).  At level `ℓ < s−1`
the decomposition runs over `∅ ⊂ D_{ℓ+1} ⊆ [k−ℓ−1]`; `y` has at most
`k−1` elements equal to `x_{a₁}` and `s−1` of them are already accounted for
(`y_{a₁} = ⋯ = y_{a_{s−1}} = x_{a₁}`), leaving at most `k−1−(s−1)` faults.
Since `k−1−(s−1) = k−s < k−ℓ−1`, the non-fault set `I ⊆ [k−ℓ−1]` is
non-empty — the hypothesis needed by `nonempty_alternating_sum`. -/
theorem nonfault_card_lt (k ℓ s faults : ℕ) (hℓs : ℓ + 1 < s) (hsk : s ≤ k)
    (hfaults : faults ≤ k - 1 - (s - 1)) : faults < k - ℓ - 1 := by
  omega

/-! ## The two halves of Lemma 9 -/

/-- Lemma 9, *"otherwise it is 0"* (p. 16): if `x` and `y` disagree on `S`,
they disagree on every vertex of the block, every leaf entry of type (13)
vanishes, and the block contribution is `0`. -/
theorem blockContribution_zero (levels : List (Finset ℕ)) :
    blockContribution (0 : R) levels = 0 := by
  induction levels with
  | nil => rfl
  | cons I rest ih => simp only [blockContribution, ih, mul_zero, Finset.sum_const_zero]

/-- Lemma 9, agreeing case: if `x` and `y` agree on `S` (leaf value `q`) and
every non-fault set in the decomposition is non-empty, the block contribution
is `q`.  This is the induction of §6.2: each step's alternating sum is `1` by
inclusion–exclusion (`nonempty_alternating_sum`). -/
theorem blockContribution_eq_q (q : R) (levels : List (Finset ℕ))
    (h : ∀ I ∈ levels, I.Nonempty) : blockContribution q levels = q := by
  induction levels with
  | nil => rfl
  | cons I rest ih =>
      have hI : I.Nonempty := h I (by simp)
      have hrest : ∀ J ∈ rest, J.Nonempty := fun J hJ => h J (by simp [hJ])
      show ∑ D ∈ I.powerset.filter (fun D => D.Nonempty),
          (-1 : R) ^ (D.card + 1) * blockContribution q rest = q
      rw [ih hrest, ← Finset.sum_mul, nonempty_alternating_sum I hI, one_mul]

/-- The paper's last displayed line of the proof of Lemma 9 (p. 16):
with `sD = |D₁|+⋯+|D_ℓ|`,

`Σ_{∅⊂D_{ℓ+1}⊆I} (−1)^{ℓ+1+sD+|D_{ℓ+1}|} q = (−1)^{ℓ+sD} q`.

The factor `−1` supplied by the alternating sum cancels the `+1` of the
induction's exponent. -/
theorem inclusion_exclusion_step (q : R) (ℓ sD : ℕ) (I : Finset ℕ) (hI : I.Nonempty) :
    ∑ D ∈ I.powerset.filter (fun D => D.Nonempty),
        (-1 : R) ^ (ℓ + 1 + sD + D.card) * q
      = (-1 : R) ^ (ℓ + sD) * q := by
  have hsig : ∑ D ∈ I.powerset.filter (fun D => D.Nonempty),
        (-1 : R) ^ (ℓ + 1 + sD + D.card) = (-1 : R) ^ (ℓ + sD) := by
    have hstep : ∀ D : Finset ℕ,
        (-1 : R) ^ (ℓ + 1 + sD + D.card)
          = (-1 : R) ^ (ℓ + sD) * (-1 : R) ^ (D.card + 1) := by
      intro D
      rw [← pow_add]
      congr 1
      omega
    calc ∑ D ∈ I.powerset.filter (fun D => D.Nonempty),
            (-1 : R) ^ (ℓ + 1 + sD + D.card)
        = ∑ D ∈ I.powerset.filter (fun D => D.Nonempty),
            (-1 : R) ^ (ℓ + sD) * (-1 : R) ^ (D.card + 1) :=
          Finset.sum_congr rfl (fun D _ => hstep D)
      _ = (-1 : R) ^ (ℓ + sD) *
            (∑ D ∈ I.powerset.filter (fun D => D.Nonempty),
              (-1 : R) ^ (D.card + 1)) := by
          rw [Finset.mul_sum]
      _ = (-1 : R) ^ (ℓ + sD) := by
          rw [nonempty_alternating_sum I hI, mul_one]
  rw [← Finset.sum_mul, hsig]

/-- Fixed arXiv:1205.1534v2, **Lemma 9** (p. 16), agreeing case.  Let the
vertex be `S = R[D₁←a₁, …, D_ℓ←a_ℓ]` with `sD = |D₁|+⋯+|D_ℓ|`, and let
`levels` be the `s−1−ℓ` non-fault sets of the block decomposition, all
non-empty.  If `x` and `y` agree on `S`, the contribution of the block on `S`
is `(−1)^{ℓ+|D₁|+⋯+|D_ℓ|} q`. -/
theorem source_lemma9_agree (q : R) (ℓ sD : ℕ) (levels : List (Finset ℕ))
    (hnonempty : ∀ I ∈ levels, I.Nonempty) :
    sourceBlockContribution q ℓ sD levels = (-1 : R) ^ (ℓ + sD) * q := by
  unfold sourceBlockContribution
  rw [blockContribution_eq_q q levels hnonempty]

/-- Fixed arXiv:1205.1534v2, **Lemma 9** (p. 16), disagreeing case: if `x` and
`y` disagree on `S` the block contribution is `0`. -/
theorem source_lemma9_disagree (ℓ sD : ℕ) (levels : List (Finset ℕ)) :
    sourceBlockContribution (0 : R) ℓ sD levels = 0 := by
  unfold sourceBlockContribution
  rw [blockContribution_zero]
  ring

end Qatlib.Papers.LearnGraphDis12.MainResults.SourceLemma9
