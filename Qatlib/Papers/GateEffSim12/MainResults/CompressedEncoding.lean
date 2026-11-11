/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GateEffSim12.MainResults.SourceModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# CompressedEncoding — Theorem 4.3 of arXiv:1211.4637v2

Fixed paper version: arXiv:1211.4637v2 (5 April 2013), PDF SHA-256
`aef583fed3675ee75a251ed7438ab99cb4c16b34697dd8f4293f3d39d07d471d`.
Theorem 4.3 and Eqs. (10)–(18) are on pp. 8–9; Definition 4.1 (`C_m^k`) is on
p. 7 and Definition 4.2 (`B_q^k`) on p. 8.

This file formalises the paper's encoding at the level of amplitudes:

* `phiAmp` / `phiTensor` — the exponential superposition
  `|φ_q> = Σ_{s<q} β α^s |s> + α^q |q>` of Eq. (10), and its `(k+1)`-fold
  tensor product of Eq. (15).
* `gapList` — the zero-run lengths `s_1, …, s_h` of a Boolean word, i.e. the
  paper's gap encoding `x = 0^{s_1} 1 0^{s_2} 1 … 1 0^{t}`.
* `bVec` — the amplitude function of Definition 4.2, Eq. (14):
  `B_q^k|x> = |s_1,…,s_h> (Σ_{j<q-t} α^j β |j+t> + α^{q-t}|q>) |φ_q>^{⊗(k-h)}`.
* `cEnc` — Definition 4.1, Eq. (7): `C_m^k|x> = |s_1,…,s_h,m,…,m>`.

Theorem 4.3 (p. 9) states that the `B_q^k|x>` are orthonormal and that
`|φ_q>^{⊗(k+1)} = Σ_x α^{m-|x|} β^{|x|} B_q^k|x> + μ|ν'>` with `|ν'>`
orthogonal to every `B_q^k|x>` (Eq. (15)).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.GateEffSim12.MainResults.CompressedEncoding

/-! ## Boolean words and their gap encoding -/

/-- The Boolean word of a bit string `x : Fin m → Bool`. -/
def word {m : ℕ} (x : Fin m → Bool) : List Bool := List.ofFn x

/-- The zero-run lengths preceding the `1`s of a Boolean word: for
`w = 0^{s_1} 1 0^{s_2} 1 … 1 0^{s_h}` this is `[s_1, …, s_h]`.  This is the
paper's gap encoding used in Definitions 4.1 and 4.2 (Eqs. (7) and (14)). -/
def gapList : List Bool → List ℕ
  | [] => []
  | true :: tl => 0 :: gapList tl
  | false :: tl => (gapList tl).map (fun a => a + 1)

/-- Every gap of a word is at most the length of the word. -/
theorem gapList_entry_le : ∀ (w : List Bool) (a : ℕ), a ∈ gapList w → a ≤ w.length
  | [], a, ha => by simp [gapList] at ha
  | true :: tl, a, ha => by
      rcases (by simpa [gapList] using ha : a = 0 ∨ a ∈ gapList tl) with rfl | h
      · simp
      · have := gapList_entry_le tl a h
        simp only [List.length_cons]
        omega
  | false :: tl, a, ha => by
      obtain ⟨b, hb, rfl⟩ := by
        simpa [gapList, List.mem_map] using ha
      have := gapList_entry_le tl b hb
      simp only [List.length_cons]
      omega

/-- The number of trailing zeros of a Boolean word (the paper's `t`). -/
def trailingZeros (w : List Bool) : ℕ :=
  (w.reverse.takeWhile (fun b => b = false)).length

/-! ## The encoding `C_m^k` (Definition 4.1, Eq. (7)) -/

/-- Definition 4.1, Eq. (7) of arXiv:1211.4637v2 (p. 7): the compressed basis
state `C_m^k|x> = |s_1,…,s_h,m,…,m>` in `(k+1)` registers of dimension `m+1`.
Registers beyond the number of ones are padded with `m`; for words with more
than `k+1` ones the first `k+1` gap positions are encoded, as in the paper. -/
def cEnc {m k : ℕ} (x : Fin m → Bool) : Fin (k + 1) → Fin (m + 1) :=
  fun i =>
    if h : i.val < (gapList (word x)).length then
      ⟨(gapList (word x)).get ⟨i.val, h⟩,
        Nat.lt_succ_of_le (by
          have h1 : (gapList (word x)).get ⟨i.val, h⟩ ≤ (word x).length :=
            gapList_entry_le (word x) ((gapList (word x)).get ⟨i.val, h⟩)
              (List.get_mem (gapList (word x)) ⟨i.val, h⟩)
          simpa [word] using h1)⟩
    else ⟨m, Nat.lt_succ_self m⟩

/-! ## The state `|φ_q>` and its tensor powers (Eqs. (10) and (15)) -/

/-- Amplitude of `|φ_q> = Σ_{s<q} β α^s |s> + α^q |q>` (Eq. (10), p. 8) at
the basis state `|s>`. -/
def phiAmp (q : ℕ) (α β : ℝ) (s : ℕ) : ℂ :=
  if s < q then ((β * α ^ s : ℝ) : ℂ)
  else if s = q then ((α ^ q : ℝ) : ℂ) else 0

/-- The `(k+1)`-fold tensor power `|φ_q>^{⊗(k+1)}` of Eq. (15), as an amplitude
function on `(k+1)` registers with values in `{0, …, q}`. -/
def phiTensor (q k : ℕ) (α β : ℝ) (v : Fin (k + 1) → Fin (q + 1)) : ℂ :=
  ∏ i : Fin (k + 1), phiAmp q α β (v i).val

/-! ## The encoding `B_q^k` (Definition 4.2, Eq. (14)) -/

/-- Amplitude of the state `B_q^k|x>` of Definition 4.2, Eq. (14) (p. 8).
`g` is the list of gaps `s_1,…,s_h` of `x` and `t = m - Σ s_i - h` is its
number of trailing zeros.  The first `h` registers hold `s_1,…,s_h`; the
`(h+1)`-st register holds the superposition `Σ_{j<q-t} α^j β |j+t> +
α^{q-t}|q>`; the remaining registers hold `|φ_q>`. -/
def bVec {q k : ℕ} (α β : ℝ) (g : List ℕ) (t : ℕ) (hk : g.length ≤ k)
    (v : Fin (k + 1) → Fin (q + 1)) : ℂ :=
  (∏ i : Fin g.length,
      if (v ⟨i.val, (by omega)⟩).val = g.get i
      then (1 : ℂ) else 0) *
  (if (v ⟨g.length, by omega⟩).val = q then
      ((α ^ (q - t) : ℝ) : ℂ)
   else if t ≤ (v ⟨g.length, by omega⟩).val then
      ((β * α ^ ((v ⟨g.length, by omega⟩).val - t) : ℝ) : ℂ)
   else 0) *
  (∏ i : Fin (k + 1),
      if g.length < i.val then phiAmp q α β (v i).val else 1)

/-! ## Theorem 4.3 (p. 9) -/

/-- **Theorem 4.3, arXiv:1211.4637v2, p. 9 (Eqs. (15)–(18)).**  For `q ≥ m`,
the states `B_q^k|x>` with `|x| ≤ k` are orthonormal, and
`|φ_q>^{⊗(k+1)} = Σ_{|x|≤k} α^{m-|x|} β^{|x|} B_q^k|x> + μ|ν'>` with `|ν'>`
normalised and orthogonal to all `B_q^k|x>` (Eq. (15)).  Here `|x|` is the
number of ones, i.e. `(gapList (word x)).length`, and the residual `μ|ν'>` is
the sum (18) over words with `Σ s_i + k + 1 ≤ m`, quantified existentially.
The statement is recorded as the `Prop`-valued definition below; its proof is
not formalised.

Proof route (paper, pp. 9–10): expand `|φ_q>^{⊗(k+1)}` in the computational
basis as in Eq. (16); partition the basis states into the classes `P_x` (all
`|s'_1,…,s'_{k+1}>` whose encoded `m`-bit prefix is `x`, i.e. the first `h`
registers equal the gaps of `x`, the `(h+1)`-st is `≥ t`, the rest arbitrary)
and the residual class `Σ s_i + k + 1 ≤ m`; the sum over `P_x` is Eq. (17),
which is exactly `α^{m-|x|}β^{|x|} B_q^k|x>`; disjointness of the classes gives
orthogonality and orthonormality.

Lean gap: the combinatorial partition argument (that the classes `P_x` are
disjoint and cover the low-weight basis states, and the amplitude identity
Eq. (17)) is not formalised.  Candidate dependencies: this file's `phiAmp`,
`phiTensor`, `bVec`, `gapList`, and Mathlib's `Finset.prod_sum`/
`Finset.sum_comm` for the product-sum rearrangement of Eq. (16).  Suggested
tactics: prove `bVec` has support in `P_x` (`by_cases` on register equalities,
`simp [bVec]`), show `∑_v φ(v) · conj (B_x v) = α^{m-h}β^h` by
`Finset.sum_eq_single`/geometric-series summation `geom_sum_eq`, then
conclude orthonormality from disjoint supports via `Finset.sum_eq_zero`. -/
def theorem_4_3 (q k m : ℕ) (α β : ℝ) (hq : m ≤ q)
    (hα : α ^ 2 + β ^ 2 = 1) : Prop :=
  (∀ (x y : Fin m → Bool)
        (hx : (gapList (word x)).length ≤ k)
        (hy : (gapList (word y)).length ≤ k),
      (∑ v : Fin (k + 1) → Fin (q + 1),
          starRingEnd ℂ (bVec α β (gapList (word x))
              (m - (gapList (word x)).sum - (gapList (word x)).length) hx v) *
            bVec α β (gapList (word y))
              (m - (gapList (word y)).sum - (gapList (word y)).length) hy v)
        = if x = y then 1 else 0) ∧
    ∃ (μ : ℝ) (ν : (Fin (k + 1) → Fin (q + 1)) → ℂ),
      (∀ v : Fin (k + 1) → Fin (q + 1),
        phiTensor q k α β v =
          (∑ x : {x : Fin m → Bool // (gapList (word x)).length ≤ k},
            ((α ^ (m - (gapList (word x.val)).length) *
                β ^ (gapList (word x.val)).length : ℝ) : ℂ) *
              bVec α β (gapList (word x.val))
                (m - (gapList (word x.val)).sum - (gapList (word x.val)).length)
                x.property v) +
          (μ : ℂ) * ν v) ∧
      (∀ (x : {x : Fin m → Bool // (gapList (word x)).length ≤ k}),
        (∑ v : Fin (k + 1) → Fin (q + 1),
            starRingEnd ℂ (ν v) *
              bVec α β (gapList (word x.val))
                (m - (gapList (word x.val)).sum - (gapList (word x.val)).length)
                x.property v) = 0) ∧
      (∑ v : Fin (k + 1) → Fin (q + 1), starRingEnd ℂ (ν v) * ν v) = 1

end Qatlib.Papers.GateEffSim12.MainResults.CompressedEncoding
