/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Paper-layer source model for M. Imran and G. Ivanyos,
"Zero sum subsequences and hidden subgroups".

Fixed source version: arXiv:2304.08376v1 (17 Apr 2023), 20 pages.
PDF obtained from https://arxiv.org/pdf/2304.08376, text via `pdftotext -layout`.

This module fixes the vocabulary shared by every claim in block `MainResults`:
vectors over `Z_p`, signed subsets and their sums (paper §5), the weighted
relation `∑_i i·w_i = 0` of Lemma 3, collisions (Proposition 5) and the
deterministic witness predicates that model the paper's algorithms. A Lean
function is a total deterministic map, so "there is a deterministic procedure"
is modelled by an explicit witness map / existence predicate; the paper's
`poly(·)` running-time bookkeeping is represented by the explicit input-size
functions of Propositions 4/5 and by the number of subroutine applications.
No Turing-machine cost model is claimed here.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.ZeroSumImran24.MainResults

/-! ## Vectors and signed subsets -/

/-- The ambient space `Z_p^n` of the paper's zero-sum problem (§5). -/
abbrev ZVec (p n : ℕ) := Fin n → ZMod p

/-- A signed subset of an `S`-element sequence: an integer coefficient in
`{-1,0,1}` attached to every position (paper §5, "signed subsets"). -/
structure SignedSubset (S : ℕ) where
  coeff : Fin S → ℤ
  isSigned : ∀ i : Fin S, coeff i = -1 ∨ coeff i = 0 ∨ coeff i = 1

namespace SignedSubset

variable {S : ℕ}

/-- Support: positions carrying a nonzero coefficient (paper §5). -/
def support (σ : SignedSubset S) : Finset (Fin S) :=
  Finset.univ.filter (fun i => σ.coeff i ≠ 0)

/-- The `mem_support` result for the ZeroSumImran24 paper model. -/
@[simp] theorem mem_support {σ : SignedSubset S} {i : Fin S} :
    i ∈ σ.support ↔ σ.coeff i ≠ 0 := by
  simp [support]

/-- The signed subset sum in `Z_p^n` (paper §5): `∑_i c_i · v_i`. -/
def value (p n : ℕ) (v : Fin S → ZVec p n) (σ : SignedSubset S) : ZVec p n :=
  fun k => ∑ i : Fin S, (σ.coeff i : ZMod p) * v i k

/-- The empty signed subset (all coefficients zero). -/
def IsEmpty (σ : SignedSubset S) : Prop := σ.support = ∅

/-- A nonempty signed subset (some coefficient nonzero). -/
def Nonempty (σ : SignedSubset S) : Prop := σ.support.Nonempty

end SignedSubset

/-- Two signed subsets are disjoint when their supports are disjoint (§5). -/
def SupportDisjoint {S : ℕ} (σ τ : SignedSubset S) : Prop :=
  σ.support ∩ τ.support = ∅

/-- Pairwise disjointness of a finite family of signed subsets (§5). -/
def PairwiseSupportDisjoint {S d : ℕ} (σ : Fin d → SignedSubset S) : Prop :=
  ∀ i j : Fin d, i ≠ j → SupportDisjoint (σ i) (σ j)

/-- The paper's weighted relation `∑_{i=1}^{d} i · w_i = 0`, with `i` read as
an element of `Z_p` (Lemma 3, §5). -/
def weightedSum (p n d : ℕ) (w : Fin d → ZVec p n) : ZVec p n :=
  fun k => ∑ i : Fin d, ((i.val + 1 : ℕ) : ZMod p) * w i k

/-! ## Deterministic witness predicates modelling the paper's procedures -/

/-- Hypothesis of Lemma 3 (§5, p.14): a deterministic procedure `A` which,
from `h d m` vectors in `Z_p^m`, produces `d` pairwise-disjoint signed subset
sums, not all empty, satisfying `∑_{i=1}^d i·v_i = 0`. Formalised as the
existence guarantee for every dimension `m` and every input sequence of length
`S ≥ h d m`; `A` is used at two different dimensions in the proof. -/
def HasWeightedZeroSumExtractor (p d : ℕ) (h : ℕ → ℕ → ℕ) : Prop :=
  ∀ (m S : ℕ), h d m ≤ S → ∀ v : Fin S → ZVec p m,
    ∃ σ : Fin d → SignedSubset S,
      PairwiseSupportDisjoint σ ∧
      (∃ i : Fin d, (σ i).Nonempty) ∧
      weightedSum p m d (fun i => (σ i).value p m v) = 0

/-- A collision (§5, before Proposition 5): two disjoint signed subsets whose
sums are equal and of which not both are empty. A nonempty zero-sum signed
subset is the special case `τ = ∅`. -/
def IsCollision (p n : ℕ) {S : ℕ} (v : Fin S → ZVec p n)
    (σ τ : SignedSubset S) : Prop :=
  SupportDisjoint σ τ ∧
  ((σ.Nonempty) ∨ (τ.Nonempty)) ∧
  (σ.value p n v = τ.value p n v)

/-- Hypothesis of Proposition 5 (§5, p.16): an algorithm `B` finding a
collision in any `S`-element set of vectors of `Z_p^n`. -/
def HasCollisionFinder (p n S : ℕ) : Prop :=
  ∀ v : Fin S → ZVec p n, ∃ σ τ : SignedSubset S, IsCollision p n v σ τ

/-- A nonempty zero-sum subsequence of the input sequence (Theorem 2). -/
def IsZeroSumSubsequence (p n : ℕ) {S : ℕ} (v : Fin S → ZVec p n)
    (J : Finset (Fin S)) : Prop :=
  J.Nonempty ∧ (∑ j ∈ J, v j) = 0

/-- Existence of a nontrivial (nonempty) zero-sum subsequence (Theorem 2). -/
def HasNontrivialZeroSumSubsequence (p n S : ℕ) (v : Fin S → ZVec p n) : Prop :=
  ∃ J : Finset (Fin S), IsZeroSumSubsequence p n v J

/-- Existence of a nontrivial signed zero-sum subset (Proposition 4). -/
def HasNontrivialSignedZeroSum (p n S : ℕ) (v : Fin S → ZVec p n) : Prop :=
  ∃ σ : SignedSubset S, σ.Nonempty ∧ σ.value p n v = 0

/-! ## Elementary algebraic facts about signed subsets -/

/-- The coefficient set `{-1,0,1}` is closed under multiplication. -/
theorem signed_mul_closed {a b : ℤ}
    (ha : a = -1 ∨ a = 0 ∨ a = 1) (hb : b = -1 ∨ b = 0 ∨ b = 1) :
    a * b = -1 ∨ a * b = 0 ∨ a * b = 1 := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> decide

end Qatlib.Papers.ZeroSumImran24.MainResults
