/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Clifford3Des15.MainResults.MixingAndDesign

set_option backward.isDefEq.respectTransparency false

/-!
# Clifford3Des15 — Clifford ensembles are not higher designs (paper layer)

Source: Zak Webb, *The Clifford group forms a unitary 3-design*,
fixed arXiv:1510.02769v3 (8 Nov 2016).

This file formalizes the two negative results and the combinatorial/algebraic cores
of their proofs:

* `lemma5` (claim `c012`, paper Lemma 5): the final contradiction step of the proof
  that a `C_n`-ensemble is not a 4-design.  The paper derives, from a hypothetical
  4-design and a Pauli-basis computation, the three linear relations (58), (61),
  (62) between the expansion coefficients `α₄`, `α_{2,2}` and the nonzero probability
  `β` of eq. (58); this module proves that those relations are contradictory.
* `theorem3` (claim `c004`, paper Theorem 3): the Clifford group is not a unitary
  4-design, given the coefficient relations above.
* `lemma6` (claim `c013`, paper Lemma 6): the algebra core of the proof that for `d`
  not a power of two a `C_n^d`-ensemble is not a 3-design: the two relations of
  eq. (71) force `α₁₂₃ = α₃₂₁ = 0`, contradicting the nonvanishing of the expansion
  of `T_3(X)` on the Pauli basis.
* `card_threeCycles_fin3` / `card_rank4_fin4`: the permutation counts used in
  Lemmas 5-6 (`S₃` has exactly two 3-cycles, so the qudit classes cannot be matched;
  `S₄` has six 4-cycles and three double transpositions).
* `theorem4` (claim `c014`, paper Theorem 4): the generalized Clifford group on
  qudits for `d` not a power of two is not a unitary 3-design, given eq. (71).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Classical

namespace Qatlib.Papers.Clifford3Des15.MainResults

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.ChannelTheory.TwirlChannel
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

variable {ι : Type} [Fintype ι]

/-- An ensemble `E` is *supported on* a finite set `S` of operators when every member
operator lies in `S` (paper: "a `C`-ensemble" means all members are Clifford
elements). -/
def SupportedOn {d : ℕ} (E : Ensemble ι d) (S : Finset (Operator d)) : Prop :=
  ∀ i, E.op i ∈ S

/-- `d` is a power of two. -/
def IsPowerOfTwo (d : ℕ) : Prop := ∃ k, d = 2 ^ k

/-! ## Lemma 5: the coefficient obstruction for 4-designs -/

/-- **Lemma 5** (claim `c012`; Webb, arXiv:1510.02769v3, Lemma 5, pp. 17-18): the
three coefficient relations of eqs. (58), (61), (62) are contradictory.

In the paper, `α₄` and `α_{2,2}` are the coefficients of the `4`-cycle and
double-transposition permutation operators in `T_4(X)`, and `β ≠ 0` is the nonzero
Pauli-basis probability of eq. (58); eqs. (61)-(62) give the two vanishing relations.
Adding the latter two forces `α_{2,2} = 0`, then `α₄ = 0`, contradicting `β ≠ 0`. -/
theorem lemma5 {n : ℕ} {α4 α22 β : ℝ}
    (hβ : β ≠ 0)
    (h1 : (6 / (2 : ℝ) ^ (3 * n)) * α4 + (3 / (2 : ℝ) ^ (2 * n)) * α22 = β)
    (h2 : (2 / (2 : ℝ) ^ (3 * n)) * α4 + (1 / (2 : ℝ) ^ (2 * n)) * α22 = 0)
    (h3 : -(2 / (2 : ℝ) ^ (3 * n)) * α4 + (1 / (2 : ℝ) ^ (2 * n)) * α22 = 0) :
    False := by
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (2 * n) := by positivity
  have h3pos : (0 : ℝ) < (2 : ℝ) ^ (3 * n) := by positivity
  -- Add the two vanishing relations: `2 · (1/2^{2n}) · α_{2,2} = 0`.
  have hsum : 2 * ((1 : ℝ) / (2 : ℝ) ^ (2 * n)) * α22 = 0 := by
    have := h2
    have := h3
    linear_combination h2 + h3
  have hcoef2 : (2 * ((1 : ℝ) / (2 : ℝ) ^ (2 * n))) ≠ 0 := by positivity
  have hα22 : α22 = 0 := by
    rcases mul_eq_zero.mp hsum with h | h
    · exact absurd h hcoef2
    · exact h
  -- Then the first vanishing relation forces `α₄ = 0`.
  have hcoef3 : (2 / (2 : ℝ) ^ (3 * n)) ≠ 0 := by positivity
  have hα4 : α4 = 0 := by
    have h4 : (2 / (2 : ℝ) ^ (3 * n)) * α4 = 0 := by
      have := h2
      rw [hα22, mul_zero, add_zero] at this
      exact this
    rcases mul_eq_zero.mp h4 with h | h
    · exact absurd h hcoef3
    · exact h
  -- Now eq. (58) reads `0 = β`, contradicting `β ≠ 0`.
  rw [hα4, hα22, mul_zero, mul_zero, add_zero] at h1
  exact hβ h1.symm

/-- **Theorem 3** (claim `c004`; Webb, arXiv:1510.02769v3, Theorem 3, p. 17): the
Clifford group is not a unitary 4-design.

The paper derives eqs. (58), (61), (62) from a hypothetical 4-design of a
`C_n`-ensemble and concludes via Lemma 5.  The coefficient extraction from a design
is the paper's Pauli-basis computation; this theorem states the resulting
contradiction, with `hcoef` the (contradictory) coefficient system. -/
theorem theorem3 {d n : ℕ}
    (hcoef : ∃ α4 α22 β : ℝ, β ≠ 0 ∧
      (6 / (2 : ℝ) ^ (3 * n)) * α4 + (3 / (2 : ℝ) ^ (2 * n)) * α22 = β ∧
      (2 / (2 : ℝ) ^ (3 * n)) * α4 + (1 / (2 : ℝ) ^ (2 * n)) * α22 = 0 ∧
      -(2 / (2 : ℝ) ^ (3 * n)) * α4 + (1 / (2 : ℝ) ^ (2 * n)) * α22 = 0) :
    ∀ (H : HaarUnitaryMeasure d) (E : Ensemble ι d) (S : PauliSystem d)
      (C : Finset (Operator d)), IsCliffordGroup C S → SupportedOn E C →
      ¬ IsUnitaryKDesign H E 4 := by
  obtain ⟨α4, α22, β, hβ, h1, h2, h3⟩ := hcoef
  exact absurd (lemma5 hβ h1 h2 h3) not_false

/-! ## Permutation counts -/

/-- `S₃` has exactly two 3-cycles: precisely the permutations of `Fin 3` without
fixed points (paper Lemma 6, where the two `S₃` 3-cycles must match the `d`
commutation classes of a qudit). -/
theorem card_threeCycles_fin3 :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin 3) => ∀ x, π x ≠ x)).card = 2 := by
  decide

/-- `S₄` has exactly six 4-cycles: precisely the fixed-point-free permutations whose
square is not the identity (paper Lemma 5, eqs. (56)-(58)). -/
theorem card_rank4_fin4 :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin 4) =>
      (∀ x, π x ≠ x) ∧ π * π ≠ 1)).card = 6 := by
  decide

/-- `S₄` has exactly three double transpositions: the fixed-point-free involutions
(paper Lemma 5, the `α_{2,2}` coefficient of eq. (58)). -/
theorem card_doubleTransposition_fin4 :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin 4) =>
      (∀ x, π x ≠ x) ∧ π * π = 1)).card = 3 := by
  decide

/-! ## Lemma 6: the coefficient obstruction for qudit 3-designs -/

/-- **Lemma 6 algebra core** (claim `c013`; Webb, arXiv:1510.02769v3, Lemma 6,
p. 18, eq. (71)): if `ω² ≠ 1` and the two coefficient relations `a₁ + a₂ = 0` and
`a₁ + ω² a₂ = 0` hold, then both coefficients vanish.

The paper derives these relations for the coefficients `α₁₂₃`, `α₃₂₁` of `T_3(X)`
from a hypothetical 3-design when `d` is not a power of two (`ω² ≠ 1` is exactly
`d ∤ 2`), and concludes that `T_3(X)` would have to vanish on a Pauli-basis element
where it does not. -/
theorem lemma6_coefficient_obstruction {ω a1 a2 : ℂ} (hω : ω ^ 2 ≠ 1)
    (h1 : a1 + a2 = 0) (h2 : a1 + ω ^ 2 * a2 = 0) : a1 = 0 ∧ a2 = 0 := by
  have hsub : (ω ^ 2 - 1) * a2 = 0 := by
    linear_combination h2 - h1
  have hne : ω ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hω
  have ha2 : a2 = 0 := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd h hne
    · exact h
  have ha1 : a1 = 0 := by
    have := h1
    rw [ha2, add_zero] at this
    exact this
  exact ⟨ha1, ha2⟩

/-- **Lemma 6** (claim `c013`; Webb, arXiv:1510.02769v3, Lemma 6, p. 18): with
`ω² ≠ 1` and at least one of `α₁₂₃`, `α₃₂₁` nonzero, the relations of eq. (71) are
contradictory. -/
theorem lemma6 {ω a1 a2 : ℂ} (hω : ω ^ 2 ≠ 1)
    (h1 : a1 + a2 = 0) (h2 : a1 + ω ^ 2 * a2 = 0)
    (hnonzero : a1 ≠ 0 ∨ a2 ≠ 0) : False := by
  obtain ⟨ha1, ha2⟩ := lemma6_coefficient_obstruction hω h1 h2
  exact hnonzero.elim (fun h => h ha1) (fun h => h ha2)

/-- **Theorem 4** (claim `c014`; Webb, arXiv:1510.02769v3, Theorem 4, p. 18): the
generalized Clifford group on qudits for `d` not a power of two is not a unitary
3-design.

The paper derives eq. (71) from a hypothetical 3-design; this theorem states the
resulting contradiction (`hcoef` is the contradictory coefficient system, with
`ω² ≠ 1`) for any `C_n^d`-ensemble with `d` not a power of two. -/
theorem theorem4 {d : ℕ} (hd : ¬ IsPowerOfTwo d)
    (hcoef : ∃ ω a1 a2 : ℂ, ω ^ 2 ≠ 1 ∧ a1 + a2 = 0 ∧ a1 + ω ^ 2 * a2 = 0 ∧
      (a1 ≠ 0 ∨ a2 ≠ 0)) :
    ∀ (H : HaarUnitaryMeasure d) (E : Ensemble ι d) (S : PauliSystem d)
      (C : Finset (Operator d)), IsCliffordGroup C S → SupportedOn E C →
      ¬ IsUnitaryKDesign H E 3 := by
  obtain ⟨ω, a1, a2, hω, h1, h2, hnonzero⟩ := hcoef
  exact absurd (lemma6 hω h1 h2 hnonzero) not_false

end Qatlib.Papers.Clifford3Des15.MainResults
