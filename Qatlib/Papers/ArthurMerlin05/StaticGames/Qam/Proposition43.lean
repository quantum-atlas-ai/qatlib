/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ArthurMerlin05.StaticGames.Model.PaperGamesModel

/-!
# Proposition 4.3 — random Arthur-coin sampling bound

Source: Marriott--Watrous, *Quantum Arthur--Merlin Games*, arXiv:cs/0506068v1,
Proposition 4.3 (page 17), proof page 17.

Statement (verbatim): if `{A_{x,y}}` is a QAM verification procedure for `L`
with completeness and soundness errors bounded by `1/9`, then for a uniformly
random `y ∈ Σ^{s(|x|)}`,
`x ∈ L ⇒ Pr[μ(A_{x,y}) ≥ 2/3] ≥ 2/3` and
`x ∉ L ⇒ Pr[μ(A_{x,y}) ≤ 1/3] ≥ 2/3`.

The proof is Markov's inequality applied to `Z(y) = 1 − μ(A_{x,y})` (for
`x ∈ L`): `E[Z] ≤ 1/9`, hence `Pr[Z > 1/3] ≤ E[Z]/(1/3) ≤ 1/3`, i.e.
`Pr[μ ≥ 2/3] ≥ 2/3`.  The `x ∉ L` direction is the same argument with
`Z(y) = μ(A_{x,y})`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ArthurMerlin05.StaticGames.Qam

open Qatlib.Papers.ArthurMerlin05.StaticGames

/-- The Markov step behind Proposition 4.3 (page 17): if `Z : Y → [0,∞)` has
mean at most `1/9`, then a fraction at least `2/3` of the points satisfy
`Z ≤ 1/3`. -/
theorem markov_threshold {Y : Type*} [Fintype Y] (Z : Y → ℝ)
    (hNpos : 0 < Fintype.card Y)
    (hZ : ∀ y, 0 ≤ Z y)
    (hmean : (∑ y, Z y) / (Fintype.card Y : ℝ) ≤ 1 / 9) :
    (↑(Finset.univ.filter (fun y => Z y ≤ 1 / 3)).card : ℝ) / (Fintype.card Y : ℝ) ≥
      2 / 3 := by
  classical
  set N : ℝ := (Fintype.card Y : ℝ) with hN
  have hN0 : 0 < N := by rw [hN]; exact_mod_cast hNpos
  set S := Finset.univ.filter (fun y => Z y ≤ 1 / 3) with hS
  set T := Finset.univ.filter (fun y => ¬ Z y ≤ 1 / 3) with hT
  have hsplit : (∑ y, Z y) = (∑ y ∈ S, Z y) + (∑ y ∈ T, Z y) := by
    rw [hS, hT]
    rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset Y))
      (f := Z) (p := fun y => Z y ≤ 1 / 3)]
  have hTmass : (∑ y ∈ T, (1 / 3 : ℝ)) ≤ (∑ y ∈ T, Z y) := by
    refine Finset.sum_le_sum ?_
    intro y hy
    have : ¬ Z y ≤ 1 / 3 := (Finset.mem_filter.mp hy).2
    linarith
  have hTcard : (∑ _y ∈ T, (1 / 3 : ℝ)) = (T.card : ℝ) / 3 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hSmass : 0 ≤ (∑ y ∈ S, Z y) :=
    Finset.sum_nonneg fun y _ => hZ y
  have htotal : (∑ y, Z y) ≤ N / 9 := by
    have h := (div_le_iff₀ hN0).mp hmean
    simpa [hN, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hTle : (T.card : ℝ) / 3 ≤ N / 9 := by
    calc
      (T.card : ℝ) / 3 = (∑ y ∈ T, (1 / 3 : ℝ)) := hTcard.symm
      _ ≤ (∑ y ∈ T, Z y) := hTmass
      _ ≤ (∑ y ∈ S, Z y) + (∑ y ∈ T, Z y) := le_add_of_nonneg_left hSmass
      _ = (∑ y, Z y) := hsplit.symm
      _ ≤ N / 9 := htotal
  have hTle' : (T.card : ℝ) ≤ N / 3 := by linarith
  have hcard : (S.card : ℝ) + (T.card : ℝ) = N := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset Y)) (p := fun y => Z y ≤ 1 / 3)
    have hsum : (S.card + T.card : ℕ) = Fintype.card Y := by
      rw [hS, hT, h, Finset.card_univ]
    have hcast : ((S.card : ℝ) + (T.card : ℝ)) = (Fintype.card Y : ℝ) := by
      rw [← Nat.cast_add, hsum]
    rw [hcast, ← hN]
  have hSge : (S.card : ℝ) ≥ 2 * N / 3 := by linarith
  have hone : (2 / 3 : ℝ) ≤ (S.card : ℝ) / N := by
    rw [le_div_iff₀ hN0]
    nlinarith [hSge]
  simpa [hS, hN, ge_iff_le] using hone

/-- Proposition 4.3 (page 17), `x ∈ L` direction: if the completeness error is
at most `1/9` (`coinAverage (1 − μ) ≤ 1/9`), then with probability at least
`2/3` over the uniform coin string `y`, `μ(A_{x,y}) ≥ 2/3`. -/
theorem prop_4_3_yes {s : ℕ} (μ : Fin (Qdim s) → ℝ)
    (hμ1 : ∀ y, μ y ≤ 1)
    (hcomp : coinAverage (fun y => 1 - μ y) ≤ 1 / 9) :
    (↑(Finset.univ.filter (fun y => 2 / 3 ≤ μ y)).card : ℝ) / (Qdim s : ℝ) ≥ 2 / 3 := by
  have hNpos : 0 < Fintype.card (Fin (Qdim s)) := by
    rw [Fintype.card_fin]
    exact Nat.pos_of_ne_zero (by positivity)
  have hZ : ∀ y : Fin (Qdim s), 0 ≤ 1 - μ y := fun y => by linarith [hμ1 y]
  have hmean : (∑ y, (1 - μ y)) / (Fintype.card (Fin (Qdim s)) : ℝ) ≤ 1 / 9 := by
    simpa [coinAverage, Fintype.card_fin] using hcomp
  have h := markov_threshold (fun y : Fin (Qdim s) => 1 - μ y) hNpos hZ hmean
  have hfilt : (Finset.univ.filter (fun y : Fin (Qdim s) => 1 - μ y ≤ 1 / 3)) =
      (Finset.univ.filter (fun y : Fin (Qdim s) => 2 / 3 ≤ μ y)) := by
    apply Finset.filter_congr
    intro y __
    constructor <;> intro hh <;> linarith
  rw [hfilt] at h
  simpa [Fintype.card_fin] using h

/-- Proposition 4.3 (page 17), `x ∉ L` direction: if the soundness error is at
most `1/9` (`coinAverage μ ≤ 1/9`) and `μ ∈ [0,1]`, then with probability at
least `2/3` over `y`, `μ(A_{x,y}) ≤ 1/3`. -/
theorem prop_4_3_no {s : ℕ} (μ : Fin (Qdim s) → ℝ)
    (hμ0 : ∀ y, 0 ≤ μ y)
    (hsnd : coinAverage μ ≤ 1 / 9) :
    (↑(Finset.univ.filter (fun y => μ y ≤ 1 / 3)).card : ℝ) / (Qdim s : ℝ) ≥ 2 / 3 := by
  have hNpos : 0 < Fintype.card (Fin (Qdim s)) := by
    rw [Fintype.card_fin]
    exact Nat.pos_of_ne_zero (by positivity)
  have hmean : (∑ y, μ y) / (Fintype.card (Fin (Qdim s)) : ℝ) ≤ 1 / 9 := by
    simpa [coinAverage, Fintype.card_fin] using hsnd
  have h := markov_threshold μ hNpos hμ0 hmean
  simpa [Fintype.card_fin] using h

/-- Proposition 4.3 (page 17), full statement.  `μ : Fin (2^{s}) → [0,1]` are
the maximum acceptance probabilities `μ(A_{x,y})`; `hcomp`/`hsnd` encode the
completeness/soundness error bound `1/9`. -/
theorem prop_4_3 {s : ℕ} (μ : Fin (Qdim s) → ℝ)
    (hμ0 : ∀ y, 0 ≤ μ y) (hμ1 : ∀ y, μ y ≤ 1)
    (hcomp : coinAverage (fun y => 1 - μ y) ≤ 1 / 9)
    (hsnd : coinAverage μ ≤ 1 / 9) :
    ((↑(Finset.univ.filter (fun y => 2 / 3 ≤ μ y)).card : ℝ) / (Qdim s : ℝ) ≥ 2 / 3) ∧
      ((↑(Finset.univ.filter (fun y => μ y ≤ 1 / 3)).card : ℝ) / (Qdim s : ℝ) ≥ 2 / 3) :=
  ⟨prop_4_3_yes μ hμ1 hcomp, prop_4_3_no μ hμ0 hsnd⟩

end Qatlib.Papers.ArthurMerlin05.StaticGames.Qam
