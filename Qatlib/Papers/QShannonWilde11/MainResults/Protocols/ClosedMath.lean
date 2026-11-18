/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.ChannelCaps

@[expose] public section


/-!
# Reviewed closed fragment of Wilde, arXiv:1106.1445v8

Only closed definitions and proofs are present. Capacity records have unconstrained
fields; conditional limits and averaging steps do not establish operational coding
or source algorithm costs. See the per-declaration source review receipt.
-/

namespace Qatlib.Papers.QShannonWilde11.MainResults.Protocols

open Matrix
open Classical
open Qatlib.Papers.QShannonWilde11.MainResults.Model
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

/-- Typicality of a length-`n` sequence w.r.t. `p` at tolerance `δ`. -/
def IsTypical {X : Type} [Fintype X] (p : X → ℝ) (n : ℕ) (δ : ℝ)
    (xn : Fin n → X) : Prop :=
  |(1 / (n : ℝ)) * (∑ i, -Real.log (p (xn i))) - classicalEntropy p| ≤ δ

/-- Conditional typicality of `yn` given `xn`. -/
def IsCondTypical {X Y : Type} [Fintype X] [Fintype Y] (pXY : X × Y → ℝ)
    (n : ℕ) (δ : ℝ) (xn : Fin n → X) (yn : Fin n → Y) : Prop :=
  |(1 / (n : ℝ)) *
      (∑ i, -Real.log (pXY (xn i, yn i) / (∑ y, pXY (xn i, y)))) -
    (classicalEntropy pXY - classicalEntropy (fun x => ∑ y, pXY (x, y)))| ≤ δ

/-- Ordered product of a list of matrices. -/
def matProd {d : ℕ} (L : List (Matrix (Fin d) (Fin d) ℂ)) :
    Matrix (Fin d) (Fin d) ℂ := L.foldr (· * ·) 1

/-- Averaging lemma: if a real number is bounded by the `Pr`-average of `f`
over a finite probability space, then some point attains at least that value.
This is the probabilistic-method step shared by the packing, derandomisation and
covering lemmas (Lem 16.3.1, Cor 16.5.1, Lem 17.2.1); it is proved by
contradiction from `∑ Pr·f < ∑ Pr·a = a` when every `f ω < a`. -/
theorem exists_ge_of_weighted_average {Ω : Type} [Fintype Ω] (Pr : Ω → ℝ)
    (hPr : IsProb Pr) (f : Ω → ℝ) (a : ℝ)
    (havg : a ≤ ∑ ω, Pr ω * f ω) :
    ∃ ω, a ≤ f ω := by
  by_contra h
  push Not at h
  have hne : ∃ ω, 0 < Pr ω := by
    by_contra h0
    push Not at h0
    have hzero : ∑ ω, Pr ω = 0 :=
      Finset.sum_eq_zero (fun ω _ => le_antisymm (h0 ω) (hPr.1 ω))
    linarith [hPr.2]
  obtain ⟨ω₀, hω₀⟩ := hne
  have hlt : ∑ ω, Pr ω * f ω < ∑ ω, Pr ω * a := by
    apply Finset.sum_lt_sum
    · intro ω _
      exact mul_le_mul_of_nonneg_left (le_of_lt (h ω)) (hPr.1 ω)
    · exact ⟨ω₀, Finset.mem_univ ω₀, mul_lt_mul_of_pos_left (h ω₀) hω₀⟩
  have hconst : ∑ ω, Pr ω * a = a := by
    rw [← Finset.sum_mul, hPr.2, one_mul]
  linarith

/-- A scalar sample attains the packing-shaped lower bound supplied for its average.
This is the averaging step associated with Lemma 16.3.1 of arXiv:1106.1445v8,
fixed PDF p. 488. The analytic bound is assumed in `havg`; this statement does
not construct a code or POVM or establish the source packing estimate. -/
theorem exists_success_ge_packing_bound_of_average
    {Ω : Type} [Fintype Ω] (Pr : Ω → ℝ) (hPr : IsProb Pr)
    (succ : Ω → ℝ) (ε : ℝ) (M d D : ℝ)
    (_hD : 0 < D) (havg : 1 - 2 * (Real.sqrt ε + 2 * ε - 4 * M * d / D) ≤
      ∑ ω, Pr ω * succ ω) :
    ∃ ω, 1 - 2 * (Real.sqrt ε + 2 * ε - 4 * M * d / D) ≤ succ ω :=
  exists_ge_of_weighted_average Pr hPr succ _ havg

/-- A scalar sample attains the derandomisation-shaped bound assumed for its average.
This is the averaging step associated with Corollary 16.5.1 of arXiv:1106.1445v8,
fixed PDF p. 496. It supplies neither a code or POVM nor a per-message guarantee;
the analytic estimate is the hypothesis `havg`. -/
theorem exists_success_ge_derandomisation_bound_of_average
    {Ω : Type} [Fintype Ω] (Pr : Ω → ℝ) (hPr : IsProb Pr)
    (succ : Ω → ℝ) (ε : ℝ) (M d D : ℝ) (_hD : 0 < D)
    (havg : 1 - 4 * (Real.sqrt ε + 2 * ε - 16 * M * d / D) ≤
      ∑ ω, Pr ω * succ ω) :
    ∃ ω, 1 - 4 * (Real.sqrt ε + 2 * ε - 16 * M * d / D) ≤ succ ω :=
  exists_ge_of_weighted_average Pr hPr succ _ havg

/-- An error sample attains a lower bound supplied for its weighted average.
The expression comes from the legacy target for Lemma 17.2.1 of
arXiv:1106.1445v8, fixed PDF p. 507. The conclusion is a lower bound on one
scalar error value, not a covering-code error upper bound or a tail estimate. -/
theorem exists_error_ge_covering_bound_of_average
    {Ω : Type} [Fintype Ω] (Pr : Ω → ℝ) (hPr : IsProb Pr)
    (oe : Ω → ℝ) (ε : ℝ) (_M _d D : ℝ) (_hD : 0 < D) (_hε : 0 ≤ ε)
    (havg : ε + 4 * Real.sqrt ε + 24 * ε ≤ ∑ ω, Pr ω * oe ω) :
    ∃ ω, ε + 4 * Real.sqrt ε + 24 * ε ≤ oe ω :=
  exists_ge_of_weighted_average Pr hPr oe _ havg

end

end Qatlib.Papers.QShannonWilde11.MainResults.Protocols
