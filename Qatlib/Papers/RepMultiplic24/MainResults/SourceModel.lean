/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Combinatorics.Young.SemistandardTableau
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# RepMultiplic24.MainResults — source model

Paper: *Quantum Algorithms for Representation-Theoretic Multiplicities*,
fixed arXiv:2407.17649 (2024). The source PDF/text were read locally; the qatlas
markdown endpoint was unavailable (server-side 503, issue #4).

This file provides the paper-layer vocabulary shared by the individual claim files:

* the two-outcome **shot law** of Eq. (10) / Eq. (17), the empirical frequency
  estimator and the rounding estimator used in the supplementary proof of
  Lemma 2 (Eq. (94)-(97));
* the **shot cost** bookkeeping for the circuit of Theorem 1 / Theorem 3
  (single shot = H-QFT + state preparation + controlled regular action);
* the **hook-length dimension** `d_λ` of an `Sₙ` irrep (hook-length formula,
  Eq. (37)) and the **Kostka number** as the number of semistandard tableaux of
  given shape and content (Supp. Mat. around Eq. (99)-(101));
* the combinatorics needed to state Proposition 1: cells, standard Young
  tableaux and Yamanouchi words (Def. around Eq. (26)-(28)).

Boundary. There is no representation theory of the symmetric group in the
library (neither in `QuantumAlgorithmDev/` nor in Frozen v2.0.2), so the actual
irreps, their restriction/induction and their characters are **not** formalised.
The statements below are therefore stated in the paper's computational
vocabulary: dimensions, multiplicities and shot frequencies. The probability
content is genuine (finite distributions, Chebyshev); the representation-theoretic
content is carried by the dimension/multiplicity parameters exactly as in the
paper's formulas.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.RepMultiplic24.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open scoped BigOperators unitInterval

/-! ## Bernoulli shot law and frequency estimator -/

/-- The two-outcome law of one shot of the multiplicity algorithm. `true` means that
the measured irrep label is the requested label `β` (resp. `α`); by Eq. (10) the
probability is `p = mult · dβ / dα`, and by Eq. (17) it is
`p = mult · |H| dα / (|G| dβ)`. Both are of the form `p = m · ε` for an integral
multiplicity `m` and a scale `ε` supplied by the paper. The parameter is packaged
in the unit interval `I`, so no proof argument is needed at the call site. -/
noncomputable def bernoulliLaw (p : I) : FinDist Bool where
  prob b := if b then (p : ℝ) else 1 - (p : ℝ)
  nonneg b := by
    cases b
    · simp only [Bool.false_eq_true, if_false]
      have := p.2.2
      linarith
    · simp only [if_true]
      exact p.2.1
  sum_one := by
    rw [Fintype.sum_bool]
    simp

/-- The indicator of a successful shot. -/
def shotIndicator (b : Bool) : ℝ := if b then 1 else 0

/-- The mean of the shot indicator under the shot law is the single-shot probability. -/
theorem expect_bernoulli_indicator (p : I) :
    (bernoulliLaw p).expect shotIndicator = (p : ℝ) := by
  rw [FinDist.expect, Fintype.sum_bool]
  simp [bernoulliLaw, shotIndicator]

/-- The variance of the shot indicator is `p(1-p)`, hence at most `p`. -/
theorem variance_bernoulli_indicator_le (p : I) :
    (bernoulliLaw p).variance shotIndicator ≤ (p : ℝ) := by
  have hcalc : (bernoulliLaw p).variance shotIndicator = (p : ℝ) * (1 - (p : ℝ)) := by
    unfold FinDist.variance
    rw [expect_bernoulli_indicator p]
    rw [FinDist.expect, Fintype.sum_bool]
    simp only [bernoulliLaw, shotIndicator, Bool.false_eq_true, if_false, if_true,
      Fin.sum_univ_two, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
      one_mul, smul_eq_mul]
    ring
  rw [hcalc]
  have h1 : 1 - (p : ℝ) ≤ 1 := by linarith [p.2.1]
  have h2 := mul_le_mul_of_nonneg_left h1 p.2.1
  linarith [h2]

/-- The rounded frequency estimator: given the empirical mean frequency of a run of
shots and the single-shot scale `ε`, round `frequency / ε` to the nearest integer.
This is the quantity `X dα / (dβ N)` (resp. `X |G| dβ / (|H| dα N)`) rounded in the
proof of Lemma 2, Eq. (95)-(97). -/
noncomputable def frequencyEstimate {N : ℕ} (ε : ℝ) (ω : Fin N → Bool) : ℕ :=
  Nat.floor (FinDist.avg shotIndicator ω / ε + 1 / 2)

/-- Failure event of the frequency estimator: the empirical frequency is more than
`ε/4` away from the true single-shot probability `p = m·ε`. -/
abbrev frequencyBad {N : ℕ} (p ε : ℝ) (ω : Fin N → Bool) : Prop :=
  ε / 4 < |FinDist.avg shotIndicator ω - p|

/-- **Core finite concentration lemma (engine of Lemma 2).**

Let each shot be independently distributed according to `bernoulliLaw p`, where
`p = m·ε` for an integral multiplicity `m` and a scale `ε`. If the number of shots
satisfies `16 p ≤ C ε² N` then

* the probability that the empirical frequency deviates from `p` by more than
  `ε/4` is at most `C` (Chebyshev applied to the indicator of a success), and
* on the complementary event the rounded estimator returns exactly `m`.

This is the finite-probability version of the Chernoff/Chebyshev step of
Supp. Mat. Eq. (94)-(97). The quarter-`ε` margin (instead of the paper's `ε/2`)
avoids the half-integer rounding boundary and changes only the universal constant;
the shot count is still `Θ(1/ε²)`. -/
theorem shot_estimation_bound (p : I) {ε : ℝ} {m N : ℕ}
    (hε : 0 < ε) (hN : 0 < N)
    (hpm : (p : ℝ) = (m : ℝ) * ε)
    {C : ℝ} (hC0 : 0 < C) (hC1 : C < 1)
    (hbound : 16 * (p : ℝ) ≤ C * ε ^ 2 * (N : ℝ)) :
    (∑ ω ∈ Finset.univ.filter (frequencyBad (N := N) (p : ℝ) ε),
        (bernoulliLaw p).probOf ω) ≤ C ∧
      ∀ ω : Fin N → Bool, ¬ frequencyBad (N := N) (p : ℝ) ε ω →
        frequencyEstimate ε ω = m := by
  classical
  have hε4 : 0 < ε / 4 := by positivity
  have hcheb := FinDist.chebyshev_avg (bernoulliLaw p) shotIndicator hN (ε / 4) hε4
  have hexp : (bernoulliLaw p).expect shotIndicator = (p : ℝ) :=
    expect_bernoulli_indicator p
  have hvar : (bernoulliLaw p).variance shotIndicator ≤ (p : ℝ) :=
    variance_bernoulli_indicator_le p
  constructor
  · -- rewrite the Chebyshev statement and bound the variance term
    have hcheb' : (∑ ω ∈ Finset.univ.filter (frequencyBad (N := N) (p : ℝ) ε),
        (bernoulliLaw p).probOf ω) ≤
        (bernoulliLaw p).variance shotIndicator / ((N : ℝ) * (ε / 4) ^ 2) := by
      simpa only [FinDist.probEvent, frequencyBad, hexp] using hcheb
    refine le_trans hcheb' ?_
    have hden : (0 : ℝ) < (N : ℝ) * (ε / 4) ^ 2 := by positivity
    have hstep : (bernoulliLaw p).variance shotIndicator / ((N : ℝ) * (ε / 4) ^ 2)
        ≤ (p : ℝ) / ((N : ℝ) * (ε / 4) ^ 2) :=
      div_le_div_of_nonneg_right hvar hden.le
    refine le_trans hstep ?_
    -- `p/(N (ε/4)²) = 16p/(N ε²) ≤ C`
    rw [div_le_iff₀ hden]
    nlinarith [hbound, hε, hC0, p.2.1, p.2.2]
  · -- rounding: on the good event the scaled frequency is within `1/4` of `m`
    intro ω hgood
    have hle : |FinDist.avg shotIndicator ω - (p : ℝ)| ≤ ε / 4 := le_of_not_gt hgood
    have havg : FinDist.avg shotIndicator ω =
        (p : ℝ) + (FinDist.avg shotIndicator ω - (p : ℝ)) := by ring
    have hratio : FinDist.avg shotIndicator ω / ε =
        (m : ℝ) + (FinDist.avg shotIndicator ω - (p : ℝ)) / ε := by
      rw [havg, hpm]
      field_simp
      ring
    have hbnd : |(FinDist.avg shotIndicator ω - (p : ℝ)) / ε| ≤ 1 / 4 := by
      rw [abs_div, abs_of_pos hε]
      rw [div_le_iff₀ hε]
      nlinarith [hle, hε]
    have hdiff_le : (FinDist.avg shotIndicator ω - (p : ℝ)) / ε ≤ 1 / 4 :=
      (abs_le.mp hbnd).2
    have hdiff_ge : -(1 / 4 : ℝ) ≤ (FinDist.avg shotIndicator ω - (p : ℝ)) / ε :=
      (abs_le.mp hbnd).1
    rw [frequencyEstimate, hratio]
    rw [Nat.floor_eq_iff (by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
      nlinarith [hdiff_ge, hm0])]
    constructor
    · -- lower bound `m ≤ m + d/ε + 1/2`
      nlinarith [hdiff_ge]
    · -- upper bound `m + d/ε + 1/2 < m + 1`
      push_cast
      nlinarith [hdiff_le]

/-! ## Circuit cost bookkeeping (Theorem 1 / Theorem 3 / Lemma 6) -/

/-- Cost of one shot of the restriction algorithm of Theorem 1: an H-QFT, the
preparation of `ρ_G^α` (Eq. (8)) and one controlled action of the regular
representation. A run of `shots` copies costs `shots * (H + R + D)` gates. -/
structure RestrictionShotCost (H R D : ℕ) where
  /-- Gates for the H-QFT. -/
  qftGates : ℕ
  /-- Gates for preparing `ρ_G^α`. -/
  prepareGates : ℕ
  /-- Gates for the controlled regular action. -/
  actionGates : ℕ
  qft_le : qftGates ≤ H
  prepare_le : prepareGates ≤ R
  action_le : actionGates ≤ D

/-- Gate cost of one shot. -/
def RestrictionShotCost.perShot {H R D : ℕ} (c : RestrictionShotCost H R D) : ℕ :=
  c.qftGates + c.prepareGates + c.actionGates

/-- The `RestrictionShotCost.perShot_le` result for the RepMultiplic24 paper model. -/
theorem RestrictionShotCost.perShot_le {H R D : ℕ} (c : RestrictionShotCost H R D) :
    c.perShot ≤ H + R + D := by
  have h1 := c.qft_le
  have h2 := c.prepare_le
  have h3 := c.action_le
  unfold RestrictionShotCost.perShot
  have := Nat.add_le_add (Nat.add_le_add h1 h2) h3
  exact this

/-- Gate cost of a complete run: number of shots times the per-shot cost. -/
def runCost {H R D : ℕ} (c : RestrictionShotCost H R D) (shots : ℕ) : ℕ :=
  shots * c.perShot

/-- The `runCost_le` result for the RepMultiplic24 paper model. -/
theorem runCost_le {H R D : ℕ} (c : RestrictionShotCost H R D) (shots : ℕ) :
    runCost c shots ≤ shots * (H + R + D) := by
  unfold runCost
  exact Nat.mul_le_mul_left _ c.perShot_le

/-! ## Hook-length dimensions and Kostka numbers -/

/-- Hook length of the cell `(i,j)` of `μ`: the number of cells strictly to the
right plus the number strictly below plus one. For cells of `μ` this is the usual
formula `rowLen i + colLen j - i - j - 1`. -/
def hookLength (μ : YoungDiagram) (i j : ℕ) : ℕ :=
  μ.rowLen i + μ.colLen j - i - j - 1

/-- The hook product `∏_{(i,j) ∈ μ} h(i,j)` of the hook-length formula, Eq. (37). -/
def hookProduct (μ : YoungDiagram) : ℕ :=
  ∏ c ∈ μ.cells, hookLength μ c.1 c.2

/-- The dimension `d_μ` of the `Sₙ` irrep labelled by `μ`, via the hook-length
formula `d_μ = n! / ∏ h(i,j)` (Eq. (37)). Kept as a rational so the division is
literal. -/
noncomputable def hookDim (μ : YoungDiagram) : ℚ :=
  ((Nat.factorial μ.cells.card : ℕ) : ℚ) / (hookProduct μ : ℚ)

/-- A cell of a Young diagram. -/
abbrev Cell (μ : YoungDiagram) := {c : ℕ × ℕ // c ∈ μ.cells}

/-- A filling of the cells of `μ` by values in `Fin (n+1)`; a representative of the
positive integers `1..n`. This bounded model makes the set of tableaux finite. -/
abbrev Filling (μ : YoungDiagram) (n : ℕ) := Cell μ → Fin (n + 1)

/-- A filling is a semistandard Young tableau: weakly increasing along rows and
strictly increasing down columns. -/
def IsSSYT {μ : YoungDiagram} {n : ℕ} (f : Filling μ n) : Prop :=
  (∀ c c' : Cell μ, c.1.1 = c'.1.1 → c.1.2 < c'.1.2 → f c ≤ f c') ∧
    (∀ c c' : Cell μ, c.1.2 = c'.1.2 → c.1.1 < c'.1.1 → f c < f c')

/-- The content of a filling: the number of cells carrying each value. -/
noncomputable def fillingContent {μ : YoungDiagram} {n : ℕ} (f : Filling μ n)
    (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun c : Cell μ => (f c : ℕ) = k)).card

/-- A filling has content `ν` when the number of cells carrying the value `k`
equals the `k`-th row length of `ν`. -/
def HasContent {μ : YoungDiagram} {n : ℕ} (f : Filling μ n) (ν : YoungDiagram) : Prop :=
  ∀ k, fillingContent f k = ν.rowLen k

/-- The Kostka number `K^μ_ν`: the number of semistandard Young tableaux of shape
`μ` and content `ν` (Eq. (99)-(101), and the paragraph around Eq. (23)). -/
noncomputable def kostkaNumber (μ ν : YoungDiagram) : ℕ := by
  classical
  exact (Finset.univ.filter (fun f : Filling μ (μ.cells.card) =>
    IsSSYT f ∧ HasContent f ν)).card

/-! ## Standard tableaux and Yamanouchi words (Proposition 1) -/

/-- A standard Young tableau of shape `μ`: a bijective filling whose entries
strictly increase along rows and down columns (Supp. Mat. Eq. (22), (25)). -/
structure StandardYoungTableau (μ : YoungDiagram) where
  /-- The entry in each cell, valued in `Fin |μ|`. -/
  entry : Cell μ → Fin μ.cells.card
  /-- The filling is a bijection. -/
  injective : Function.Injective entry
  /-- Strictly increasing along rows. -/
  row_mono : ∀ c c' : Cell μ, c.1.1 = c'.1.1 → c.1.2 < c'.1.2 → entry c < entry c'
  /-- Strictly increasing down columns. -/
  col_mono : ∀ c c' : Cell μ, c.1.2 = c'.1.2 → c.1.1 < c'.1.1 → entry c < entry c'

/-- The Yamanouchi (ballot) condition, Eq. (28): in every prefix and for every
letter `i+1`, the letter `i+2` occurs no more often than `i+1`. -/
def IsYamanouchi (w : List ℕ) : Prop :=
  (∀ x ∈ w, 0 < x) ∧
    ∀ j, j ≤ w.length → ∀ i, (w.take j).count (i + 2) ≤ (w.take j).count (i + 1)

/-- The Yamanouchi words of type `λ`: `Y_n^λ` of the paragraph before
Proposition 1. The letter `i+1` occurs exactly `λᵢ` times, and the total length
is `|λ|`. -/
def YamanouchiWord (lam : YoungDiagram) : Type :=
  {w : List ℕ // w.length = lam.cells.card ∧ IsYamanouchi w ∧
    ∀ i, w.count (i + 1) = lam.rowLen i}

end Qatlib.Papers.RepMultiplic24.MainResults
