/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.FidelityLevelSubgoalQuan

set_option backward.isDefEq.respectTransparency false

/-!
# Quantum rejection sampling: query lower bound (Lemma 2)

Fixed source: Ozols–Roetteler–Roland, *Quantum rejection sampling*,
arXiv:1103.2774v4, Section 3 (Lemma 2, Eqs. (6)–(10) and program (9)) and
Appendix A (Lemma 1, program (22), SDP (4)).

Lemma 2 states that any quantum algorithm solving `QSampling^p_{π→σ}` with
`p ∈ [pmin, pmax]` needs `Ω(1/‖ε^p_{π→σ}‖₂)` queries to `O` and `O†`.  The
source proof has four steps.

1. *Restriction and symmetrization.*  Only the oracles `O_{x,u}` with phases
   `x ∈ F₂ⁿ` and `u ∈ U(n−1)` are used.  Averaging a `T`-query algorithm over
   the automorphism group `F₂ⁿ × U(n−1)` replaces its final state by one whose
   first register carries the phases `(-1)^{x_k}` and whose workspace vectors
   `|γ_k(x,u)⟩` are replaced by their average; the averaged direction vector
   `γ̄` no longer depends on `(x,u)`.  Success forces `σᵀγ̄ ≥ √p`, and because
   the average is a convex combination of vectors of norm at most one,
   `‖γ̄‖₂ ≤ 1`.
2. *Hybrid argument.*  Final states of two oracle words differ by at most `T`
   times the one-step operator gap (source Eq. (6) and its footnote), while
   the phase pattern makes them differ by at least `2|γ̄_l|` for the words
   `x = 0` and `x = e_l` (source Eq. (10)).
3. *Operator gap.*  For the adversarially chosen `u'` the two oracles satisfy
   `‖O_{0,I} − O_{e_l,u'}‖∞ = 2π_l`, hence `|γ̄_l| ≤ Tπ_l` — the three
   constraints of source Eq. (8).
4. *Program equivalence.*  Substituting `ε := γ̄/T` rewrites program (9) as
   program (22), and `M = ε·εᵀ` turns program (22) into the rank-one part of
   SDP (4), whose optimum `‖ε^p‖₂²` is Lemma 1.

This module formalises steps 2–4 in the form the source uses.

* `oracleWalk` and `oracleWalk_diff_norm_le` are the `T`-step hybrid bound of
  Eq. (6); `oracleWalk_norm_le` is the contraction estimate used inside it.
* `norm_weightedSum_le` is the convexity step behind `‖γ̄‖₂ ≤ 1`.
* `samplingAngleFeasible` is the constraint set of Eq. (8), and
  `angleCoordinate_le` is the passage from Eq. (7) with gap `2π_l` to the
  coordinate bound of Eq. (8).
* `scaledAngleVector_feasible` is the substitution `ε = γ̄/T` into program (22).
* `samplingQueryLowerBound` is the resulting lower bound `T ≥ 1/‖ε^p‖₂`.  The
  rank-one optimality of program (22) is discharged by the frozen
  `sourceFidelityLevelSubgoal`, which is Lemma 1's rank-one statement.

Not formalised here, and therefore not claimed: the averaging over the
automorphism group as a transformation of *algorithms* (step 1 is used only
through its output vector `γ̄`), the explicit construction of the adversarial
unitary `u'`, the operator-norm identity `‖O_{0,I} − O_{e_l,u'}‖∞ = 2π_l`
(step 3 enters through the hypothesis `δ = 2π_l`), and the two easy branches of
Theorem 1 (`p ≤ pmin` with complexity one, `p > pmax` unsolvable). -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Qatlib.Concepts.Waterfill.LevelFidelity
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity

open scoped BigOperators

namespace Qatlib.Papers.RejectSample11.MainResults

/-! ## Source Eq. (8): the phase-averaged direction vector -/

/-- The constraints of source Eq. (8) on the phase-averaged direction vector
`γ̄` of a symmetrized `T`-query algorithm: unit norm, the coordinate bound
`|γ̄_i| ≤ Tπ_i`, and the success constraint `σᵀγ̄ ≥ √p`.

The source reduces program (9) to this form by increasing a sub-unit `γ̄` to
unit norm inside the box `0 ≤ γ̄_i ≤ tπ_i` (the argument between programs (9)
and (22)), so the unit-norm equality and the nonnegativity of the coordinates
are carried as part of the feasible set rather than as separate hypotheses. -/
def samplingAngleFeasible {m : ℕ} (π σ : Fin m → ℚ) (p T : ℝ) (g : Fin m → ℝ) : Prop :=
  (∑ i, g i ^ 2) = 1 ∧
    (∀ i, 0 ≤ g i ∧ g i ≤ T * (π i : ℝ)) ∧
      Real.sqrt p ≤ ∑ i, (σ i : ℝ) * g i

/-! ## Hybrid argument (source Eq. (6)) -/

/-- The state prepared by a `T`-query algorithm whose `k`-th query applies the
linear operator `O k`; `O k` is an oracle or its inverse in the source, and the
initial state is the algorithm's start state. -/
def oracleWalk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (O : ℕ → E →L[ℂ] E) : ℕ → E → E
  | 0, ψ => ψ
  | k + 1, ψ => O k (oracleWalk O k ψ)

/-- Unfolding lemma for `oracleWalk` at a positive number of queries. -/
theorem oracleWalk_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (O : ℕ → E →L[ℂ] E) (k : ℕ) (ψ : E) :
    oracleWalk O (k + 1) ψ = O k (oracleWalk O k ψ) := rfl

/-- A word of contracting operators does not increase the state norm: this is
the estimate `‖O_k‖∞ ≤ 1` for unitary oracle calls used inside the hybrid
argument. -/
theorem oracleWalk_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (O : ℕ → E →L[ℂ] E) (hO : ∀ k, ‖O k‖ ≤ 1) (ψ : E) :
    ∀ T : ℕ, ‖oracleWalk O T ψ‖ ≤ ‖ψ‖ := by
  intro T
  induction T with
  | zero => simp [oracleWalk]
  | succ k ih =>
      rw [oracleWalk_succ]
      calc ‖O k (oracleWalk O k ψ)‖ ≤ ‖O k‖ * ‖oracleWalk O k ψ‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖ψ‖ := by
            have h1 : (0 : ℝ) ≤ ‖oracleWalk O k ψ‖ := norm_nonneg _
            nlinarith [hO k, ih, h1]
        _ = ‖ψ‖ := one_mul _

/-- Source Eq. (6) and its footnote: two oracle words that agree in the start
state and differ by at most `δ` per query in operator norm prepare states at
distance at most `T·δ`. -/
theorem oracleWalk_diff_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (O O' : ℕ → E →L[ℂ] E) (ψ₀ : E) {δ : ℝ} (hδ : 0 ≤ δ)
    (hstep : ∀ k, ‖O k - O' k‖ ≤ δ)
    (hO : ∀ k, ‖O k‖ ≤ 1) (hO' : ∀ k, ‖O' k‖ ≤ 1) :
    ∀ T : ℕ, ‖oracleWalk O T ψ₀ - oracleWalk O' T ψ₀‖ ≤ T * δ * ‖ψ₀‖ := by
  intro T
  induction T with
  | zero => simp [oracleWalk]
  | succ k ih =>
      have hb : ‖oracleWalk O' k ψ₀‖ ≤ ‖ψ₀‖ := oracleWalk_norm_le O' hO' ψ₀ k
      have hdecomp : oracleWalk O (k + 1) ψ₀ - oracleWalk O' (k + 1) ψ₀ =
          O k (oracleWalk O k ψ₀ - oracleWalk O' k ψ₀) +
            (O k - O' k) (oracleWalk O' k ψ₀) := by
        rw [oracleWalk_succ, oracleWalk_succ, map_sub, ContinuousLinearMap.sub_apply]
        abel
      rw [hdecomp]
      calc ‖O k (oracleWalk O k ψ₀ - oracleWalk O' k ψ₀) +
              (O k - O' k) (oracleWalk O' k ψ₀)‖
          ≤ ‖O k (oracleWalk O k ψ₀ - oracleWalk O' k ψ₀)‖ +
              ‖(O k - O' k) (oracleWalk O' k ψ₀)‖ := norm_add_le _ _
        _ ≤ ‖O k‖ * ‖oracleWalk O k ψ₀ - oracleWalk O' k ψ₀‖ +
              ‖O k - O' k‖ * ‖oracleWalk O' k ψ₀‖ :=
            add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
        _ ≤ 1 * ((k : ℝ) * δ * ‖ψ₀‖) + δ * ‖ψ₀‖ :=
            add_le_add
              (mul_le_mul (hO k) ih (norm_nonneg _) zero_le_one)
              (mul_le_mul (hstep k) hb (norm_nonneg _) hδ)
        _ = ((k : ℝ) + 1) * δ * ‖ψ₀‖ := by ring
        _ = ((k + 1 : ℕ) : ℝ) * δ * ‖ψ₀‖ := by push_cast; ring

/-! ## Symmetrization (the step `‖γ̄‖₂ ≤ 1` before source Eq. (10)) -/

/-- A convex combination of vectors of norm at most one has norm at most one.
This is the source's "note that `‖γ̄‖₂ ≤ 1` by triangle inequality": `γ̄` is the
average of the per-oracle direction vectors `γ(y,v)`. -/
theorem norm_weightedSum_le {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : ι → ℝ) (γ : ι → E) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (hγ : ∀ i, ‖γ i‖ ≤ 1) :
    ‖∑ i, w i • γ i‖ ≤ 1 := by
  calc ‖∑ i, w i • γ i‖ ≤ ∑ i, ‖w i • γ i‖ := norm_sum_le _ _
    _ = ∑ i, w i * ‖γ i‖ := by
        exact Finset.sum_congr rfl fun i _ => by
          rw [norm_smul, Real.norm_of_nonneg (hw i)]
    _ ≤ ∑ i, w i * 1 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hγ i) (hw i)
    _ = 1 := by simpa using hsum

/-- Source Eq. (7) with the operator gap `‖O_{0,I} − O_{e_l,u'}‖∞ = 2π_l`
gives the coordinate bound `|γ̄_l| ≤ Tπ_l` of Eq. (8). -/
theorem angleCoordinate_le {m : ℕ} (π : Fin m → ℚ) (l : Fin m) {T δ gl : ℝ}
    (hgap : δ = 2 * (π l : ℝ)) (hdiff : 2 * |gl| ≤ T * δ) :
    |gl| ≤ T * (π l : ℝ) := by
  rw [hgap] at hdiff
  nlinarith [abs_nonneg gl]

/-! ## Program (22) -/

/-- The substitution `ε := γ̄/T` of the source maps the feasible set of program
(9) into program (22): `ε` stays inside the source box `0 ≤ ε_i ≤ π_i` and
satisfies the fidelity constraint `σᵀε ≥ √p·‖ε‖₂`, here in the squared form
`p·‖ε‖₂² ≤ (σᵀε)²` used by the rank-one optimality statement. -/
theorem scaledAngleVector_feasible {m : ℕ} (π σ : Fin m → ℚ) (p T : ℝ)
    (g : Fin m → ℝ) (hp : 0 ≤ p) (hT : 0 < T)
    (h : samplingAngleFeasible π σ p T g) :
    (∀ i, 0 ≤ g i / T ∧ g i / T ≤ (π i : ℝ)) ∧
      p * (∑ i, (g i / T) ^ 2) ≤ (∑ i, (σ i : ℝ) * (g i / T)) ^ 2 := by
  obtain ⟨hnorm, hcoord, hsucc⟩ := h
  have hmass : (∑ i, (g i / T) ^ 2) = 1 / T ^ 2 := by
    simp_rw [div_pow]
    rw [← Finset.sum_div, hnorm]
  have hdot : (∑ i, (σ i : ℝ) * (g i / T)) = (∑ i, (σ i : ℝ) * g i) / T := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨h0, hle⟩ := hcoord i
    refine ⟨div_nonneg h0 hT.le, ?_⟩
    rw [div_le_iff₀ hT]
    linarith [hle]
  · have hd0 : (0 : ℝ) ≤ ∑ i, (σ i : ℝ) * g i := le_trans (Real.sqrt_nonneg p) hsucc
    have hsq : p ≤ (∑ i, (σ i : ℝ) * g i) ^ 2 := by
      nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p, hsucc]
    rw [hmass, hdot, mul_one_div, div_pow, div_le_div_iff_of_pos_right (by positivity)]
    exact hsq

/-! ## Lemma 2: the lower bound -/

/-- **Lemma 2 (lower bound).**  Assume a phase-averaged direction vector `γ̄`
satisfying the constraints of source Eq. (8) exists for a `T`-query algorithm.
Then `T` is at least the reciprocal norm of the water-filling vector
`ε^p_{π→σ}`, i.e. `1 ≤ T·‖ε^p_{π→σ}‖₂`.

The proof is the source's final chain: program (9) → program (22) with
`ε = γ̄/T`, then `M = ε·εᵀ` gives the rank-one point of SDP (4) whose optimal
value is `‖ε^p‖₂²` by Lemma 1 (frozen `sourceFidelityLevelSubgoal`). -/
theorem samplingQueryLowerBound {m : ℕ} (π σ : Fin m → ℚ) (γlo γhi p T : ℝ)
    (g : Fin m → ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hσ : ∀ i, 0 < σ i)
    (hπnorm : (∑ i, (π i : ℝ) ^ 2) = 1) (hσnorm : (∑ i, (σ i : ℝ) ^ 2) = 1)
    (hlohi : γlo < γhi)
    (hlow : ∀ i, 0 < π i → γlo * (σ i : ℝ) ≤ (π i : ℝ))
    (hwit : ∃ i₀, 0 < π i₀ ∧ γlo * (σ i₀ : ℝ) = (π i₀ : ℝ))
    (hhigh : ∀ i, (π i : ℝ) ≤ γhi * (σ i : ℝ))
    (hwit2 : ∃ i₁, 0 < π i₁ ∧ (π i₁ : ℝ) = γhi * (σ i₁ : ℝ))
    (hpmin : waterPmin π σ ≤ p) (hpmax : p ≤ waterPmax π σ)
    (hp : 0 ≤ p) (hT : 0 < T) (h : samplingAngleFeasible π σ p T g) :
    ∃ gbar : ℝ, γlo ≤ gbar ∧ gbar ≤ γhi ∧
      levelDot π σ gbar ^ 2 = p * levelMass π σ gbar ∧
        1 ≤ T * Real.sqrt (levelMass π σ gbar) := by
  obtain ⟨gbar, h1, h2, h3, hmax⟩ :=
    sourceFidelityLevelSubgoal m π σ γlo γhi hπ hσ hπnorm hσnorm hlohi hlow hwit
      hhigh hwit2 p hpmin hpmax
  refine ⟨gbar, h1, h2, h3, ?_⟩
  obtain ⟨hbox, hfid⟩ := scaledAngleVector_feasible π σ p T g hp hT h
  have hmass := hmax (fun i => g i / T) hbox hfid
  have hone : (∑ i, (g i / T) ^ 2) = 1 / T ^ 2 := by
    obtain ⟨hnorm, _, _⟩ := h
    simp_rw [div_pow]
    rw [← Finset.sum_div, hnorm]
  rw [hone] at hmass
  have hL0 : (0 : ℝ) ≤ levelMass π σ gbar :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hT2 : (0 : ℝ) < T ^ 2 := by positivity
  have hkey : (1 : ℝ) ≤ T ^ 2 * levelMass π σ gbar := by
    have := mul_le_mul_of_nonneg_left hmass hT2.le
    rw [one_div, mul_inv_cancel₀ (ne_of_gt hT2)] at this
    exact this
  have hsq : Real.sqrt 1 ≤ Real.sqrt (T ^ 2 * levelMass π σ gbar) :=
    Real.sqrt_le_sqrt hkey
  rw [Real.sqrt_one, Real.sqrt_mul (by positivity), Real.sqrt_sq hT.le] at hsq
  exact hsq

/-- The lower-bound rate of Lemma 2: `1/‖ε^p_{π→σ}‖₂` at the water level that
realises the source fidelity `p`. -/
noncomputable def samplingLowerBoundQueries {m : ℕ} (π σ : Fin m → ℚ) (gbar : ℝ) : ℝ :=
  1 / Real.sqrt (levelMass π σ gbar)

/-- Lemma 2 in the source's `Ω(1/‖ε^p‖₂)` shape: any `T` satisfying the Eq. (8)
constraints is at least `1/‖ε^p_{π→σ}‖₂`. -/
theorem samplingLowerBoundQueries_le {m : ℕ} (π σ : Fin m → ℚ) (gbar T : ℝ)
    (hL : 0 < levelMass π σ gbar) (h : 1 ≤ T * Real.sqrt (levelMass π σ gbar)) :
    samplingLowerBoundQueries π σ gbar ≤ T := by
  have hs : 0 < Real.sqrt (levelMass π σ gbar) := Real.sqrt_pos.mpr hL
  rw [samplingLowerBoundQueries, div_le_iff₀ hs]
  exact h

end Qatlib.Papers.RejectSample11.MainResults
