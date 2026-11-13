/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

/-!
# Finite phase ensembles and forward-query algorithms

Defines uniform and biased finite phase laws, their independent product ensembles, and
normalized trace observables. The biased law is represented on a disjoint union of the full root
set and the arc with exponents from `-floor(q/4)` to `floor(q/4)`.

The structure `ForwardQueryAlgorithm` specifies normalized initial data, unitary interleaving
steps, and a Boolean readout. Its forward evolution determines output probabilities and
equal-prior ensemble distinguishing success. See [TangWright2025].

## Main statements

* `muEps`: the mixture of the full and arc phase laws.
* `ForwardQueryAlgorithm`: the forward diagonal-query algorithm data.
* `successProb`: the success probability for the two phase ensembles.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.AmpInvReqTang26.AccessModel

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration

/-- The complex root `exp(2πi / q)`. -/
def omega (q : ℕ) : ℂ :=
  Complex.exp (Complex.ofReal (2 * Real.pi / (q : ℝ)) * Complex.I)

/-- The root `omega q` has complex norm one. -/
theorem norm_omega (q : ℕ) : ‖omega q‖ = 1 := by
  rw [omega, Complex.norm_exp_ofReal_mul_I]

/-- The phase `omega q` raised to the natural index `k`. -/
def phase (q : ℕ) (k : Fin q) : ℂ := omega q ^ (k : ℕ)

/-- Every phase `phase q k` has complex norm one. -/
theorem norm_phase (q : ℕ) (k : Fin q) : ‖phase q k‖ = 1 := by
  rw [phase, norm_pow, norm_omega, one_pow]

/-- The number `2 * (q / 4) + 1` of integer exponents in the chosen arc. -/
def halfCount (q : ℕ) : ℕ := 2 * (q / 4) + 1

/-- The phase with integer exponent `j - q / 4`, indexing the chosen arc of roots. -/
def rightPhase (q : ℕ) (j : Fin (halfCount q)) : ℂ :=
  omega q ^ (((j : ℕ) : ℤ) - ((q / 4 : ℕ) : ℤ))

/-- Every arc phase `rightPhase q j` has complex norm one. -/
theorem norm_rightPhase (q : ℕ) (j : Fin (halfCount q)) : ‖rightPhase q j‖ = 1 := by
  rw [rightPhase, norm_zpow, norm_omega, _root_.one_zpow]

/-- The uniform probability law on `Fin q` for positive `q`. -/
def mu0 (q : ℕ) (hq : 0 < q) : FinDist (Fin q) where
  prob _ := (q : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg q)
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
    field_simp

/-- The uniform probability law on the `halfCount q` arc indices. -/
def mu1 (q : ℕ) : FinDist (Fin (halfCount q)) where
  prob _ := (halfCount q : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hm : (halfCount q : ℝ) ≠ 0 := by
      have : 0 < halfCount q := by unfold halfCount; omega
      exact Nat.cast_ne_zero.mpr this.ne'
    field_simp

/-- The phase map on the disjoint union, using full-root phases on the left and arc phases on
the right. -/
def phaseEps (q : ℕ) : Fin q ⊕ Fin (halfCount q) → ℂ :=
  Sum.elim (phase q) (rightPhase q)

/-- The disjoint-union probability law with mass `1 - ε` on the uniform full-root law and mass
`ε` on the uniform arc law. -/
def muEps (ε : ℝ) (q : ℕ) (hq : 0 < q) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    FinDist (Fin q ⊕ Fin (halfCount q)) where
  prob x :=
    match x with
    | Sum.inl _ => (1 - ε) * (q : ℝ)⁻¹
    | Sum.inr _ => ε * (halfCount q : ℝ)⁻¹
  nonneg x := by
    cases x with
    | inl _ => exact mul_nonneg (by linarith) (inv_nonneg.mpr (Nat.cast_nonneg _))
    | inr _ => exact mul_nonneg hε0 (inv_nonneg.mpr (Nat.cast_nonneg _))
  sum_one := by
    rw [Fintype.sum_sum_type]
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
      have hm0 : (halfCount q : ℝ) ≠ 0 := by
        have : 0 < halfCount q := by unfold halfCount; omega
        exact Nat.cast_ne_zero.mpr this.ne'
      field_simp
      ring

/-- The complex expectation of `φ` under a finite probability law `p`. -/
def cExpect {X : Type} [Fintype X] (p : FinDist X) (φ : X → ℂ) : ℂ :=
  ∑ x, (p.prob x : ℂ) * φ x

/-- The product law of `d` independent uniform full-root indices [Tang and Wright, Definition
2.4][TangWright2025]. -/
def ensemble0 (d q : ℕ) (hq : 0 < q) : FinDist (Fin d → Fin q) :=
  independent (fun _ : Fin d => mu0 q hq)

/-- The product law of `d` independent indices drawn from the biased phase mixture [Tang and
Wright, Definition 2.4][TangWright2025]. -/
def ensemble1 (d q : ℕ) (ε : ℝ) (hq : 0 < q) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    FinDist (Fin d → Fin q ⊕ Fin (halfCount q)) :=
  independent (fun _ : Fin d => muEps ε q hq hε0 hε1)

/-- The normalized sum of the phases `φ (U i)` over the data coordinates. -/
def normTrace {d : ℕ} {X : Type} (φ : X → ℂ) (U : Fin d → X) : ℂ :=
  (d : ℂ)⁻¹ * ∑ i, φ (U i)

/-- The expected phase `cExpect p φ` associated with the normalized trace observable. -/
def expectedNormTrace {X : Type} [Fintype X] (p : FinDist X)
    (φ : X → ℂ) : ℂ :=
  cExpect p φ

/-- The diagonal oracle matrix applying the phase of each data coordinate and acting identically
on the auxiliary coordinate. -/
def queryMat {d a : ℕ} {X : Type} (φ : X → ℂ)
    (U : Fin d → X) : Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ :=
  diagonal (fun p => φ (U p.1))

/-- A forward diagonal-query algorithm with a normalized initial state, unitary interleaving
steps, and a Boolean label on basis outcomes. -/
structure ForwardQueryAlgorithm (d a : ℕ) where

  init : (Fin d × Fin a) → ℂ

  hinit : ∑ x, ‖init x‖ ^ 2 = 1

  step : ℕ → Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ

  hstep : ∀ t, (step t)ᴴ * step t = 1

  good : (Fin d × Fin a) → Bool

/-- The state obtained from the initial vector by the zeroth step and then `n` forward diagonal
queries with interleaving steps. -/
def run {d a : ℕ} {X : Type} (φ : X → ℂ) (Alg : ForwardQueryAlgorithm d a) :
    ℕ → (Fin d → X) → (Fin d × Fin a) → ℂ
  | 0, _ => Alg.step 0 *ᵥ Alg.init
  | n + 1, U => Alg.step (n + 1) *ᵥ (queryMat φ U *ᵥ run φ Alg n U)

/-- The sum of squared output amplitudes on basis outcomes labeled `b`. -/
def outProb {d a : ℕ} {X : Type} (φ : X → ℂ) (Alg : ForwardQueryAlgorithm d a)
    (n : ℕ) (U : Fin d → X) (b : Bool) : ℝ :=
  ∑ x : Fin d × Fin a, if Alg.good x = b then ‖run φ Alg n U x‖ ^ 2 else 0

/-- The expectation of the output mass labeled `b` over an oracle distribution `p`. -/
def distProb {d a : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist (Fin d → X)) (φ : X → ℂ) (Alg : ForwardQueryAlgorithm d a)
    (n : ℕ) (b : Bool) : ℝ :=
  p.expect (fun U => outProb φ Alg n U b)

/-- The equal-prior success probability for labeling the uniform ensemble false and the biased
ensemble true. -/
def successProb {d a : ℕ} (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ) : ℝ :=
  (1 / 2) * (distProb (ensemble0 d q hq) (phase q) Alg n false +
    distProb (ensemble1 d q ε hq hε0 hε1) (phaseEps q) Alg n true)

/-- The sum of squared complex norms of the state coordinates. -/
def stateNormSq {d a : ℕ} (v : (Fin d × Fin a) → ℂ) : ℝ :=
  ∑ x, ‖v x‖ ^ 2

/-- Both states are normalized and one minus their squared inner-product norm is at most `ε^2`. -/
def PureClose {d a : ℕ} (φ ψ : (Fin d × Fin a) → ℂ) (ε : ℝ) : Prop :=
  ∃ (_hφ : stateNormSq φ = 1) (_hψ : stateNormSq ψ = 1),
    1 - ‖∑ x, star (φ x) * ψ x‖ ^ 2 ≤ ε ^ 2

/-- The coordinate indicator of the pair of zero data and auxiliary indices. -/
def zeroState {d a : ℕ} : (Fin d × Fin a) → ℂ :=
  fun x => if (x.1 : ℕ) = 0 ∧ (x.2 : ℕ) = 0 then 1 else 0

end Qatlib.Papers.AmpInvReqTang26.AccessModel
