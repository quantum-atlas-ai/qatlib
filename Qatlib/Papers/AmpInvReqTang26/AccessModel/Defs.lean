/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.AmpInvReqTang26.AccessModel

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration

def omega (q : ℕ) : ℂ :=
  Complex.exp (Complex.ofReal (2 * Real.pi / (q : ℝ)) * Complex.I)

theorem norm_omega (q : ℕ) : ‖omega q‖ = 1 := by
  rw [omega, Complex.norm_exp_ofReal_mul_I]

def phase (q : ℕ) (k : Fin q) : ℂ := omega q ^ (k : ℕ)

theorem norm_phase (q : ℕ) (k : Fin q) : ‖phase q k‖ = 1 := by
  rw [phase, norm_pow, norm_omega, one_pow]

def halfCount (q : ℕ) : ℕ := 2 * (q / 4) + 1

def rightPhase (q : ℕ) (j : Fin (halfCount q)) : ℂ :=
  omega q ^ (((j : ℕ) : ℤ) - ((q / 4 : ℕ) : ℤ))

theorem norm_rightPhase (q : ℕ) (j : Fin (halfCount q)) : ‖rightPhase q j‖ = 1 := by
  rw [rightPhase, norm_zpow, norm_omega, _root_.one_zpow]

def mu0 (q : ℕ) (hq : 0 < q) : FinDist (Fin q) where
  prob _ := (q : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg q)
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
    field_simp

def mu1 (q : ℕ) : FinDist (Fin (halfCount q)) where
  prob _ := (halfCount q : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hm : (halfCount q : ℝ) ≠ 0 := by
      have : 0 < halfCount q := by unfold halfCount; omega
      exact Nat.cast_ne_zero.mpr this.ne'
    field_simp

def phaseEps (q : ℕ) : Fin q ⊕ Fin (halfCount q) → ℂ :=
  Sum.elim (phase q) (rightPhase q)

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

def cExpect {X : Type} [Fintype X] (p : FinDist X) (φ : X → ℂ) : ℂ :=
  ∑ x, (p.prob x : ℂ) * φ x

def ensemble0 (d q : ℕ) (hq : 0 < q) : FinDist (Fin d → Fin q) :=
  independent (fun _ : Fin d => mu0 q hq)

def ensemble1 (d q : ℕ) (ε : ℝ) (hq : 0 < q) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    FinDist (Fin d → Fin q ⊕ Fin (halfCount q)) :=
  independent (fun _ : Fin d => muEps ε q hq hε0 hε1)

def normTrace {d : ℕ} {X : Type} (φ : X → ℂ) (U : Fin d → X) : ℂ :=
  (d : ℂ)⁻¹ * ∑ i, φ (U i)

def expectedNormTrace {X : Type} [Fintype X] (p : FinDist X)
    (φ : X → ℂ) : ℂ :=
  cExpect p φ

def queryMat {d a : ℕ} {X : Type} (φ : X → ℂ)
    (U : Fin d → X) : Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ :=
  diagonal (fun p => φ (U p.1))

structure ForwardQueryAlgorithm (d a : ℕ) where

  init : (Fin d × Fin a) → ℂ

  hinit : ∑ x, ‖init x‖ ^ 2 = 1

  step : ℕ → Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ

  hstep : ∀ t, (step t)ᴴ * step t = 1

  good : (Fin d × Fin a) → Bool

def run {d a : ℕ} {X : Type} (φ : X → ℂ) (Alg : ForwardQueryAlgorithm d a) :
    ℕ → (Fin d → X) → (Fin d × Fin a) → ℂ
  | 0, _ => Alg.step 0 *ᵥ Alg.init
  | n + 1, U => Alg.step (n + 1) *ᵥ (queryMat φ U *ᵥ run φ Alg n U)

def outProb {d a : ℕ} {X : Type} (φ : X → ℂ) (Alg : ForwardQueryAlgorithm d a)
    (n : ℕ) (U : Fin d → X) (b : Bool) : ℝ :=
  ∑ x : Fin d × Fin a, if Alg.good x = b then ‖run φ Alg n U x‖ ^ 2 else 0

def distProb {d a : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist (Fin d → X)) (φ : X → ℂ) (Alg : ForwardQueryAlgorithm d a)
    (n : ℕ) (b : Bool) : ℝ :=
  p.expect (fun U => outProb φ Alg n U b)

def successProb {d a : ℕ} (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ) : ℝ :=
  (1 / 2) * (distProb (ensemble0 d q hq) (phase q) Alg n false +
    distProb (ensemble1 d q ε hq hε0 hε1) (phaseEps q) Alg n true)

def stateNormSq {d a : ℕ} (v : (Fin d × Fin a) → ℂ) : ℝ :=
  ∑ x, ‖v x‖ ^ 2

def PureClose {d a : ℕ} (φ ψ : (Fin d × Fin a) → ℂ) (ε : ℝ) : Prop :=
  ∃ (_hφ : stateNormSq φ = 1) (_hψ : stateNormSq ψ = 1),
    1 - ‖∑ x, star (φ x) * ψ x‖ ^ 2 ≤ ε ^ 2

def zeroState {d a : ℕ} : (Fin d × Fin a) → ℂ :=
  fun x => if (x.1 : ℕ) = 0 ∧ (x.2 : ℕ) = 0 then 1 else 0

end Qatlib.Papers.AmpInvReqTang26.AccessModel
