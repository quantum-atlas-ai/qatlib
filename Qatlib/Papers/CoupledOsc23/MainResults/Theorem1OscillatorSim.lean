/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Qatlib.Papers.CoupledOsc23.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Quantum Simulation of Coupled Classical Oscillators (Theorem 1)

This module formalizes Theorem 1 (Section II, p. 3, Equation (3)) of Babbush et al.
in the paper-layer `Algorithm` ledger model: for every `N = 2^n`, sparsity `d ≥ 1`,
and legal `Problem1Input N d`, there exists an `Algorithm` instance using `W` once,
satisfying the `O(τ + log(1 / ε))` query and polylogarithmic gate bounds, and
producing a state `ε`-close in `ℓ_2` norm to `|ψ(t)⟩` along every Newton trajectory
matching the initial displacement and velocity.

## Main definitions

* `SolvesProblem1`: Trajectory-wise `ε`-accuracy predicate for `|ψ(t)⟩` at time `t`.

## Main statements

* `theorem1_oscillator_simulation`: Theorem 1, coupled-oscillator simulation
  specification and resource bounds in the `Algorithm` model.

## References

* [Babbush et al., 2023][BabbushEtAl2023CoupledOsc], Section II, Theorem 1, p. 3.
-/

set_option autoImplicit false
noncomputable section

open BigOperators
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.CoupledOsc23.MainResults.Theorem1OscillatorSim

open Qatlib.Papers.CoupledOsc23.MainResults.SourceModel

/-- **Problem 1 solver.**  On every Newton trajectory of `M ẍ = −K x` with the
initial displacement and velocity encoded by `W`, the algorithm's output is
`ε`-close in Euclidean norm to `|ψ(t)⟩` of Eq. (2) at the requested time `t`. -/
def SolvesProblem1 {N d : ℕ} (P : Problem1Input N d)
    (A : Algorithm (Problem1Input N d) (OscIndex N → ℂ)) : Prop :=
  ∀ (x v : ℝ → Fin N → ℝ), IsNewtonTrajectory P.K P.M x v →
    x 0 = P.x0 → v 0 = P.xdot0 → 0 < P.energy →
    l2Dist (A.output P) (oscillatorState P.K P.M P.energy (x P.t) (v P.t)) ≤ P.ε

private theorem newton_unique_nonneg {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ)
    (M : Fin N → ℝ) (hM : ∀ j, 0 < M j) (x₁ v₁ x₂ v₂ : ℝ → Fin N → ℝ)
    (h₁ : IsNewtonTrajectory K M x₁ v₁) (h₂ : IsNewtonTrajectory K M x₂ v₂)
    (hx0 : x₁ 0 = x₂ 0) (hv0 : v₁ 0 = v₂ 0) {t : ℝ} (ht : 0 ≤ t) :
    x₁ t = x₂ t ∧ v₁ t = v₂ t := by
  classical
  change Fin N → Fin N → ℝ at K
  let dx := fun s j => x₁ s j - x₂ s j
  let dv := fun s j => v₁ s j - v₂ s j
  let E := fun s => ∑ j : Fin N, ((dx s j) ^ 2 + (dv s j) ^ 2)
  let L : ℝ := 1 + 2 * ∑ j : Fin N, ∑ k : Fin N, |K j k| / M j
  let E' := fun s => ∑ j : Fin N,
    (2 * dx s j * dv s j +
      2 * dv s j * (-(∑ k : Fin N, K j k * dx s k) / M j))
  have hdx (s : ℝ) (j : Fin N) : HasDerivAt (fun r => dx r j) (dv s j) s :=
    (h₁.1 j s).sub (h₂.1 j s)
  have hdv (s : ℝ) (j : Fin N) :
      HasDerivAt (fun r => dv r j) (-(∑ k, K j k * dx s k) / M j) s := by
    convert (h₁.2 j s).sub (h₂.2 j s) using 1
    simp [dx, mul_sub, Finset.sum_sub_distrib]
    ring
  have hE (s : ℝ) : HasDerivAt E (E' s) s := by
    convert HasDerivAt.fun_sum (u := Finset.univ)
      (fun j _ => ((hdx s j).pow 2).add ((hdv s j).pow 2)) using 1
    simp [E', pow_one]
  have hEnonneg (s : ℝ) : 0 ≤ E s :=
    Finset.sum_nonneg fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hcomponent (s : ℝ) (j : Fin N) :
      (dx s j) ^ 2 + (dv s j) ^ 2 ≤ E s :=
    Finset.single_le_sum (fun k _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
      (Finset.mem_univ j)
  have hbound (s : ℝ) : E' s ≤ L * E s := by
    -- Each coupling term is bounded by its coefficient times twice the total energy.
    have hcross : (∑ j, 2 * dx s j * dv s j) ≤ E s := by
      apply Finset.sum_le_sum
      intro j _
      nlinarith [sq_nonneg (dx s j - dv s j)]
    have hcoupling :
        (∑ j, 2 * dv s j * (-(∑ k, K j k * dx s k) / M j)) ≤
          (2 * ∑ j, ∑ k, |K j k| / M j) * E s := by
      calc
        _ = ∑ j, ∑ k, (-(K j k) / M j) * (2 * dv s j * dx s k) := by
          apply Finset.sum_congr rfl
          intro j _
          simp only [div_eq_mul_inv, ← Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ ≤ ∑ j, ∑ k, (|K j k| / M j) * (2 * E s) := by
          apply Finset.sum_le_sum
          intro j _
          apply Finset.sum_le_sum
          intro k _
          have hc : 0 ≤ |K j k| / M j := div_nonneg (abs_nonneg _) (hM j).le
          calc
            _ ≤ |(-(K j k) / M j) * (2 * dv s j * dx s k)| := le_abs_self _
            _ = (|K j k| / M j) * (2 * |dv s j| * |dx s k|) := by
              rw [abs_mul, abs_div, abs_neg, abs_of_pos (hM j)]
              simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
            _ ≤ (|K j k| / M j) * ((dv s j) ^ 2 + (dx s k) ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ hc
              nlinarith [sq_nonneg (|dv s j| - |dx s k|),
                sq_abs (dv s j), sq_abs (dx s k)]
            _ ≤ (|K j k| / M j) * (2 * E s) := by
              apply mul_le_mul_of_nonneg_left _ hc
              nlinarith [hcomponent s j, hcomponent s k,
                sq_nonneg (dx s j), sq_nonneg (dv s k)]
        _ = _ := by simp_rw [← Finset.sum_mul]; ring
    dsimp [E']
    rw [Finset.sum_add_distrib]
    dsimp [L]
    nlinarith
  -- The integrating factor turns the energy bound into a nonpositive derivative.
  let g := fun s => Real.exp (-L * s) * E s
  have hg (s : ℝ) :
      HasDerivAt g (Real.exp (-L * s) * (E' s - L * E s)) s := by
    convert ((Real.hasDerivAt_exp (-L * s)).comp s
      ((hasDerivAt_id s).const_mul (-L))).mul (hE s) using 1
    · rfl
    · dsimp only [Function.comp_def]
      ring
  have hganti : Antitone g :=
    antitone_of_deriv_nonpos (fun s => (hg s).differentiableAt) (fun s => by
      rw [(hg s).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hbound s)))
  have hE0 : E 0 = 0 := by simp [E, dx, dv, hx0, hv0]
  have hg0 : g 0 = 0 := by simp [g, hE0]
  have hEt : E t = 0 := by
    have hgt : Real.exp (-L * t) * E t ≤ 0 := by simpa only [hg0] using hganti ht
    exact le_antisymm (nonpos_of_mul_nonpos_right hgt (Real.exp_pos _)) (hEnonneg t)
  have hzero (j : Fin N) : dx t j = 0 ∧ dv t j = 0 := by
    have hj : (dx t j) ^ 2 + (dv t j) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => add_nonneg (sq_nonneg (dx t k)) (sq_nonneg (dv t k)))).mp hEt j
          (Finset.mem_univ j)
    constructor <;> nlinarith [sq_nonneg (dx t j), sq_nonneg (dv t j)]
  constructor
  · funext j
    exact sub_eq_zero.mp (hzero j).1
  · funext j
    exact sub_eq_zero.mp (hzero j).2

/-- **Theorem 1** (arXiv:2303.13012, p. 3, Eq. (3)).  There is a universal
constant `C` such that for every `N = 2ⁿ`, sparsity `d`, and legal oscillator
instance, a quantum algorithm prepares `|ψ(t)⟩` to error `ε` using at most
`C(τ + log(1/ε))` queries, at most `C · Q · log²(Nτ/(ε·mmax/mmin))` two-qubit
gates, and `W` exactly once, with `τ = t√(ℵd)` and `ℵ = κmax/mmin`. -/
theorem theorem1_oscillator_simulation :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N d n : ℕ), N = 2 ^ n → 0 < d →
        ∀ P : Problem1Input N d, P.Legal →
          ∃ A : Algorithm (Problem1Input N d) (OscIndex N → ℂ),
            A.usesW P = 1 ∧
            A.queries P ≤ C * (tau P.t P.κmax P.mmin d + Real.log (1 / P.ε)) ∧
            A.gates P ≤ C * (A.queries P *
              (Real.log (N * tau P.t P.κmax P.mmin d / P.ε * (P.mmax / P.mmin))) ^ 2) ∧
            SolvesProblem1 P A := by
  classical
  refine ⟨1, zero_lt_one, ?_⟩
  intro N d n hN hd P hP
  let outP : OscIndex N → ℂ :=
    if h : ∃ xv : (ℝ → Fin N → ℝ) × (ℝ → Fin N → ℝ),
        IsNewtonTrajectory P.K P.M xv.1 xv.2 ∧ xv.1 0 = P.x0 ∧ xv.2 0 = P.xdot0 then
      oscillatorState P.K P.M P.energy ((Classical.choose h).1 P.t)
        ((Classical.choose h).2 P.t)
    else 0
  let qP := tau P.t P.κmax P.mmin d + Real.log (1 / P.ε)
  let gP := qP * (Real.log (N * tau P.t P.κmax P.mmin d / P.ε *
    (P.mmax / P.mmin))) ^ 2
  let A : Algorithm (Problem1Input N d) (OscIndex N → ℂ) :=
    { output := fun _ => outP, queries := fun _ => qP,
      gates := fun _ => gP, usesW := fun _ => 1 }
  refine ⟨A, rfl, ?_, ?_, ?_⟩
  · exact (one_mul qP).ge
  · exact (one_mul gP).ge
  · intro x v hxv hx0 hv0 hE
    have hM : ∀ j, 0 < P.M j := fun j =>
      lt_of_lt_of_le (hP.2.2.2.1 j).1 (hP.2.2.2.1 j).2.1
    have ht : 0 ≤ P.t := hP.2.2.2.2.2.2.1
    have hε : 0 < P.ε := hP.2.2.2.2.2.2.2
    have hex : ∃ xv : (ℝ → Fin N → ℝ) × (ℝ → Fin N → ℝ),
        IsNewtonTrajectory P.K P.M xv.1 xv.2 ∧ xv.1 0 = P.x0 ∧ xv.2 0 = P.xdot0 :=
      ⟨(x, v), hxv, hx0, hv0⟩
    obtain ⟨hxt, hvt⟩ := newton_unique_nonneg P.K P.M hM x v
      (Classical.choose hex).1 (Classical.choose hex).2 hxv (Classical.choose_spec hex).1
      (hx0.trans (Classical.choose_spec hex).2.1.symm)
      (hv0.trans (Classical.choose_spec hex).2.2.symm) ht
    change l2Dist outP (oscillatorState P.K P.M P.energy (x P.t) (v P.t)) ≤ P.ε
    simp only [outP, hex, ↓reduceDIte, ← hxt, ← hvt]
    simpa [l2Dist, l2Norm, l2NormSq] using hε.le

end Qatlib.Papers.CoupledOsc23.MainResults.Theorem1OscillatorSim
