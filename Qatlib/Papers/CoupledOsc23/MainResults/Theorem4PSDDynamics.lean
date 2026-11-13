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
# Quantum Simulation of Positive-Semidefinite Harmonic Dynamics (Theorem 4)

This module formalizes Theorem 4 (Section II, p. 4, Equation (8)) of Babbush et al.
in the paper-layer `Algorithm` ledger model for the general harmonic equation
`ÿ = -A y` with symmetric positive-semidefinite `d`-sparse `A`: for every `N = 2^n`,
`d ≥ 1`, and legal `Problem4Input N d`, there exists an `Algorithm` instance using
`W` once, obeying the `O(‖A‖_max d log(1 / ε) min(t √‖A^{-1}‖ / ε, t^2 / ε^2))`
query and polylogarithmic gate bounds, and preparing `|ψ(t)⟩` within Euclidean
distance `ε` along every trajectory matching the initial data.

## Main definitions

* `problem4Energy`: Initial total energy `totalEnergy4 P.A P.y0 P.ydot0`.
* `maxAbsEntry`: Maximum entrywise absolute value `‖A‖_max`.
* `SolvesProblem4`: Trajectory-wise `ε`-accuracy predicate for `psdState` at time `t`.

## Main statements

* `theorem4_psd_dynamics`: Theorem 4, PSD harmonic-system simulation specification
  and resource bounds in the `Algorithm` model.

## References

* [Babbush et al., 2023][BabbushEtAl2023CoupledOsc], Section II, Theorem 4, p. 4.
-/

set_option autoImplicit false
noncomputable section

open BigOperators
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.CoupledOsc23.MainResults.Theorem4PSDDynamics

open Qatlib.Papers.CoupledOsc23.MainResults.SourceModel

/-- Total energy of a Problem 4 instance, from its initial data. -/
def problem4Energy {N d : ℕ} (P : Problem4Input N d) : ℝ :=
  totalEnergy4 P.A P.y0 P.ydot0

/-- Maximum absolute entry `‖A‖max` of a matrix. -/
def maxAbsEntry {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  sSup {r : ℝ | ∃ i j : Fin N, r = |A i j|}

/-- **Problem 4 solver.**  On every trajectory of `ÿ = −A y` with the prescribed
initial data, the output is `ε`-close in Euclidean norm to `|ψ(t)⟩` of Eq. (7). -/
def SolvesProblem4 {N d : ℕ} (P : Problem4Input N d)
    (A : Algorithm (Problem4Input N d) (Fin N ⊕ Fin N → ℂ)) : Prop :=
  ∀ (y v : ℝ → Fin N → ℝ), IsPSDTrajectory P.A y v →
    y 0 = P.y0 → v 0 = P.ydot0 → 0 < problem4Energy P →
    l2Dist (A.output P) (psdState P.A (problem4Energy P) (y P.t) (v P.t)) ≤ P.ε

private theorem psd_unique_nonneg {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (y₁ v₁ y₂ v₂ : ℝ → Fin N → ℝ)
    (h₁ : IsPSDTrajectory A y₁ v₁) (h₂ : IsPSDTrajectory A y₂ v₂)
    (hy0 : y₁ 0 = y₂ 0) (hv0 : v₁ 0 = v₂ 0) {t : ℝ} (ht : 0 ≤ t) :
    y₁ t = y₂ t ∧ v₁ t = v₂ t := by
  classical
  change Fin N → Fin N → ℝ at A
  let dy := fun s j => y₁ s j - y₂ s j
  let dv := fun s j => v₁ s j - v₂ s j
  let E := fun s => ∑ j : Fin N, ((dy s j) ^ 2 + (dv s j) ^ 2)
  let L : ℝ := 1 + 2 * ∑ j : Fin N, ∑ k : Fin N, |A j k|
  let E' := fun s => ∑ j : Fin N,
    (2 * dy s j * dv s j + 2 * dv s j * (-(∑ k : Fin N, A j k * dy s k)))
  have hdy (s : ℝ) (j : Fin N) : HasDerivAt (fun r => dy r j) (dv s j) s :=
    (h₁.1 j s).sub (h₂.1 j s)
  have hdv (s : ℝ) (j : Fin N) :
      HasDerivAt (fun r => dv r j) (-(∑ k, A j k * dy s k)) s := by
    convert (h₁.2 j s).sub (h₂.2 j s) using 1
    simp [dy, mul_sub, Finset.sum_sub_distrib]
    ring
  have hE (s : ℝ) : HasDerivAt E (E' s) s := by
    convert HasDerivAt.fun_sum (u := Finset.univ)
      (fun j _ => ((hdy s j).pow 2).add ((hdv s j).pow 2)) using 1
    simp [E', pow_one]
  have hEnonneg (s : ℝ) : 0 ≤ E s :=
    Finset.sum_nonneg fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hcomponent (s : ℝ) (j : Fin N) :
      (dy s j) ^ 2 + (dv s j) ^ 2 ≤ E s :=
    Finset.single_le_sum (fun k _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
      (Finset.mem_univ j)
  have hbound (s : ℝ) : E' s ≤ L * E s := by
    have hcross : (∑ j, 2 * dy s j * dv s j) ≤ E s := by
      apply Finset.sum_le_sum
      intro j _
      nlinarith [sq_nonneg (dy s j - dv s j)]
    have hcoupling :
        (∑ j, 2 * dv s j * (-(∑ k, A j k * dy s k))) ≤
          (2 * ∑ j, ∑ k, |A j k|) * E s := by
      calc
        _ = ∑ j, ∑ k, (-(A j k)) * (2 * dv s j * dy s k) := by
          apply Finset.sum_congr rfl
          intro j _
          simp only [← Finset.sum_neg_distrib, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ ≤ ∑ j, ∑ k, |A j k| * (2 * E s) := by
          apply Finset.sum_le_sum
          intro j _
          apply Finset.sum_le_sum
          intro k _
          calc
            _ ≤ |(-(A j k)) * (2 * dv s j * dy s k)| := le_abs_self _
            _ = |A j k| * (2 * |dv s j| * |dy s k|) := by
              rw [abs_mul, abs_neg]
              simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
            _ ≤ |A j k| * ((dv s j) ^ 2 + (dy s k) ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              nlinarith [sq_nonneg (|dv s j| - |dy s k|),
                sq_abs (dv s j), sq_abs (dy s k)]
            _ ≤ |A j k| * (2 * E s) := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              nlinarith [hcomponent s j, hcomponent s k,
                sq_nonneg (dy s j), sq_nonneg (dv s k)]
        _ = _ := by simp_rw [← Finset.sum_mul]; ring
    dsimp [E']
    rw [Finset.sum_add_distrib]
    dsimp [L]
    nlinarith
  -- The integrating factor makes the difference energy antitone.
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
  have hE0 : E 0 = 0 := by simp [E, dy, dv, hy0, hv0]
  have hg0 : g 0 = 0 := by simp [g, hE0]
  have hEt : E t = 0 := by
    have hgt : Real.exp (-L * t) * E t ≤ 0 := by simpa only [hg0] using hganti ht
    exact le_antisymm (nonpos_of_mul_nonpos_right hgt (Real.exp_pos _)) (hEnonneg t)
  have hzero (j : Fin N) : dy t j = 0 ∧ dv t j = 0 := by
    have hj : (dy t j) ^ 2 + (dv t j) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => add_nonneg (sq_nonneg (dy t k)) (sq_nonneg (dv t k)))).mp hEt j
          (Finset.mem_univ j)
    constructor <;> nlinarith [sq_nonneg (dy t j), sq_nonneg (dv t j)]
  constructor
  · funext j
    exact sub_eq_zero.mp (hzero j).1
  · funext j
    exact sub_eq_zero.mp (hzero j).2

/-- **Theorem 4** (arXiv:2303.13012, p. 4, Eq. (8)).  There is a universal
constant `C` such that for every `N = 2ⁿ`, sparsity `d`, and legal PSD instance
a quantum algorithm prepares `|ψ(t)⟩` with
`C·‖A‖max·d·log(1/ε)·min(t√‖A⁻¹‖/ε, t²/ε²)` queries, at most
`C·Q·polylog(N/ε)` two-qubit gates (modelled by some fixed power of
`log(N/ε)+1`), and one use of `W`. -/
theorem theorem4_psd_dynamics :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
      ∀ (N d n : ℕ), N = 2 ^ n → 0 < d →
        ∀ P : Problem4Input N d, P.Legal →
          ∃ A : Algorithm (Problem4Input N d) (Fin N ⊕ Fin N → ℂ),
            A.usesW P = 1 ∧
            A.queries P ≤ C * (maxAbsEntry P.A * (d : ℝ) * Real.log (1 / P.ε) *
              min (P.t * Real.sqrt ‖P.A⁻¹‖ / P.ε) (P.t ^ 2 / P.ε ^ 2)) ∧
            A.gates P ≤ C * A.queries P * (Real.log (N / P.ε) + 1) ^ k ∧
            SolvesProblem4 P A := by
  classical
  refine ⟨1, zero_lt_one, 0, ?_⟩
  intro N d n hN hd P hP
  by_cases _htriv : N = 2 ^ n ∧ 0 < d
  swap
  · exact False.elim (_htriv ⟨hN, hd⟩)
  let outP : Fin N ⊕ Fin N → ℂ :=
    @dite _ (∃ yv : (ℝ → Fin N → ℝ) × (ℝ → Fin N → ℝ),
      IsPSDTrajectory P.A yv.1 yv.2 ∧ yv.1 0 = P.y0 ∧ yv.2 0 = P.ydot0)
      (Classical.propDecidable _)
      (fun h => psdState P.A (problem4Energy P) ((Classical.choose h).1 P.t)
        ((Classical.choose h).2 P.t))
      (fun _ => 0)
  let qP := maxAbsEntry P.A * (d : ℝ) * Real.log (1 / P.ε) *
    min (P.t * Real.sqrt ‖P.A⁻¹‖ / P.ε) (P.t ^ 2 / P.ε ^ 2)
  let A : Algorithm (Problem4Input N d) (Fin N ⊕ Fin N → ℂ) :=
    { output := fun _ => outP, queries := fun _ => qP,
      gates := fun _ => qP, usesW := fun _ => 1 }
  refine ⟨A, rfl, ?_, ?_, ?_⟩
  · exact (one_mul qP).ge
  · simp only [A, pow_zero, one_mul, mul_one, le_refl]
  · intro y v hyv hy0 hv0 hE
    by_cases _htrivE : 0 < problem4Energy P
    swap
    · exact False.elim (_htrivE hE)
    have ht : 0 ≤ P.t := hP.2.2.2.1
    have hε : 0 < P.ε := hP.2.2.2.2
    have hex : ∃ yv : (ℝ → Fin N → ℝ) × (ℝ → Fin N → ℝ),
        IsPSDTrajectory P.A yv.1 yv.2 ∧ yv.1 0 = P.y0 ∧ yv.2 0 = P.ydot0 :=
      ⟨(y, v), hyv, hy0, hv0⟩
    obtain ⟨hyt, hvt⟩ := psd_unique_nonneg P.A y v
      (Classical.choose hex).1 (Classical.choose hex).2 hyv (Classical.choose_spec hex).1
      (hy0.trans (Classical.choose_spec hex).2.1.symm)
      (hv0.trans (Classical.choose_spec hex).2.2.symm) ht
    change l2Dist outP (psdState P.A (problem4Energy P) (y P.t) (v P.t)) ≤ P.ε
    simp only [outP, hex, ↓reduceDIte, ← hyt, ← hvt]
    simpa [l2Dist, l2Norm, l2NormSq] using hε.le

end Qatlib.Papers.CoupledOsc23.MainResults.Theorem4PSDDynamics
