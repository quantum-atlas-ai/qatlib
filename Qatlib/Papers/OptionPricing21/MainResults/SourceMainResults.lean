/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Post-Selection Success Bounds for Quantum Option Pricing Simulation

This module formalizes the discretized Black-Scholes spatial grid, duplicated payoff state
normalizations, momentum-space eigenvalues, and post-selection success probability lower bounds
for Hamiltonian-simulation option pricing. Both the symbolic $k = 0$ Fourier-mode lower bound
and the 9-qubit ($N_x = 512$) benchmark lower bound exceeding $60\%$ are proved analytically.

## Main statements

* `postselection_success_lower_bound`: General $k = 0$ Fourier-mode lower bound
  $P_s \ge e^{-2 T r} \gamma(N_x, K)$.
* `nineQubits_normalized_success_above_sixty`: Analytical proof that at the 9-qubit benchmark
  parameters ($N_x = 512, K = 50, S_{\max} = 150, T = 1, r = 0.04, \sigma = 0.2$), the
  unit-normalized post-selection success probability exceeds $3/5 = 60\%$.
* `nineQubits_main_result`: Combined 9-qubit grid-size and post-selection threshold theorem.

## References

* [Gonzalez-Conde et al., 2023][GonzalezCondeEtAl2023]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OptionPricing21.MainResults

open scoped BigOperators

/-! ## Part 1. Grid and normalization data -/

/-- With `n` position qubits, the spatial grid has `Nx = 2 ^ n` points [GonzalezCondeEtAl2023]. -/
def gridSize (n : ℕ) : ℕ := 2 ^ n

/-- At `n = 9` qubits, the spatial grid has `512` points. -/
theorem gridSize_nine : gridSize 9 = 512 := by
  norm_num [gridSize]

/-- Spatial grid spacing `δx = 2 * xmax / (Nx - 1)` [GonzalezCondeEtAl2023]. -/
def deltaX (Nx : ℕ) (xmax : ℝ) : ℝ := 2 * xmax / ((Nx : ℝ) - 1)

/-- Largest grid index `N_max` at which the put payoff `K - e^{x_j}` is nonnegative
[GonzalezCondeEtAl2023]. -/
def nMax (Nx : ℕ) (xmax K : ℝ) : ℕ :=
  ⌊((Nx : ℝ) - 1) * (Real.log K / (2 * xmax) + 1 / 4)⌋.toNat

/-- Printed amplitude-sum square normalization `Λ = (2 ∑_{m=0}^{N_max} (K - e^{-xmax/2 + m δx}))²`
[GonzalezCondeEtAl2023]. -/
def Lambda (Nmax : ℕ) (xmax δx K : ℝ) : ℝ :=
  (2 * ∑ m ∈ Finset.range (Nmax + 1), (K - Real.exp (-xmax / 2 + m * δx))) ^ 2

/-- Unit-vector squared-norm normalization `Λ_norm = 2 ∑_{j=0}^{N_max} (K - e^{-xmax/2 + j δx})²`
for the duplicated payoff state [GonzalezCondeEtAl2023]. -/
def LambdaNorm (Nmax : ℕ) (xmax δx K : ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.range (Nmax + 1), (K - Real.exp (-xmax / 2 + j * δx)) ^ 2

/-- Zero-mode factorized payoff square `γ0(N_x, K) = (∑_{j=0}^{N_max} (K - e^{-xmax/2 + j δx}))²`
[GonzalezCondeEtAl2023]. -/
def gamma0 (Nmax : ℕ) (xmax δx K : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (Nmax + 1), (K - Real.exp (-xmax / 2 + j * δx))) ^ 2

/-- Zero-mode post-selection ratio `γ(N_x, K) = 4 * γ0 / (Λ * N_x)` [GonzalezCondeEtAl2023]. -/
def gamma (Nx Nmax : ℕ) (xmax δx K : ℝ) : ℝ :=
  4 * gamma0 Nmax xmax δx K / (Lambda Nmax xmax δx K * (Nx : ℝ))

/-- Structural identity `Λ = 4 * γ0`. -/
theorem Lambda_eq_four_gamma0 (Nmax : ℕ) (xmax δx K : ℝ) :
    Lambda Nmax xmax δx K = 4 * gamma0 Nmax xmax δx K := by
  unfold Lambda gamma0
  ring

/-- Boundary constraint equivalence `e^{xmax / 2} = 3 * K ↔ xmax = 2 * log (3 * K)` for `K > 0`. -/
theorem exp_half_eq_three_mul {xmax K : ℝ} (hK : 0 < K) :
    Real.exp (xmax / 2) = 3 * K ↔ xmax = 2 * Real.log (3 * K) := by
  constructor
  · intro h
    have hlog : xmax / 2 = Real.log (3 * K) := by
      rw [← h, Real.log_exp]
    linarith
  · intro h
    rw [h, show (2 * Real.log (3 * K)) / 2 = Real.log (3 * K) by ring,
      Real.exp_log (by positivity)]

/-! ## Part 2. Momentum eigenvalues and post-selection probability -/

/-- Discrete momentum eigenvalues `p_k = sin (2πk / Nx) / δx` [GonzalezCondeEtAl2023]. -/
def momentum (Nx : ℕ) (δx : ℝ) (k : ℕ) : ℝ :=
  Real.sin (2 * Real.pi * (k : ℝ) / (Nx : ℝ)) / δx

/-- At `k = 0`, the discrete momentum eigenvalue vanishes. -/
theorem momentum_zero (Nx : ℕ) (δx : ℝ) : momentum Nx δx 0 = 0 := by
  simp [momentum]

/-- First Fourier block amplitude `A_k` of the duplicated initial condition
[GonzalezCondeEtAl2023]. -/
def ampFirst (Nmax Nx : ℕ) (xmax δx K : ℝ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (Nmax + 1),
    ((K - Real.exp (-xmax / 2 + (j : ℝ) * δx) : ℝ) : ℂ) *
      Complex.exp (Complex.I * (2 * Real.pi * (k : ℝ) * (j : ℝ) / (Nx : ℝ)))

/-- Reflected second Fourier block amplitude `B_k` of the duplicated initial condition
[GonzalezCondeEtAl2023]. -/
def ampSecond (Nmax Nx : ℕ) (xmax δx K : ℝ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (Nx - 1 - Nmax) (Nx - 1),
    ((K - Real.exp (-xmax / 2 + (((Nx : ℝ) - 1) - (j : ℝ)) * δx) : ℝ) : ℂ) *
      Complex.exp (Complex.I * (2 * Real.pi * (k : ℝ) * (j : ℝ) / (Nx : ℝ)))

/-- Post-selection success probability parameterized by an explicit normalization `Lam`
[GonzalezCondeEtAl2023]. -/
def successProbWith (Nx Nmax : ℕ) (xmax δx K T r σ Lam : ℝ) : ℝ :=
  (1 / ((Nx : ℝ) * Lam)) *
    ∑ k ∈ Finset.range Nx,
      Complex.normSq (ampFirst Nmax Nx xmax δx K k + ampSecond Nmax Nx xmax δx K k) *
        Real.exp (-2 * T * (σ ^ 2 * (momentum Nx δx k) ^ 2 / 2 + r))

/-- Post-selection success probability with normalization `Lambda` [GonzalezCondeEtAl2023]. -/
def postSelectionProb (Nx Nmax : ℕ) (xmax δx K T r σ : ℝ) : ℝ :=
  successProbWith Nx Nmax xmax δx K T r σ (Lambda Nmax xmax δx K)

/-- Post-selection success probability with unit-state normalization `LambdaNorm`
[GonzalezCondeEtAl2023]. -/
def postSelectionProbNorm (Nx Nmax : ℕ) (xmax δx K T r σ : ℝ) : ℝ :=
  successProbWith Nx Nmax xmax δx K T r σ (LambdaNorm Nmax xmax δx K)

/-! ## Part 3. Finite-sum factorizations -/

/-- At `k = 0`, `ampFirst` reduces to the real payoff sum. -/
lemma ampFirst_zero (Nmax Nx : ℕ) (xmax δx K : ℝ) :
    ampFirst Nmax Nx xmax δx K 0 =
      ((∑ j ∈ Finset.range (Nmax + 1), (K - Real.exp (-xmax / 2 + (j : ℝ) * δx))) : ℝ) := by
  simp [ampFirst, Complex.ofReal_sum]

/-- Reflection `j ↦ Nx - 1 - j` identifies the upper-block payoff sum with the lower-block sum. -/
lemma reflected_coeff_sum
    (Nmax Nx : ℕ) (hNx : 1 ≤ Nx) (h : Nmax ≤ Nx - 1) (xmax δx K : ℝ) :
    (∑ j ∈ Finset.Icc (Nx - 1 - Nmax) (Nx - 1),
        (K - Real.exp (-xmax / 2 + (((Nx : ℝ) - 1) - (j : ℝ)) * δx))) =
      ∑ j ∈ Finset.range (Nmax + 1), (K - Real.exp (-xmax / 2 + (j : ℝ) * δx)) := by
  refine Finset.sum_bij (fun j _ => Nx - 1 - j) ?hi ?hinj ?hsurj ?h
  · intro j hj
    simp only [Finset.mem_range]
    rw [Finset.mem_Icc] at hj
    omega
  · intro j1 hj1 j2 hj2 heq
    rw [Finset.mem_Icc] at hj1 hj2
    omega
  · intro b hb
    rw [Finset.mem_range] at hb
    refine ⟨Nx - 1 - b, ?_, ?_⟩
    · rw [Finset.mem_Icc]; omega
    · omega
  · intro a ha
    obtain ⟨_, ha2⟩ := Finset.mem_Icc.mp ha
    have hcast : (((Nx : ℝ) - 1) - (a : ℝ)) = ((Nx - 1 - a : ℕ) : ℝ) := by
      rw [Nat.cast_sub ha2, Nat.cast_sub hNx, Nat.cast_one]
    rw [hcast]

/-- At `k = 0`, `ampSecond` also equals the real payoff sum. -/
lemma ampSecond_zero (Nmax Nx : ℕ) (hNx : 1 ≤ Nx) (h : Nmax ≤ Nx - 1)
    (xmax δx K : ℝ) :
    ampSecond Nmax Nx xmax δx K 0 =
      ((∑ j ∈ Finset.range (Nmax + 1), (K - Real.exp (-xmax / 2 + (j : ℝ) * δx))) : ℝ) := by
  calc ampSecond Nmax Nx xmax δx K 0
      = ((∑ j ∈ Finset.Icc (Nx - 1 - Nmax) (Nx - 1),
          (K - Real.exp (-xmax / 2 + (((Nx : ℝ) - 1) - (j : ℝ)) * δx))) : ℝ) := by
          unfold ampSecond
          rw [Complex.ofReal_sum]
          apply Finset.sum_congr rfl
          intro _ _
          simp
    _ = ((∑ j ∈ Finset.range (Nmax + 1), (K - Real.exp (-xmax / 2 + (j : ℝ) * δx))) : ℝ) := by
          rw [reflected_coeff_sum Nmax Nx hNx h xmax δx K]

/-! ## Part 4. Post-selection success lower bound -/

/-- Zero-mode post-selection lower bound `postSelectionProb ≥ exp (-2 * T * r) * gamma`
[GonzalezCondeEtAl2023]. -/
theorem postselection_success_lower_bound
    (Nx Nmax : ℕ) (xmax δx K T r σ : ℝ)
    (hNx : 1 ≤ Nx) (hNmax : Nmax ≤ Nx - 1)
    (hLam : 0 < Lambda Nmax xmax δx K) :
    postSelectionProb Nx Nmax xmax δx K T r σ ≥
      Real.exp (-2 * T * r) * gamma Nx Nmax xmax δx K := by
  have hNxR : (0 : ℝ) < (Nx : ℝ) := by exact_mod_cast hNx
  have hc : (0 : ℝ) < 1 / ((Nx : ℝ) * Lambda Nmax xmax δx K) := by
    apply div_pos one_pos
    exact mul_pos hNxR hLam
  have hterm_nonneg : ∀ k ∈ Finset.range Nx,
      0 ≤ Complex.normSq (ampFirst Nmax Nx xmax δx K k + ampSecond Nmax Nx xmax δx K k) *
        Real.exp (-2 * T * (σ ^ 2 * (momentum Nx δx k) ^ 2 / 2 + r)) := by
    intro _ _
    exact mul_nonneg (Complex.normSq_nonneg _) (Real.exp_pos _).le
  have hsingle :
      Complex.normSq (ampFirst Nmax Nx xmax δx K 0 + ampSecond Nmax Nx xmax δx K 0) *
          Real.exp (-2 * T * (σ ^ 2 * (momentum Nx δx 0) ^ 2 / 2 + r)) ≤
        ∑ k ∈ Finset.range Nx,
          Complex.normSq (ampFirst Nmax Nx xmax δx K k + ampSecond Nmax Nx xmax δx K k) *
            Real.exp (-2 * T * (σ ^ 2 * (momentum Nx δx k) ^ 2 / 2 + r)) := by
    apply Finset.single_le_sum hterm_nonneg
    rw [Finset.mem_range]; omega
  set S : ℝ := ∑ j ∈ Finset.range (Nmax + 1),
    (K - Real.exp (-xmax / 2 + (j : ℝ) * δx)) with hS
  have hA : ampFirst Nmax Nx xmax δx K 0 = ((S : ℝ) : ℂ) := by
    rw [ampFirst_zero, ← hS]
  have hB : ampSecond Nmax Nx xmax δx K 0 = ((S : ℝ) : ℂ) := by
    rw [ampSecond_zero Nmax Nx hNx hNmax, ← hS]
  have hmom : momentum Nx δx 0 = 0 := momentum_zero Nx δx
  have hnorm :
      Complex.normSq (ampFirst Nmax Nx xmax δx K 0 + ampSecond Nmax Nx xmax δx K 0)
        = 4 * gamma0 Nmax xmax δx K := by
    rw [hA, hB]
    have h2 : ((S : ℝ) : ℂ) + ((S : ℝ) : ℂ) = ((2 * S : ℝ) : ℂ) := by push_cast; ring
    rw [h2, Complex.normSq_ofReal]
    unfold gamma0
    rw [← hS]
    ring
  have hexp :
      Real.exp (-2 * T * (σ ^ 2 * (momentum Nx δx 0) ^ 2 / 2 + r))
        = Real.exp (-2 * T * r) := by
    rw [hmom]; ring_nf
  have hterm0 :
      Complex.normSq (ampFirst Nmax Nx xmax δx K 0 + ampSecond Nmax Nx xmax δx K 0) *
          Real.exp (-2 * T * (σ ^ 2 * (momentum Nx δx 0) ^ 2 / 2 + r))
        = 4 * gamma0 Nmax xmax δx K * Real.exp (-2 * T * r) := by
    rw [hnorm, hexp]
  calc postSelectionProb Nx Nmax xmax δx K T r σ
      = (1 / ((Nx : ℝ) * Lambda Nmax xmax δx K)) *
          ∑ k ∈ Finset.range Nx,
            Complex.normSq (ampFirst Nmax Nx xmax δx K k + ampSecond Nmax Nx xmax δx K k) *
              Real.exp (-2 * T * (σ ^ 2 * (momentum Nx δx k) ^ 2 / 2 + r)) := by
          unfold postSelectionProb successProbWith; rfl
    _ ≥ (1 / ((Nx : ℝ) * Lambda Nmax xmax δx K)) *
          (Complex.normSq (ampFirst Nmax Nx xmax δx K 0 + ampSecond Nmax Nx xmax δx K 0) *
            Real.exp (-2 * T * (σ ^ 2 * (momentum Nx δx 0) ^ 2 / 2 + r))) := by
          apply mul_le_mul_of_nonneg_left hsingle hc.le
    _ = Real.exp (-2 * T * r) * gamma Nx Nmax xmax δx K := by
          rw [hterm0]
          unfold gamma
          field_simp

/-- Constrained variant of `postselection_success_lower_bound` under `e^{xmax / 2} = 3 * K`
[GonzalezCondeEtAl2023]. -/
theorem postselection_success_lower_bound_under_constraint
    (Nx Nmax : ℕ) (xmax δx K T r σ : ℝ)
    (hNx : 1 ≤ Nx) (hNmax : Nmax ≤ Nx - 1)
    (hLam : 0 < Lambda Nmax xmax δx K)
    (_hK : 0 < K) (_hconstraint : Real.exp (xmax / 2) = 3 * K) :
    postSelectionProb Nx Nmax xmax δx K T r σ ≥
      Real.exp (-2 * T * r) * gamma Nx Nmax xmax δx K :=
  postselection_success_lower_bound Nx Nmax xmax δx K T r σ hNx hNmax hLam

/-! ## Part 5. 9-qubit benchmark post-selection threshold -/

/-- Benchmark strike price `K = 50` [GonzalezCondeEtAl2023]. -/
def benchmarkK : ℝ := 50

/-- Benchmark log-domain cutoff `xmax = 2 * log (3 * 50)` [GonzalezCondeEtAl2023]. -/
def benchmarkXmax : ℝ := 2 * Real.log (3 * 50)

/-- Benchmark grid spacing `δx` at `Nx = 512` [GonzalezCondeEtAl2023]. -/
def benchmarkDx : ℝ := deltaX 512 benchmarkXmax

/-- Benchmark put-payoff cutoff index `N_max` at `Nx = 512` [GonzalezCondeEtAl2023]. -/
def benchmarkNmax : ℕ := nMax 512 benchmarkXmax 50

/-- At the 9-qubit benchmark (`Nx = 512, K = 50, S_max = 150, T = 1, r = 0.04, σ = 0.2`), the
unit-normalized post-selection success probability is at least `3 / 5 = 60%`
[GonzalezCondeEtAl2023]. -/
theorem nineQubits_normalized_success_above_sixty :
    postSelectionProbNorm 512 benchmarkNmax benchmarkXmax benchmarkDx 50 1 0.04 0.2 ≥ 3 / 5 := by
  have hlog : 0 < Real.log 150 := Real.log_pos (by norm_num)
  have hxmax : benchmarkXmax = 2 * Real.log 150 := by norm_num [benchmarkXmax]
  have hdx : benchmarkDx = 4 * Real.log 150 / 511 := by
    norm_num [benchmarkDx, deltaX, hxmax]
    ring
  let X : ℝ := 511 * (Real.log 50 / (4 * Real.log 150) + 1 / 4)
  have hcutoff : benchmarkNmax = ⌊X⌋.toNat := by
    unfold benchmarkNmax nMax
    congr 2
    norm_num [X, hxmax]
    ring
  have hlog_lower : 7 * Real.log 150 < 9 * Real.log 50 := by
    have h := Real.log_lt_log (by positivity : (0 : ℝ) < 150 ^ 7)
      (by norm_num : (150 : ℝ) ^ 7 < 50 ^ 9)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hlog_upper : 5 * Real.log 50 < 4 * Real.log 150 := by
    have h := Real.log_lt_log (by positivity : (0 : ℝ) < 50 ^ 5)
      (by norm_num : (50 : ℝ) ^ 5 < 150 ^ 4)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hratio_lower : (7 / 36 : ℝ) < Real.log 50 / (4 * Real.log 150) := by
    apply (lt_div_iff₀ (by positivity : 0 < 4 * Real.log 150)).2
    linarith
  have hratio_upper : Real.log 50 / (4 * Real.log 150) < (1 / 5 : ℝ) := by
    apply (div_lt_iff₀ (by positivity : 0 < 4 * Real.log 150)).2
    linarith
  have hX_lower : (227 : ℝ) < X := by dsimp [X]; linarith
  have hX_upper : X < (230 : ℝ) := by dsimp [X]; linarith
  have hfloor_nonneg : 0 ≤ ⌊X⌋ := Int.floor_nonneg.mpr (by linarith)
  have hN_lower : 227 ≤ benchmarkNmax := by
    rw [hcutoff, Int.le_toNat hfloor_nonneg]
    exact Int.le_floor.mpr hX_lower.le
  have hN_upper : benchmarkNmax ≤ 229 := by
    rw [hcutoff, Int.toNat_le]
    exact Int.floor_le_iff.mpr (by norm_num; exact hX_upper)
  have hN_real : (benchmarkNmax : ℝ) ≤ X := by
    rw [hcutoff, ← Int.cast_natCast, Int.toNat_of_nonneg hfloor_nonneg]
    exact Int.floor_le X
  have hgrid (j : ℕ) :
      -benchmarkXmax / 2 + (j : ℝ) * benchmarkDx =
        (-1 + 4 * (j : ℝ) / 511) * Real.log 150 := by
    rw [hxmax, hdx]
    ring
  have hpayoff_exponent (j : ℕ) (hj : j ≤ benchmarkNmax) :
      -benchmarkXmax / 2 + (j : ℝ) * benchmarkDx ≤ Real.log 50 := by
    have hjR : (j : ℝ) ≤ (benchmarkNmax : ℝ) := by exact_mod_cast hj
    have hjX : (j : ℝ) ≤ X := hjR.trans hN_real
    have hscaled := mul_le_mul_of_nonneg_right hjX (by positivity : 0 ≤ 4 * Real.log 150)
    have hX_scaled : X * (4 * Real.log 150) = 511 * (Real.log 50 + Real.log 150) := by
      dsimp [X]
      field_simp
    rw [hX_scaled] at hscaled
    rw [hgrid]
    nlinarith
  let t (j : ℕ) : ℝ := 50 - Real.exp (-benchmarkXmax / 2 + (j : ℝ) * benchmarkDx)
  let S : ℝ := ∑ j ∈ Finset.range (benchmarkNmax + 1), t j
  have ht_nonneg (j : ℕ) (hj : j ∈ Finset.range (benchmarkNmax + 1)) : 0 ≤ t j := by
    have hjN : j ≤ benchmarkNmax := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    have h := Real.exp_le_exp.mpr (hpayoff_exponent j hjN)
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 50)] at h
    dsimp [t]
    linarith
  have ht_le (j : ℕ) : t j ≤ 50 := by
    dsimp [t]
    linarith [Real.exp_pos (-benchmarkXmax / 2 + (j : ℝ) * benchmarkDx)]
  have hLam_upper : LambdaNorm benchmarkNmax benchmarkXmax benchmarkDx 50 ≤ 100 * S := by
    have hsum : (∑ j ∈ Finset.range (benchmarkNmax + 1), t j ^ 2) ≤
        ∑ j ∈ Finset.range (benchmarkNmax + 1), 50 * t j := by
      apply Finset.sum_le_sum
      intro j hj
      nlinarith [ht_nonneg j hj, ht_le j]
    rw [← Finset.mul_sum] at hsum
    change 2 * (∑ j ∈ Finset.range (benchmarkNmax + 1), t j ^ 2) ≤ 100 * S
    dsimp [S]
    linarith
  have ht_first (j : ℕ) (hj : j ∈ Finset.range 128) : 49 ≤ t j := by
    have hjR : (j : ℝ) ≤ 127 := by
      have : j ≤ 127 := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
      exact_mod_cast this
    have hexponent : -benchmarkXmax / 2 + (j : ℝ) * benchmarkDx ≤ 0 := by
      rw [hgrid]
      apply mul_nonpos_of_nonpos_of_nonneg _ hlog.le
      linarith
    have h := Real.exp_le_exp.mpr hexponent
    rw [Real.exp_zero] at h
    dsimp [t]
    linarith
  have hlog_thirteen : Real.log 150 < 2 * Real.log 13 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 150)
      (by norm_num : (150 : ℝ) < 13 ^ 2)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have ht_second (j : ℕ) (hj : j ∈ Finset.Ico 128 192) : 37 ≤ t j := by
    have hjR : (j : ℝ) ≤ 191 := by
      have : j ≤ 191 := by have := (Finset.mem_Ico.mp hj).2; omega
      exact_mod_cast this
    have hexponent : -benchmarkXmax / 2 + (j : ℝ) * benchmarkDx ≤ Real.log 13 := by
      rw [hgrid]
      have hcoeff : (-1 + 4 * (j : ℝ) / 511) ≤ (1 / 2 : ℝ) := by linarith
      have := mul_le_mul_of_nonneg_right hcoeff hlog.le
      linarith
    have h := Real.exp_le_exp.mpr hexponent
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 13)] at h
    dsimp [t]
    linarith
  have hsum_first : (6272 : ℝ) ≤ ∑ j ∈ Finset.range 128, t j := by
    calc
      (6272 : ℝ) = ∑ _j ∈ Finset.range 128, (49 : ℝ) := by norm_num
      _ ≤ _ := Finset.sum_le_sum ht_first
  have hsum_second : (2368 : ℝ) ≤ ∑ j ∈ Finset.Ico 128 192, t j := by
    calc
      (2368 : ℝ) = ∑ _j ∈ Finset.Ico 128 192, (37 : ℝ) := by norm_num
      _ ≤ _ := Finset.sum_le_sum ht_second
  have hS_lower : 8640 ≤ S := by
    have hsubset : Finset.range 192 ⊆ Finset.range (benchmarkNmax + 1) :=
      Finset.range_mono (by omega)
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun j hj _ => ht_nonneg j hj)
    have hsplit := Finset.sum_range_add_sum_Ico t (by norm_num : 128 ≤ 192)
    dsimp [S]
    linarith
  have hS_pos : 0 < S := by linarith
  have hLam_pos : 0 < LambdaNorm benchmarkNmax benchmarkXmax benchmarkDx 50 := by
    have ht0 := ht_first 0 (by simp)
    have hsingle : t 0 ^ 2 ≤ ∑ j ∈ Finset.range (benchmarkNmax + 1), t j ^ 2 := by
      apply Finset.single_le_sum (fun j _ => sq_nonneg (t j))
      simp
    change 0 < 2 * (∑ j ∈ Finset.range (benchmarkNmax + 1), t j ^ 2)
    nlinarith [sq_nonneg (t 0 - 49)]
  have hexp_lower : (0.92 : ℝ) ≤ Real.exp (-0.08) := by
    have := Real.add_one_le_exp (-0.08)
    linarith
  have hmode : 4 * S ^ 2 * Real.exp (-0.08) ≤
      ∑ k ∈ Finset.range 512,
        Complex.normSq
            (ampFirst benchmarkNmax 512 benchmarkXmax benchmarkDx 50 k +
              ampSecond benchmarkNmax 512 benchmarkXmax benchmarkDx 50 k) *
          Real.exp (-2 * 1 * ((0.2 : ℝ) ^ 2 * (momentum 512 benchmarkDx k) ^ 2 / 2 + 0.04)) := by
    have hsingle := Finset.single_le_sum
      (s := Finset.range 512)
      (f := fun k => Complex.normSq
          (ampFirst benchmarkNmax 512 benchmarkXmax benchmarkDx 50 k +
            ampSecond benchmarkNmax 512 benchmarkXmax benchmarkDx 50 k) *
        Real.exp (-2 * 1 * ((0.2 : ℝ) ^ 2 * (momentum 512 benchmarkDx k) ^ 2 / 2 + 0.04)))
      (fun k _ => mul_nonneg (Complex.normSq_nonneg _) (Real.exp_pos _).le)
      (by simp : 0 ∈ Finset.range 512)
    have hA : ampFirst benchmarkNmax 512 benchmarkXmax benchmarkDx 50 0 = (S : ℂ) :=
      ampFirst_zero _ _ _ _ _
    have hB : ampSecond benchmarkNmax 512 benchmarkXmax benchmarkDx 50 0 = (S : ℂ) :=
      ampSecond_zero _ _ (by norm_num) (by omega) _ _ _
    have hnorm : Complex.normSq ((S : ℂ) + (S : ℂ)) = 4 * S ^ 2 := by
      rw [← Complex.ofReal_add, Complex.normSq_ofReal]
      ring
    simpa only [hA, hB, hnorm, momentum_zero, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, zero_div, zero_add, show (-2 * (1 : ℝ) * 0.04) = -0.08 by norm_num]
      using hsingle
  have hprob : (4 * S ^ 2 * Real.exp (-0.08)) /
      (512 * LambdaNorm benchmarkNmax benchmarkXmax benchmarkDx 50) ≤
      postSelectionProbNorm 512 benchmarkNmax benchmarkXmax benchmarkDx 50 1 0.04 0.2 := by
    unfold postSelectionProbNorm successProbWith
    simpa only [Nat.cast_ofNat, one_div_mul_eq_div] using
      mul_le_mul_of_nonneg_left hmode
        (by positivity : 0 ≤ 1 / (512 * LambdaNorm benchmarkNmax benchmarkXmax benchmarkDx 50))
  have hbound : (0.92 / 12800 : ℝ) * S ≤
      (4 * S ^ 2 * Real.exp (-0.08)) /
        (512 * LambdaNorm benchmarkNmax benchmarkXmax benchmarkDx 50) := by
    apply (le_div_iff₀ (by positivity :
      0 < 512 * LambdaNorm benchmarkNmax benchmarkXmax benchmarkDx 50)).2
    have hnorm_bound := mul_le_mul_of_nonneg_left hLam_upper
      (by positivity : 0 ≤ (0.92 / 12800 : ℝ) * S * 512)
    have hexp_bound := mul_le_mul_of_nonneg_left hexp_lower (by positivity : 0 ≤ 4 * S ^ 2)
    nlinarith
  have hthreshold : (3 / 5 : ℝ) ≤ (0.92 / 12800 : ℝ) * S := by linarith
  exact hthreshold.trans (hbound.trans hprob)

/-- Combined 9-qubit grid size and `≥ 60%` post-selection success probability result
[GonzalezCondeEtAl2023]. -/
theorem nineQubits_main_result :
    gridSize 9 = 512 ∧
      postSelectionProbNorm 512 benchmarkNmax benchmarkXmax benchmarkDx 50 1 0.04 0.2 ≥ 3 / 5 :=
  ⟨gridSize_nine, nineQubits_normalized_success_above_sixty⟩

end Qatlib.Papers.OptionPricing21.MainResults
