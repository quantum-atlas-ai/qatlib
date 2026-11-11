/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DynamicProg24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# DynamicProg24 — global convergence of quantum dynamic programming

Source: arXiv:2403.09187 (Quantum Dynamic Programming).  Fixed text: `assets/2403.09187.txt`.
Theorem 9 (p. 14–15, Eq. (S31)–(S40)), Theorem 12 (p. 18, Eq. (S55)–(S66)),
Lemma 19 (p. 26, Eq. (S121)–(S127)) and Theorem 22 (p. 28–29, Eq. (S136)–(S139)).

The common analytic engine is the accumulated-error estimate (Eq. (S32), (S39)): if the
`n`-th emulated step lands within `η` of the exact recursion and the profile `h` is
`r`-Lipschitz with `r < 1`, then the distance after `N` steps is at most
`h^[N] (δ₀) + η / (1 - r)`.  All convergence statements below are consequences of it.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Papers.DynamicProg24.MainResults

/-- **Accumulated-error estimate** (arXiv:2403.09187, Eq. (S32), (S39)).

Let `h` be `r`-Lipschitz with `0 ≤ r < 1` and let `δ n` be the distance of the `n`-th
emulated iterate to the fixed point, each step adding at most `η` over the exact recursion:
`δ (n+1) ≤ h (δ n) + η`.  Then `δ N ≤ h^[N] (δ 0) + η / (1 - r)`.

This is the quantitative core of Theorem 9 used at every level of the paper's nesting. -/
theorem accumulated_error_le {h : ℝ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hmono : Monotone h)
    (hlip : ∀ x e : ℝ, 0 ≤ e → h (x + e) ≤ h x + r * e)
    (δ : ℕ → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hrec : ∀ n : ℕ, δ (n + 1) ≤ h (δ n) + η) :
    ∀ N : ℕ, δ N ≤ (h^[N]) (δ 0) + η * (1 - r)⁻¹ := by
  have hrneg : (0:ℝ) ≤ 1 - r := by linarith
  intro N
  induction N with
  | zero =>
      have hB : 0 ≤ η * (1 - r)⁻¹ := mul_nonneg hη (inv_nonneg.mpr hrneg)
      simp only [Function.iterate_zero_apply]
      linarith
  | succ k ih =>
      have hB : 0 ≤ η * (1 - r)⁻¹ := mul_nonneg hη (inv_nonneg.mpr hrneg)
      have h1 : h (δ k) ≤ h ((h^[k]) (δ 0) + η * (1 - r)⁻¹) := hmono ih
      have h2 : h ((h^[k]) (δ 0) + η * (1 - r)⁻¹)
          ≤ h ((h^[k]) (δ 0)) + r * (η * (1 - r)⁻¹) := hlip _ _ hB
      have hk : (h^[k + 1]) (δ 0) = h ((h^[k]) (δ 0)) :=
        Function.iterate_succ_apply' (f := h) k (δ 0)
      have hkey : r * (η * (1 - r)⁻¹) + η = η * (1 - r)⁻¹ := by
        have hrne : (1:ℝ) - r ≠ 0 := by linarith
        field_simp
        ring
      rw [hk]
      linarith [hrec k, h1, h2]

/-- Theorem 9 (arXiv:2403.09187, p. 14–15): *spectral convergence is sufficient for efficient
global convergence of QDP*.

If a quantum recursion `U` satisfies fast spectral convergence towards `τ` with profile `h`
(Definition 8, with Lipschitz constant `r < 1`), and the QDP implementation of the `N`
iterations produces iterates `ρ n` whose one-step distance exceeds the exact recursion by at
most `ε (1 - r)` per step, then the final state satisfies `δ_{ρ'_N} ≤ h^N (δ_0) + ε`, as in the
displayed conclusion of Theorem 9. -/
theorem theorem9_qdp_global_convergence {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (τ : Matrix (Fin d) (Fin d) ℂ) (h : ℝ → ℝ) {r : ℝ}
    (hFSC : FastSpectralConvergence U τ h r)
    (hmono : Monotone h)
    {ε : ℝ} (hε : 0 ≤ ε)
    (ρ : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (hstep : ∀ n : ℕ,
      traceDistance (ρ (n + 1)) τ ≤ h (traceDistance (ρ n) τ) + ε * (1 - r))
    (N : ℕ) :
    traceDistance (ρ N) τ ≤ (h^[N]) (traceDistance (ρ 0) τ) + ε := by
  have hη : 0 ≤ ε * (1 - r) := mul_nonneg hε (by linarith [hFSC.hr1])
  have h := accumulated_error_le hFSC.hr0 hFSC.hr1 hmono hFSC.lipschitz
    (fun n => traceDistance (ρ n) τ) hη hstep N
  have hrne : (1:ℝ) - r ≠ 0 := by linarith [hFSC.hr1]
  have heq : ε * (1 - r) * (1 - r)⁻¹ = ε := by
    rw [mul_assoc, mul_inv_cancel₀ hrne, mul_one]
  rwa [heq] at h

/-- Theorem 9 (arXiv:2403.09187, p. 15), circuit-depth accounting: emulating each of the `N`
steps with per-step error `ε (1 - r) / (N + 1)` keeps the accumulated error `ε` and costs a
total depth of `K · N · (N + 1) / (ε (1 - r))`, i.e. `O (N² / ε)` as displayed in Theorem 9. -/
theorem theorem9_epsilon_depth {K r ε : ℝ} (hε : 0 < ε) (hr1 : r < 1) (N : ℕ) :
    qdpDepth K (ε * (1 - r) / ((N : ℝ) + 1)) N
      = K * (N : ℝ) * ((N : ℝ) + 1) / (ε * (1 - r)) := by
  unfold qdpDepth stepDepth
  have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
  have hεr : ε * (1 - r) ≠ 0 := mul_ne_zero hε.ne' (by linarith)
  field_simp
  try ring

/-- Theorem 12 (arXiv:2403.09187, p. 18, Eq. (S55)): *efficient QDP for pure states*.

The error bound of Theorem 9 holds when the initial state `ψ 0` is pure (assumed idempotent
here: `ψ 0 * ψ 0 = ψ 0`, i.e. a rank-one projection), for any `0 < ε < 2/3`.  This
implementation achieves depth `O (N / ε)` (Lemma 19 accounting), unlike the `O (N² / ε)` of
Theorem 9.

The two remaining clauses of Theorem 12 — success probability `1 - p_th` and
`ε^{-N} e^{O (N)} log (p_th⁻¹)` copies of `ψ 0` — are the output guarantees of the
mixedness-reduction subroutine (Lemma 11, claim c005) and of the polynomial exponentiation
(Lemma 7, claim c002); they are not re-derived here. -/
theorem theorem12_pure_state_qdp {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (τ : Matrix (Fin d) (Fin d) ℂ) (h : ℝ → ℝ) {r : ℝ}
    (hFSC : FastSpectralConvergence U τ h r)
    (hmono : Monotone h)
    {ε pth : ℝ} (hε0 : 0 < ε) (hε23 : ε < 2 / 3) (hpth0 : 0 < pth) (hpth1 : pth < 1)
    (ψ : ℕ → Matrix (Fin d) (Fin d) ℂ) (hpure0 : ψ 0 * ψ 0 = ψ 0)
    (hstep : ∀ n : ℕ,
      traceDistance (ψ (n + 1)) τ ≤ h (traceDistance (ψ n) τ) + ε * (1 - r))
    (K : ℝ) (N : ℕ) :
    traceDistance (ψ N) τ ≤ (h^[N]) (traceDistance (ψ 0) τ) + ε ∧
    qdpDepth K (ε * (1 - r)) N = K * (N : ℝ) / (ε * (1 - r)) := by
  refine ⟨theorem9_qdp_global_convergence U τ h hFSC hmono hε0.le ψ hstep N, ?_⟩
  unfold qdpDepth stepDepth
  rw [div_eq_mul_inv]
  ring

/-- Lemma 19 (arXiv:2403.09187, p. 26, Eq. (S121)): *QDP Grover search*, distance clause.

With `2L` partial reflections at each of `N` recursion steps and per-step implementation error
`ε (1 - r)` on top of the exact recursion profile `h (x) = sech ((2L+1) arcsech x)`
(Eq. (S128)), the final state is within `h^N (δ₀) + ε` of the target — the `δ_N` recursion of
Eq. (S121) in accumulated form; `Eq. (S121)` also carries the DME implementation error
`ε / (2 L π)` of Proposition 16.  The final conjunct records the depth `K N / ε = O (L² N / ε)`. -/
theorem lemma19_qdp_grover {d : ℕ}
    (τ : Matrix (Fin d) (Fin d) ℂ) (L : ℕ) {r ε : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hε : 0 ≤ ε)
    (hmono : Monotone (hProfile L))
    (hlip : ∀ x e : ℝ, 0 ≤ e →
      hProfile L (x + e) ≤ hProfile L x + r * e)
    (ρ : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (hstep : ∀ n : ℕ,
      traceDistance (ρ (n + 1)) τ ≤ hProfile L (traceDistance (ρ n) τ) + ε * (1 - r))
    (K : ℝ) (N : ℕ) :
    traceDistance (ρ N) τ ≤ ((hProfile L)^[N]) (traceDistance (ρ 0) τ) + ε ∧
    qdpDepth K ε N = K * (N : ℝ) / ε := by
  refine ⟨?_, ?_⟩
  · have hη : 0 ≤ ε * (1 - r) := mul_nonneg hε (by linarith)
    have := accumulated_error_le hr0 hr1 hmono hlip (fun n => traceDistance (ρ n) τ) hη hstep N
    have hrne : (1:ℝ) - r ≠ 0 := by linarith
    have heq : ε * (1 - r) * (1 - r)⁻¹ = ε := by
      rw [mul_assoc, mul_inv_cancel₀ hrne, mul_one]
    rwa [heq] at this
  · unfold qdpDepth stepDepth
    rw [div_eq_mul_inv]
    ring

/-- Theorem 22 (arXiv:2403.09187, p. 28–29, Eq. (S136)): *efficient QDP Grover search*.

If the QDP implementation `ρ N` is within `η` of the output `ψ N` of the exact nested
fixed-point Grover algorithm, then its distance to the target `τ` exceeds that of the exact
output by at most `η`: `½‖τ - ρ_N‖₁ ≤ ½‖τ - ψ_N‖₁ + η`.  This is Eq. (S136); the closeness of
`ρ N` to `ψ N` is supplied by Lemma 19 / Corollary 18. -/
theorem theorem22_qdp_grover_algorithm {d : ℕ} (τ : Matrix (Fin d) (Fin d) ℂ)
    (ρ ψ : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ) {η : ℝ}
    (hclose : traceDistance (ρ N) (ψ N) ≤ η) :
    traceDistance (ρ N) τ ≤ traceDistance (ψ N) τ + η := by
  calc traceDistance (ρ N) τ ≤ traceDistance (ρ N) (ψ N) + traceDistance (ψ N) τ :=
        traceDistance_triangle _ _ _
    _ ≤ traceDistance (ψ N) τ + η := by
        have hcomm := traceDistance_comm (ρ N) (ψ N)
        linarith

end Qatlib.Papers.DynamicProg24.MainResults
