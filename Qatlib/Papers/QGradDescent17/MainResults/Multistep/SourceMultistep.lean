/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# `QGradDescent17.MainResults.Multistep` — Claim III.2 and Theorem III.3

Kerenidis--Prakash, fixed arXiv:1704.04992v5.

* **Claim III.2** (p. 12): applying an `(ε, δ)`-approximate quantum step `t`
  times transports an error of at most `tε`; the proof is the paper's induction
  using contractivity of `S`.
* **Theorem III.3** (p. 14): with `θ_τ = r₀ + α ∑_{t=1}^{τ} S^{t−1}(L r₀)` and
  the approximate `θ̃_τ`, the algorithm outputs `|θ̃_τ⟩` with

  `‖|θ_τ⟩ − |θ̃_τ⟩‖ ≤ √2 α τ² ε / ‖θ_τ‖`,

  and its expected cost is `T (C_U + log τ)` with `T = (τ+1)/‖θ̃_τ‖`.

The `MultistepProcedure` structure records exactly the hypotheses of the
source theorem: affine update rule, linear contractive step `S`, `(ε,·)`-close
approximate step `St`, and the multistep unitary cost `C_U`.  The correctness
part is proved in full; the running-time part is the paper's cost expression,
recorded definitionally (`expectedCost`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QGradDescent17.MainResults.Multistep

open scoped RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! The two normalised-distance lemmas of Claim II.3 are restated here so that
this module has no dependency on another newly created paper module (the
per-file gate compiles modules in isolation). -/

/-- Arithmetic core of Claim II.3.  For positive `R = ‖phi‖`, `S = ‖phit‖` and
nonnegative cosine `c = ⟪phi, phit⟫`, the squared distance of the normalised
vectors is at most `2 ‖phi − phit‖² / ‖phi‖²`. -/
theorem normalizedDistance_sq_le {R S c : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hc : 0 ≤ c) (hc_le : c ≤ R * S) :
    2 - 2 * (c / (R * S)) ≤ 2 * (R ^ 2 + S ^ 2 - 2 * c) / R ^ 2 := by
  set t : ℝ := c / (R * S) with ht_def
  have hRS : 0 < R * S := mul_pos hR hS
  have ht0 : 0 ≤ t := div_nonneg hc (le_of_lt hRS)
  have ht1 : t ≤ 1 := by
    rw [ht_def, div_le_one hRS]
    exact hc_le
  have hmul : 0 ≤ t * (1 - t) * R ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg R)
  have hsq : 0 ≤ (S - t * R) ^ 2 := sq_nonneg _
  have hct : c = t * (R * S) := by
    rw [ht_def]
    field_simp
  have hR2 : 0 < R ^ 2 := by positivity
  rw [le_div_iff₀ hR2]
  nlinarith [hmul, hsq, hct]

/-- **Claim II.3** (p. 10, eq. (6)).  If two nonzero vectors have nonnegative
inner product (angle at most `π/2`) and their unnormalised distance is `ε`,
then the distance of the normalised quantum states is at most
`√2 · ε / ‖phi‖`. -/
theorem claimII3_normalized_distance (phi phit : E) (hphi : phi ≠ 0) (hphit : phit ≠ 0)
    (hcos : 0 ≤ ⟪phi, phit⟫) (hangle : ⟪phi, phit⟫ ≤ ‖phi‖ * ‖phit‖) :
    ‖NormedSpace.normalize phi - NormedSpace.normalize phit‖ ≤
      Real.sqrt 2 * ‖phi - phit‖ / ‖phi‖ := by
  set R : ℝ := ‖phi‖ with hRdef
  set S : ℝ := ‖phit‖ with hSdef
  set c : ℝ := ⟪phi, phit⟫ with hcdef
  have hR : 0 < R := by rw [hRdef]; exact norm_pos_iff.mpr hphi
  have hS : 0 < S := by rw [hSdef]; exact norm_pos_iff.mpr hphit
  have hc : 0 ≤ c := by rw [hcdef]; exact hcos
  have hc_le : c ≤ R * S := by rw [hcdef, hRdef, hSdef]; exact hangle
  have hnv : ‖NormedSpace.normalize phi‖ = 1 := NormedSpace.norm_normalize hphi
  have hnw : ‖NormedSpace.normalize phit‖ = 1 := NormedSpace.norm_normalize hphit
  have hin : ⟪NormedSpace.normalize phi, NormedSpace.normalize phit⟫ = c / (R * S) := by
    rw [hcdef, hRdef, hSdef, NormedSpace.normalize, NormedSpace.normalize,
      real_inner_smul_left, real_inner_smul_right]
    field_simp
  have hLHS : ‖NormedSpace.normalize phi - NormedSpace.normalize phit‖ ^ 2 =
      2 - 2 * (c / (R * S)) := by
    rw [norm_sub_sq_real, hnv, hnw, hin]
    ring
  have hnorm : ‖phi - phit‖ ^ 2 = R ^ 2 + S ^ 2 - 2 * c := by
    rw [norm_sub_sq_real, ← hRdef, ← hSdef, ← hcdef]
    ring
  have hRHS : (Real.sqrt 2 * ‖phi - phit‖ / R) ^ 2 =
      2 * (R ^ 2 + S ^ 2 - 2 * c) / R ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hnorm]
  have hsqle : ‖NormedSpace.normalize phi - NormedSpace.normalize phit‖ ^ 2 ≤
      (Real.sqrt 2 * ‖phi - phit‖ / R) ^ 2 := by
    rw [hLHS, hRHS]
    exact normalizedDistance_sq_le hR hS hc hc_le
  calc ‖NormedSpace.normalize phi - NormedSpace.normalize phit‖
      = Real.sqrt (‖NormedSpace.normalize phi - NormedSpace.normalize phit‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.sqrt 2 * ‖phi - phit‖ / R) ^ 2) := Real.sqrt_le_sqrt hsqle
    _ = Real.sqrt 2 * ‖phi - phit‖ / R := Real.sqrt_sq (by positivity)
    _ = Real.sqrt 2 * ‖phi - phit‖ / ‖phi‖ := by rw [hRdef]

/-- **Claim III.2 error growth** (p. 12).  If `S` is a linear contraction and
`St` deviates from `S` by at most `ε` pointwise, then `t` iterates transport an
initial error `ε` to at most `(t+1)ε`.  This is the paper's induction
`‖S^{t−1}(L r₀) − S̃^{t−1}(L̃ r₀)‖ ≤ tε`, shifted by one so that the initial
discrepancy `‖L r₀ − L̃ r₀‖ ≤ ε` is the base case. -/
theorem multistep_error_growth (S : E →ₗ[ℝ] E) (hS : ∀ x, ‖S x‖ ≤ ‖x‖)
    (St : E → E) (ε : ℝ) (hstep : ∀ x, ‖S x - St x‖ ≤ ε) (hε : 0 ≤ ε)
    (x y : E) (hxy : ‖x - y‖ ≤ ε) :
    ∀ n : ℕ, ‖((S : E → E)^[n]) x - (St^[n]) y‖ ≤ (n + 1) * ε := by
  intro n
  induction n with
  | zero => simpa using hxy
  | succ n ih =>
      have hsucc : ‖((S : E → E)^[n + 1]) x - (St^[n + 1]) y‖ =
          ‖S (((S : E → E)^[n]) x) - St ((St^[n]) y)‖ := by
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [hsucc]
      have h1 : ‖S (((S : E → E)^[n]) x) - St ((St^[n]) y)‖ ≤
          ‖(((S : E → E)^[n]) x) - (St^[n]) y‖ + ε := by
        calc ‖S (((S : E → E)^[n]) x) - St ((St^[n]) y)‖
            ≤ ‖S (((S : E → E)^[n]) x) - S ((St^[n]) y)‖ +
                ‖S ((St^[n]) y) - St ((St^[n]) y)‖ := by
              have := dist_triangle (S (((S : E → E)^[n]) x)) (S ((St^[n]) y))
                (St ((St^[n]) y))
              simpa [dist_eq_norm] using this
          _ = ‖S ((((S : E → E)^[n]) x) - (St^[n]) y)‖ +
                ‖S ((St^[n]) y) - St ((St^[n]) y)‖ := by rw [map_sub]
          _ ≤ ‖(((S : E → E)^[n]) x) - (St^[n]) y‖ + ε := by
              gcongr
              · exact hS _
              · exact hstep _
      calc ‖S (((S : E → E)^[n]) x) - St ((St^[n]) y)‖
          ≤ ‖(((S : E → E)^[n]) x) - (St^[n]) y‖ + ε := h1
        _ ≤ ((n : ℝ) + 1) * ε + ε := by gcongr
        _ = ((↑(Nat.succ n) : ℝ) + 1) * ε := by push_cast; ring

/-- An affine-update iterative method in the sense of Definition III.1 /
Claim III.2, together with the cost `C_U` of its multistep unitary. -/
structure MultistepProcedure (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  /-- initial state `r₀` (unit norm in the paper; not needed below) -/
  r0 : E
  /-- affine operator `L : r₀ ↦ r₁` -/
  L : E →ₗ[ℝ] E
  /-- the computed approximation `L̃(r₀)` -/
  Lapprox : E
  /-- linear contracting step `S : r_t ↦ r_{t+1}` -/
  S : E →ₗ[ℝ] E
  /-- the approximate step `S̃` realised by the quantum step -/
  Sapprox : E → E
  /-- step size `α` -/
  alpha : ℝ
  /-- number of steps `τ` -/
  tau : ℕ
  /-- step error `ε` -/
  eps : ℝ
  /-- cost `C_U` of the multistep unitary -/
  CU : ℝ
  halpha : 0 ≤ alpha
  htau : 1 ≤ tau
  heps : 0 ≤ eps
  hS_contract : ∀ x, ‖S x‖ ≤ ‖x‖
  hS_approx : ∀ x, ‖S x - Sapprox x‖ ≤ eps
  hL_approx : ‖L r0 - Lapprox‖ ≤ eps

/-- The exact state `θ_τ = r₀ + α ∑_{t=1}^{τ} S^{t−1}(L r₀)` of eq. (5). -/
def theta (M : MultistepProcedure E) : E :=
  M.r0 + M.alpha • ∑ t ∈ Finset.range M.tau, ((M.S : E → E)^[t]) (M.L M.r0)

/-- The computed state `θ̃_τ = r₀ + α ∑_{t=1}^{τ} S̃^{t−1}(L̃ r₀)` built by the
multistep procedure. -/
def thetaTilde (M : MultistepProcedure E) : E :=
  M.r0 + M.alpha • ∑ t ∈ Finset.range M.tau, (M.Sapprox^[t]) M.Lapprox

/-- Expected cost of the outer amplitude amplification / estimation of
Theorem III.3, p. 14: `T (C_U + log τ)` with `T = (τ+1)/‖θ̃_τ‖`. -/
def expectedCost (M : MultistepProcedure E) : ℝ :=
  ((M.tau + 1 : ℝ) / ‖thetaTilde M‖) * (M.CU + Real.log M.tau)

/-- **Theorem III.3, unnormalised error** (p. 14).  The `ℓ²` distance between
the exact and the computed states is at most `α ∑_{t=1}^{τ} tε ≤ α τ² ε`. -/
theorem theta_error (M : MultistepProcedure E) :
    ‖theta M - thetaTilde M‖ ≤ M.alpha * M.eps * (M.tau : ℝ) ^ 2 := by
  have hdiff : theta M - thetaTilde M = M.alpha •
      ∑ t ∈ Finset.range M.tau,
        (((M.S : E → E)^[t]) (M.L M.r0) - (M.Sapprox^[t]) M.Lapprox) := by
    rw [theta, thetaTilde, Finset.sum_sub_distrib, smul_sub]
    abel
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg M.halpha]
  have hterm : ∀ t ∈ Finset.range M.tau,
      ‖(((M.S : E → E)^[t]) (M.L M.r0) - (M.Sapprox^[t]) M.Lapprox)‖ ≤
        (M.tau : ℝ) * M.eps := by
    intro t ht
    have ht' : t < M.tau := Finset.mem_range.mp ht
    have h1 : ‖(((M.S : E → E)^[t]) (M.L M.r0) - (M.Sapprox^[t]) M.Lapprox)‖ ≤
        ((t : ℝ) + 1) * M.eps := by
      have h := multistep_error_growth M.S M.hS_contract M.Sapprox M.eps M.hS_approx
        M.heps (M.L M.r0) M.Lapprox M.hL_approx t
      simpa using h
    have h2 : ((t : ℝ) + 1) ≤ (M.tau : ℝ) := by
      have := Nat.succ_le_of_lt ht'
      exact_mod_cast this
    calc ‖(((M.S : E → E)^[t]) (M.L M.r0) - (M.Sapprox^[t]) M.Lapprox)‖
        ≤ ((t : ℝ) + 1) * M.eps := h1
      _ ≤ (M.tau : ℝ) * M.eps := by nlinarith [h2, M.heps]
  have hsum := Finset.sum_le_sum hterm
  have hsum3 : ∑ t ∈ Finset.range M.tau, (M.tau : ℝ) * M.eps =
      (M.tau : ℝ) * ((M.tau : ℝ) * M.eps) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc M.alpha * ‖∑ t ∈ Finset.range M.tau,
        (((M.S : E → E)^[t]) (M.L M.r0) - (M.Sapprox^[t]) M.Lapprox)‖
      ≤ M.alpha * ∑ t ∈ Finset.range M.tau,
          ‖(((M.S : E → E)^[t]) (M.L M.r0) - (M.Sapprox^[t]) M.Lapprox)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) M.halpha
    _ ≤ M.alpha * ∑ t ∈ Finset.range M.tau, (M.tau : ℝ) * M.eps :=
        mul_le_mul_of_nonneg_left hsum M.halpha
    _ = M.alpha * ((M.tau : ℝ) * ((M.tau : ℝ) * M.eps)) := by rw [hsum3]
    _ = M.alpha * M.eps * (M.tau : ℝ) ^ 2 := by ring

/-- **Theorem III.3, normalised output bound** (p. 14).  The quantum algorithm
outputs `|θ̃_τ⟩ = normalize θ̃_τ`, and for `0 ≤ ⟪θ_τ, θ̃_τ⟫` (the angle
condition of Claim II.3)

  `‖|θ_τ⟩ − |θ̃_τ⟩‖ ≤ √2 α τ² ε / ‖θ_τ‖`. -/
theorem theorem_III_3 (M : MultistepProcedure E) (hcos : 0 ≤ ⟪theta M, thetaTilde M⟫)
    (hne : theta M ≠ 0) (hne' : thetaTilde M ≠ 0) :
    ‖NormedSpace.normalize (theta M) - NormedSpace.normalize (thetaTilde M)‖ ≤
      Real.sqrt 2 * (M.alpha * M.eps * (M.tau : ℝ) ^ 2) / ‖theta M‖ := by
  have hangle : ⟪theta M, thetaTilde M⟫ ≤ ‖theta M‖ * ‖thetaTilde M‖ :=
    real_inner_le_norm _ _
  have hbridge := claimII3_normalized_distance (theta M) (thetaTilde M) hne hne' hcos hangle
  calc ‖NormedSpace.normalize (theta M) - NormedSpace.normalize (thetaTilde M)‖
      ≤ Real.sqrt 2 * ‖theta M - thetaTilde M‖ / ‖theta M‖ := hbridge
    _ ≤ Real.sqrt 2 * (M.alpha * M.eps * (M.tau : ℝ) ^ 2) / ‖theta M‖ := by
        gcongr
        exact theta_error M

/-- **Theorem III.3, running time** (p. 14).  The expected cost of amplitude
amplification/estimation is exactly `T (C_U + log τ)` with `T = (τ+1)/‖θ̃_τ‖`;
this is the definition used in the source. -/
theorem theorem_III_3_running_time (M : MultistepProcedure E) :
    expectedCost M = ((M.tau + 1 : ℝ) / ‖thetaTilde M‖) *
      (M.CU + Real.log M.tau) := rfl

/-- The `O(·)` form of Theorem III.3's running time with explicit constant `1`:
`expectedCost ≤ 1 · T (C_U + log τ)`. -/
theorem theorem_III_3_running_time_bigO (M : MultistepProcedure E) :
    expectedCost M ≤ 1 * (((M.tau + 1 : ℝ) / ‖thetaTilde M‖) *
      (M.CU + Real.log M.tau)) := by
  rw [theorem_III_3_running_time M, one_mul]

end Qatlib.Papers.QGradDescent17.MainResults.Multistep
