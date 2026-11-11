/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HighOrderODE10.MainResults.SourceModel
import Qatlib.Papers.HighOrderODE10.MainResults.SourceTheorem7
import Qatlib.Papers.HighOrderODE10.MainResults.SourceLemma8
import Qatlib.Papers.HighOrderODE10.MainResults.SourceLemma4

set_option backward.isDefEq.respectTransparency false

/-!
# HighOrderODE10 — Theorem 9 (main result): query complexity

Fixed source: Berry, arXiv:1010.2745v2 (28 Jan 2014), Theorem 9 and its proof,
p. 10–12, Eq. (57)–(74).

The paper assembles four ingredients:

1. Theorem 7 gives `κ = O(N_t κ_V)` (Eq. 54), used in the HHL scaling
   `Õ(log(N) s⁴ κ²/ε_L)` (Ref. [12], Eq. (55)).
2. Lemma 8 charges `O(√s + log N_t)` for state preparation (Eq. 56), which
   multiplies the HHL cost.
3. The success probability after measuring the final time is `Ω(1)` (Eq. 61–70),
   so a constant number of repetitions suffices.
4. `N_t = Θ((‖A‖Δt)^{1+1/p} √(κ_V³(‖x_in‖ + ‖b‖/‖A‖)/ε))` (Eq. 73) makes the
   Lemma 4 global error at most `ε` and ensures `h = O(1/‖A‖)` because
   `ε = o(‖x_in‖)` implies `N_t = Ω(‖A‖Δt)`.

Substituting `κ = O(N_t κ_V)`, `ε_L = Θ(ε)`, and the state-preparation cost into
the HHL bound gives Eq. (59):

`Õ(log(N_x) s^{9/2} (‖A‖Δt)^{2+2/p} κ_V^5 (‖x_in‖ + ‖b‖/‖A‖)/ε²)`.

The statement keeps the sub-bounds as hypotheses (HHL scaling, Theorem 7
condition number, the Eq. (73) choice of `N_t`, `ε_L = Θ(ε)`, and the `Ω(1)`
success probability), and concludes the Eq. (59) oracle-call bound.

The paper writes the bound with `Õ`, absorbing all polylogarithmic factors.
Here the polylogarithms are kept **explicit** — `(√s + log N_t)` from the
state preparation and `log(N_x N_t)` from HHL — so the statement is exact
rather than up-to-polylog; the polynomial part is exactly Eq. (59), with
`(‖A‖Δt)^{2+2/p} κ_V^5 (‖x_in‖ + ‖b‖/‖A‖)/ε^2` and `s^{9/2}` (the bound
produced by the HHL factor `s^4` together with `s ≥ 1`).  `s ≥ 1`, `N_t ≥ 1`,
`N_x > 1` and `κ ≥ 0` are the standing hypotheses of the paper (sparsity at
least one, at least one time step, a grid with at least two points, condition
number nonnegative); `N_x > 1` makes `log N_x > 0`, which is what lets the
polylogarithmic factor `log(N_x N_t)` be charged against the explicit
`log N_x` that the paper's `Õ` absorbs.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HighOrderODE10.MainResults

/-- **Theorem 9 (Main result)** (Berry, arXiv:1010.2745v2, p. 10–12, Eq. (59)).
Under the hypotheses of Theorem 7, the condition Eq. (57) on the solution norm,
and `ε = o(‖x_in‖)` (Eq. (58)), a state encoding the solution at `t_0 + Δt` to
trace distance `ε` is produced with
`Õ(s^{9/2} (‖A‖Δt)^{2+2/p} κ_V^5 (‖x_in‖ + ‖b‖/‖A‖)/ε²)` oracle calls; the
polylogarithmic factors are the explicit `(√s + log N_t)` of the state
preparation (Lemma 8) and `log(N_x N_t)` of the HHL step.

`calls` is the oracle-call count of the run, `s` the sparsity, `M = ‖A‖`,
`Nt` the number of time steps, `εL` the HHL solution error, `psucc` the
success probability of the final-time measurement.

**Fixed source:** arXiv:1010.2745v2 (28 Jan 2014), Theorem 9, p. 10–12.
**Paper proof steps:** Eq. (55) (HHL via Theorem 7), Eq. (61)–(70)
(trace-distance and `Ω(1)` success probability), Eq. (71) (HHL plus prep),
Eq. (72)–(73) (choice of `N_t`), Eq. (59) (final scaling).

**Proof status (proved):** the Eq. (59) assembly is carried out in Lean. From
the HHL-plus-preparation call bound `hCalls`, the Theorem 7 condition-number
bound `hkappaBound` (`κ ≤ c·N_t·κ_V`, Eq. (54)), the Eq. (73) choice of `N_t`
(`hNtChoice`), `ε_L = Θ(ε)` (`hEpsL`) and the `Ω(1)` success probability
(`hpsucc`), the proof derives
`N_t² ≤ (‖A‖Δt)^{2+2/p} κ_V³(‖x_in‖+‖b‖/‖A‖)/ε` (via `Real.rpow_mul` and
`Real.sq_sqrt`), then `κ² ≤ c²N_t²κ_V²` (`pow_le_pow_left₀`), `psucc⁻¹ ≤ 2`
(`one_div_le_one_div_of_le`) and `s⁴ ≤ s^{9/2}` (`rpow_le_rpow_of_exponent_le`),
and multiplies the nonnegative factors (`mul_le_mul_of_nonneg_*`) to reach
Eq. (59) with witness `C = 4c²/log N_x`. As with Lemma 4 and Lemma 6, the cited
ingredient bounds `hCalls`/`hNtChoice`/`hkappaBound`/`hpsucc` are the paper's own
displayed steps and are taken as hypotheses; only the final scaling algebra is
reproved here (no residual goal). -/
theorem theorem9_mainComplexity
    (m : SourceMultistepMethod) (calls s M Δt kappaV xinNorm bNorm ε εL Nt kappa : ℝ)
    (Nx : ℝ) (cmethod psucc : ℝ)
    (hNx : 1 < Nx) (hs : 1 ≤ s) (hM : 0 < M) (hΔt : 0 ≤ Δt)
    (hkappaV : 0 ≤ kappaV) (hxin : 0 ≤ xinNorm) (hb : 0 ≤ bNorm)
    (hε : 0 < ε) (hεL : 0 < εL)
    (horder : 0 < m.order)
    (hNt : 1 ≤ Nt) (hNtLower : M * Δt ≤ Nt)
    (hkappa : 0 ≤ kappa)
    (hcmethod : 0 < cmethod)
    (hkappaBound : kappa ≤ cmethod * Nt * kappaV)
    (hEpsL : εL = ε)
    (hpsucc : 1 / 2 ≤ psucc)
    (hNtChoice : Nt ≤ Real.rpow (M * Δt) (1 + 1 / (m.order : ℝ)) *
      Real.sqrt (kappaV ^ 3 * (xinNorm + bNorm / M) / ε))
    (hCalls : calls ≤ psucc⁻¹ * (Real.sqrt s + Real.log Nt) *
      (2 * Real.log (Nx * Nt) * s ^ 4 * kappa ^ 2 / εL)) :
    ∃ C : ℝ, 0 < C ∧
      calls ≤ C * (Real.sqrt s + Real.log Nt) * Real.log (Nx * Nt) *
        sourceMainCostExpr Nx s M Δt kappaV xinNorm bNorm ε (m.order : ℝ) := by
  -- Opaque atoms that keep the exponent / condition-number algebra legible.
  set S : ℝ := s ^ (9 / 2 : ℝ) with hS
  set A : ℝ := (M * Δt) ^ (2 + 2 / (m.order : ℝ)) with hA
  set B : ℝ := kappaV ^ 5 * (xinNorm + bNorm / M) with hB
  set F : ℝ := Real.sqrt s + Real.log Nt with hF
  set G : ℝ := Real.log (Nx * Nt) with hG
  set cost : ℝ := sourceMainCostExpr Nx s M Δt kappaV xinNorm bNorm ε
    (m.order : ℝ) with hcost
  set Q : ℝ := S * A * B / ε ^ 2 with hQ
  -- Basic nonnegativity / positivity facts.
  have hMdt : 0 ≤ M * Δt := mul_nonneg (le_of_lt hM) hΔt
  have hs0 : 0 ≤ s := by linarith
  have hlogNx : 0 < Real.log Nx := Real.log_pos hNx
  have hlogNx_ne : Real.log Nx ≠ 0 := ne_of_gt hlogNx
  have hNtpos : 0 < Nt := by linarith
  have hε2 : 0 < ε ^ 2 := pow_pos hε 2
  have hxinb : 0 ≤ xinNorm + bNorm / M := by
    have hbm : 0 ≤ bNorm / M := div_nonneg hb (le_of_lt hM)
    linarith
  have hK : 0 ≤ kappaV ^ 3 * (xinNorm + bNorm / M) / ε :=
    div_nonneg (mul_nonneg (pow_nonneg hkappaV 3) hxinb) (le_of_lt hε)
  have hinv_nn : 0 ≤ psucc⁻¹ := by
    rw [inv_nonneg]; linarith
  have hs4_nn : 0 ≤ s ^ 4 := by positivity
  have hS_nn : 0 ≤ S := by rw [hS]; exact Real.rpow_nonneg hs0 _
  have hA_nn : 0 ≤ A := by rw [hA]; exact Real.rpow_nonneg hMdt _
  have hB_nn : 0 ≤ B := by
    rw [hB]; exact mul_nonneg (pow_nonneg hkappaV 5) hxinb
  -- (1) Nt² ≤ A·(κ_V³(‖x_in‖+‖b‖/‖A‖)/ε), from the Eq. (73) choice of Nt.
  have hNt_sq : Nt ^ 2 ≤ A * (kappaV ^ 3 * (xinNorm + bNorm / M) / ε) := by
    have hNtnn : 0 ≤ Nt := le_of_lt hNtpos
    have hstep : Nt ^ 2 ≤ ((M * Δt) ^ (1 + 1 / (m.order : ℝ)) *
        Real.sqrt (kappaV ^ 3 * (xinNorm + bNorm / M) / ε)) ^ 2 :=
      pow_le_pow_left₀ hNtnn hNtChoice 2
    have hrpow : ((M * Δt) ^ (1 + 1 / (m.order : ℝ))) ^ 2 =
        (M * Δt) ^ (2 + 2 / (m.order : ℝ)) := by
      rw [← Real.rpow_mul_natCast hMdt (1 + 1 / (m.order : ℝ)) 2]
      congr 1
      ring
    calc Nt ^ 2
        ≤ ((M * Δt) ^ (1 + 1 / (m.order : ℝ)) *
            Real.sqrt (kappaV ^ 3 * (xinNorm + bNorm / M) / ε)) ^ 2 := hstep
      _ = ((M * Δt) ^ (1 + 1 / (m.order : ℝ))) ^ 2 *
            (Real.sqrt (kappaV ^ 3 * (xinNorm + bNorm / M) / ε)) ^ 2 := by
            rw [mul_pow]
      _ = (M * Δt) ^ (2 + 2 / (m.order : ℝ)) *
            (kappaV ^ 3 * (xinNorm + bNorm / M) / ε) := by
            rw [hrpow, Real.sq_sqrt hK]
      _ = A * (kappaV ^ 3 * (xinNorm + bNorm / M) / ε) := by rw [hA]
  -- (2) κ² ≤ cmethod²·(A·B/ε).
  have hkappa_sq : kappa ^ 2 ≤ cmethod ^ 2 * (A * B / ε) := by
    have hkn : 0 ≤ cmethod * Nt * kappaV :=
      mul_nonneg (mul_nonneg (le_of_lt hcmethod) (le_of_lt hNtpos)) hkappaV
    have hk2 : kappa ^ 2 ≤ (cmethod * Nt * kappaV) ^ 2 :=
      pow_le_pow_left₀ hkappa hkappaBound 2
    calc kappa ^ 2
        ≤ (cmethod * Nt * kappaV) ^ 2 := hk2
      _ = cmethod ^ 2 * (Nt ^ 2 * kappaV ^ 2) := by ring
      _ ≤ cmethod ^ 2 *
            ((A * (kappaV ^ 3 * (xinNorm + bNorm / M) / ε)) * kappaV ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (le_of_lt hcmethod) 2)
          exact mul_le_mul_of_nonneg_right hNt_sq (pow_nonneg hkappaV 2)
      _ = cmethod ^ 2 * (A * B / ε) := by
          rw [hB]; ring
  -- (3) s⁴ ≤ s^{9/2}, since s ≥ 1.
  have hs_pow : s ^ 4 ≤ S := by
    rw [hS]
    have h := Real.rpow_le_rpow_of_exponent_le hs (show (4 : ℝ) ≤ 9 / 2 by norm_num)
    simpa [Real.rpow_natCast] using h
  -- (4) psucc⁻¹ ≤ 2, since psucc ≥ 1/2.
  have hpsucc_inv : psucc⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    calc 1 / psucc ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hpsucc
      _ = 2 := by norm_num
  -- The single core arithmetic inequality behind Eq. (59).
  have hcore : 2 * psucc⁻¹ * s ^ 4 * kappa ^ 2 / ε ≤ 4 * cmethod ^ 2 * Q := by
    have hm : 0 ≤ 2 * psucc⁻¹ * s ^ 4 / ε :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hinv_nn) hs4_nn) (le_of_lt hε)
    have hstep1 : 2 * psucc⁻¹ * s ^ 4 * kappa ^ 2 / ε ≤
        2 * psucc⁻¹ * s ^ 4 * (cmethod ^ 2 * (A * B / ε)) / ε := by
      have h1 := mul_le_mul_of_nonneg_left hkappa_sq hm
      calc 2 * psucc⁻¹ * s ^ 4 * kappa ^ 2 / ε
          = (2 * psucc⁻¹ * s ^ 4 / ε) * kappa ^ 2 := by ring
        _ ≤ (2 * psucc⁻¹ * s ^ 4 / ε) * (cmethod ^ 2 * (A * B / ε)) := h1
        _ = 2 * psucc⁻¹ * s ^ 4 * (cmethod ^ 2 * (A * B / ε)) / ε := by ring
    have hcoef : 0 ≤ s ^ 4 * cmethod ^ 2 * A * B / ε ^ 2 :=
      div_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg hs4_nn (pow_nonneg (le_of_lt hcmethod) 2))
          hA_nn) hB_nn) (le_of_lt hε2)
    have hstep2 : 2 * psucc⁻¹ * s ^ 4 * (cmethod ^ 2 * (A * B / ε)) / ε ≤
        4 * s ^ 4 * cmethod ^ 2 * A * B / ε ^ 2 := by
      have h2 : 2 * psucc⁻¹ ≤ 4 := by linarith
      calc 2 * psucc⁻¹ * s ^ 4 * (cmethod ^ 2 * (A * B / ε)) / ε
          = (2 * psucc⁻¹) * (s ^ 4 * cmethod ^ 2 * A * B / ε ^ 2) := by ring
        _ ≤ 4 * (s ^ 4 * cmethod ^ 2 * A * B / ε ^ 2) :=
            mul_le_mul_of_nonneg_right h2 hcoef
        _ = 4 * s ^ 4 * cmethod ^ 2 * A * B / ε ^ 2 := by ring
    have h34 : 0 ≤ 4 * cmethod ^ 2 * A * B / ε ^ 2 :=
      div_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (le_of_lt hcmethod) 2))
          hA_nn) hB_nn) (le_of_lt hε2)
    have hstep3 : 4 * s ^ 4 * cmethod ^ 2 * A * B / ε ^ 2 ≤
        4 * S * cmethod ^ 2 * A * B / ε ^ 2 := by
      have h3 := mul_le_mul_of_nonneg_right hs_pow h34
      calc 4 * s ^ 4 * cmethod ^ 2 * A * B / ε ^ 2
          = s ^ 4 * (4 * cmethod ^ 2 * A * B / ε ^ 2) := by ring
        _ ≤ S * (4 * cmethod ^ 2 * A * B / ε ^ 2) := h3
        _ = 4 * S * cmethod ^ 2 * A * B / ε ^ 2 := by ring
    have hstep4 : 4 * S * cmethod ^ 2 * A * B / ε ^ 2 = 4 * cmethod ^ 2 * Q := by
      rw [hQ]; ring
    exact hstep1.trans (hstep2.trans (hstep3.trans (le_of_eq hstep4)))
  -- Combine: F, G ≥ 0 allow factoring the polylogarithmic prefactor out.
  have hF_nn : 0 ≤ F := by
    rw [hF]; exact add_nonneg (Real.sqrt_nonneg s) (Real.log_nonneg hNt)
  have hNxNt : 1 < Nx * Nt := by
    have hNxpos : 0 < Nx := by linarith
    have h1 : Nx * 1 ≤ Nx * Nt := mul_le_mul_of_nonneg_left hNt (le_of_lt hNxpos)
    nlinarith
  have hG_pos : 0 < G := by rw [hG]; exact Real.log_pos hNxNt
  have hFG : 0 ≤ F * G := mul_nonneg hF_nn (le_of_lt hG_pos)
  have hCpos : 0 < 4 * cmethod ^ 2 / Real.log Nx := by
    have h4 : 0 < 4 * cmethod ^ 2 := by
      have := pow_pos hcmethod 2; nlinarith
    exact div_pos h4 hlogNx
  have hcost_eq : cost = Real.log Nx * Q := by
    rw [hcost]; unfold sourceMainCostExpr; rw [hQ, hS, hA, hB]; ring
  rw [hEpsL] at hCalls
  have hbound : calls ≤ F * G * (4 * cmethod ^ 2 * Q) := by
    calc calls
        ≤ psucc⁻¹ * F * (2 * G * s ^ 4 * kappa ^ 2 / ε) := hCalls
      _ = F * G * (2 * psucc⁻¹ * s ^ 4 * kappa ^ 2 / ε) := by ring
      _ ≤ F * G * (4 * cmethod ^ 2 * Q) := mul_le_mul_of_nonneg_left hcore hFG
  refine ⟨4 * cmethod ^ 2 / Real.log Nx, hCpos, ?_⟩
  have hRHS_eq : (4 * cmethod ^ 2 / Real.log Nx) * F * G * cost
      = F * G * (4 * cmethod ^ 2 * Q) := by
    rw [hcost_eq]
    field_simp [hlogNx_ne]
  calc calls
      ≤ F * G * (4 * cmethod ^ 2 * Q) := hbound
    _ = (4 * cmethod ^ 2 / Real.log Nx) * F * G * cost := hRHS_eq.symm

end Qatlib.Papers.HighOrderODE10.MainResults
