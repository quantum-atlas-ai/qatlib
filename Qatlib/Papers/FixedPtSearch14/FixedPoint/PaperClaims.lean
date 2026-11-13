/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalFixedPoint
import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalWordConstruction

set_option backward.isDefEq.respectTransparency false

open Qatlib.Papers.FixedPtSearch14.FixedPoint
open Polynomial

/-!
# FixedPtSearch14 — paper-layer statements for every active claim

Source: Theodore J. Yoder, Guang Hao Low, Isaac L. Chuang,
*Fixed-point quantum search with an optimal number of queries*,
arXiv:1409.3305v2, Physical Review Letters 113, 210501 (2014).

This module is the paper-layer entry point for the six active claims of
`FixedPtSearch14`.  Each theorem restates one claim of the paper in the
notation already fixed by the Dev/Frozen construction layer:

* Eq. (1)  — Chebyshev success probability `P_L`;
* Eq. (3)  — query complexity `L = O(log(2/δ)/√λ)`;
* Eq. (11) — the analytic phase schedule `α_j = −β_{l−j+1} = 2cot⁻¹(…)`;
* Eq. (15) — the three-term amplitude recurrence and its Chebyshev solution;
* Eq. (18) — nesting/polynomial composition `P_{L2}(P_{L1}(λ,δ₁),δ₂) = P_{L₁L₂}(λ,δ)`;
* Abstract + p. 4 — Dolph–Chebyshev maximality of the λ-range.

The underlying constructions and long proofs live in the sibling modules of
`QuantumAlgorithmDev.Papers.FixedPtSearch14.FixedPoint` and in the package
under `Qatlib.Papers.FixedPtSearch14.FixedPoint`.
Each bridge theorem below names the exact reused fully-qualified result.
-/

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint.PaperClaims

/-! ## Claim c001 — Eq. (1): the Chebyshev success probability -/

/-- **Claim c001 (Eq. (1), pp. 1–2).**
For every odd `L = 2l+1 ≥ 1` and every `δ ∈ (0,1)`, the actual YLC word `S_L`
has success probability
`P_L = 1 − δ² · T_L(√(1−λ)/γ)²`, with `γ = T_{1/L}(1/δ)^{-1}`; moreover the
word length is chosen from the public lower bound `λ₀` only, and the same word
then satisfies the fixed-point guarantee `P_L ≥ 1 − δ²` for every unknown
`λ ≥ λ₀`.

Reused results:
* `publicWord_success_response` (this paper block) — response of the actual
  two-level word for every `l`;
* `responseProb_eq` (Frozen) — definitional closed form of the response;
* `publicWord_uniform_guarantee` (this paper block) — uniform word choice. -/
theorem claim_c001_chebyshev_success :
    (∀ (l : ℕ) (delta lam : ℝ), 0 < delta → delta < 1 → 0 ≤ lam → lam ≤ 1 →
      publicSuccessProb l delta lam =
        1 - delta ^ 2 *
          (cheb (2 * l + 1) (Real.sqrt (1 - lam) / ylcGamma (2 * l + 1) delta)) ^ 2) ∧
    (∀ (lam0 delta : ℝ), 0 < lam0 → lam0 < 1 → 0 < delta → delta < 1 →
      ∀ lam : ℝ, lam0 ≤ lam → lam ≤ 1 →
        1 - delta ^ 2 ≤
          publicSuccessProb (publicIterateCount lam0 delta) delta lam) := by
  constructor
  · intro l delta lam hd hdu hl hu
    rw [publicWord_success_response l delta lam hd hdu hl hu, responseProb_eq]
    ring
  · intro lam0 delta h0 h0u hd hdu lam hl hu
    exact publicWord_uniform_guarantee lam0 delta h0 h0u hd hdu lam hl hu

/-! ## Claim c002 — Eq. (3): query complexity `O(log(2/δ)/√λ)` -/

/-- **Claim c002 (Eq. (3) and p. 2).**
There is an absolute constant `C > 0`, chosen before the unknown good mass,
such that the number of generalized Grover iterates `l` of the unified public
word is at most `C·log(2/δ)/√λ₀` for every `λ ≥ λ₀` simultaneously.  Since
`L = 2l+1` and each iterate makes `2` oracle queries (`wordQueryCount l = 2l`),
this yields the paper's query complexity `L = O(log(2/δ)/√λ)`.

Reused result: `clause2_uniform_constant_before_good_mass` from
`Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalWordConstruction`,
whose proof is unconditional (`accessCountOBound`); the length/query-count
identification is `MarkedSearch.publicLength_as_iterates` in this block. -/
theorem claim_c002_query_complexity :
    ∃ C : ℝ, 0 < C ∧
      ∀ (lam0 delta : ℝ), 0 < lam0 → lam0 < 1 → 0 < delta → delta < 1 →
        ∀ lam : ℝ, lam0 ≤ lam → lam ≤ 1 →
          ((publicLength lam0 delta : ℝ) = 2 * (publicIterateCount lam0 delta : ℝ) + 1) ∧
          (wordQueryCount (publicIterateCount lam0 delta) = 2 * publicIterateCount lam0 delta) ∧
          ((publicIterateCount lam0 delta : ℕ) : ℝ) ≤
            C * Real.log (2 / delta) / Real.sqrt lam0 := by
  obtain ⟨C, hC, hbound⟩ :=
    clause2_uniform_constant_before_good_mass
  refine ⟨C, hC, ?_⟩
  intro lam0 delta hl0 hl0' hd hdu lam hlam hlam1
  refine ⟨?_, rfl, hbound lam0 delta hl0 hl0' hd hdu lam hlam hlam1⟩
  have hlen := MarkedSearch.publicLength_as_iterates lam0 delta
  have hcast : ((2 * publicIterateCount lam0 delta + 1 : ℕ) : ℝ) =
      (publicLength lam0 delta : ℝ) := by exact_mod_cast hlen
  push_cast at hcast
  linarith

/-! ## Claim c003 — Eq. (11): the analytic phase schedule -/

/-- **Claim c003 (Eq. (11), p. 3).**
For `L = 2l+1`, `γ = T_{1/L}(1/δ)^{-1}` and every `j = 1,…,l`, the analytic
phase is
`α_j = 2cot⁻¹(tan(2πj/L)·√(1−γ²))`, written here with the principal branch
`cot⁻¹(u) = π/2 − arctan u`, and the second reflection phase of the `j`-th
generalized Grover iterate is `β_j = −α_{l−j+1}` (phase matching).

The two parts are definitional in the construction layer (`wordPhase` is
`ylcAlpha`, and `publicPhases` stores `(α_{i+1}, −α_{l−i})`), so this theorem
records Eq. (11) exactly as used by `publicWord`. -/
theorem claim_c003_analytic_phase_schedule (l : ℕ) (delta : ℝ) :
    (∀ j : ℕ, 1 ≤ j → j ≤ l →
      wordPhase (2 * l + 1) j (ylcGamma (2 * l + 1) delta) =
        2 * (Real.pi / 2 -
          Real.arctan (Real.tan (2 * Real.pi * j / (2 * l + 1)) *
            Real.sqrt (1 - ylcGamma (2 * l + 1) delta ^ 2)))) ∧
    (publicPhases l delta =
      ((List.range l).map fun i =>
        (wordPhase (2 * l + 1) (i + 1) (ylcGamma (2 * l + 1) delta),
         -(wordPhase (2 * l + 1) (l - i) (ylcGamma (2 * l + 1) delta)))).reverse) := by
  constructor
  · intro j _ _
    simp only [wordPhase, ylcAlpha]
    push_cast
    rfl
  · rfl

/-! ## Claim c004 — Eq. (15): amplitude recurrence and Chebyshev solution -/

/-- **Claim c004 (Eq. (15), p. 3).**
With `x = √(1−λ)`, `μ = √(1−γ²)` and `w_h = e^{−i(ζ_h−ζ_{h−1})}`, the
amplitudes `a_h` obey `a_0 = 1`, `a_1 = x` and
`a_h = x(1+w_h)a_{h−1} − w_h a_{h−2}`, and for odd `L = 2l+1` the endpoint is
the normalized Chebyshev value
`a_L = T_L(x/γ)/T_L(1/γ) = δ·T_L(x/γ)`.

Reused result: `ylcRecA_miracle` (this paper block), which in turn is proved
from `ylcRecA_chebyshev_of_width`. -/
theorem claim_c004_amplitude_recurrence (l : ℕ) (delta x : ℝ)
    (hd : 0 < delta) (hdu : delta < 1) :
    ylcRecA (2 * l + 1) (Real.sqrt (1 - ylcGamma (2 * l + 1) delta ^ 2)) x 0 = 1 ∧
    ylcRecA (2 * l + 1) (Real.sqrt (1 - ylcGamma (2 * l + 1) delta ^ 2)) x 1 = (x : ℂ) ∧
    (∀ h : ℕ,
      ylcRecA (2 * l + 1) (Real.sqrt (1 - ylcGamma (2 * l + 1) delta ^ 2)) x (h + 2) =
        (x : ℂ) *
            (1 + ylcRecW (2 * l + 1)
              (Real.sqrt (1 - ylcGamma (2 * l + 1) delta ^ 2)) (h + 2)) *
            ylcRecA (2 * l + 1) (Real.sqrt (1 - ylcGamma (2 * l + 1) delta ^ 2)) x (h + 1)
          - ylcRecW (2 * l + 1)
              (Real.sqrt (1 - ylcGamma (2 * l + 1) delta ^ 2)) (h + 2) *
            ylcRecA (2 * l + 1) (Real.sqrt (1 - ylcGamma (2 * l + 1) delta ^ 2)) x h) ∧
    ylcRecA (2 * l + 1) (Real.sqrt (1 - ylcGamma (2 * l + 1) delta ^ 2)) x (2 * l + 1) =
      ((delta * cheb (2 * l + 1) (x / ylcGamma (2 * l + 1) delta) : ℝ) : ℂ) := by
  refine ⟨rfl, rfl, ?_, ylcRecA_miracle l delta x hd hdu⟩
  intro h
  rfl

/-! ## Claim c005 — Eq. (18): nesting composes the Chebyshev response -/

/-- **Claim c005 (Eq. (18), p. 4).**
Choose the inner error bound `δ₁ = T_{1/L₂}(1/δ)^{-1} = γ_{L₂}(δ)` and the
outer error bound `δ₂ = δ`; then running an `L₁`-word at `δ₁` inside an
`L₂`-word at `δ` gives the response of a single word of length `L₁L₂`:
`P_{L₂}(P_{L₁}(λ,δ₁),δ₂) = P_{L₁L₂}(λ,δ)`.

Reused result: `nestedResponseIdentity` from
`Qatlib.Papers.FixedPtSearch14.FixedPoint.InfrastructureOptimalFixedPoint`,
proved from the Chebyshev semigroup law. -/
theorem claim_c005_nesting_composition (L1 L2 : ℕ) (delta lam : ℝ)
    (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (hd : 0 < delta) (hdu : delta < 1)
    (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    responseProb L2 delta (responseProb L1 (ylcGamma L2 delta) lam) =
      responseProb (L1 * L2) delta lam :=
  nestedResponseIdentity L1 L2 delta lam hL1 hL2 hd hdu hl hu

/-! ## Claim c006 — Abstract and p. 4: maximal λ-range (Dolph–Chebyshev) -/

/-- **Claim c006 (Abstract, p. 1 and p. 4).**
For a fixed degree budget `L`, the Dolph–Chebyshev response is optimal: any real
polynomial `q` of degree at most `L` with `q(1) = 1` that is bounded by `δ` on
`[-a, a]` must satisfy `a ≤ γ_L(δ) = T_{1/L}(1/δ)^{-1}`.  In terms of the
failure amplitude `a = √(1−λ)`, this says that the set of `λ` on which the
success probability can be kept at least `1−δ²` is widest for the
Chebyshev/Dolph response — the paper's "broadest possible range of λ".

Reused result: `chebyshev_suppression_optimal` from
`Qatlib.Papers.FixedPtSearch14.FixedPoint.InfrastructureOptimalFixedPoint`,
proved from Mathlib's Chebyshev extremal property. -/
theorem claim_c006_optimal_lambda_range {L : ℕ} {delta : ℝ} {q : ℝ[X]} {a : ℝ}
    (hL : 1 ≤ L) (hd : 0 < delta) (hdu : delta < 1)
    (hdeg : q.degree ≤ (L : ℕ)) (hq1 : q.eval 1 = 1) (ha : 0 < a)
    (hbound : ∀ y ∈ Set.Icc (-a) a, |q.eval y| ≤ delta) :
    a ≤ ylcGamma L delta :=
  chebyshev_suppression_optimal hL hd hdu hdeg hq1 ha hbound

end Qatlib.Papers.FixedPtSearch14.FixedPoint.PaperClaims
