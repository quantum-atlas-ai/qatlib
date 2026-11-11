/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroundStPrep17.MainResults.SourceModel
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

set_option backward.isDefEq.respectTransparency false

/-!
# GroundStPrep17.MainResults.CostLedger

Cost ledgers of the constructions of arXiv:1712.03193v2 (Ge-Tura-Cirac), and the
`Õ`/`O` bounds they satisfy.  Each definition is transcribed from an equation of
the paper:

* `lcuRuns` / `unknownEnergyGateCost` - eqs. (3), (C21): the unknown-energy
  ground state preparation repeats the (known-energy) run `√L/χ` times with
  `L = Θ(Δ⁻¹ log(1/(χε)))` and per-run cost `Λ/Δ + Φ`;
* `phaseEstimationPriorCost` / `minLabelSearchCost` / `combinedGateCost` -
  eqs. (4), (6), (C38): a prior phase-estimation run at precision `Δ^κ`
  followed by minimum-label based energy search on an interval of size `Δ^κ`;
* `peRunCost` - eq. (A1): `1/χ` phase-estimation runs of cost `2^k Λ + Φ` with
  `2^k = O(1/(χξ))`;
* `knownEnergyPEGateCost` - eq. (B1): fixed point search with `1/|φ₀|` runs of
  phase estimation at precision `|φ₀|εΔ`;
* `filteringGateCost` - eqs. (C5)/(C19): `η² k` filter applications per run and
  `1/|φ₀|` runs, `η = log(1/(χε))/log log(1/(χε))`;
* `minLabelCallCost` / `minLabelGateCost` - eqs. (31)/(32): `n` binary-search
  stages with `log(n/δ)` repetitions of `O(1/ζ)` fixed point searches.

The companion lemmas below establish the displayed `Õ`/`O` bounds.  The
paper's `Δ^{3/2}` is written as `Δ * √Δ` (equal for `Δ > 0`; see
`mul_sqrt_eq_rpow`), and the `ξ^{3/2}` of (5)/(C36) likewise.  Exponents
`Δ^κ` with real `κ ∈ [0,1]` are the genuine real powers.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.GroundStPrep17.MainResults

/-! ## Elementary `O`-calculus helpers -/

/-- `O` bound with an additive constant, for a positive quantity. -/
lemma isBigO_add_one_of_half_le {f : ℝ} (hf : 1 / 2 ≤ f) : IsBigO (f + 1) f :=
  ⟨3, by norm_num, by linarith⟩

/-- `Õ` bound from a plain inequality. -/
lemma isTildeO_of_le {cost bound scale : ℝ} (h : cost ≤ bound) :
    IsTildeO cost bound scale := by
  refine ⟨1, one_pos, 0, ?_⟩
  simpa using h

/-- Monotonicity of `IsTildeO` in the bound, up to a constant factor of the
displayed bound. -/
lemma IsTildeO_mono_bound {cost bound bound' scale K : ℝ} (hs : 0 ≤ scale)
    (h : IsTildeO cost bound scale) (hle : bound ≤ K * bound') (hK : 0 < K) :
    IsTildeO cost bound' scale := by
  obtain ⟨C, hC, a, ha⟩ := h
  refine ⟨K * C, mul_pos hK hC, a, ?_⟩
  have h0 : 0 ≤ (1 + scale) ^ a := pow_nonneg (by linarith) a
  have hfac : 0 ≤ C * (1 + scale) ^ a * (K * bound' - bound) :=
    mul_nonneg (mul_nonneg hC.le h0) (sub_nonneg.mpr hle)
  nlinarith [ha, hfac]

/-- The natural logarithm of two is at least one half. -/
lemma log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  linarith

/-- Adding two to a natural number gives a logarithm at least log two. -/
lemma log_nat_add_two_ge_log_two (N : ℕ) : Real.log 2 ≤ Real.log ((N : ℝ) + 2) := by
  apply Real.log_le_log (by norm_num)
  have := Nat.cast_nonneg (α := ℝ) N
  linarith

/-- `x·√x = x^{3/2}` for `x > 0` (the paper writes `Δ^{3/2}`). -/
lemma mul_sqrt_eq_rpow {x : ℝ} (hx : 0 < x) : x * Real.sqrt x = x ^ (3 / 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

/-! ## The unknown-energy construction: eqs. (3), (C21) -/

/-- `√L` for `L = Θ(Δ⁻¹ log(1/(χε)))`, the number of LCU terms (eqs. (17), (22)). -/
def lcuRuns (Δ χ ε : ℝ) : ℝ := Real.sqrt (Δ⁻¹ * Real.log (1 / (χ * ε)))

/-- Gate ledger of the unknown-energy construction (eqs. (3), (C21)):
`(Λ/Δ + Φ)·√L/χ`. -/
def unknownEnergyGateCost (Λ Φ Δ χ ε : ℝ) : ℝ := (Λ / Δ + Φ) * (lcuRuns Δ χ ε / χ)

/-- The displayed bound (3)/(5)/(C36):
`Λ/(χ·ξ^{3/2}) + Φ/(χ·√ξ)`, with `ξ^{3/2}` written as `ξ·√ξ`. -/
def unknownEnergyBound (Λ Φ ξ χ : ℝ) : ℝ :=
  Λ / (χ * (ξ * Real.sqrt ξ)) + Φ / (χ * Real.sqrt ξ)

/-- The number of LCU runs is bounded by the inverse-gap square root times a polylogarithmic factor. -/
lemma lcuRuns_le (N : ℕ) {Δ ε φ0 χ : ℝ}
    (hΔ : 0 < Δ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ0 : 0 < φ0) (hχ : 0 < χ) (hχ1 : χ ≤ 1) :
    lcuRuns Δ χ ε ≤ Real.sqrt (Δ⁻¹) * (1 + polylogScale N Δ ε φ0 χ) := by
  set P := polylogScale N Δ ε φ0 χ with hP
  have hP0 : 0 ≤ P := polylogScale_nonneg N hΔ hε hφ0 hχ
  have hχε : 0 < χ * ε := mul_pos hχ hε
  have hL0 : 0 ≤ Real.log (1 / (χ * ε)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hχε]
    nlinarith [mul_le_mul hχ1 hε1 (le_of_lt hε) (by norm_num : (0 : ℝ) ≤ 1)]
  have hLP : Real.log (1 / (χ * ε)) ≤ P := log_inv_mul_le_polylog N hΔ hε hφ0 hχ
  have hΔinv : 0 ≤ Δ⁻¹ := by positivity
  have hprod : Δ⁻¹ * Real.log (1 / (χ * ε)) ≤ (Real.sqrt (Δ⁻¹) * (1 + P)) ^ 2 := by
    have h1 : Δ⁻¹ * Real.log (1 / (χ * ε)) ≤ Δ⁻¹ * (1 + P) :=
      mul_le_mul_of_nonneg_left (by linarith) hΔinv
    have h2 : Δ⁻¹ * (1 + P) ≤ Δ⁻¹ * (1 + P) ^ 2 := by
      have h3 : 1 + P ≤ (1 + P) ^ 2 := by nlinarith [hP0]
      exact mul_le_mul_of_nonneg_left h3 hΔinv
    calc Δ⁻¹ * Real.log (1 / (χ * ε)) ≤ Δ⁻¹ * (1 + P) := h1
      _ ≤ Δ⁻¹ * (1 + P) ^ 2 := h2
      _ = (Real.sqrt (Δ⁻¹) * (1 + P)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
  calc lcuRuns Δ χ ε = Real.sqrt (Δ⁻¹ * Real.log (1 / (χ * ε))) := rfl
    _ ≤ Real.sqrt ((Real.sqrt (Δ⁻¹) * (1 + P)) ^ 2) := Real.sqrt_le_sqrt hprod
    _ = Real.sqrt (Δ⁻¹) * (1 + P) := Real.sqrt_sq (by positivity)

/-- **Theorem 2 / Proposition 5 / Corollary 2, gate part (eqs. (3), (C21), (C36);
also Theorem 4 eq. (5))**: the ledger `(Λ/Δ + Φ)√L/χ` is
`Õ(Λ/(χΔ^{3/2}) + Φ/(χ√Δ))`. -/
theorem unknownEnergyGateCost_le (N : ℕ) {Λ Φ Δ χ ε φ0 : ℝ}
    (hΛ : 0 < Λ) (hΦ : 0 < Φ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ0 : 0 < φ0) :
    IsTildeO (unknownEnergyGateCost Λ Φ Δ χ ε)
      (unknownEnergyBound Λ Φ Δ χ) (polylogScale N Δ ε φ0 χ) := by
  set P := polylogScale N Δ ε φ0 χ with hP
  have hP0 : 0 ≤ P := polylogScale_nonneg N hΔ hε hφ0 hχ
  have hrun := lcuRuns_le N hΔ hε hε1 hφ0 hχ hχ1
  have hcost : unknownEnergyGateCost Λ Φ Δ χ ε
      ≤ (Λ / Δ + Φ) * (Real.sqrt (Δ⁻¹) * (1 + P) / χ) := by
    unfold unknownEnergyGateCost
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hrun (le_of_lt hχ)) (by positivity)
  have hsimp : (Λ / Δ + Φ) * (Real.sqrt (Δ⁻¹) * (1 + P) / χ)
      = (1 + P) * unknownEnergyBound Λ Φ Δ χ := by
    rw [Real.sqrt_inv]
    unfold unknownEnergyBound
    field_simp [hΔ.ne', (Real.sqrt_pos.mpr hΔ).ne', hχ.ne'] <;> ring
  have hB : 0 ≤ unknownEnergyBound Λ Φ Δ χ := by
    unfold unknownEnergyBound
    have hs : 0 < Real.sqrt Δ := Real.sqrt_pos.mpr hΔ
    have hx : 0 < Δ * Real.sqrt Δ := mul_pos hΔ hs
    positivity
  refine ⟨2, by norm_num, 1, ?_⟩
  calc unknownEnergyGateCost Λ Φ Δ χ ε
      ≤ (1 + P) * unknownEnergyBound Λ Φ Δ χ := by rw [← hsimp]; exact hcost
    _ ≤ 2 * unknownEnergyBound Λ Φ Δ χ * (1 + P) ^ 1 := by
        have h1 : (1 + P) ≤ 2 * (1 + P) := by linarith
        nlinarith [hB, hP0]

/-! ## Phase-estimation ledgers: eqs. (A1), (B1), (B10) -/

/-- Ledger of Proposition 2 (eq. (A1)): `1/χ` phase-estimation runs of cost
`2^k Λ + Φ` with `2^k = 1/(χξ)`. -/
def peRunCost (Λ Φ χ ξ : ℝ) : ℝ := (1 / χ) * (Λ / (χ * ξ) + Φ)

/-- Ledger of Proposition 3 (eq. (B1)): `1/|φ₀|` runs of phase estimation at
precision `|φ₀|εΔ`. -/
def knownEnergyPEGateCost (Λ Φ φ0 Δ ε : ℝ) : ℝ :=
  (1 / φ0) * (Λ / (φ0 * Δ * ε) + Φ)

/-- **Proposition 2, eq. (A1)**: the phase-estimation ledger is
`Õ(Λ/(χ³ξ) + Φ/χ)`. -/
theorem peRunCost_le (N : ℕ) {Λ Φ Δ ε φ0 χ ξ : ℝ}
    (hΛ : 0 < Λ) (hΦ : 0 < Φ) (hΔ : 0 < Δ) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hε : 0 < ε) (hφ0 : 0 < φ0) (hξ : 0 < ξ) :
    IsTildeO (peRunCost Λ Φ χ ξ) (Λ / (χ ^ 3 * ξ) + Φ / χ)
      (polylogScale N Δ ε φ0 χ) := by
  refine ⟨1, one_pos, 0, ?_⟩
  have h1 : (1 / χ) * (Λ / (χ * ξ)) = Λ / (χ ^ 2 * ξ) := by
    field_simp [hχ.ne', hξ.ne'] <;> ring
  have h2 : (1 / χ) * Φ = Φ / χ := by
    ring
  have hstep : Λ / (χ ^ 2 * ξ) ≤ Λ / (χ ^ 3 * ξ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hχ3 : χ ^ 3 ≤ χ ^ 2 := by nlinarith [hχ, hχ1]
    nlinarith [mul_pos hΛ hξ, sq_pos_of_pos hχ]
  have hmain : peRunCost Λ Φ χ ξ ≤ Λ / (χ ^ 3 * ξ) + Φ / χ := by
    unfold peRunCost
    rw [mul_add, h1, h2]
    linarith
  simpa using hmain

/-- **Proposition 3, eq. (B1)**: the known-energy phase-estimation ledger equals
`Λ/(|φ₀|²Δε) + Φ/|φ₀|` exactly. -/
theorem knownEnergyPEGateCost_le (N : ℕ) {Λ Φ Δ ε φ0 χ : ℝ}
    (hΛ : 0 < Λ) (hΦ : 0 < Φ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hφ0 : 0 < φ0) (hχ : 0 < χ) (hε1 : ε ≤ 1) (hφ01 : φ0 ≤ 1) :
    IsTildeO (knownEnergyPEGateCost Λ Φ φ0 Δ ε)
      (Λ / (φ0 ^ 2 * Δ * ε) + Φ / φ0) (polylogScale N Δ ε φ0 χ) := by
  refine ⟨1, one_pos, 0, ?_⟩
  have heq : knownEnergyPEGateCost Λ Φ φ0 Δ ε
      = Λ / (φ0 ^ 2 * Δ * ε) + Φ / φ0 := by
    unfold knownEnergyPEGateCost
    field_simp [hφ0.ne'] <;> ring
  simpa [heq]

/-! ## The combined phase-estimation + search ledgers: eqs. (4), (6), (C38) -/

/-- Prior phase-estimation cost at precision `Δ^κ` (eq. (A1) with `ξ = Δ^κ`). -/
def phaseEstimationPriorCost (Λ Φ Δ χ κ : ℝ) : ℝ :=
  (1 / χ) * (Λ / (χ * Δ ^ κ) + Φ)

/-- The `Õ` form of `phaseEstimationPriorCost` in eqs. (4), (6), (C38). -/
def phaseEstimationPriorBound (Λ Φ Δ χ κ : ℝ) : ℝ :=
  Λ / (χ ^ 3 * Δ ^ κ) + Φ / χ

/-- Minimum-label energy search cost on an interval of size `Δ^κ`:
`(Λ/Δ + Φ)·√(Δ^κ/Δ)/χ`. -/
def minLabelSearchCost (Λ Φ Δ χ κ : ℝ) : ℝ :=
  (Λ / Δ + Φ) * (Real.sqrt (Δ ^ κ / Δ) / χ)

/-- Ledger of the combined approach (eqs. (4), (6), (C38)): prior phase
estimation plus minimum-label energy search. -/
def combinedGateCost (Λ Φ Δ χ κ : ℝ) : ℝ :=
  phaseEstimationPriorCost Λ Φ Δ χ κ + minLabelSearchCost Λ Φ Δ χ κ

/-- The displayed bound (4)/(6)/(C38):
`Λ/(χ³Δ^κ) + Λ/(χΔ^{(3-κ)/2}) + Φ/(χΔ^{(1-κ)/2})`. -/
def combinedBound (Λ Φ Δ χ κ : ℝ) : ℝ :=
  phaseEstimationPriorBound Λ Φ Δ χ κ
    + (Λ / (χ * Δ ^ ((3 - κ) / 2)) + Φ / (χ * Δ ^ ((1 - κ) / 2)))

/-- The square root of a quotient of positive real powers has the expected exponent. -/
lemma sqrt_rpow_div_eq {Δ : ℝ} (hΔ : 0 < Δ) (κ : ℝ) :
    Real.sqrt (Δ ^ κ / Δ) = Δ ^ ((κ - 1) / 2) := by
  have h1 : Δ ^ κ / Δ = Δ ^ (κ - 1) := by
    calc Δ ^ κ / Δ = Δ ^ κ / Δ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = Δ ^ (κ - 1) := (Real.rpow_sub hΔ κ 1).symm
  rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_mul hΔ.le]
  congr 1
  ring

/-- The minimum-label search ledger equals the displayed sum of inverse real powers. -/
lemma minLabelSearchCost_eq {Δ : ℝ} (hΔ : 0 < Δ) (κ : ℝ) (Λ Φ χ : ℝ) (hχ : χ ≠ 0) :
    minLabelSearchCost Λ Φ Δ χ κ
      = Λ / (χ * Δ ^ ((3 - κ) / 2)) + Φ / (χ * Δ ^ ((1 - κ) / 2)) := by
  have hpowA : Δ ^ ((3 - κ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hΔ _).ne'
  have hpowB : Δ ^ ((1 - κ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hΔ _).ne'
  have hΛ : Δ⁻¹ * Δ ^ ((κ - 1) / 2) = (Δ ^ ((3 - κ) / 2))⁻¹ := by
    rw [show Δ⁻¹ = Δ ^ (-1 : ℝ) by rw [Real.rpow_neg hΔ.le, Real.rpow_one],
      ← Real.rpow_add hΔ (-1) ((κ - 1) / 2), ← Real.rpow_neg hΔ.le ((3 - κ) / 2)]
    congr 1
    ring
  have hΦ : Δ ^ ((κ - 1) / 2) = (Δ ^ ((1 - κ) / 2))⁻¹ := by
    rw [← Real.rpow_neg hΔ.le ((1 - κ) / 2)]
    congr 1
    ring
  unfold minLabelSearchCost
  rw [sqrt_rpow_div_eq hΔ κ]
  have hsplit : (Λ / Δ + Φ) * (Δ ^ ((κ - 1) / 2) / χ)
      = (Λ * (Δ⁻¹ * Δ ^ ((κ - 1) / 2)) + Φ * Δ ^ ((κ - 1) / 2)) / χ := by
    field_simp [hΔ.ne', hχ] <;> ring
  rw [hsplit, hΛ, hΦ]
  field_simp [hpowA, hpowB]

/-- **Theorem 3 / Theorem 4 eq. (6) / Proposition 6, eq. (4)/(6)/(C38)**: the
combined ledger is `Õ(Λ/(χ³Δ^κ) + Λ/(χΔ^{(3-κ)/2}) + Φ/(χΔ^{(1-κ)/2}))` for
`κ ∈ [0,1]`. -/
theorem combinedGateCost_le (N : ℕ) {Λ Φ Δ χ ε φ0 κ : ℝ}
    (hΛ : 0 < Λ) (hΦ : 0 < Φ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hε : 0 < ε) (hφ0 : 0 < φ0)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    IsTildeO (combinedGateCost Λ Φ Δ χ κ) (combinedBound Λ Φ Δ χ κ)
      (polylogScale N Δ ε φ0 χ) := by
  refine ⟨1, one_pos, 0, ?_⟩
  have hsearch := minLabelSearchCost_eq hΔ κ Λ Φ χ hχ.ne'
  have hΔκ : 0 < Δ ^ κ := Real.rpow_pos_of_pos hΔ κ
  have hprior1 : (1 / χ) * (Λ / (χ * Δ ^ κ)) ≤ Λ / (χ ^ 3 * Δ ^ κ) := by
    have heq : (1 / χ) * (Λ / (χ * Δ ^ κ)) = Λ / (χ ^ 2 * Δ ^ κ) := by
      field_simp [hχ.ne', hΔκ.ne'] <;> ring
    rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
    have hχ3 : χ ^ 3 ≤ χ ^ 2 := by nlinarith [hχ, hχ1]
    nlinarith [mul_pos hΛ hΔκ, sq_pos_of_pos hχ]
  have hprior2 : (1 / χ) * Φ = Φ / χ := by ring
  have hprior : phaseEstimationPriorCost Λ Φ Δ χ κ ≤ phaseEstimationPriorBound Λ Φ Δ χ κ := by
    unfold phaseEstimationPriorCost phaseEstimationPriorBound
    have heq : (1 / χ) * (Λ / (χ * Δ ^ κ) + Φ)
        = (1 / χ) * (Λ / (χ * Δ ^ κ)) + (1 / χ) * Φ := by ring
    rw [heq]
    linarith [hprior1]
  have hmain : combinedGateCost Λ Φ Δ χ κ ≤ combinedBound Λ Φ Δ χ κ := by
    unfold combinedGateCost combinedBound
    rw [hsearch]
    exact add_le_add hprior le_rfl
  simpa using hmain


/-! ## The filtering-method ledgers: eqs. (C5), (C6), (C19), (C20) -/

/-- The filter-order factor `η = log(1/(χε))/log log(1/(χε))` of eqs. (C16)-(C18). -/
def filteringEta (χ ε : ℝ) : ℝ :=
  Real.log (1 / (χ * ε)) / Real.log (Real.log (1 / (χ * ε)))

/-- `k = log₂(1/Δ)` up to constants (the number of filter ancillas of eq. (C16)). -/
def filteringK (Δ : ℝ) : ℝ := Real.log (Δ⁻¹ + 2)

/-- Gate ledger of the filtering method (eqs. (C19)): `(η² k Λ + Φ)/|φ₀|`. -/
def filteringGateCost (Λ Φ φ0 χ ε Δ : ℝ) : ℝ :=
  (1 / φ0) * (filteringEta χ ε ^ 2 * filteringK Δ * Λ + Φ)

/-- Qubit ledger of eq. (C6): `log N + log 1/ε + η log 1/Δ`. -/
def filteringQubitLedger (N : ℕ) (χ ε Δ : ℝ) : ℝ :=
  Real.log ((N : ℝ) + 2) + Real.log (ε⁻¹ + 2) + filteringEta χ ε * Real.log (Δ⁻¹ + 2)

/-- Qubit ledger of eq. (C37): `log N + (log χ⁻¹/log log χ⁻¹) log 1/ξ`. -/
def filteringQubitXiLedger (N : ℕ) (χ ξ : ℝ) : ℝ :=
  Real.log ((N : ℝ) + 2)
    + (Real.log (χ⁻¹) / Real.log (Real.log (χ⁻¹))) * Real.log (ξ⁻¹ + 2)

/-- Qubit ledger of eqs. (A1)/(2)/(B1)-type estimates: `log N + log 1/ξ`. -/
def estimationQubitLedger (N : ℕ) (ξ : ℝ) : ℝ :=
  Real.log ((N : ℝ) + 2) + Real.log (ξ⁻¹ + 2)

/-- Qubit ledger `log N + log 1/ε + log 1/Δ` of Prop. 3 / Cor. 1. -/
def prepQubitLedger (N : ℕ) (ε Δ : ℝ) : ℝ :=
  Real.log ((N : ℝ) + 2) + Real.log (ε⁻¹ + 2) + Real.log (Δ⁻¹ + 2)

/-- The filtering logarithm is nonnegative when the overlap-error product is at most one. -/
lemma filteringLog_nonneg {χ ε : ℝ} (hχ : 0 < χ) (hε : 0 < ε) (hχε : χ * ε ≤ 1) :
    0 ≤ Real.log (1 / (χ * ε)) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ (mul_pos hχ hε)]
  simpa using hχε

/-- The filtering truncation parameter is nonnegative under the logarithmic size assumptions. -/
lemma filteringEta_nonneg {χ ε : ℝ} (hχ : 0 < χ) (hε : 0 < ε) (hχε : χ * ε ≤ 1)
    (hL : Real.exp 1 ≤ Real.log (1 / (χ * ε))) : 0 ≤ filteringEta χ ε := by
  have hL0 : 0 ≤ Real.log (1 / (χ * ε)) := filteringLog_nonneg hχ hε hχε
  have hlogL : 1 ≤ Real.log (Real.log (1 / (χ * ε))) := by
    have h1 := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at h1
  have hpos : 0 < Real.log (Real.log (1 / (χ * ε))) := by linarith
  unfold filteringEta
  exact div_nonneg hL0 (le_of_lt hpos)

/-- The filtering truncation parameter is bounded by the common polylogarithmic scale. -/
lemma filteringEta_le_polylog (N : ℕ) {Δ ε φ0 χ : ℝ}
    (hΔ : 0 < Δ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ0 : 0 < φ0) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hχε : χ * ε ≤ 1) (hL : Real.exp 1 ≤ Real.log (1 / (χ * ε))) :
    filteringEta χ ε ≤ polylogScale N Δ ε φ0 χ := by
  have hP0 : 0 ≤ polylogScale N Δ ε φ0 χ := polylogScale_nonneg N hΔ hε hφ0 hχ
  have hLP : Real.log (1 / (χ * ε)) ≤ polylogScale N Δ ε φ0 χ :=
    log_inv_mul_le_polylog N hΔ hε hφ0 hχ
  have hlogL : 1 ≤ Real.log (Real.log (1 / (χ * ε))) := by
    have h1 := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at h1
  have hpos : 0 < Real.log (Real.log (1 / (χ * ε))) := by linarith
  have hL0 : 0 ≤ Real.log (1 / (χ * ε)) := filteringLog_nonneg hχ hε hχε
  unfold filteringEta
  rw [div_le_iff₀ hpos]
  calc Real.log (1 / (χ * ε)) ≤ polylogScale N Δ ε φ0 χ := hLP
    _ ≤ polylogScale N Δ ε φ0 χ * Real.log (Real.log (1 / (χ * ε))) := by
        have : 1 ≤ Real.log (Real.log (1 / (χ * ε))) := hlogL
        nlinarith [hP0]

/-- The filtering gap logarithm is bounded by the common polylogarithmic scale. -/
lemma filteringK_le_polylog (N : ℕ) {Δ ε φ0 χ : ℝ}
    (hΔ : 0 < Δ) (hε : 0 < ε) (hφ0 : 0 < φ0) (hχ : 0 < χ) :
    filteringK Δ ≤ polylogScale N Δ ε φ0 χ := by
  unfold filteringK polylogScale
  have h1 : 0 < Real.log ((N : ℝ) + 2) := Real.log_pos (one_lt_nat_add_two N)
  have h2 : 0 < Real.log (ε⁻¹ + 2) := Real.log_pos (one_lt_inv_add_two hε)
  have h3 : 0 < Real.log (φ0⁻¹ + 2) := Real.log_pos (one_lt_inv_add_two hφ0)
  have h4 : 0 < Real.log (χ⁻¹ + 2) := Real.log_pos (one_lt_inv_add_two hχ)
  linarith

/-- **Proposition 4, eq. (C5)**: the filtering-method ledger `(η²kΛ + Φ)/|φ₀|`
is `Õ(Λ/(|φ₀|Δ) + Φ/|φ₀|)`. -/
theorem filteringGateCost_le (N : ℕ) {Λ Φ Δ χ ε φ0 : ℝ}
    (hΛ : 0 < Λ) (hΦ : 0 < Φ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ0 : 0 < φ0)
    (hχε : χ * ε ≤ 1) (hL : Real.exp 1 ≤ Real.log (1 / (χ * ε))) :
    IsTildeO (filteringGateCost Λ Φ φ0 χ ε Δ)
      (Λ / (φ0 * Δ) + Φ / φ0) (polylogScale N Δ ε φ0 χ) := by
  set P := polylogScale N Δ ε φ0 χ with hP
  have hP0 : 0 ≤ P := polylogScale_nonneg N hΔ hε hφ0 hχ
  have heta := filteringEta_le_polylog N hΔ hε hε1 hφ0 hχ hχ1 hχε hL
  have hk := filteringK_le_polylog N hΔ hε hφ0 hχ
  have heta0 : 0 ≤ filteringEta χ ε := filteringEta_nonneg hχ hε hχε hL
  have hk0 : 0 ≤ filteringK Δ := by
    unfold filteringK
    apply Real.log_nonneg
    have : 0 < Δ⁻¹ := inv_pos.mpr hΔ
    linarith
  have hprod : filteringEta χ ε ^ 2 * filteringK Δ ≤ P ^ 3 := by
    have h1 : filteringEta χ ε ^ 2 ≤ P ^ 2 := by nlinarith [heta, heta0, hP0]
    calc filteringEta χ ε ^ 2 * filteringK Δ ≤ P ^ 2 * P :=
          mul_le_mul h1 hk hk0 (by positivity)
      _ = P ^ 3 := by ring
  have hΛle : Λ ≤ Λ / Δ := by
    rw [le_div_iff₀ hΔ]
    nlinarith [mul_le_mul_of_nonneg_left hΔ1 hΛ.le]
  have hP3le : P ^ 3 ≤ (1 + P) ^ 3 := by
    apply pow_le_pow_left₀ hP0
    linarith
  have h1P : (1 : ℝ) ≤ (1 + P) ^ 3 := by
    have h1 : (1 : ℝ) ≤ 1 + P := by linarith
    nlinarith [sq_nonneg P, mul_nonneg (by linarith : (0:ℝ) ≤ 1 + P)
      (by linarith : (0:ℝ) ≤ 1 + P)]
  refine ⟨1, one_pos, 3, ?_⟩
  have hmain : filteringGateCost Λ Φ φ0 χ ε Δ
      ≤ (Λ / (φ0 * Δ) + Φ / φ0) * (1 + P) ^ 3 := by
    unfold filteringGateCost
    have hfac : filteringEta χ ε ^ 2 * filteringK Δ * Λ ≤ P ^ 3 * Λ :=
      mul_le_mul_of_nonneg_right hprod hΛ.le
    have hA : (1 / φ0) * (filteringEta χ ε ^ 2 * filteringK Δ * Λ)
        ≤ (Λ / (φ0 * Δ)) * (1 + P) ^ 3 := by
      calc (1 / φ0) * (filteringEta χ ε ^ 2 * filteringK Δ * Λ)
          ≤ (1 / φ0) * (P ^ 3 * Λ) :=
            mul_le_mul_of_nonneg_left hfac (by positivity)
        _ ≤ (1 / φ0) * ((1 + P) ^ 3 * (Λ / Δ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc P ^ 3 * Λ ≤ (1 + P) ^ 3 * Λ :=
                  mul_le_mul_of_nonneg_right hP3le hΛ.le
              _ ≤ (1 + P) ^ 3 * (Λ / Δ) :=
                  mul_le_mul_of_nonneg_left hΛle (by positivity)
        _ = (Λ / (φ0 * Δ)) * (1 + P) ^ 3 := by
            field_simp [hφ0.ne'] <;> ring
    have hB : (1 / φ0) * Φ ≤ (Φ / φ0) * (1 + P) ^ 3 := by
      have heq : (1 / φ0) * Φ = Φ / φ0 := by ring
      rw [heq]
      have := mul_le_mul_of_nonneg_left h1P (by positivity : (0:ℝ) ≤ Φ / φ0)
      simpa using this
    calc (1 / φ0) * (filteringEta χ ε ^ 2 * filteringK Δ * Λ + Φ)
        = (1 / φ0) * (filteringEta χ ε ^ 2 * filteringK Δ * Λ) + (1 / φ0) * Φ := by ring
      _ ≤ (Λ / (φ0 * Δ)) * (1 + P) ^ 3 + (Φ / φ0) * (1 + P) ^ 3 := add_le_add hA hB
      _ = (Λ / (φ0 * Δ) + Φ / φ0) * (1 + P) ^ 3 := by ring
  calc filteringGateCost Λ Φ φ0 χ ε Δ
      ≤ (Λ / (φ0 * Δ) + Φ / φ0) * (1 + P) ^ 3 := hmain
    _ = 1 * (Λ / (φ0 * Δ) + Φ / φ0) * (1 + P) ^ 3 := by ring

/-- Adding one to the estimation qubit ledger preserves its big-O bound. -/
lemma estimationQubitLedger_bigO (N : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    IsBigO (estimationQubitLedger N ξ + 1) (estimationQubitLedger N ξ) := by
  apply isBigO_add_one_of_half_le
  unfold estimationQubitLedger
  have h1 := log_nat_add_two_ge_log_two N
  have h2 : 0 ≤ Real.log (ξ⁻¹ + 2) := by
    apply Real.log_nonneg
    have : 0 < ξ⁻¹ := inv_pos.mpr hξ
    linarith
  linarith [log_two_ge_half]

/-- Adding one to the preparation qubit ledger preserves its big-O bound. -/
lemma prepQubitLedger_bigO (N : ℕ) {ε Δ : ℝ} (hε : 0 < ε) (hΔ : 0 < Δ) :
    IsBigO (prepQubitLedger N ε Δ + 1) (prepQubitLedger N ε Δ) := by
  apply isBigO_add_one_of_half_le
  unfold prepQubitLedger
  have h1 := log_nat_add_two_ge_log_two N
  have h2 : 0 ≤ Real.log (ε⁻¹ + 2) := by
    apply Real.log_nonneg
    have : 0 < ε⁻¹ := inv_pos.mpr hε
    linarith
  have h3 : 0 ≤ Real.log (Δ⁻¹ + 2) := by
    apply Real.log_nonneg
    have : 0 < Δ⁻¹ := inv_pos.mpr hΔ
    linarith
  linarith [log_two_ge_half]

/-- Adding one to the filtering qubit ledger preserves its big-O bound. -/
lemma filteringQubitLedger_bigO (N : ℕ) {χ ε Δ : ℝ}
    (hχ : 0 < χ) (hε : 0 < ε) (hχε : χ * ε ≤ 1)
    (hL : Real.exp 1 ≤ Real.log (1 / (χ * ε))) (hΔ : 0 < Δ) :
    IsBigO (filteringQubitLedger N χ ε Δ + 1) (filteringQubitLedger N χ ε Δ) := by
  apply isBigO_add_one_of_half_le
  unfold filteringQubitLedger
  have h1 := log_nat_add_two_ge_log_two N
  have heta0 := filteringEta_nonneg hχ hε hχε hL
  have hk0 : 0 ≤ Real.log (Δ⁻¹ + 2) := by
    apply Real.log_nonneg
    have : 0 < Δ⁻¹ := inv_pos.mpr hΔ
    linarith
  have hε0 : 0 ≤ Real.log (ε⁻¹ + 2) := by
    apply Real.log_nonneg
    have : 0 < ε⁻¹ := inv_pos.mpr hε
    linarith
  have hprod : 0 ≤ filteringEta χ ε * Real.log (Δ⁻¹ + 2) := mul_nonneg heta0 hk0
  linarith [log_two_ge_half]

/-- Adding one to the precision-dependent filtering qubit ledger preserves its big-O bound. -/
lemma filteringQubitXiLedger_bigO (N : ℕ) {χ ξ : ℝ}
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hξ : 0 < ξ)
    (hL : Real.exp 1 ≤ Real.log (χ⁻¹)) :
    IsBigO (filteringQubitXiLedger N χ ξ + 1) (filteringQubitXiLedger N χ ξ) := by
  apply isBigO_add_one_of_half_le
  unfold filteringQubitXiLedger
  have h1 := log_nat_add_two_ge_log_two N
  have hL0 : 0 ≤ Real.log (χ⁻¹) := le_trans (by positivity : (0:ℝ) ≤ Real.exp 1) hL
  have hlogL : 1 ≤ Real.log (Real.log (χ⁻¹)) := by
    have h2 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    rw [← h2]
    exact Real.log_le_log (Real.exp_pos 1) hL
  have hpos : 0 < Real.log (Real.log (χ⁻¹)) := by linarith
  have hratio : 0 ≤ Real.log (χ⁻¹) / Real.log (Real.log (χ⁻¹)) :=
    div_nonneg hL0 (le_of_lt hpos)
  have hk : 0 ≤ Real.log (ξ⁻¹ + 2) := by
    apply Real.log_nonneg
    have : 0 < ξ⁻¹ := inv_pos.mpr hξ
    linarith
  have hprod : 0 ≤ (Real.log (χ⁻¹) / Real.log (Real.log (χ⁻¹))) * Real.log (ξ⁻¹ + 2) :=
    mul_nonneg hratio hk
  linarith [log_two_ge_half]

/-! ## The minimum-label search ledgers: eqs. (31), (32) and Prop. 1 -/

/-- Calls to `C_Φ` (eq. (31)): `n` binary-search stages, each with
`log(n/δ)+1` repetitions of `O(1/ζ)` fixed point searches. -/
def minLabelCallCost (n : ℕ) (ζ δ : ℝ) : ℝ :=
  (n : ℝ) * (Real.log ((n : ℝ) / δ) + 1) / ζ

/-- The displayed bound of eq. (31): `(n/ζ) log²(n/δ)`. -/
def minLabelCallBound (n : ℕ) (ζ δ : ℝ) : ℝ :=
  ((n : ℝ) / ζ) * (Real.log ((n : ℝ) / δ)) ^ 2

/-- Elementary-gate ledger of eq. (32): each call of `C_Φ` costs
`poly(q,n,m) = (q+n+m+1)²` elementary gates. -/
def minLabelGateLedger (q n m : ℕ) (ζ δ : ℝ) : ℝ :=
  minLabelCallCost n ζ δ * (((q + n + m + 1 : ℕ) : ℝ)) ^ 2

/-- The displayed bound of eq. (32). -/
def minLabelGateBound (q n m : ℕ) (ζ δ : ℝ) : ℝ :=
  (((q + n + m + 1 : ℕ) : ℝ)) ^ 2 * minLabelCallBound n ζ δ

/-- Qubit count of Prop. 1: `q + n + m + 1`. -/
def minLabelQubitCount (q n m : ℕ) : ℕ := q + n + m + 1

/-- **Proposition 1, eq. (31)**: the number of calls to `C_Φ` is
`O((n/ζ) log²(n/δ))`. -/
theorem minLabelCallCost_le {n : ℕ} {ζ δ : ℝ}
    (hn : 1 ≤ n) (hζ : 0 < ζ) (hL : 1 ≤ Real.log ((n : ℝ) / δ)) :
    IsBigO (minLabelCallCost n ζ δ) (minLabelCallBound n ζ δ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hL0 : 0 ≤ Real.log ((n : ℝ) / δ) := by linarith
  refine ⟨2, by norm_num, ?_⟩
  unfold minLabelCallCost minLabelCallBound
  have hstep : Real.log ((n : ℝ) / δ) + 1 ≤ 2 * (Real.log ((n : ℝ) / δ)) ^ 2 := by
    nlinarith [hL0]
  calc (n : ℝ) * (Real.log ((n : ℝ) / δ) + 1) / ζ
      ≤ (n : ℝ) * (2 * (Real.log ((n : ℝ) / δ)) ^ 2) / ζ := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hζ)
        exact mul_le_mul_of_nonneg_left hstep (le_of_lt hn0)
    _ = 2 * (((n : ℝ) / ζ) * (Real.log ((n : ℝ) / δ)) ^ 2) := by
        field_simp [hζ.ne'] <;> ring

/-- **Proposition 1, eq. (32)**: the elementary-gate count is
`O(poly(q,n,m)/ζ log²(n/δ))`. -/
theorem minLabelGateLedger_le {q n m : ℕ} {ζ δ : ℝ}
    (hn : 1 ≤ n) (hζ : 0 < ζ) (hL : 1 ≤ Real.log ((n : ℝ) / δ)) :
    IsBigO (minLabelGateLedger q n m ζ δ) (minLabelGateBound q n m ζ δ) := by
  have hc := minLabelCallCost_le hn hζ hL
  obtain ⟨C, hC, hle⟩ := hc
  refine ⟨C, hC, ?_⟩
  unfold minLabelGateLedger minLabelGateBound
  have hP2 : 0 ≤ (((q + n + m + 1 : ℕ) : ℝ)) ^ 2 := by positivity
  calc minLabelCallCost n ζ δ * (((q + n + m + 1 : ℕ) : ℝ)) ^ 2
      ≤ (C * minLabelCallBound n ζ δ) * (((q + n + m + 1 : ℕ) : ℝ)) ^ 2 := by
        exact mul_le_mul_of_nonneg_right hle hP2
    _ = C * ((((q + n + m + 1 : ℕ) : ℝ)) ^ 2 * minLabelCallBound n ζ δ) := by
        ring

end Qatlib.Papers.GroundStPrep17.MainResults
