/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# GroundStPrep17.MainResults.SourceModel

Source complexity model for Ge, Tura and Cirac,
*Faster ground state preparation and high-precision ground energy estimation with
fewer qubits*, arXiv:1712.03193v2 (fixed version: v2, 2 Feb 2018).

The paper states every result as a gate/qubit complexity bound for an explicit
construction.  This module records the asymptotic vocabulary and the cost
ledgers of the constructions, so that the per-claim theorems can be stated as
sharp statements about those ledgers:

* `polylogScale` is the polylogarithmic factor of the paper (p. 2, below eq. (2)):
  `Õ(·)` is understood up to powers of `log N`, `log Δ⁻¹`, `log ε⁻¹`,
  `log |φ₀|⁻¹` and `log χ⁻¹`;
* `IsTildeO` / `IsBigO` are the corresponding upper-bound relations;
* `cosPowerCount` (eq. (17)), `truncationOrder` (eq. (22)) and
  `sectionIIIGateCost` (eq. (28)) are the ledger of the Section III
  (known-ground-energy) construction;
* `paperQubitBound` is the qubit count of eq. (2).

The arithmetic lemmas at the bottom (`sectionIIIGateCost_le`,
`sectionIIIQubitCost_le`) discharge the substitution of eqs. (17)/(22) into
eq. (28), which is precisely the derivation of eq. (1) in the paper.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.GroundStPrep17.MainResults

/-- The paper's polylogarithmic scale (p. 2, below eq. (2)): every `Õ(·)` absorbs
powers of `log N`, `log Δ⁻¹`, `log ε⁻¹`, `log |φ₀|⁻¹` and `log χ⁻¹`.  Each
argument is written as `x + 2` so all logarithms are positive. -/
def polylogScale (N : ℕ) (Δ ε φ0 χ : ℝ) : ℝ :=
  Real.log ((N : ℝ) + 2) + Real.log (Δ⁻¹ + 2) + Real.log (ε⁻¹ + 2)
    + Real.log (φ0⁻¹ + 2) + Real.log (χ⁻¹ + 2)

/-- `Õ`-type upper bound: `cost ≤ C · bound · (1 + scale)^a` with absolute
constants `C > 0` and `a : ℕ`. -/
def IsTildeO (cost bound scale : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, cost ≤ C * bound * (1 + scale) ^ a

/-- Plain `O`-type upper bound. -/
def IsBigO (cost bound : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ cost ≤ C * bound

/-- `M`, eq. (17) p. 6: the number of cosine powers used by the Section III
construction, `M = Θ(Δ⁻² log²(1/(χε)))`. -/
def cosPowerCount (Δ χ ε : ℝ) : ℝ :=
  (Δ⁻¹) ^ 2 * (Real.log (1 / (χ * ε))) ^ 2

/-- `m₀`, eq. (22) p. 6: the truncation order of the Fourier expansion of
`cos^{2m} H`, `m₀ = Θ(√(M log(1/(χε)))) = Θ(Δ⁻¹ log^{3/2}(1/(χε)))`. -/
def truncationOrder (Δ χ ε : ℝ) : ℝ :=
  Real.sqrt ((Δ⁻¹) ^ 2 * (Real.log (1 / (χ * ε))) ^ 3)

/-- Gate cost of one Section III run, eq. (28) p. 7:
`|φ₀|⁻¹ (m₀ Λ polylog + Φ)` (fixed-point search / amplitude amplification
accounted for). -/
def sectionIIIGateCost (N : ℕ) (Λ Φ φ0 Δ ε χ : ℝ) : ℝ :=
  (1 / φ0) * (truncationOrder Δ χ ε * Λ * polylogScale N Δ ε φ0 χ) + Φ / φ0

/-- Qubit cost of the Section III construction, eq. (2) p. 2: the `log N` state
register plus the `b = ⌈log₂(2m₀+1)⌉` Fourier ancillas of eq. (23).  The ledger
keeps the explicit `log log(1/(χε))` produced by `m₀` (22), which the paper
absorbs into its polylog convention. -/
def sectionIIIQubitCost (N : ℕ) (Δ ε χ : ℝ) : ℝ :=
  Real.log ((N : ℝ) + 2) + Real.log (Real.log (1 / (χ * ε)) + 2)
    + Real.log (Δ⁻¹ + 2) + 1

/-- The qubit count displayed in eq. (2) p. 2,
`log N + log log(1/ε) + log(1/Δ)`, guarded so that every logarithm is positive. -/
def paperQubitBound (N : ℕ) (Δ ε : ℝ) : ℝ :=
  Real.log ((N : ℝ) + 2) + Real.log (Real.log (ε⁻¹) + 2) + Real.log (Δ⁻¹ + 2) + 1

/-! ## Elementary lemmas on the polylogarithmic scale -/

/-- `1 < N + 2` for every natural `N`. -/
lemma one_lt_nat_add_two (N : ℕ) : (1 : ℝ) < (N : ℝ) + 2 := by
  have := Nat.cast_nonneg (α := ℝ) N
  linarith

/-- `1 < x⁻¹ + 2` for `x > 0`. -/
lemma one_lt_inv_add_two {x : ℝ} (hx : 0 < x) : (1 : ℝ) < x⁻¹ + 2 := by
  have := inv_pos.mpr hx
  linarith

/-- `polylogScale` is nonnegative for positive parameters. -/
lemma polylogScale_nonneg (N : ℕ) {Δ ε φ0 χ : ℝ}
    (hΔ : 0 < Δ) (hε : 0 < ε) (hφ0 : 0 < φ0) (hχ : 0 < χ) :
    0 ≤ polylogScale N Δ ε φ0 χ := by
  have h1 : 0 < Real.log ((N : ℝ) + 2) := Real.log_pos (one_lt_nat_add_two N)
  have h2 : 0 < Real.log (Δ⁻¹ + 2) := Real.log_pos (one_lt_inv_add_two hΔ)
  have h3 : 0 < Real.log (ε⁻¹ + 2) := Real.log_pos (one_lt_inv_add_two hε)
  have h4 : 0 < Real.log (φ0⁻¹ + 2) := Real.log_pos (one_lt_inv_add_two hφ0)
  have h5 : 0 < Real.log (χ⁻¹ + 2) := Real.log_pos (one_lt_inv_add_two hχ)
  unfold polylogScale
  linarith

/-- For `0 < χ, ε ≤ 1`, `log(1/(χε)) = log χ⁻¹ + log ε⁻¹` is dominated by the
polylogarithmic scale. -/
lemma log_inv_mul_le_polylog (N : ℕ) {Δ ε φ0 χ : ℝ}
    (hΔ : 0 < Δ) (hε : 0 < ε) (hφ0 : 0 < φ0) (hχ : 0 < χ) :
    Real.log (1 / (χ * ε)) ≤ polylogScale N Δ ε φ0 χ := by
  have hχε : 0 < χ * ε := mul_pos hχ hε
  have hlog : Real.log (1 / (χ * ε)) = Real.log (χ⁻¹) + Real.log (ε⁻¹) := by
    rw [one_div, Real.log_inv, Real.log_mul hχ.ne' hε.ne', Real.log_inv, Real.log_inv]
    ring
  rw [hlog]
  have h1 : Real.log (χ⁻¹) ≤ Real.log (χ⁻¹ + 2) :=
    Real.log_le_log (inv_pos.mpr hχ) (by linarith)
  have h2 : Real.log (ε⁻¹) ≤ Real.log (ε⁻¹ + 2) :=
    Real.log_le_log (inv_pos.mpr hε) (by linarith)
  have h3 : 0 ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_nonneg (le_of_lt (one_lt_nat_add_two N))
  have h4 : 0 ≤ Real.log (Δ⁻¹ + 2) := Real.log_nonneg (le_of_lt (one_lt_inv_add_two hΔ))
  have h5 : 0 ≤ Real.log (φ0⁻¹ + 2) := Real.log_nonneg (le_of_lt (one_lt_inv_add_two hφ0))
  unfold polylogScale
  linarith

/-- Elementary bound `√y ≤ 1 + y` for `y ≥ 0`. -/
lemma sqrt_le_one_add {y : ℝ} (hy : 0 ≤ y) : Real.sqrt y ≤ 1 + y := by
  have h1 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  nlinarith [Real.sq_sqrt hy, sq_nonneg (Real.sqrt y - 1)]

/-! ## The ledger of Theorem 1 (Section III, eqs. (17), (22), (28)) -/

/-- Substituting `m₀ = Θ(Δ⁻¹ log^{3/2}(1/(χε)))` (eq. (22)) into the gate ledger
(28) gives the advertised `Õ` bound (1):
`|φ₀|⁻¹(m₀Λ polylog + Φ) ≤ 9 (Λ/(|φ₀|Δ) + Φ/|φ₀|) (1 + polylog)^4`. -/
theorem truncationOrder_le (N : ℕ) {Δ ε φ0 χ : ℝ}
    (hΔ : 0 < Δ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ0 : 0 < φ0)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) :
    truncationOrder Δ χ ε ≤ 9 * Δ⁻¹ * (1 + polylogScale N Δ ε φ0 χ) ^ 3 := by
  set P := polylogScale N Δ ε φ0 χ with hP
  have hP0 : 0 ≤ P := polylogScale_nonneg N hΔ hε hφ0 hχ
  have hχε : 0 < χ * ε := mul_pos hχ hε
  have hL0 : 0 ≤ Real.log (1 / (χ * ε)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hχε]
    nlinarith [mul_le_mul hχ1 hε1 (le_of_lt hε) (by norm_num : (0:ℝ) ≤ 1)]
  have hLP : Real.log (1 / (χ * ε)) ≤ P :=
    log_inv_mul_le_polylog N hΔ hε hφ0 hχ
  have hLP' : Real.log (1 / (χ * ε)) ≤ 2 * P := by linarith
  have h2P : 0 ≤ 2 * P := by linarith
  have hsq : Real.log (1 / (χ * ε)) ^ 2 ≤ (2 * P) ^ 2 := by nlinarith
  have hL3 : Real.log (1 / (χ * ε)) ^ 3 ≤ 8 * P ^ 3 := by
    calc Real.log (1 / (χ * ε)) ^ 3
        = Real.log (1 / (χ * ε)) * Real.log (1 / (χ * ε)) ^ 2 := by ring
      _ ≤ (2 * P) * (2 * P) ^ 2 := by
          apply mul_le_mul hLP' hsq (by positivity) h2P
      _ = 8 * P ^ 3 := by ring
  calc truncationOrder Δ χ ε
      = Real.sqrt ((Δ⁻¹) ^ 2) * Real.sqrt ((Real.log (1 / (χ * ε))) ^ 3) := by
        unfold truncationOrder
        rw [Real.sqrt_mul (by positivity)]
    _ = Δ⁻¹ * Real.sqrt ((Real.log (1 / (χ * ε))) ^ 3) := by
        rw [Real.sqrt_sq (by positivity)]
    _ ≤ Δ⁻¹ * (1 + (Real.log (1 / (χ * ε))) ^ 3) := by
        gcongr
        exact sqrt_le_one_add (by positivity)
    _ ≤ Δ⁻¹ * (1 + 8 * P ^ 3) := by gcongr
    _ ≤ 9 * Δ⁻¹ * (1 + P) ^ 3 := by
        have hΔinv : 0 ≤ Δ⁻¹ := by positivity
        have hpoly : 1 + 8 * P ^ 3 ≤ 9 * (1 + P) ^ 3 := by
          nlinarith [hP0, sq_nonneg P, mul_nonneg hP0 (sq_nonneg P)]
        calc Δ⁻¹ * (1 + 8 * P ^ 3) ≤ Δ⁻¹ * (9 * (1 + P) ^ 3) :=
              mul_le_mul_of_nonneg_left hpoly hΔinv
          _ = 9 * Δ⁻¹ * (1 + P) ^ 3 := by ring

/-- **Theorem 1, eq. (1) (arXiv:1712.03193v2, p. 2).**  The gate ledger (28) of
the Section III construction is `Õ(Λ/(|φ₀|Δ) + Φ/|φ₀|)`. -/
theorem sectionIIIGateCost_le (N : ℕ) {Λ Φ φ0 Δ ε χ : ℝ}
    (hΛ : 0 < Λ) (hΦ : 0 < Φ) (hφ0 : 0 < φ0)
    (hΔ : 0 < Δ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hχ : 0 < χ) (hχ1 : χ ≤ 1) :
    IsTildeO (sectionIIIGateCost N Λ Φ φ0 Δ ε χ)
      (Λ / (φ0 * Δ) + Φ / φ0) (polylogScale N Δ ε φ0 χ) := by
  set P := polylogScale N Δ ε φ0 χ with hP
  have hP0 : 0 ≤ P := polylogScale_nonneg N hΔ hε hφ0 hχ
  have hm0 := truncationOrder_le N hΔ hε hε1 hφ0 hχ hχ1
  refine ⟨9, by norm_num, 4, ?_⟩
  have h2 : truncationOrder Δ χ ε * Λ * P ≤ 9 * Δ⁻¹ * Λ * (1 + P) ^ 4 := by
    calc truncationOrder Δ χ ε * Λ * P
        ≤ (9 * Δ⁻¹ * (1 + P) ^ 3) * Λ * P := by gcongr
      _ ≤ (9 * Δ⁻¹ * (1 + P) ^ 3) * Λ * (1 + P) := by
          gcongr
          linarith
      _ = 9 * Δ⁻¹ * Λ * (1 + P) ^ 4 := by ring
  have h3 : sectionIIIGateCost N Λ Φ φ0 Δ ε χ
      ≤ (1 / φ0) * (9 * Δ⁻¹ * Λ * (1 + P) ^ 4) + (1 / φ0) * Φ := by
    unfold sectionIIIGateCost
    have hΦ' : Φ / φ0 = (1 / φ0) * Φ := by ring
    rw [hΦ']
    exact add_le_add (mul_le_mul_of_nonneg_left h2 (by positivity)) le_rfl
  have hpow : 1 ≤ (1 + P) ^ 4 := by
    have h1P : (1 : ℝ) ≤ 1 + P := by linarith
    nlinarith [sq_nonneg P, mul_nonneg (by linarith : (0:ℝ) ≤ 1 + P)
      (by linarith : (0:ℝ) ≤ 1 + P)]
  have h4 : (1 / φ0) * (9 * Δ⁻¹ * Λ * (1 + P) ^ 4) + (1 / φ0) * Φ
      ≤ 9 * (Λ / (φ0 * Δ) + Φ / φ0) * (1 + P) ^ 4 := by
    have hΦle : Φ ≤ 9 * Φ * (1 + P) ^ 4 := by nlinarith [hΦ, hpow]
    have hΛle : 9 * Δ⁻¹ * Λ * (1 + P) ^ 4 + Φ
        ≤ 9 * (Δ⁻¹ * Λ + Φ) * (1 + P) ^ 4 := by
      nlinarith [hΛ, hΦ, hpow, mul_pos hΔ (mul_pos (by norm_num : (0:ℝ) < 9) hΛ)]
    have hφ0inv : 0 ≤ 1 / φ0 := by positivity
    have hstep : (1 / φ0) * (9 * Δ⁻¹ * Λ * (1 + P) ^ 4) + (1 / φ0) * Φ
        = (1 / φ0) * (9 * Δ⁻¹ * Λ * (1 + P) ^ 4 + Φ) := by ring
    rw [hstep]
    have := mul_le_mul_of_nonneg_left hΛle hφ0inv
    calc (1 / φ0) * (9 * Δ⁻¹ * Λ * (1 + P) ^ 4 + Φ)
        ≤ (1 / φ0) * (9 * (Δ⁻¹ * Λ + Φ) * (1 + P) ^ 4) := this
      _ = 9 * (Λ / (φ0 * Δ) + Φ / φ0) * (1 + P) ^ 4 := by
          field_simp [hφ0.ne']
  linarith [h3, h4]

/-- `log(1 + P) ≤ P` for `P ≥ 0`. -/
lemma log_one_add_le {P : ℝ} (hP : 0 ≤ P) : Real.log (1 + P) ≤ P := by
  have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + P)
  linarith

/-- **Theorem 1, eq. (2) (arXiv:1712.03193v2, p. 2).**  The qubit ledger (2) of
the Section III construction is `O(log N + log log(1/ε) + log(1/Δ))` up to the
`log log(1/χ)` factor produced by `m₀`, which the paper absorbs into `Õ`. -/
theorem sectionIIIQubitCost_le (N : ℕ) {Δ ε φ0 χ : ℝ}
    (hΔ : 0 < Δ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ0 : 0 < φ0)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) :
    IsTildeO (sectionIIIQubitCost N Δ ε χ) (paperQubitBound N Δ ε)
      (polylogScale N Δ ε φ0 χ) := by
  set P := polylogScale N Δ ε φ0 χ with hP
  have hP0 : 0 ≤ P := polylogScale_nonneg N hΔ hε hφ0 hχ
  have hχε : 0 < χ * ε := mul_pos hχ hε
  have hL0 : 0 ≤ Real.log (1 / (χ * ε)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hχε]
    nlinarith [mul_le_mul hχ1 hε1 (le_of_lt hε) (by norm_num : (0:ℝ) ≤ 1)]
  have hLP : Real.log (1 / (χ * ε)) ≤ P :=
    log_inv_mul_le_polylog N hΔ hε hφ0 hχ
  have hN0 : 0 ≤ Real.log ((N : ℝ) + 2) := by
    apply Real.log_nonneg
    have hcast : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hΔ0 : 0 ≤ Real.log (Δ⁻¹ + 2) := by
    apply Real.log_nonneg
    have : 0 < Δ⁻¹ := inv_pos.mpr hΔ
    linarith
  have hε0 : 0 ≤ Real.log (ε⁻¹ + 2) := by
    apply Real.log_nonneg
    have : 0 < ε⁻¹ := inv_pos.mpr hε
    linarith
  have hφ00 : 0 ≤ Real.log (φ0⁻¹ + 2) := by
    apply Real.log_nonneg
    have : 0 < φ0⁻¹ := inv_pos.mpr hφ0
    linarith
  have hχ0 : 0 ≤ Real.log (χ⁻¹ + 2) := by
    apply Real.log_nonneg
    have : 0 < χ⁻¹ := inv_pos.mpr hχ
    linarith
  have hN : Real.log ((N : ℝ) + 2) ≤ P := by
    rw [hP]; unfold polylogScale; linarith
  have hΔq : Real.log (Δ⁻¹ + 2) ≤ P := by
    rw [hP]; unfold polylogScale; linarith
  have hLq : Real.log (Real.log (1 / (χ * ε)) + 2) ≤ 1 + P := by
    have hpos : 0 < Real.log (1 / (χ * ε)) + 2 := by linarith
    have hle : Real.log (1 / (χ * ε)) + 2 ≤ 2 * (1 + P) := by linarith
    have h2pos : 0 < 2 * (1 + P) := by linarith
    have hmono : Real.log (Real.log (1 / (χ * ε)) + 2) ≤ Real.log (2 * (1 + P)) :=
      Real.log_le_log hpos hle
    have hsplit : Real.log (2 * (1 + P)) = Real.log 2 + Real.log (1 + P) :=
      Real.log_mul (by norm_num) (by linarith)
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      linarith
    have hlog1P : Real.log (1 + P) ≤ P := log_one_add_le hP0
    linarith
  have hQ : sectionIIIQubitCost N Δ ε χ ≤ 3 * (1 + P) := by
    unfold sectionIIIQubitCost
    linarith
  have hεq : 0 ≤ Real.log (Real.log (ε⁻¹) + 2) := by
    apply Real.log_nonneg
    have h1 : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
    have h2 : 0 ≤ Real.log (ε⁻¹) := Real.log_nonneg h1
    linarith
  have hbound : 1 ≤ paperQubitBound N Δ ε := by
    unfold paperQubitBound
    linarith [hN0, hΔ0, hεq]
  refine ⟨3, by norm_num, 1, ?_⟩
  calc sectionIIIQubitCost N Δ ε χ ≤ 3 * (1 + P) := hQ
    _ ≤ 3 * paperQubitBound N Δ ε * (1 + P) ^ 1 := by
        have : 1 ≤ (1 + P) ^ 1 := by simp; linarith
        nlinarith [hbound, hP0]

end Qatlib.Papers.GroundStPrep17.MainResults
