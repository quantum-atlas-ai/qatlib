/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Retry budget turning the deficit estimate into the target error

[ChildsWiebe2012], Lemma 11 uses the repetition threshold (64) to bound the error in (66).
Write `A = 2m(5/3)^{k-1}ht`. With the factor `C = 5` fixed uniformly, the threshold
`r ≥ A^{1+1/(4k)} / (ε/C)^{1/(4k)}` reduces the assumed deficit bound
`‖M - U‖ ≤ C r (A/r)^{4k+1}` to the target error `ε`. The deficit estimate from the
Suzuki analysis and the probability of meeting it lie outside this result. The norm is the
Euclidean operator norm on a finite, nonempty register.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HamLCUSim12.FullSimulation

open scoped Matrix.Norms.L2Operator

/-- The powered repetition budget bounds the assumed operator deficit by the error tolerance.
The factor `C = 5` is uniform in the positive order index `k`, repetition count `r`, scale
`A`, and tolerance `ε`. The budget `C * A ^ (4 * k + 1) ≤ ε * r ^ (4 * k)` is the
`4k`-th power of (64) in [ChildsWiebe2012], Lemma 11. The deficit assumption
`‖M - U‖ ≤ C * r * (A / r) ^ (4 * k + 1)` is (66) in the Euclidean operator norm. -/
theorem retry_error_budget : ∃ C : ℝ, C = 5 ∧ 0 < C ∧
    ∀ (k r : ℕ) (A ε : ℝ), 1 ≤ k → 0 < r → 0 < A → 0 < ε →
      C * A ^ (4 * k + 1) ≤ ε * (r : ℝ) ^ (4 * k) →
      ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (M U : Matrix I I ℂ),
        ‖M - U‖ ≤ C * (r : ℝ) * (A / (r : ℝ)) ^ (4 * k + 1) →
        ‖M - U‖ ≤ ε := by
  refine ⟨5, rfl, by norm_num, ?_⟩
  intro k r A ε _hk hr _hA _hε hbudget I _ _ _ M U hdeficit
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  calc ‖M - U‖ ≤ 5 * (r : ℝ) * (A / (r : ℝ)) ^ (4 * k + 1) := hdeficit
    _ = 5 * A ^ (4 * k + 1) / (r : ℝ) ^ (4 * k) := by
        rw [div_pow]
        field_simp
        ring
    _ ≤ ε := by
        rw [div_le_iff₀ (pow_pos hrpos _)]
        linarith [hbudget]

/-- The real-power repetition threshold bounds the assumed operator deficit by the error tolerance.
For the uniform factor `C = 5`, the threshold `A ^ (1 + 1 / (4k)) / (ε / C) ^ (1 / (4k)) ≤ r`
is (64) in [ChildsWiebe2012], Lemma 11. The assumed deficit estimate is
`‖M - U‖ ≤ C * r * (A / r) ^ (4 * k + 1)`. -/
theorem retry_error_budget_rpow : ∃ C : ℝ, C = 5 ∧ 0 < C ∧
    ∀ (k r : ℕ) (A ε : ℝ), 1 ≤ k → 0 < r → 0 < A → 0 < ε →
      A ^ ((1 : ℝ) + 1 / (4 * k)) / (ε / C) ^ ((1 : ℝ) / (4 * k)) ≤ (r : ℝ) →
      ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (M U : Matrix I I ℂ),
        ‖M - U‖ ≤ C * (r : ℝ) * (A / (r : ℝ)) ^ (4 * k + 1) →
        ‖M - U‖ ≤ ε := by
  obtain ⟨C, hCeq, hC, h⟩ := retry_error_budget
  refine ⟨C, hCeq, hC, ?_⟩
  intro k r A ε hk hr hA hε hbudget I _ _ _ M U hdeficit
  apply h k r A ε hk hr hA hε _ M U hdeficit
  have hεC : 0 < ε / C := div_pos hε hC
  have hexp : A ^ ((1 : ℝ) + 1 / (4 * k))
      = A * A ^ ((1 : ℝ) / (4 * k)) := by
    rw [add_comm, Real.rpow_add hA, Real.rpow_one, mul_comm]
  rw [hexp, mul_div_assoc, ← Real.div_rpow hA.le hεC.le] at hbudget
  have hrewrite : A / (ε / C) = C * A / ε := by
    rw [div_div_eq_mul_div, mul_comm A C]
  rw [hrewrite] at hbudget
  have h2 : A * (C * A / ε) ^ ((1 : ℝ) / (4 * k)) ≤ (r : ℝ) := hbudget
  have h3 : (A * (C * A / ε) ^ ((1 : ℝ) / (4 * k))) ^ (4 * k)
      ≤ (r : ℝ) ^ (4 * k) := pow_le_pow_left₀ (by positivity) h2 (4 * k)
  have h4 : (A * (C * A / ε) ^ ((1 : ℝ) / (4 * k))) ^ (4 * k)
      = A ^ (4 * k) * (C * A / ε) := by
    rw [mul_pow]
    congr 1
    have hkn : (4 * k : ℕ) ≠ 0 := by omega
    have hinv : (1 : ℝ) / (4 * k) = ((4 * k : ℕ) : ℝ)⁻¹ := by
      rw [Nat.cast_mul, Nat.cast_ofNat, inv_eq_one_div]
    rw [hinv, Real.rpow_inv_natCast_pow (by positivity) hkn]
  rw [h4] at h3
  have h5 : C * A ^ (4 * k + 1) = A ^ (4 * k) * (C * A / ε) * ε := by
    field_simp
    ring
  rw [h5, mul_comm ε ((r : ℝ) ^ (4 * k))]
  exact mul_le_mul_of_nonneg_right h3 hε.le

end Qatlib.Papers.HamLCUSim12.FullSimulation
