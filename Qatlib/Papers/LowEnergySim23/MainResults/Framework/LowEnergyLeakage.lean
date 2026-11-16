/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LowEnergySim23.MainResults.Framework.Core

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5 and Lemma 6 — imaginary-time growth and low-energy leakage

This premise-repaired module proves only the commuting-observable special
case of the displayed estimates.  The Hamiltonian structure does not encode
locality or relate `g` to `H`, so it cannot support the general paper bounds.
Commutation expresses exact conservation and is satisfied, for example, by
`A = 1`; it does not assume either desired bound.  Growth also needs `0 ≤ R_A`.

Fixed paper version: arXiv:2312.08867v3 (Quantum **8**, 1409 (2024)).
The fixed PDF has Lemma 5 on p.27 and Lemma 6 on p.28, §3.3.
The authors are Weiyuan Gong, Shuo Zhou and Tongyang Li.

Lemma 5: for a Hamiltonian with 2-local terms whose interaction on each qubit is
bounded by strength `g`, for any `0 ≤ s ≤ 1/(2g)`,
`‖e^{sH} A e^{-sH}‖ ≤ ‖A‖ (1-2gs)^{-R_A/(2g)}`, where `R_A` bounds the sum
of strengths of the Hamiltonian terms that do not commute with `A` (p.27).
That local-term definition is not represented by the free scalar parameter below.

Lemma 6: with `λ := (4g)^{-1}`,
`‖Π_{>Λ'} A Π_{≤Λ}‖ ≤ ‖A‖ · e^{-λ(Λ'-Λ-2R_A)}`.

**Formalization boundary.** At `s = 1/(2g)`, Lean's totalized real power makes
the displayed right-hand side zero when `R_A > 0`. For a nonzero commuting
observable the left-hand side remains `‖A‖ > 0`. The source's singular endpoint
is therefore not interpreted as a finite real bound here; the contract uses
`0 ≤ s < 1/(2g)`, which is the range used in the proof of Lemma 6
(`s = λ = 1/(4g) = (1/2)·(1/(2g))`).  This is documented rather than silently
weakened.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.LowEnergySim23.MainResults.Framework
open Qatlib.Papers.LowEnergySim23.MainResults.Framework

/-- Hermitian Hamiltonian data with a positive scale `g`.  This structure does
not encode locality or relate `g` to the Hamiltonian's interaction strength. -/
structure TwoLocalHamiltonian (D : ℕ) where
  /-- the Hamiltonian -/
  H : Op D
  /-- Hermiticity of `H` -/
  hermitian : H.IsHermitian
  /-- A positive scale parameter, without a certified local-interaction interpretation. -/
  g : ℝ
  g_pos : 0 < g

/-- The commuting-observable special case of Lemma 5 (p.27): imaginary-time
conjugation fixes `A`, and the power factor is at least one for nonnegative
`R_A` and `0 ≤ s < 1/(2g)`. -/
theorem imaginary_time_growth_bound {D : ℕ} (M : TwoLocalHamiltonian D) (A : Op D)
    (R_A : ℝ) (hR : 0 ≤ R_A) (hA : Commute M.H A)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1 / (2 * M.g)) :
    ‖imaginaryConjugate s M.H A‖ ≤
      ‖A‖ * Real.rpow (1 - 2 * M.g * s) (-(R_A / (2 * M.g))) := by
  have hcomm : Commute A (s • M.H) := hA.symm.smul_right s
  have hconj : imaginaryConjugate s M.H A = A := by
    let : NormedAlgebra ℚ (Op D) := .restrictScalars ℚ ℂ (Op D)
    simpa [imaginaryConjugate] using
      (hcomm.neg_right.exp_neg_mul_mul_exp_eq_self)
  rw [hconj]
  have hg : 0 < 2 * M.g := mul_pos (by norm_num) M.g_pos
  have hbase : 0 < 1 - 2 * M.g * s := by
    exact sub_pos.mpr (by simpa [mul_comm] using (lt_div_iff₀ hg).mp hs1)
  have hbase1 : 1 - 2 * M.g * s ≤ 1 :=
    sub_le_self _ (mul_nonneg hg.le hs0)
  have hexp : -(R_A / (2 * M.g)) ≤ 0 := neg_nonpos.mpr (div_nonneg hR hg.le)
  have hpow := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hbase hbase1 hexp
  simpa using mul_le_mul_of_nonneg_left hpow (norm_nonneg A)

/-- The commuting-observable special case of Lemma 6 (p.28): commutation
forces zero leakage between ordered spectral windows, which implies the
nonnegative exponential upper bound. -/
theorem low_energy_leakage_bound {D : ℕ} (M : TwoLocalHamiltonian D) (A : Op D)
    (R_A Λ Λ' : ℝ) (hΛ : Λ ≤ Λ') (hA : Commute M.H A) :
    ‖highEnergyProjector M.H M.hermitian Λ' * A * lowEnergyProjector M.H M.hermitian Λ‖ ≤
      ‖A‖ * Real.exp (-(4 * M.g)⁻¹ * (Λ' - Λ - 2 * R_A)) := by
  classical
  let U : Op D := M.hermitian.eigenvectorUnitary
  let E : Op D := lowEnergyIndicator M.H M.hermitian Λ
  let E' : Op D := lowEnergyIndicator M.H M.hermitian Λ'
  have hEE : E' * E = E := by
    simp only [E, E', lowEnergyIndicator, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : M.hermitian.eigenvalues i ≤ Λ
    · simp [hi, le_trans hi hΛ]
    · simp [hi]
  have hPP : lowEnergyProjector M.H M.hermitian Λ' *
      lowEnergyProjector M.H M.hermitian Λ =
      lowEnergyProjector M.H M.hermitian Λ := by
    rw [lowEnergyProjector_eq, lowEnergyProjector_eq]
    change U * E' * star U * (U * E * star U) = U * E * star U
    have hUU : star U * U = 1 := star_eigenvectorUnitary_mul M.H M.hermitian
    calc
      U * E' * star U * (U * E * star U) = U * (E' * (star U * U) * E) * star U := by
        simp only [Matrix.mul_assoc]
      _ = U * E * star U := by rw [hUU, mul_one, hEE]
  have hAP := commute_lowEnergyProjector_of_commute M.H A M.hermitian Λ hA.symm.eq
  have hzero : highEnergyProjector M.H M.hermitian Λ' * A *
      lowEnergyProjector M.H M.hermitian Λ = 0 := by
    rw [highEnergyProjector, Matrix.mul_assoc, hAP, ← Matrix.mul_assoc,
      sub_mul, one_mul, hPP, sub_self, zero_mul]
  rw [hzero, norm_zero]
  positivity

/-- A nonzero one-dimensional Hamiltonian and identity observable satisfy the repaired
growth premises at positive time `1/4`, scale one and positive support parameter one. -/
theorem identity_growth_example :
    ‖imaginaryConjugate (1 / 4) (1 : Op 1) 1‖ ≤
      ‖(1 : Op 1)‖ * Real.rpow (1 - 2 * 1 * (1 / 4)) (-(1 / (2 * 1))) := by
  let M : TwoLocalHamiltonian 1 :=
    ⟨1, Matrix.isHermitian_one, 1, by norm_num⟩
  exact imaginary_time_growth_bound M 1 1 (by norm_num) (Commute.one_right _)
    (by norm_num) (by norm_num [M])

end Qatlib.Papers.LowEnergySim23.MainResults.Framework
