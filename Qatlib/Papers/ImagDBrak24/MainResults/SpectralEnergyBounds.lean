/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ImagDBrak24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Spectral energy/variance bounds — Lemma 3 and Lemma 12

Fixed paper version: arXiv:2412.04554v2 (2 Jul 2025).

The paper writes `Ĥ = Σ_j λ_j |λ_j⟩⟨λ_j|` with `λ_0 = 0`, eigenvalues ordered
increasingly, and the initial/target state `|Ω⟩ = Σ_j c_j |λ_j⟩`. In the
eigen-basis the state is the vector `ψ`, the ground-state fidelity is
`p_0 = ‖ψ_0‖² = 1 - ε`, the expected energy is
`E = Σ_j λ_j p_j` and the variance is `V = Σ_j λ_j² p_j - E²`, with
`p_j = ‖ψ_j‖²`.

* `lemma3_energyVarianceBounds` — Eq. (30): `E ≥ λ_1 ε` and `V ≤ λ_{d-1}² ε`.
* `lemma12_energyOverVariance` — Eq. (102): `E / V ≥ 1/‖Ĥ‖`.

Proofs follow the paper's Supplemental Material Sec. I item 4 (Lemma 3,
p.12, Eq. (31)) and Sec. III C (Lemma 12, p.20, Eq. (103)-(104)).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.ImagDBrak24.MainResults

open Matrix
open scoped BigOperators ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lemma 3 (Eq. (30), p.12): for a Hamiltonian in spectral form `diag λ` with
`λ_0 = 0`, `0 ≤ λ_j ≤ Λ` and `λ_1 ≤ λ_j` for every `j ≠ 0`, any state with
ground-state fidelity `p_0 = 1 - ε` satisfies
`E ≥ λ_1 ε` and `V ≤ Λ² ε`. -/
theorem lemma3_energyVarianceBounds
    (lam : ι → ℝ) (zero : ι) (Λ mu ε : ℝ)
    (h0 : lam zero = 0)
    (hnonneg : ∀ i, 0 ≤ lam i)
    (hupper : ∀ i, lam i ≤ Λ)
    (hgap : ∀ i, i ≠ zero → mu ≤ lam i)
    (ψ : ι → ℂ) (hψ : normSq ψ = 1)
    (hε : weight ψ zero = 1 - ε) :
    expectedEnergy lam ψ ≥ mu * ε ∧ energyVariance lam ψ ≤ Λ ^ 2 * ε := by
  have hΛ0 : 0 ≤ Λ := (hnonneg zero).trans (hupper zero)
  -- total weight is 1, so the non-ground weight is `ε`
  have hsum : ∑ i ∈ Finset.univ.erase zero, weight ψ i = ε := by
    have h := Finset.sum_erase_add (s := Finset.univ) (f := weight ψ) (a := zero)
      (Finset.mem_univ zero)
    rw [sum_weight, hψ] at h
    linarith [hε, h]
  -- energy restricted to the non-ground components
  have hE : expectedEnergy lam ψ = ∑ i ∈ Finset.univ.erase zero, lam i * weight ψ i := by
    unfold expectedEnergy
    exact (Finset.sum_erase (s := Finset.univ) (f := fun i => lam i * weight ψ i)
      (a := zero) (by simp [h0])).symm
  have hS2 : secondMoment lam ψ = ∑ i ∈ Finset.univ.erase zero, lam i ^ 2 * weight ψ i := by
    unfold secondMoment
    exact (Finset.sum_erase (s := Finset.univ) (f := fun i => lam i ^ 2 * weight ψ i)
      (a := zero) (by simp [h0])).symm
  constructor
  · rw [hE]
    calc
      ∑ i ∈ Finset.univ.erase zero, lam i * weight ψ i
          ≥ ∑ i ∈ Finset.univ.erase zero, mu * weight ψ i := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_right (hgap i (Finset.ne_of_mem_erase hi))
              (weight_nonneg ψ i)
      _ = mu * ε := by
            rw [← Finset.mul_sum, hsum]
  · have hVle : energyVariance lam ψ ≤ secondMoment lam ψ := by
      unfold energyVariance
      linarith [sq_nonneg (expectedEnergy lam ψ)]
    refine hVle.trans ?_
    rw [hS2]
    calc
      ∑ i ∈ Finset.univ.erase zero, lam i ^ 2 * weight ψ i
          ≤ ∑ i ∈ Finset.univ.erase zero, Λ ^ 2 * weight ψ i := by
            apply Finset.sum_le_sum
            intro i _
            apply mul_le_mul_of_nonneg_right _ (weight_nonneg ψ i)
            exact pow_le_pow_left₀ (hnonneg i) (hupper i) 2
      _ = Λ ^ 2 * ε := by
            rw [← Finset.mul_sum, hsum]

/-- Lemma 12 (Eq. (102), p.20): under the same spectral hypotheses, with
positive variance, the energy-over-variance ratio obeys `E / V ≥ 1/‖Ĥ‖`
with `Λ = ‖Ĥ‖` the spectral radius. -/
theorem lemma12_energyOverVariance
    (lam : ι → ℝ) (zero : ι) (Λ : ℝ)
    (h0 : lam zero = 0)
    (hnonneg : ∀ i, 0 ≤ lam i)
    (hupper : ∀ i, lam i ≤ Λ)
    (hΛpos : 0 < Λ)
    (ψ : ι → ℂ) (hψ : normSq ψ = 1)
    (hVpos : 0 < energyVariance lam ψ) :
    1 / Λ ≤ expectedEnergy lam ψ / energyVariance lam ψ := by
  -- `E - V/Λ ≥ 0`, proved by non-negativity of each spectral term
  have hE : expectedEnergy lam ψ = ∑ i ∈ Finset.univ.erase zero, lam i * weight ψ i := by
    unfold expectedEnergy
    exact (Finset.sum_erase (s := Finset.univ) (f := fun i => lam i * weight ψ i)
      (a := zero) (by simp [h0])).symm
  have hS2 : secondMoment lam ψ = ∑ i ∈ Finset.univ.erase zero, lam i ^ 2 * weight ψ i := by
    unfold secondMoment
    exact (Finset.sum_erase (s := Finset.univ) (f := fun i => lam i ^ 2 * weight ψ i)
      (a := zero) (by simp [h0])).symm
  have hΛne : Λ ≠ 0 := ne_of_gt hΛpos
  have hterm : ∑ i ∈ Finset.univ.erase zero, lam i * weight ψ i
      - (1 / Λ) * ∑ i ∈ Finset.univ.erase zero, lam i ^ 2 * weight ψ i
      = ∑ i ∈ Finset.univ.erase zero, lam i * (1 - lam i / Λ) * weight ψ i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hΛne]
  have hnonneg_sum : 0 ≤ ∑ i ∈ Finset.univ.erase zero, lam i * (1 - lam i / Λ) * weight ψ i := by
    apply Finset.sum_nonneg
    intro i hi
    have hli : 0 ≤ lam i := hnonneg i
    have hle : lam i ≤ Λ := hupper i
    have hfactor : 0 ≤ 1 - lam i / Λ := by
      rw [sub_nonneg, div_le_one hΛpos]
      exact hle
    exact mul_nonneg (mul_nonneg hli hfactor) (weight_nonneg ψ i)
  -- therefore `V ≤ Λ E`
  have hVE : energyVariance lam ψ ≤ Λ * expectedEnergy lam ψ := by
    have hVle : energyVariance lam ψ ≤ secondMoment lam ψ := by
      unfold energyVariance
      linarith [sq_nonneg (expectedEnergy lam ψ)]
    have hS2le : secondMoment lam ψ ≤ Λ * expectedEnergy lam ψ := by
      rw [hS2, hE, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hli : 0 ≤ lam i := hnonneg i
      have hle : lam i ≤ Λ := hupper i
      have hw : 0 ≤ weight ψ i := weight_nonneg ψ i
      have hpos : 0 ≤ lam i * (Λ - lam i) := mul_nonneg hli (by linarith)
      have hkey : Λ * (lam i * weight ψ i) - lam i ^ 2 * weight ψ i
          = weight ψ i * (lam i * (Λ - lam i)) := by ring
      nlinarith [mul_nonneg hw hpos]
    linarith
  -- divide through by `V > 0` and `Λ > 0`
  rw [le_div_iff₀ hVpos, div_mul_eq_mul_div, one_mul, div_le_iff₀ hΛpos]
  nlinarith [hVE]

end Qatlib.Papers.ImagDBrak24.MainResults
