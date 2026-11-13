/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabEquiv04.MainResults.Model.ComputationDefs
import Qatlib.Papers.AdiabEquiv04.MainResults.Model.EigenRayleigh
import Qatlib.Papers.AdiabEquiv04.MainResults.Model.SpectralBasics

/-!
# Spectral perturbation statements

The module defines the propositions corresponding to the perturbation and three-local
conclusions in Lemmas 3.17–3.19 of [AharonovEtAl2007Adiabatic]. It also proves an elementary
Rayleigh lower bound, vanishing of a compressed penalty matrix, and the ground-energy upper
bound `lemma_3_17_ground_upper`.

## Main statements

* `lemma_3_17_perturbationStatement`: the energy and ground-vector overlap assertions.
* `lemma_3_17_ground_upper`: the upper bound from restriction to the penalty kernel.
* `lemma_3_18_gap_three_localStatement` and `lemma_3_19_final_ground_closeStatement`: the gap
  and final-state propositions.

## References

* [Aharonov et al., 2007][AharonovEtAl2007Adiabatic]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.AdiabEquiv04.MainResults.Perturbation

open Qatlib.Papers.AdiabEquiv04.MainResults.Model

/-- If the absolute Rayleigh expression of `H₁` is bounded by `K` on normalized vectors, adding
`H₁` lowers the Rayleigh expression of `H₂` by at most `K` on such vectors. See
[AharonovEtAl2007Adiabatic]. -/
theorem rayleigh_add_lower_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (H₁ H₂ : Hamiltonian ι) (K : ℝ)
    (hK : ∀ ψ : Vector ι, IsNormalized ψ → |rayleigh H₁.mat ψ| ≤ K)
    (ψ : Vector ι) (hψ : IsNormalized ψ) :
    rayleigh (H₁.add H₂).mat ψ ≥ rayleigh H₂.mat ψ - K := by
  have h1 : rayleigh (H₁.add H₂).mat ψ = rayleigh H₁.mat ψ + rayleigh H₂.mat ψ :=
    rayleigh_add _ _ _
  rw [h1]
  have hψK := hK ψ hψ
  have hle : -(K) ≤ rayleigh H₁.mat ψ := by
    have := neg_abs_le (rayleigh H₁.mat ψ)
    linarith
  linarith

/-- If `H₂` annihilates every vector in the range of `V`, then its compression `Vᴴ * H₂.mat * V`
is zero. See [AharonovEtAl2007Adiabatic]. -/
theorem hzero_of_hvan {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
    [DecidableEq σ] (V : Matrix ι σ ℂ) (H₂ : Hamiltonian ι)
    (hvan : ∀ a : Vector σ, H₂.mat *ᵥ (V *ᵥ a) = 0) :
    Vᴴ * H₂.mat * V = 0 := by
  have hMV : H₂.mat * V = 0 := by
    ext i j
    have hcol : V *ᵥ basisKet j = fun i => V i j := by
      ext i
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
      · simp [basisKet]
      · intro k _ hk; simp [basisKet, if_neg hk]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    have h := congrFun (hvan (basisKet j)) i
    rw [hcol] at h
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  rw [Matrix.mul_assoc, hMV, Matrix.mul_zero]

/-- **Statement only — not proved in Qatlib.** The statement of Lemma 3.17: under the specified isometry, kernel, penalty, and bilinear
bounds, the first two energies obey the stated perturbation estimates and a positive
restricted gap gives a ground-vector overlap bound. See [AharonovEtAl2007Adiabatic]. -/
def lemma_3_17_perturbationStatement : Prop :=
  ∀ {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (V : Matrix ι σ ℂ) (hV : Vᴴ * V = 1)
    (H₁ H₂ : Hamiltonian ι) (J K : ℝ) (hJ : 2 * K < J) (hK0 : 0 ≤ K)
    (hcardS : 2 ≤ Fintype.card σ) (hcard : 2 ≤ Fintype.card ι)
    (hvan : ∀ a : Vector σ, H₂.mat *ᵥ (V *ᵥ a) = 0)
    (hpos : ∀ ψ : Vector ι, IsNormalized ψ → Vᴴ *ᵥ ψ = 0 →
      J ≤ rayleigh H₂.mat ψ)
    (hKoff : ∀ x y : Vector ι,
      |((star x) ⬝ᵥ (H₁.mat *ᵥ y)).re| ≤
        K * Real.sqrt (normSq x) * Real.sqrt (normSq y)),
    (groundEnergy (H₁.add H₂) (by omega) ≥
        groundEnergy (restrict V H₁ hV) (by omega) - K ^ 2 / (J - 2 * K) ∧
      groundEnergy (H₁.add H₂) (by omega) ≤ groundEnergy (restrict V H₁ hV) (by omega) ∧
      secondLowestEnergy (H₁.add H₂) hcard ≥
        secondLowestEnergy (restrict V H₁ hV) hcardS - K ^ 2 / (J - 2 * K)) ∧
    (secondLowestEnergy (restrict V H₁ hV) hcardS >
        groundEnergy (restrict V H₁ hV) (by omega) →
      ∀ (ξ : Vector σ) (ξ' : Vector ι),
        IsGroundVector (restrict V H₁ hV) ξ →
        IsGroundVector (H₁.add H₂) ξ' →
        Complex.normSq (innerVec (V *ᵥ ξ) ξ') ≥
          1 - K ^ 2 / ((secondLowestEnergy (restrict V H₁ hV) hcardS -
            groundEnergy (restrict V H₁ hV) (by omega)) * (J - 2 * K)))

/-- Under the stated perturbation hypotheses, the ground energy of `H₁ + H₂` is at most that of
the restriction of `H₁` to the isometric range annihilated by `H₂`. See
[AharonovEtAl2007Adiabatic]. -/
theorem lemma_3_17_ground_upper {ι σ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ]
    (V : Matrix ι σ ℂ) (hV : Vᴴ * V = 1)
    (H₁ H₂ : Hamiltonian ι) (J K : ℝ) (_hJ : 2 * K < J) (_hK0 : 0 ≤ K)
    (_hcardS : 2 ≤ Fintype.card σ) (_hcard : 2 ≤ Fintype.card ι)
    (hvan : ∀ a : Vector σ, H₂.mat *ᵥ (V *ᵥ a) = 0)
    (_hpos : ∀ ψ : Vector ι, IsNormalized ψ → Vᴴ *ᵥ ψ = 0 → J ≤ rayleigh H₂.mat ψ)
    (_hKoff : ∀ x y : Vector ι,
      |((star x) ⬝ᵥ (H₁.mat *ᵥ y)).re| ≤
        K * Real.sqrt (normSq x) * Real.sqrt (normSq y)) :
    groundEnergy (H₁.add H₂) (by omega) ≤
      groundEnergy (restrict V H₁ hV) (by omega) :=
  ground_add_le_ground_restrict V hV H₁ H₂ (hzero_of_hvan V H₂ hvan) (by omega) (by omega)

/-- **Statement only — not proved in Qatlib.** The statement that, for each circuit and positive `ε`, a positive constant bounds the gap of
`Hpath3` below by `c / (L + 1)³` uniformly on `[0, 1]`, with penalty `ε⁻² L⁶`. See
[AharonovEtAl2007Adiabatic]. -/
def lemma_3_18_gap_three_localStatement : Prop :=
  ∀ (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) (ε : ℝ), 0 < ε →
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      GapAtLeast (Hpath3 n L hL2 gates ((ε ^ 2)⁻¹ * (L : ℝ) ^ 6) s)
        (c / ((L : ℝ) + 1) ^ 3)

/-- **Statement only — not proved in Qatlib.** The statement that the final Hamiltonian of `Hpath3`, with penalty `ε⁻² L⁶`, possesses a
ground vector within `PhaseClose` tolerance `ε` of the history state for every positive `ε`.
See [AharonovEtAl2007Adiabatic]. -/
def lemma_3_19_final_ground_closeStatement : Prop :=
  ∀ (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) (ε : ℝ), 0 < ε →
    ∃ ψ : Vector (TotalBasis n L),
      IsGroundVector (Hpath3 n L hL2 gates ((ε ^ 2)⁻¹ * (L : ℝ) ^ 6) 1) ψ ∧
      PhaseClose ψ (historyState (L := L) gates) ε

end Qatlib.Papers.AdiabEquiv04.MainResults.Perturbation
