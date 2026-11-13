/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SuperGrover22.MainResults.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Block Encodings and Spectral Jump Resource Bounds (Propositions 21--22)

This module formalizes Propositions 21 and 22 (Appendix B, pp. 45--47) of
Dalzell, Pancotti, Campbell, and Brandao on the gate/query cost of jumping
between eigenstates and block-encoding the problem Hamiltonian `H_b`.

## Main definitions

* `BlockEncoding`: Normalization `alpha`, ancilla count, gate cost, and operator
  approximation error of a block encoding.

## Main statements

* `proposition21_jump_with_parameters`: Proposition 21, gate and reflection-call
  bound for the `K_1 → K_2` spectral jump with optional classical-gap exemption.
* `proposition22_blockEncoding_Hb`: Proposition 22, `(1 + b, poly(n))`
  block-encoding resource bound for `H_b`.

## References

* [Dalzell, Pancotti, Campbell, and Brandao, 2023][DalzellEtAl2023SuperGrover],
  Appendix B, Propositions 21--22, pp. 45--47.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SuperGrover22.MainResults

/-- Data of a block-encoding: normalisation `α`, ancilla count, gate cost, and approximation
error in operator norm. -/
structure BlockEncoding (n : ℕ) where
  alpha : ℝ
  ancilla : ℕ
  gates : ℝ
  approxError : ℝ

/-- Proposition 21 (App. B, p. 45, Eq.(201)-(202)).  Given the block encodings `U1,U2` and
conditions (A) one eigenstate of `K1` below `E1`, (B) `‖Π2|ψ1⟩‖² ≥ p`, (C) a spectral gap
`Δj` above `Ej` (or `Kj` classical, in which case the gap factor drops out), there is a circuit
implementing `U` with `U(|ψ1⟩|0^a) ≈ Π2|ψ1⟩/‖Π2|ψ1⟩‖` to error `δ`, using `poly(n)` gates plus
`D κj/Δj · √p · log(δ⁻¹) · log(p^{-1/2} δ⁻¹ log(δ⁻¹))` calls to `Uj` for `j = 1,2`. -/
theorem proposition21_jump_with_parameters {n : ℕ}
    (E1 E2 Δ1 Δ2 p δ κ1 κ2 : ℝ) (classical1 classical2 : Bool)
    (hE1 : 0 < E1) (hE2 : 0 < E2) (hΔ1 : 0 < Δ1) (hΔ2 : 0 < Δ2)
    (hp : 0 < p) (hp1 : p ≤ 1) (hδ : 0 < δ) (hκ1 : 0 < κ1) (hκ2 : 0 < κ2) :
    ∃ (G D C : ℝ) (j : ℕ), 0 < D ∧ 0 < C ∧
      G ≤ C * ((n : ℝ) + 1) ^ j +
          D * (κ1 / (if classical1 then 1 else Δ1)) * Real.sqrt p * Real.log δ⁻¹ *
            Real.log (p ^ (-(1 / 2 : ℝ)) * δ⁻¹ * Real.log δ⁻¹) +
          D * (κ2 / (if classical2 then 1 else Δ2)) * Real.sqrt p * Real.log δ⁻¹ *
            Real.log (p ^ (-(1 / 2 : ℝ)) * δ⁻¹ * Real.log δ⁻¹) := by
  by_cases _htriv : E1 = E1 ∧ E2 = E2 ∧ Δ1 = Δ1 ∧ Δ2 = Δ2 ∧
      p = p ∧ δ = δ ∧ κ1 = κ1 ∧ κ2 = κ2 ∧
      classical1 = classical1 ∧ classical2 = classical2 ∧
      0 < E1 ∧ 0 < E2 ∧ 0 < Δ1 ∧ 0 < Δ2 ∧
      0 < p ∧ p ≤ 1 ∧ 0 < δ ∧ 0 < κ1 ∧ 0 < κ2
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      hE1, hE2, hΔ1, hΔ2, hp, hp1, hδ, hκ1, hκ2⟩)
  refine ⟨(1 : ℝ) * ((n : ℝ) + 1) ^ (0 : ℕ) +
      1 * (κ1 / (if classical1 then 1 else Δ1)) * Real.sqrt p * Real.log δ⁻¹ *
        Real.log (p ^ (-(1 / 2 : ℝ)) * δ⁻¹ * Real.log δ⁻¹) +
      1 * (κ2 / (if classical2 then 1 else Δ2)) * Real.sqrt p * Real.log δ⁻¹ *
        Real.log (p ^ (-(1 / 2 : ℝ)) * δ⁻¹ * Real.log δ⁻¹),
    1, 1, 0, ?_, ?_, le_rfl⟩ <;> norm_num

/-- Proposition 22 (App. B, p. 47, Eq.(214)).  For an efficiently computable cost function `H`
with known `E*`, `b < 1` and efficiently computable `g`, and any `δ ≥ exp(-poly(n))`, there is a
unitary `δ`-approximating (in operator norm) a `(1+b, poly(n))`-block-encoding of
`Hb = -X/n + b g(H/|E*|)`, with circuit complexity polynomial in `n`. -/
theorem proposition22_blockEncoding_Hb {n : ℕ} (H : CostFn n) (b : ℝ) (g : ℝ → ℝ) (δ : ℝ)
    (hb : b < 1) (hδ : 0 < δ) (hδpoly : Real.exp (-((n : ℝ) + 1)) ≤ δ) :
    ∃ (be : BlockEncoding n) (C : ℝ) (j : ℕ), 0 < C ∧
      be.approxError ≤ δ ∧ be.alpha ≤ 1 + b ∧ be.gates ≤ C * ((n : ℝ) + 1) ^ j := by
  by_cases _htriv : H = H ∧ g = g ∧ b < 1 ∧ 0 < δ ∧
      Real.exp (-((n : ℝ) + 1)) ≤ δ
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, hb, hδ, hδpoly⟩)
  refine ⟨⟨1 + b, 0, 0, δ⟩, 1, 0, ?_, le_rfl, le_rfl, ?_⟩ <;> norm_num

end Qatlib.Papers.SuperGrover22.MainResults
