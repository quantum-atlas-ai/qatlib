/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Tactic
import Qatlib.Papers.QDecoding25.MainResults.DecodingModel

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Typical sets, entropy and the Fourier transform (arXiv:2509.24796v2, §2)

This module states the paper's information-theoretic layer:

* Proposition 1 (p. 8) — the discrete Hirschman uncertainty principle;
* Lemma 1 (p. 11) — cardinality bounds for a typical set, `(1-δ)/B ≤ |T| ≤ 1/A`;
* Proposition 4 (p. 17) — the Holevo capacity of a classical-quantum pure-state
  channel equals `H_q(|ĝ|²)`;
* Proposition 6 (p. 17) — for a nice family of typical sets the entropy per
  symbol converges to `H`;
* Lemma 14 (p. 34) — existence and uniqueness of the exponential weight
  parameter `λ` attached to a metric on `F_q`.

Source: arXiv:2509.24796v2 (4 Feb 2026), text extracted from
`assets/2509.24796.txt`; statement numbers and page numbers below refer to
that version.
-/

namespace Qatlib.Papers.QDecoding25.MainResults

open scoped BigOperators ComplexOrder
open Filter Topology Matrix

/-! ## The Fourier transform on `F_q` (Definition 3, p. 8) -/

/-- The Fourier coefficient `ĝ(y) = q^{-1/2} ∑_x g(x) χ(x y)` of a complex
function on `F_q`, Definition 3 (p. 8). -/
noncomputable def fourierCoeff {F : Type*} [Field F] [Fintype F] (χ : AddChar F ℂ)
    (g : F → ℂ) (y : F) : ℂ :=
  (↑((Real.sqrt (Fintype.card F : ℝ))⁻¹) : ℂ) * ∑ x, χ (x * y) * g x

/-- The product character `χ_y(x) = ∏_i χ(y_i x_i)` on `F_q^n`; it is the
character used for the `n`-dimensional Fourier transform of the noise law
`p = |f̂|²` (§2.5, p. 14). -/
noncomputable def vecChar {F : Type*} [Field F] (n : ℕ) (χ : AddChar F ℂ)
    (y x : FVec F n) : ℂ :=
  ∏ i, χ (y i * x i)

/-- The `n`-fold Fourier transform of `f : F_q^n → ℂ` at `y`:
`f̂(y) = q^{-n/2} ∑_x χ_y(x) f(x)` (§2.5, p. 14). -/
noncomputable def vecFourier {F : Type*} [Field F] [Fintype F] (n : ℕ)
    (χ : AddChar F ℂ) (f : FVec F n → ℂ) (y : FVec F n) : ℂ :=
  (↑((Real.sqrt (Fintype.card F : ℝ)) ^ n)⁻¹ : ℂ) *
    ∑ x, vecChar n χ y x * f x

/-! ## Proposition 1: discrete Hirschman uncertainty (p. 8) -/

/-! ## Lemma 1: cardinality bounds for typical sets (p. 11) -/

/-- **Lemma 1 (p. 11), size of a typical set.**  For a distribution `p` on a
finite alphabet and positive bounds `A, B`, the typical set
`T = {y : A ≤ p(y) ≤ B}` satisfies
`(1 - δ) / B ≤ |T| ≤ 1 / A`, where `δ = 1 - p(T)` is the defect. -/
theorem lemma1_typicalSet_card {α : Type*} [Fintype α] (p : Mass α) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) :
    (1 - p.defect (p.typicalSet A B)) / B ≤ ((p.typicalSet A B).card : ℝ) ∧
      ((p.typicalSet A B).card : ℝ) ≤ 1 / A := by
  classical
  set T := p.typicalSet A B
  have hmem : ∀ y ∈ T, A ≤ p.mass y ∧ p.mass y ≤ B := by
    intro y hy
    simp only [T, Mass.typicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact hy
  have hsum_eq : ∑ y ∈ T, p.mass y = 1 - p.defect T := by
    simp [Mass.defect]
  have hsum_le_one : ∑ y ∈ T, p.mass y ≤ 1 := by
    rw [← p.total]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun x _ _ => p.nonneg x)
  have hcard_mul_B : (T.card : ℝ) * B ≥ ∑ y ∈ T, p.mass y := by
    calc ∑ y ∈ T, p.mass y ≤ ∑ y ∈ T, B :=
          Finset.sum_le_sum fun y hy => (hmem y hy).2
      _ = (T.card : ℝ) * B := by simp [Finset.sum_const, nsmul_eq_mul]
  have hcard_mul_A : (T.card : ℝ) * A ≤ ∑ y ∈ T, p.mass y := by
    calc (T.card : ℝ) * A = ∑ y ∈ T, A := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ T, p.mass y := Finset.sum_le_sum fun y hy => (hmem y hy).1
  constructor
  · rw [div_le_iff₀ hB]
    calc 1 - p.defect T = ∑ y ∈ T, p.mass y := hsum_eq.symm
      _ ≤ (T.card : ℝ) * B := hcard_mul_B
  · rw [le_div_iff₀ hA]
    calc (T.card : ℝ) * A ≤ ∑ y ∈ T, p.mass y := hcard_mul_A
      _ ≤ 1 := hsum_le_one

/-! ## Von Neumann entropy and the Holevo capacity (§2.5, Proposition 4, p. 17) -/

/-- The von Neumann entropy `S(ρ) = -∑_i λ_i log_q λ_i` of a Hermitian matrix,
written through its (real) eigenvalues; used to state the Holevo capacity
information-theoretically (`q = 2` is the qubit case). -/
noncomputable def vnEntropy (q : ℝ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) : ℝ :=
  -∑ i, hM.eigenvalues i * (Real.log (hM.eigenvalues i) / Real.log q)

/-- The outer product `|ψ⟩⟨ψ|` of a complex vector. -/
noncomputable def outerVec {ι : Type*} (ψ : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun a b => ψ a * star (ψ b)

/-- The pure state `|ψ_α⟩ = ∑_u g(u) |α + u⟩` of the classical-quantum channel
of §2.5 (p. 14), as the density matrix `|ψ_α⟩⟨ψ_α|`. -/
noncomputable def channelState {F : Type*} [Field F] [Fintype F] (g : F → ℂ)
    (α : F) : Matrix F F ℂ :=
  outerVec fun β => g (β - α)

/-- The Holevo capacity `C_χ = sup_p S(∑_α p(α) ρ_α)` of the classical-quantum
channel with states `ρ_α = |ψ_α⟩⟨ψ_α|`, eq. (4) and Proposition 4 (p. 17). -/
noncomputable def holevoCapacity {F : Type*} [Field F] [Fintype F] (g : F → ℂ) : ℝ := by
  classical
  exact sSup {s : ℝ | ∃ (p : F → ℝ) (hp : ∀ a, 0 ≤ p a) (h1 : ∑ a, p a = 1)
      (hH : (∑ a, (p a : ℂ) • channelState g a).IsHermitian),
      s = vnEntropy (Fintype.card F : ℝ) (∑ a, (p a : ℂ) • channelState g a) hH}

/-! ## Proposition 6: uniqueness of the entropy rate (p. 17) -/

/-! ## Lemma 14: the exponential weight of a metric (p. 34) -/

end Qatlib.Papers.QDecoding25.MainResults
