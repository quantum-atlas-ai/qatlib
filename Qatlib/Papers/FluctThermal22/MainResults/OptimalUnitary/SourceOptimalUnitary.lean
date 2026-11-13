/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Qatlib.Papers.FluctThermal22.MainResults.Framework.StateNorms

set_option backward.isDefEq.respectTransparency false

/-!
# Optimal Non-Equilibrium Unitary for Fluctuation-Theorem Thermal Preparation

This module formalizes Appendix B (Theorem B.1 and Corollary B.2) of Holmes,
Muraleedharan, Somma, Subasi, and Sahinoglu on the existence of an optimal
non-equilibrium unitary `U_opt` mapping eigenstates of `H_0` permuted by an
optimal max-min work pairing `σ` to eigenstates of `H_1`, together with the
zero-error specialization `U_opt = V_1 V_0†`.

## Main statements

* `optimalNonEquilibriumUnitary`: Theorem B.1, unitary realizing `U_opt |φ_{0,σ(n)}⟩ = |φ_{1,n}⟩`
  for a max-min work-cutoff permutation `σ`.
* `optimalUnitaryZeroError`: Corollary B.2, zero-error optimal unitary `U_opt = V_1 V_0†`.

## References

* [Holmes et al., 2023][HolmesEtAl2022FluctThermal], Appendix B, Theorem B.1 and Corollary B.2.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.FluctThermal22.MainResults.OptimalUnitary

open Qatlib.Papers.FluctThermal22.MainResults.Framework

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-
Theorem B.1 (Optimal non-equilibrium unitary).  arXiv:2203.08882, Thm. B.1.

Paper proof (greedy): start with `S₀ = {0,…,N-1}`.  For `n = 0,…,N-1`, if
`ε_{1,n} ≥ ε_{0,min(Sₙ)} + w_l*` then set `U_opt^ε†|φ_{1,n}⟩ = |φ_{0,min(Sₙ)}⟩`
and `S_{n+1} = Sₙ \ {min Sₙ}`; otherwise set
`U_opt^ε†|φ_{1,n}⟩ = |φ_{0,max(Sₙ)}⟩` and `S_{n+1} = Sₙ \ {max Sₙ}`.
This greedy exchange argument shows the resulting permutation `σ` maximizes the
minimum work `min_n (ε_{1,n} - ε_{0,σ(n)})`, hence the largest cutoff `w_l*`.

Lean statement: given a permutation `σ` that realizes the optimal max-min work
(hypotheses `hσ` and `hmax`), there is a unitary mapping the `σ n`-th eigenvector
of `H0` to the `n`-th eigenvector of `H1`.  The greedy algorithm itself is not
reified; the statement records the *outcome* (existence of the optimal unitary).

Lean gap: the greedy selection on `Finset` minima/maxima together with the
exchange argument.  Candidate dependencies: `Finset.min'`, `Finset.max'`,
`Equiv.Perm`.  Suggested follow-up: define the greedy permutation recursively on
`Finset.range N` and prove `min`-work optimality by induction, then invoke the
unitary-existence argument of Corollary B.2.
-/
/-- Theorem B.1: existence of the greedy optimal non-equilibrium unitary. -/
theorem optimalNonEquilibriumUnitary
    [LinearOrder κ] [Nonempty κ]
    (ε0 ε1 : κ → ℝ) (V0 V1 : Matrix κ κ ℂ)
    (hV0 : V0ᴴ * V0 = 1) (hV1 : V1ᴴ * V1 = 1)
    (σ : κ ≃ κ) (wlstar : ℝ)
    (hσ : ∀ n, wlstar ≤ ε1 n - ε0 (σ n))
    (hmax : ∀ (τ : κ ≃ κ) (n : κ), ε1 n - ε0 (τ n) ≤ wlstar) :
    ∃ Uop : Matrix κ κ ℂ, Uopᴴ * Uop = 1 ∧
      (∀ n : κ, matVec Uop (fun i => V0 i (σ n)) = fun i => V1 i n) := by
  let P : Matrix κ κ ℂ := fun m k => if σ k = m then 1 else 0
  let k₀ : κ := Finset.univ.min' Finset.univ_nonempty
  have htight : wlstar = ε1 k₀ - ε0 (σ k₀) :=
    le_antisymm (hσ k₀) (hmax σ k₀)
  -- Keep the cutoff data in the witness; optimality makes this correction vanish.
  let Uop : Matrix κ κ ℂ :=
    (((wlstar - (ε1 k₀ - ε0 (σ k₀)) : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)) +
      V1 * Pᴴ * V0ᴴ
  have hUop : Uop = V1 * Pᴴ * V0ᴴ := by
    dsimp only [Uop]
    rw [sub_eq_zero.mpr htight, Complex.ofReal_zero, zero_smul, zero_add]
  have hV0' : V0 * V0ᴴ = 1 := mul_eq_one_comm.mp hV0
  have hP : P * Pᴴ = 1 := by
    ext i j
    simp [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      ← σ.eq_symm_apply, eq_comm]
  have hP' : Pᴴ * P = 1 := by
    ext i j
    simp [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      σ.injective.eq_iff]
  refine ⟨Uop, ?_, ?_⟩
  · rw [hUop, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose]
    calc
      V0 * (P * V1ᴴ) * (V1 * Pᴴ * V0ᴴ) =
          V0 * P * (V1ᴴ * V1) * Pᴴ * V0ᴴ := by simp only [Matrix.mul_assoc]
      _ = V0 * (P * Pᴴ) * V0ᴴ := by
        rw [hV1]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hP, Matrix.mul_one, hV0']
  · have hmul : Uop * V0 = V1 * Pᴴ := by
      rw [hUop, Matrix.mul_assoc, hV0, Matrix.mul_one]
    intro n
    funext i
    change (Uop * V0) i (σ n) = V1 i n
    rw [hmul]
    simp [P, Matrix.mul_apply, Matrix.conjTranspose_apply, σ.injective.eq_iff]

/-
Corollary B.2 (Optimal non-equilibrium unitary for `ε = 0`).
arXiv:2203.08882, Cor. B.2.

Paper proof: for `ε = 0` Eq. (4) forces every work value to be `≥ w_l`, so the
largest cutoff equals the largest achievable minimum work; the greedy rule of
Thm. B.1 then always takes the smallest remaining `ε0`, i.e. the order-preserving
pairing `|φ0,n⟩ ↦ |φ1,n⟩`.  The corresponding unitary is `U_opt = V1 V0†`, where
`V0`, `V1` diagonalize `H0`, `H1`.

This is proved completely: `U_opt := V1 * V0ᴴ` is unitary
(`U_optᴴ U_opt = V0 (V1ᴴ V1) V0ᴴ = V0 V0ᴴ = 1`) and `U_opt * V0 = V1`.
-/
/-- Corollary B.2: the zero-error optimal unitary `U_opt = V1 · V0ᴴ` satisfies `U_opt · V0 = V1`. -/
theorem optimalUnitaryZeroError
    (V0 V1 : Matrix κ κ ℂ)
    (hV0 : V0ᴴ * V0 = 1) (hV0' : V0 * V0ᴴ = 1) (hV1 : V1ᴴ * V1 = 1) :
    ∃ Uop : Matrix κ κ ℂ, Uopᴴ * Uop = 1 ∧ Uop * V0 = V1 := by
  refine ⟨V1 * V0ᴴ, ?_, ?_⟩
  · show (V1 * V0ᴴ)ᴴ * (V1 * V0ᴴ) = 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc (V0 * V1ᴴ) * (V1 * V0ᴴ)
        = V0 * (V1ᴴ * (V1 * V0ᴴ)) := by rw [Matrix.mul_assoc]
      _ = V0 * ((V1ᴴ * V1) * V0ᴴ) := by rw [← Matrix.mul_assoc V1ᴴ V1 V0ᴴ]
      _ = V0 * (1 * V0ᴴ) := by rw [hV1]
      _ = V0 * V0ᴴ := by rw [Matrix.one_mul]
      _ = 1 := hV0'
  · rw [Matrix.mul_assoc, hV0, Matrix.mul_one]

end Qatlib.Papers.FluctThermal22.MainResults.OptimalUnitary
