/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# LinearSystems15 — the Chebyshev quantum walk

Paper-layer statements for Childs–Kothari–Somma (arXiv:1511.02306), §4.1.

* `lemma15_walk_block_form` — source **Lemma 15**, eqs. (59)–(66) (p. 17):
  the walk operator `W = S(2TT† - 1)` acts on the invariant subspace
  `span{T|λ>, ST|λ>}` in the block form `[[λ, -√(1-λ²)], [√(1-λ²), λ]]`.
  Stated as the two explicit action identities (61) and (66), which are the
  paper's own proof, in finite-dimensional matrix form.
* `lemma15_walk_block_form_unit` — the `|λ| = 1` clause: `W T|λ> = λ T|λ>`.
* `lemma16_walk_power` — source **Lemma 16** (p. 17): the `n`-th power of the
  two-dimensional walk matrix has Chebyshev entries; proved via the
  substitution `λ = cos θ` and the real Chebyshev trigonometric identities.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Qatlib.Papers.LinearSystems15.MainResults.Walk

open Matrix

/-! ## Lemma 15 — block form of the walk on the invariant subspace -/

/-- **Source Lemma 15** (arXiv:1511.02306, §4.1, pp. 16–17, eqs. (56)–(66)).
Let `T : ℂ^n → ℂ^m` be an isometry (`T†T = 1`), `S` an involution on `ℂ^m`
(`S² = 1`), and `W := S(2TT† - 1)`.  Let `|λ>` be an eigenvector of
`H := T†ST` with eigenvalue `λ`, and let
`|⊥λ> := (S T|λ> - λ T|λ>)/s` with `s² = 1 - λ²`, `s ≠ 0` (the state of
eq. (58)).

Then, on the spanning states `T|λ>` and `|⊥λ>`, the walk acts as
`W T|λ> = λ T|λ> + s|⊥λ>` (eq. (61)) and
`W|⊥λ> = -s T|λ> + λ|⊥λ>` (eq. (66)) — i.e. `W` has the block form
`[[λ, -s], [s, λ]]` in this basis, as claimed by Lemma 15.  The source takes
`λ` real and `s = √(1-λ²)`; they are complex here for convenience, which is a
specialisation-free generalisation of the paper's identity. -/
theorem lemma15_walk_block_form {m n : ℕ}
    (T : Matrix (Fin m) (Fin n) ℂ) (S : Matrix (Fin m) (Fin m) ℂ)
    (ψ : Fin n → ℂ) (lam s : ℂ)
    (hsq : s ^ 2 = 1 - lam ^ 2) (hs : s ≠ 0)
    (hT : Tᴴ * T = 1) (hS2 : S * S = 1)
    (hH : (Tᴴ * S * T) *ᵥ ψ = lam • ψ) :
    let W := S * ((2 : ℂ) • (T * Tᴴ) - 1)
    let u : Fin m → ℂ := T *ᵥ ψ
    let w : Fin m → ℂ := s⁻¹ • (S *ᵥ u - lam • u)
    W *ᵥ u = lam • u + s • w ∧ W *ᵥ w = (-s) • u + lam • w := by
  intro W u w
  -- `(T T†)` fixes `u = T|lam>`.
  have hTT : (T * Tᴴ) *ᵥ u = u := by
    show (T * Tᴴ) *ᵥ (T *ᵥ ψ) = T *ᵥ ψ
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hT, Matrix.mul_one]
  -- Hence `W u = S u` (the `2TT† - 1` acts as the identity on `u`).
  have hWu : W *ᵥ u = S *ᵥ u := by
    show (S * ((2 : ℂ) • (T * Tᴴ) - 1)) *ᵥ u = S *ᵥ u
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hTT, Matrix.mulVec_sub, Matrix.mulVec_smul]
    module
  -- `T†(S u) = lam|lam>` since `H|lam> = lam|lam>`.
  have hTu : Tᴴ *ᵥ (S *ᵥ u) = lam • ψ := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact hH
  -- `(T T†)(S u) = lam u`.
  have hTTSu : (T * Tᴴ) *ᵥ (S *ᵥ u) = lam • u := by
    rw [← Matrix.mulVec_mulVec, hTu, Matrix.mulVec_smul]
  -- `W (S u) = 2lam (S u) - u`, using `S² = 1`.
  have hSS : S *ᵥ (S *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, hS2, Matrix.one_mulVec]
  have hWSu : W *ᵥ (S *ᵥ u) = (2 * lam) • (S *ᵥ u) - u := by
    have hB : ((2 : ℂ) • (T * Tᴴ) - 1) *ᵥ (S *ᵥ u) =
        (2 : ℂ) • (lam • u) - S *ᵥ u := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hTTSu]
    show (S * ((2 : ℂ) • (T * Tᴴ) - 1)) *ᵥ (S *ᵥ u) = _
    rw [← Matrix.mulVec_mulVec, hB, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hSS]
    module
  -- `s w = S u - lam u`.
  have hsw : s • w = S *ᵥ u - lam • u := by
    show s • (s⁻¹ • (S *ᵥ u - lam • u)) = _
    rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
  have hsneg : s * (-s) = lam ^ 2 - 1 := by
    linear_combination -hsq
  constructor
  · -- Equation (61): `W u = lam u + s w`.
    rw [hWu, hsw]
    module
  · -- Equation (66): `W w = -s u + lam w`.
    show W *ᵥ (s⁻¹ • (S *ᵥ u - lam • u)) = _
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, hWSu, hWu]
    have hinner : (2 * lam) • (S *ᵥ u) - u - lam • (S *ᵥ u) = lam • (S *ᵥ u) - u := by
      module
    rw [hinner]
    have hkey : lam • (S *ᵥ u) - u = s • ((-s) • u + lam • w) := by
      have hSu : S *ᵥ u = lam • u + s • w := by rw [hsw]; module
      rw [hSu]
      rw [show s • ((-s) • u + lam • w) = (s * (-s)) • u + (s * lam) • w by module]
      rw [hsneg]
      module
    rw [hkey, smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- **Source Lemma 15**, `|λ| = 1` clause (arXiv:1511.02306, §4.1, p. 17).
For an eigenvalue `λ = ±1` the state `T|λ>` is an eigenvector of the walk:
`W T|λ> = λ T|λ>`.  In this case eq. (58) degenerates to
`S T|λ> = λ T|λ>` (there is no `|⊥λ>` component), which is the hypothesis. -/
theorem lemma15_walk_block_form_unit {m n : ℕ}
    (T : Matrix (Fin m) (Fin n) ℂ) (S : Matrix (Fin m) (Fin m) ℂ)
    (ψ : Fin n → ℂ) (lam : ℂ)
    (hT : Tᴴ * T = 1)
    (hST : S *ᵥ (T *ᵥ ψ) = lam • (T *ᵥ ψ)) :
    (S * ((2 : ℂ) • (T * Tᴴ) - 1)) *ᵥ (T *ᵥ ψ) = lam • (T *ᵥ ψ) := by
  rw [← hST]
  show (S * ((2 : ℂ) • (T * Tᴴ) - 1)) *ᵥ (T *ᵥ ψ) = S *ᵥ (T *ᵥ ψ)
  rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  have hTT : (T * Tᴴ) *ᵥ (T *ᵥ ψ) = T *ᵥ ψ := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hT, Matrix.mul_one]
  rw [hTT, Matrix.mulVec_sub, Matrix.mulVec_smul]
  module

/-! ## Lemma 16 — powers of the two-dimensional walk matrix -/

/-- The two-by-two rotation matrix `[[cos t, -sin t], [sin t, cos t]]`. -/
def rot2 (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]

/-- The `rot2_add` result for the LinearSystems15 paper model. -/
theorem rot2_add (a b : ℝ) : rot2 (a + b) = rot2 a * rot2 b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot2, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

/-- **Source Lemma 16** (arXiv:1511.02306, §4.1, p. 17).
For `λ ∈ [-1,1]` and every positive integer `n`, the `n`-th power of
`W = [[λ, -√(1-λ²)], [√(1-λ²), λ]]` is
`[[T_n(λ), -√(1-λ²) U_{n-1}(λ)], [√(1-λ²) U_{n-1}(λ), T_n(λ)]]`,
where `T_n` and `U_n` are the Chebyshev polynomials of the first and second
kinds.  Proved by the paper's alternative route: substitute `λ = cos θ` and use
`T_n(cos θ) = cos(nθ)` and `U_{n-1}(cos θ) sin θ = sin(nθ)`. -/
theorem lemma16_walk_power (lam : ℝ) (hlam : lam ∈ Set.Icc (-1 : ℝ) 1)
    (n : ℕ) (hn : 0 < n) :
    (!![lam, -Real.sqrt (1 - lam ^ 2); Real.sqrt (1 - lam ^ 2), lam] : Matrix (Fin 2) (Fin 2) ℝ) ^ n
      = !![(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval lam,
          -(Real.sqrt (1 - lam ^ 2) *
            (Polynomial.Chebyshev.U ℝ (((n - 1 : ℕ)) : ℤ)).eval lam);
          Real.sqrt (1 - lam ^ 2) * (Polynomial.Chebyshev.U ℝ (((n - 1 : ℕ)) : ℤ)).eval lam,
          (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval lam] := by
  obtain ⟨hlam1, hlam2⟩ := hlam
  set θ : ℝ := Real.arccos lam with hθ
  have hcos : Real.cos θ = lam := Real.cos_arccos hlam1 hlam2
  have hsin : Real.sin θ = Real.sqrt (1 - lam ^ 2) := Real.sin_arccos lam
  -- The walk matrix is the rotation through `θ`.
  have hW : (!![lam, -Real.sqrt (1 - lam ^ 2); Real.sqrt (1 - lam ^ 2), lam] :
      Matrix (Fin 2) (Fin 2) ℝ) = rot2 θ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rot2, hcos, hsin]
  have hpow : ∀ k : ℕ, rot2 θ ^ k = rot2 ((k : ℝ) * θ) := by
    intro k
    induction k with
    | zero =>
        ext i j
        fin_cases i <;> fin_cases j <;> simp [rot2]
    | succ k ih =>
        rw [pow_succ, ih, ← rot2_add]
        congr 1
        push_cast
        ring
  rw [hW, hpow]
  -- Entrywise identification with the Chebyshev expressions.
  have hT : (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval lam = Real.cos ((n : ℝ) * θ) := by
    rw [← hcos]
    rw [Polynomial.Chebyshev.T_real_cos]
    push_cast
    ring_nf
  have hcastR : ((((n - 1 : ℕ) : ℤ)) : ℝ) + 1 = (n : ℝ) := by
    have h1 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      rw [Nat.cast_sub hn, Nat.cast_one]
      ring
    simpa using h1
  have hU : Real.sqrt (1 - lam ^ 2) *
      (Polynomial.Chebyshev.U ℝ (((n - 1 : ℕ)) : ℤ)).eval lam = Real.sin ((n : ℝ) * θ) := by
    have h := Polynomial.Chebyshev.U_real_cos θ (((n - 1 : ℕ)) : ℤ)
    rw [hcastR, hcos, hsin] at h
    rw [← h]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot2, hT, hU]

end Qatlib.Papers.LinearSystems15.MainResults.Walk
