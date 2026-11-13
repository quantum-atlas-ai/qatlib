/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option backward.isDefEq.respectTransparency false

/-!
# SparseUnitary09 — MainResults / Dilation (claim c001)

Source: Stephen P. Jordan & Pawel Wocjan, *Efficient quantum circuits for arbitrary
sparse unitaries*, fixed version **arXiv:0904.2211v2 (11 Feb 2010)**.

This file formalises the paper's central construction (Section I, p. 1, equations
(1)--(4)): for an arbitrary finite-dimensional unitary `U`, the Hermitian dilation
`H = [[0, U], [U†, 0]]` is Hermitian with `H² = 1` and `‖H‖ = 1`, its matrix
exponential is `e^{−iθH} = cos θ·1 − i·sin θ·H`, at `θ = π/2` this equals `−i·H`, and
evolving the ancilla-`|1⟩` input `|1⟩|ψ⟩` for time `π/2` produces `−i|0⟩(U|ψ⟩)`.

The remaining part of the paper's main claim — that the gate count is
`poly(log N, d, ‖Ht‖, 1/ε)` — is the standard sparse-Hamiltonian-simulation cost
([1,3] of the paper), reused at the concept layer; see the docstring of
`c001_implementation_reduction`.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.SparseUnitary09.MainResults.Dilation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The Hermitian dilation (Eq.(1)) -/

/-- Paper arXiv:0904.2211v2, Eq.(1), p. 1. The Hermitian dilation
`H = [[0, U], [U†, 0]]` of a square matrix `U`, blocked over `ι ⊕ ι`
(`Sum.inl` = ancilla `|0⟩` block, `Sum.inr` = ancilla `|1⟩` block). -/
def unitaryDilation (U : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks (0 : Matrix ι ι ℂ) U Uᴴ (0 : Matrix ι ι ℂ)

/-- Paper arXiv:0904.2211v2, p. 1: `H` is Hermitian (`H = H†`), for any `U`. -/
theorem unitaryDilation_isHermitian (U : Matrix ι ι ℂ) :
    (unitaryDilation U).IsHermitian := by
  show (unitaryDilation U)ᴴ = unitaryDilation U
  rw [unitaryDilation, Matrix.fromBlocks_conjTranspose]
  simp

/-- Paper arXiv:0904.2211v2, p. 1: `H² = 1` when `U` is unitary. -/
theorem unitaryDilation_mul_self (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    unitaryDilation U * unitaryDilation U = 1 := by
  have h1 : U * Uᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff).mp hU
    simpa only [Matrix.star_eq_conjTranspose] using this
  have h2 : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').mp hU
    simpa only [Matrix.star_eq_conjTranspose] using this
  rw [unitaryDilation, Matrix.fromBlocks_multiply]
  simpa only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, h1, h2] using
    (Matrix.fromBlocks_one (l := ι) (m := ι) (α := ℂ))

/-- Paper arXiv:0904.2211v2, p. 1: `‖H‖ = 1` when `U` is unitary and `N ≥ 1`. -/
theorem unitaryDilation_norm_eq_one [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    ‖unitaryDilation U‖ = 1 := by
  have h2 : unitaryDilation U * unitaryDilation U = 1 := unitaryDilation_mul_self U hU
  have hh : star (unitaryDilation U) = unitaryDilation U := by
    rw [Matrix.star_eq_conjTranspose]
    exact unitaryDilation_isHermitian U
  have hnorm := CStarRing.norm_star_mul_self (x := unitaryDilation U)
  rw [hh, h2, CStarRing.norm_one] at hnorm
  have hsq : ‖unitaryDilation U‖ ^ 2 = 1 := by nlinarith [hnorm]
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact h
  · exact absurd h (by have := norm_nonneg (unitaryDilation U); linarith)

/-! ## The exponential identity (Eq.(2))

We prove the generic algebraic fact behind the paper's Eq.(2): for any square matrix
`S` with `S² = 1`, `exp(t·S) = cosh t·1 + sinh t·S`.  The proof is self-contained
(no simultaneous diagonalisation), using the complementary-projector decomposition
`S = P − Q` with `P = (1+S)/2`, `Q = (1−S)/2`. -/

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- For an idempotent `P` (`P² = P`), `exp(t·P) = 1 + (e^t − 1)·P`. -/
private theorem exp_idempotent (P : Matrix κ κ ℂ) (hP : IsIdempotentElem P) (t : ℂ) :
    NormedSpace.exp (t • P) = 1 + (Complex.exp t - 1) • P := by
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) t).smul_const P
  have hz := hasSum_ite_eq (0 : ℕ) ((1 : Matrix κ κ ℂ) - P)
  have hsum := hs.add hz
  have he : (fun n : ℕ => (n.factorial : ℂ)⁻¹ • (t • P) ^ n) =
      (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • t ^ n) • P + if n = 0 then 1 - P else 0) := by
    funext n
    cases n with
    | zero => simp
    | succ n => simp [smul_pow, hP.pow_succ_eq, smul_smul]
  have hm := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (t • P)
  rw [he] at hm
  have hu := hm.unique hsum
  rw [← Complex.exp_eq_exp_ℂ] at hu
  calc
    _ = Complex.exp t • P + (1 - P) := hu
    _ = _ := by
      simp only [sub_smul, one_smul]
      abel

/-- For an involution `S` (`S² = 1`), `exp(t·S) = cosh t·1 + sinh t·S`. -/
theorem matrix_exp_reflection (S : Matrix κ κ ℂ) (hS : S * S = 1) (t : ℂ) :
    NormedSpace.exp (t • S) = Complex.cosh t • (1 : Matrix κ κ ℂ) + Complex.sinh t • S := by
  let P : Matrix κ κ ℂ := (1 / 2 : ℂ) • (1 + S)
  let Q : Matrix κ κ ℂ := (1 / 2 : ℂ) • (1 - S)
  have hP : IsIdempotentElem P := by
    change P * P = P
    dsimp [P]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, hS]
    ext i k
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hQ : IsIdempotentElem Q := by
    change Q * Q = Q
    dsimp [Q]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hS]
    ext i k
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hPQ : P * Q = 0 := by
    dsimp [P, Q]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hS]
    ext i k
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply,
      smul_eq_mul]
    ring
  have hQP : Q * P = 0 := by
    dsimp [P, Q]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, hS]
    ext i k
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply,
      smul_eq_mul]
    ring
  have hx : t • S = t • P + (-t) • Q := by
    dsimp [P, Q]
    ext i k
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hc : Commute (t • P) ((-t) • Q) := by
    change (t • P) * ((-t) • Q) = ((-t) • Q) * (t • P)
    simp only [Matrix.smul_mul, Matrix.mul_smul, hPQ, hQP, smul_zero]
  calc
    _ = NormedSpace.exp (t • P + (-t) • Q) := congrArg NormedSpace.exp hx
    _ = _ := Matrix.exp_add_of_commute _ _ hc
    _ = (1 + (Complex.exp t - 1) • P) * (1 + (Complex.exp (-t) - 1) • Q) :=
      congrArg₂ (· * ·) (exp_idempotent P hP t) (exp_idempotent Q hQ (-t))
    _ = _ := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul, hPQ, smul_zero, add_zero]
      dsimp [P, Q]
      ext i k
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Complex.cosh, Complex.sinh]
      ring

/-- Paper arXiv:0904.2211v2, Eq.(2), p. 1: `e^{−iθH} = cos θ·1 − i·sin θ·H`. -/
theorem unitaryDilation_exp (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (θ : ℝ) :
    NormedSpace.exp ((Complex.I * (-(θ : ℂ))) • unitaryDilation U)
      = (Real.cos θ : ℂ) • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
        - (Complex.I * (Real.sin θ : ℂ)) • unitaryDilation U := by
  have hS : unitaryDilation U * unitaryDilation U = 1 := unitaryDilation_mul_self U hU
  have ht : Complex.I * (-(θ : ℂ)) = (-(θ : ℂ)) * Complex.I := by ring
  rw [ht]
  rw [matrix_exp_reflection (unitaryDilation U) hS ((-(θ : ℂ)) * Complex.I)]
  have hc : Complex.cosh ((-(θ : ℂ)) * Complex.I) = (Real.cos θ : ℂ) := by
    rw [Complex.cosh_mul_I, Complex.cos_neg, ← Complex.ofReal_cos]
  have hs : Complex.sinh ((-(θ : ℂ)) * Complex.I) = -(Complex.I * (Real.sin θ : ℂ)) := by
    rw [Complex.sinh_mul_I, Complex.sin_neg, ← Complex.ofReal_sin]
    ring
  rw [hc, hs]
  simp only [neg_smul, sub_eq_add_neg]

/-- Paper arXiv:0904.2211v2, Eq.(3), p. 1: `e^{−i(π/2)H} = −i·H`. -/
theorem unitaryDilation_exp_pi_half (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    NormedSpace.exp ((Complex.I * (-(((Real.pi / 2 : ℝ) : ℂ)))) • unitaryDilation U)
      = (-Complex.I) • unitaryDilation U := by
  rw [unitaryDilation_exp U hU (Real.pi / 2), Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-! ## Ancilla states and the phase-kickback reduction (Eq.(4)) -/

/-- `|0⟩|ψ⟩` on the ancilla-system space `ι ⊕ ι`. -/
def anc0 (ψ : ι → ℂ) : ι ⊕ ι → ℂ := Sum.elim ψ (0 : ι → ℂ)

/-- `|1⟩|ψ⟩` on the ancilla-system space `ι ⊕ ι`. -/
def anc1 (ψ : ι → ℂ) : ι ⊕ ι → ℂ := Sum.elim (0 : ι → ℂ) ψ

/-- `H·(|1⟩|ψ⟩) = |0⟩(U|ψ⟩)` for the dilation `H`. -/
theorem unitaryDilation_mulVec_anc1 (U : Matrix ι ι ℂ) (ψ : ι → ℂ) :
    unitaryDilation U *ᵥ anc1 ψ = anc0 (U *ᵥ ψ) := by
  rw [unitaryDilation, Matrix.fromBlocks_mulVec]
  ext k
  cases k with
  | inl i => simp [anc0, anc1]
  | inr i => simp [anc0, anc1]

/-- Paper arXiv:0904.2211v2, Eq.(4), p. 1: `e^{−iHπ/2}|1⟩|ψ⟩ = −i|0⟩U|ψ⟩`. -/
theorem unitaryDilation_phase_kickback (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (ψ : ι → ℂ) :
    NormedSpace.exp ((Complex.I * (-(((Real.pi / 2 : ℝ) : ℂ)))) • unitaryDilation U) *ᵥ anc1 ψ
      = (-Complex.I) • anc0 (U *ᵥ ψ) := by
  rw [unitaryDilation_exp_pi_half U hU, Matrix.smul_mulVec, unitaryDilation_mulVec_anc1]

/-- Paper arXiv:0904.2211v2, Section I, p. 1 (main construction). For every finite
unitary `U`: the dilation `H = [[0,U],[U†,0]]` is Hermitian, satisfies `H² = 1` and
`‖H‖ = 1`, its evolution obeys Eq.(2), Eq.(3), and — the implementation reduction of
Eq.(4) — evolving any ancilla-`|1⟩` input `|1⟩|ψ⟩` for time `π/2` produces
`−i|0⟩(U|ψ⟩)`.

The paper's efficiency clause ("`poly(log N, d, ‖Ht‖, 1/ε)` gates") is the standard
sparse-Hamiltonian-simulation cost of `H` for time `π/2` ([1,3] of the paper, reused
at the concept layer, e.g. `Qatlib.Concepts.LcuQsvtApprox.SparseWalkFrame`),
plus the single initial NOT gate on the ancilla; the dilation is `d`-sparse whenever
`U` is `d`-sparse per row/column, since its rows are `U`- or `U†`-rows. -/
theorem sparse_unitary_dilation_main [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (unitaryDilation U).IsHermitian ∧
    unitaryDilation U * unitaryDilation U = 1 ∧
    ‖unitaryDilation U‖ = 1 ∧
    (∀ θ : ℝ, NormedSpace.exp ((Complex.I * (-(θ : ℂ))) • unitaryDilation U)
        = (Real.cos θ : ℂ) • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
          - (Complex.I * (Real.sin θ : ℂ)) • unitaryDilation U) ∧
    NormedSpace.exp ((Complex.I * (-(((Real.pi / 2 : ℝ) : ℂ)))) • unitaryDilation U)
      = (-Complex.I) • unitaryDilation U ∧
    (∀ ψ : ι → ℂ, NormedSpace.exp
        ((Complex.I * (-(((Real.pi / 2 : ℝ) : ℂ)))) • unitaryDilation U) *ᵥ anc1 ψ
      = (-Complex.I) • anc0 (U *ᵥ ψ)) :=
  ⟨unitaryDilation_isHermitian U,
   unitaryDilation_mul_self U hU,
   unitaryDilation_norm_eq_one U hU,
   unitaryDilation_exp U hU,
   unitaryDilation_exp_pi_half U hU,
   unitaryDilation_phase_kickback U hU⟩

/-- Paper arXiv:0904.2211v2, Section I, p. 1: the phase-kickback reduction implements
`U` (up to the global phase `−i`) on the ancilla-`|1⟩` sector. This is the formal
"sparse unitary is efficiently implementable" step: evolve under the sparse
Hamiltonian `H` for time `π/2`, then the ancilla carries `|1⟩ → |0⟩`. The gate cost is
exactly that of the time-`π/2` simulation of `H` plus one NOT gate. -/
theorem c001_implementation_reduction (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (ψ : ι → ℂ) :
    ∃ φ : ℂ, φ = -Complex.I ∧
      NormedSpace.exp ((Complex.I * (-(((Real.pi / 2 : ℝ) : ℂ)))) • unitaryDilation U) *ᵥ anc1 ψ
        = φ • anc0 (U *ᵥ ψ) :=
  ⟨-Complex.I, rfl, unitaryDilation_phase_kickback U hU ψ⟩

end Qatlib.Papers.SparseUnitary09.MainResults.Dilation
