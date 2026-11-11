/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QInspired25.MainResults.Algebra.WalshHadamard
import Qatlib.Papers.QInspired25.MainResults.Simulation.CoordinatorSimulation

set_option backward.isDefEq.respectTransparency false

/-!
# Sampling in the dense case — Proposition 13 (p. 9)

Fixed source: arXiv:2402.15686v3, Proposition 13 and its proof (p. 9).

With `D_f` the diagonal matrix of the Boolean function `f`, `A := D_f H^{⊗n}` and
`b := |g⟩ = 1/√(2ⁿ) Σ_x g(x)|x⟩`, the paper records

* `κ_F² = 2ⁿ`,
* `κ = γ = 1`,

and therefore, by Theorem 10 and Proposition 9 (Distributed Fourier Sampling, `Ω(2ⁿ)`
bits), that `ε`-approximately sampling from `A⁺b` requires `Ω̃(2ⁿ) = Ω̃(κ_F²)` calls to
`SQ(A), SQ(b)`.

Here we prove the linear algebra behind the two parameter claims:

* `denseA_transpose_mul` : `AᵀA = 1`, so all singular values are `1` (`κ = σ_min = 1`);
* `denseA_frobSq` : `‖A‖_F² = ‖H^{⊗n}‖_F² = 2ⁿ` (`κ_F² = 2ⁿ`);
* `denseb_frobSq` : `‖b‖ = 1`;
* `dense_gamma_sq` : `A Aᵀ = 1` makes `x* = Aᵀ b` satisfy `Ax* = b`, so `γ² = 1`.

The final theorem composes with the named hypothesis `DistributedFourierSamplingHardness`
(Proposition 9 of the source, cited there from [25]).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QInspired25.MainResults.Reductions

open Qatlib.Papers.QInspired25.MainResults.Model
open Qatlib.Papers.QInspired25.MainResults.Algebra

/-! ## §1. The sign diagonal `D_f` -/

/-- The diagonal matrix `D_f` of a Boolean function `f`: entry `(-1)^{f(x)}`. -/
def diagSign {n : ℕ} (f : (Fin n → Bool) → Bool) : Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  Matrix.diagonal (fun x => if f x then (-1 : ℝ) else 1)

/-- The diagonal sign matrix is symmetric. -/
theorem diagSign_transpose {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (diagSign f)ᵀ = diagSign f := by
  ext i j
  simp only [Matrix.transpose_apply, diagSign, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; rfl
  · simp [h, Ne.symm h]

/-- The diagonal sign matrix squares to the identity. -/
theorem diagSign_sq {n : ℕ} (f : (Fin n → Bool) → Bool) : diagSign f * diagSign f = 1 := by
  rw [show diagSign f = Matrix.diagonal (fun z => if f z then (-1 : ℝ) else 1) from rfl,
    Matrix.diagonal_mul_diagonal]
  have h : (fun x => (if f x then (-1 : ℝ) else 1) * (if f x then (-1 : ℝ) else 1))
      = (fun _ => (1 : ℝ)) := by
    funext x; by_cases hf : f x <;> simp [hf]
  rw [h, Matrix.diagonal_one]

/-- The transpose of the sign matrix times itself is the identity. -/
theorem diagSign_transpose_mul {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (diagSign f)ᵀ * diagSign f = 1 := by
  rw [diagSign_transpose, diagSign_sq]

/-! ## §2. `A = D_f H^{⊗n}` -/

/-- The matrix `A = D_f H^{⊗n}` of Proposition 13. -/
def denseA {n : ℕ} (f : (Fin n → Bool) → Bool) : Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  diagSign f * walsh n

/-- **Proposition 13, `κ = 1` (p. 9).**  `Aᵀ A = 1`: all singular values of `A` equal `1`. -/
theorem denseA_transpose_mul {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (denseA f)ᵀ * denseA f = 1 := by
  unfold denseA
  calc (diagSign f * walsh n)ᵀ * (diagSign f * walsh n)
      = (walsh n)ᵀ * (diagSign f)ᵀ * (diagSign f * walsh n) := by
        rw [Matrix.transpose_mul]
    _ = (walsh n)ᵀ * ((diagSign f)ᵀ * (diagSign f) * walsh n) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc]
    _ = (walsh n)ᵀ * (1 * walsh n) := by rw [diagSign_transpose_mul]
    _ = (walsh n)ᵀ * walsh n := by rw [Matrix.one_mul]
    _ = 1 := walsh_transpose_mul n

/-- Each Walsh–Hadamard row has Euclidean norm `√(2^n)`. -/
theorem walsh_rowNorm (n : ℕ) (x : Fin n → Bool) :
    (∑ y : Fin n → Bool, walsh n x y ^ 2) = 1 := by
  have := walsh_orthogonal n x x
  simpa [sq] using this

/-- **Proposition 13, `κ_F² = 2ⁿ` (p. 9).**  `‖D_f H^{⊗n}‖_F² = 2ⁿ`. -/
theorem denseA_frobSq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    frobSqMatGen (denseA f) = (2 : ℝ) ^ n := by
  unfold frobSqMatGen
  have hstep : ∀ x : Fin n → Bool,
      (∑ y : Fin n → Bool, (denseA f) x y ^ 2)
        = (if f x then (-1 : ℝ) else 1) ^ 2 * (∑ y : Fin n → Bool, walsh n x y ^ 2) := by
    intro x
    have hterm : ∀ y : Fin n → Bool,
        (denseA f) x y ^ 2 = (if f x then (-1 : ℝ) else 1) ^ 2 * walsh n x y ^ 2 := by
      intro y
      unfold denseA
      have h1 : (diagSign f * walsh n) x y
          = (if f x then (-1 : ℝ) else 1) * walsh n x y := by
        rw [show diagSign f = Matrix.diagonal (fun z => if f z then (-1 : ℝ) else 1) from rfl,
          Matrix.diagonal_mul]
      rw [h1]; ring
    rw [Finset.sum_congr rfl fun y _ => hterm y, ← Finset.mul_sum]
  simp only [hstep, walsh_rowNorm, mul_one]
  have hsq : ∀ x : Fin n → Bool, (if f x then (-1 : ℝ) else 1) ^ 2 = 1 := by
    intro x; by_cases hf : f x <;> simp [hf]
  simp only [hsq, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  rw [Fintype.card_pi_const, Fintype.card_bool]
  push_cast
  ring

/-! ## §3. The vector `b = |g⟩` and `γ` -/

/-- The state `|g⟩ = 1/√(2ⁿ) Σ_x g(x)|x⟩` of Proposition 13. -/
def denseb {n : ℕ} (g : (Fin n → Bool) → Bool) : (Fin n → Bool) → ℝ :=
  fun x => (if g x then (1 : ℝ) else -1) / Real.sqrt ((2 : ℝ) ^ n)

/-- `‖b‖ = 1`. -/
theorem denseb_frobSq {n : ℕ} (g : (Fin n → Bool) → Bool) : frobSqFun (denseb g) = 1 := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  unfold frobSqFun
  have hpt : ∀ x : Fin n → Bool,
      ((if g x then (1 : ℝ) else -1) / Real.sqrt ((2 : ℝ) ^ n)) ^ 2 = 1 / (2 : ℝ) ^ n := by
    intro x
    have hsqrt : Real.sqrt ((2 : ℝ) ^ n) * Real.sqrt ((2 : ℝ) ^ n) = (2 : ℝ) ^ n :=
      Real.mul_self_sqrt (le_of_lt h2)
    have hs : (if g x then (1 : ℝ) else -1) ^ 2 = 1 := by by_cases hg : g x <;> simp [hg]
    have hne : Real.sqrt ((2 : ℝ) ^ n) ≠ 0 := by positivity
    field_simp
    nlinarith [hsqrt, hs]
  simp only [denseb, hpt]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_pi_const,
    Fintype.card_bool]
  push_cast
  field_simp

/-- **Proposition 13, `γ = 1` (p. 9).**  Since `AᵀA = 1` and `A` is square, `A Aᵀ = 1`; hence
`x* = Aᵀ b` satisfies `A x* = b` and the overlap is `γ² = ‖Ax*‖²/‖b‖² = 1`. -/
theorem denseA_mulVec_transpose {n : ℕ} (f : (Fin n → Bool) → Bool)
    (g : (Fin n → Bool) → Bool) :
    denseA f *ᵥ ((denseA f)ᵀ *ᵥ denseb g) = denseb g := by
  have hAA' : denseA f * (denseA f)ᵀ = 1 :=
    mul_eq_one_comm.mpr (denseA_transpose_mul f)
  rw [Matrix.mulVec_mulVec, hAA', Matrix.one_mulVec]

/-- The dense instance's condition-number square is `2^n`. -/
theorem dense_gamma_sq {n : ℕ} (f g : (Fin n → Bool) → Bool) :
    frobSqFun (denseA f *ᵥ ((denseA f)ᵀ *ᵥ denseb g)) / frobSqFun (denseb g) = 1 := by
  rw [denseA_mulVec_transpose, denseb_frobSq, div_one]

/-! ## §4. Composing with Theorem 10 and Proposition 9 -/

/-- **Proposition 13, lower bound (p. 9).**  The `Ω(2ⁿ)` communication hardness of
Distributed Fourier Sampling (Proposition 9, named hypothesis) combined with the
`O((T+k)log(q·2ⁿ))` simulation of Theorem 10 forces
`c·2ⁿ ≤ C·(T+2)·log(q·2ⁿ)` for any `T`-query quantum-inspired classical sampler for the
dense instance.  Since `κ_F² = 2ⁿ` this is `Ω̃(κ_F²)`. -/
theorem dense_query_lower_bound (c : ℝ) (hDFS : DistributedFourierSamplingHardness c)
    (n T q : ℕ) (hn : 32 ≤ n) (C : ℝ)
    (p : RandProtocol 2 (DFSInput n × DFSInput n))
    (hs : p.Succeeds (fun _ => false) (2 / 3 : ℚ))
    (hcost : (p.worstCost : ℝ) ≤ C * ((T : ℝ) + 2) * (logBits (q * 2 ^ n) : ℝ)) :
    c * (2 : ℝ) ^ n ≤ C * ((T : ℝ) + 2) * (logBits (q * 2 ^ n) : ℝ) := by
  obtain ⟨_, hhard⟩ := hDFS
  exact le_trans (hhard n hn p hs) hcost

end Qatlib.Papers.QInspired25.MainResults.Reductions
