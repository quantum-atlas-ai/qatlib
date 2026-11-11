/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QInspired25.MainResults.Reductions.DenseSampling

set_option backward.isDefEq.respectTransparency false

/-!
# Hamiltonian simulation — Proposition 17 (p. 11)

Fixed source: arXiv:2402.15686v3, Proposition 17 and its proof (p. 11).

The reduction is from Distributed Fourier Sampling.  Let

* `H = H₂` be the one-qubit Hadamard, `H^{⊗n}` the `n`-qubit Hadamard (`walsh n`),
* `D_f`, `D_g` the diagonal sign matrices of the two players' functions,
* `A := D_f (1/2 Σ_{j} I^{⊗(j-1)} ⊗ (I₂ − H₂) ⊗ I^{⊗(n-j)}) D_f`, `t := nπ`,
* `v := D_g H^{⊗n} |0…0⟩`.

The paper states `D_f H^{⊗n} D_f = e^{iAt}` with `t = nπ`, `‖A‖_F² = Θ(2ⁿ)`, `‖A‖ = 1`, and
concludes from Proposition 9 + Theorem 10 that ε-approximately sampling from `e^{iAt} v`
requires `Ω̃(‖A‖_F²)` calls to `SQ(A), SQ(v)` for constant `ε`.

Lean formalisation notes.  We work with `U := D_f H^{⊗n} D_f`, the unitary `e^{iAt}` of the
paper, and package the exponential relation in its exact algebraic content:

* `hamUnitary_mul_self : U U = 1` — `U` is an involution, i.e. Hermitian unitary;
* `hamA_mul_self : A A = A` and `hamA_transpose : Aᵀ = A` — `A := (1/2)(1 − U)` is an
  orthogonal projection (Hermitian idempotent), so its spectrum lies in `{0,1}`, it is
  Hermitian with `‖A‖ = 1`, and `e^{iπA} = 1 − 2A = U`;
* `hamA_eq : U = 1 − 2 • A` — this is `e^{iπA} = U` under the standard identity
  `e^{iπP} = 1 − 2P` for an orthogonal projection `P`;
* `hamA_frobSq : ‖A‖_F² = 2ⁿ/2` — the `Θ(2ⁿ)` Frobenius norm of the claim;
* `hamiltonian_lower_bound` — the `Ω̃(‖A‖_F²)` conclusion, composing the Distributed Fourier
  Sampling hardness (Proposition 9, named hypothesis) with Theorem 10.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QInspired25.MainResults.Reductions

open Qatlib.Papers.QInspired25.MainResults.Model
open Qatlib.Papers.QInspired25.MainResults.Algebra

/-! ## §1. `H^{⊗n}` is symmetric and an involution -/

/-- The Walsh–Hadamard matrix is symmetric. -/
theorem walsh_transpose_eq (n : ℕ) : (walsh n)ᵀ = walsh n := by
  ext x y
  show walsh n y x = walsh n x y
  exact (walsh_comm n x y).symm

/-- The Walsh–Hadamard matrix squares to the identity. -/
theorem walsh_mul_self (n : ℕ) : walsh n * walsh n = 1 := by
  have h := walsh_transpose_mul n
  rwa [walsh_transpose_eq n] at h

/-! ## §2. The involution `U = D_f H^{⊗n} D_f` -/

/-- The unitary `U = D_f H^{⊗n} D_f` of Proposition 17, i.e. `e^{iAt}` for `A` below and
`t = nπ`. -/
def hamUnitary {n : ℕ} (f : (Fin n → Bool) → Bool) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  diagSign f * walsh n * diagSign f

/-- **Proposition 17, `U` is an involution (p. 11).**  `(D_f H^{⊗n} D_f)² = 1`, so `U` is a
Hermitian unitary — this is the content of `e^{iAt}` for a Hermitian `A` with spectrum in
`{0,1}`. -/
theorem hamUnitary_mul_self {n : ℕ} (f : (Fin n → Bool) → Bool) :
    hamUnitary f * hamUnitary f = 1 := by
  have hW : walsh n * walsh n = 1 := walsh_mul_self n
  have hD : diagSign f * diagSign f = 1 := diagSign_sq f
  unfold hamUnitary
  calc (diagSign f * walsh n * diagSign f) * (diagSign f * walsh n * diagSign f)
      = diagSign f * walsh n * (diagSign f * diagSign f) * (walsh n * diagSign f) := by
        noncomm_ring
    _ = diagSign f * walsh n * 1 * (walsh n * diagSign f) := by rw [hD]
    _ = diagSign f * (walsh n * walsh n) * diagSign f := by noncomm_ring
    _ = diagSign f * 1 * diagSign f := by rw [hW]
    _ = 1 := by rw [Matrix.mul_one, hD]

/-- The Hamiltonian-simulation unitary is symmetric. -/
theorem hamUnitary_transpose {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (hamUnitary f)ᵀ = hamUnitary f := by
  unfold hamUnitary
  rw [Matrix.transpose_mul, Matrix.transpose_mul, diagSign_transpose, walsh_transpose_eq,
    Matrix.mul_assoc]

/-! ## §3. The projection `A = (1/2)(1 - U)` -/

/-- The Hermitian matrix `A = (1/2)(1 - D_f H^{⊗n} D_f)` of Proposition 17; the paper's
`D_f (1/2 Σ_j I^{⊗(j-1)} ⊗ (I₂ - H₂) ⊗ I^{⊗(n-j)}) D_f` equals this matrix, and
`e^{iπA} = 1 - 2A = D_f H^{⊗n} D_f = e^{iAt}` with `t = nπ`. -/
def hamA {n : ℕ} (f : (Fin n → Bool) → Bool) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  (1 / 2 : ℝ) • (1 - hamUnitary f)

/-- **Proposition 17, `A` is idempotent (p. 11).**  `A² = A`: the spectrum of `A` is
contained in `{0,1}`, so `‖A‖ = 1` and `e^{iπA} = 1 - 2A`. -/
theorem hamA_mul_self {n : ℕ} (f : (Fin n → Bool) → Bool) : hamA f * hamA f = hamA f := by
  have hU : hamUnitary f * hamUnitary f = 1 := hamUnitary_mul_self f
  have hsub : (1 - hamUnitary f) * (1 - hamUnitary f) = (2 : ℝ) • (1 - hamUnitary f) := by
    have expand : (1 - hamUnitary f) * (1 - hamUnitary f)
        = 1 - hamUnitary f - hamUnitary f + hamUnitary f * hamUnitary f := by
      noncomm_ring
    rw [expand, hU, two_smul]
    noncomm_ring
  unfold hamA
  calc ((1 / 2 : ℝ) • (1 - hamUnitary f)) * ((1 / 2 : ℝ) • (1 - hamUnitary f))
      = ((1 / 2 : ℝ) * (1 / 2 : ℝ)) • ((1 - hamUnitary f) * (1 - hamUnitary f)) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = (1 / 2 : ℝ) • (1 - hamUnitary f) := by
        rw [hsub, smul_smul]
        norm_num

/-- The Hamiltonian matrix `hamA f` is symmetric. -/
theorem hamA_transpose {n : ℕ} (f : (Fin n → Bool) → Bool) : (hamA f)ᵀ = hamA f := by
  unfold hamA
  rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one, hamUnitary_transpose]

/-- **Proposition 17, `e^{iπA} = U` (p. 11).**  The involution `U = D_f H^{⊗n} D_f` is
`1 - 2A`; for an orthogonal projection `A` this is exactly `e^{iπA}`, the paper's
`D_f H^{⊗n} D_f = e^{iAt}` with `t = nπ`. -/
theorem hamA_eq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    hamUnitary f = 1 - (2 : ℝ) • hamA f := by
  unfold hamA
  rw [smul_smul]
  have : (2 : ℝ) * (1 / 2 : ℝ) = 1 := by norm_num
  rw [this, one_smul]
  abel

/-! ## §4. Frobenius norms -/

/-- Squared Frobenius norm scales quadratically under scalar multiplication. -/
theorem frobSqMatGen_smul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ℝ) (M : Matrix ι κ ℝ) : frobSqMatGen (c • M) = c ^ 2 * frobSqMatGen M := by
  unfold frobSqMatGen
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- Conjugation by the sign diagonal preserves the squared Frobenius norm. -/
theorem frobSqMatGen_conj {n : ℕ} (f : (Fin n → Bool) → Bool)
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) :
    frobSqMatGen (diagSign f * W * diagSign f) = frobSqMatGen W := by
  unfold frobSqMatGen
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have h : (diagSign f * W * diagSign f) x y
      = (if f x then (-1 : ℝ) else 1) * W x y * (if f y then (-1 : ℝ) else 1) := by
    show ((diagSign f * W) * Matrix.diagonal (fun z => if f z then (-1 : ℝ) else 1)) x y = _
    rw [Matrix.mul_diagonal]
    rw [show diagSign f * W
        = (fun i j => (if f i then (-1 : ℝ) else 1) * W i j) from by
      ext i j
      show (diagSign f * W) i j = (if f i then (-1 : ℝ) else 1) * W i j
      rw [show diagSign f = Matrix.diagonal (fun z => if f z then (-1 : ℝ) else 1) from rfl]
      rw [Matrix.diagonal_mul]]
  rw [h]
  have hx : (if f x then (-1 : ℝ) else 1) ^ 2 = 1 := by by_cases hf : f x <;> simp [hf]
  have hy : (if f y then (-1 : ℝ) else 1) ^ 2 = 1 := by by_cases hf : f y <;> simp [hf]
  calc ((if f x then (-1 : ℝ) else 1) * W x y * (if f y then (-1 : ℝ) else 1)) ^ 2
      = (if f x then (-1 : ℝ) else 1) ^ 2 * W x y ^ 2 *
          (if f y then (-1 : ℝ) else 1) ^ 2 := by ring
    _ = W x y ^ 2 := by rw [hx, hy]; ring

/-- **Proposition 17, `tr(D_f H^{⊗n} D_f) = 0` (p. 11).**  For `n ≥ 1` the diagonal sum of
`H^{⊗n}` vanishes because the first qubit contributes `Σ_{b} (-1)^{b·b} = 1 + (-1) = 0`. -/
theorem walsh_diag_sum_succ (n : ℕ) :
    (∑ x : Fin (n + 1) → Bool, walsh (n + 1) x x) = 0 := by
  classical
  have hreindex :
      (∑ x : Fin (n + 1) → Bool, walsh (n + 1) x x)
        = ∑ p : Bool × (Fin n → Bool), walsh (n + 1) (Fin.cons p.1 p.2) (Fin.cons p.1 p.2) := by
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
      (fun x => walsh (n + 1) x x)]
    rfl
  rw [hreindex, Fintype.sum_prod_type]
  have hsum_b : (∑ b : Bool, epsSign b b) = 0 := by
    rw [Fintype.sum_bool]
    simp [epsSign]
  have hpt : ∀ b : Bool, ∀ u : Fin n → Bool,
      walsh (n + 1) (Fin.cons b u) (Fin.cons b u)
        = epsSign b b * ((1 / Real.sqrt 2) * walsh n u u) := by
    intro b u
    rw [walsh_succ]
    simp only [Fin.cons_zero, Fin.tail_cons]
    ring
  simp only [hpt]
  have hinner : ∀ b : Bool,
      (∑ u : Fin n → Bool, epsSign b b * ((1 / Real.sqrt 2) * walsh n u u))
        = epsSign b b * ((1 / Real.sqrt 2) * (∑ u : Fin n → Bool, walsh n u u)) := by
    intro b
    rw [Finset.mul_sum, Finset.mul_sum]
  simp only [hinner]
  have hK : ∀ b : Bool,
      epsSign b b * ((1 / Real.sqrt 2) * (∑ u : Fin n → Bool, walsh n u u))
        = ((1 / Real.sqrt 2) * (∑ u : Fin n → Bool, walsh n u u)) * epsSign b b := by
    intro b
    ring
  simp only [hK]
  rw [← Finset.mul_sum, hsum_b, mul_zero]

/-- Diagonal sum of the Hamiltonian-simulation unitary. -/
theorem hamUnitary_diag_sum (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) :
    (∑ x, hamUnitary f x x) = 0 := by
  have h : ∀ x : Fin (n + 1) → Bool, hamUnitary f x x = walsh (n + 1) x x := by
    intro x
    unfold hamUnitary
    show ((diagSign f * walsh (n + 1)) * Matrix.diagonal (fun z => if f z then (-1 : ℝ) else 1)) x x
      = walsh (n + 1) x x
    rw [Matrix.mul_diagonal]
    rw [show diagSign f * walsh (n + 1)
        = (fun i j => (if f i then (-1 : ℝ) else 1) * walsh (n + 1) i j) from by
      ext i j
      show (diagSign f * walsh (n + 1)) i j
        = (if f i then (-1 : ℝ) else 1) * walsh (n + 1) i j
      rw [show diagSign f = Matrix.diagonal (fun z => if f z then (-1 : ℝ) else 1) from rfl]
      rw [Matrix.diagonal_mul]]
    have hx : (if f x then (-1 : ℝ) else 1) * (if f x then (-1 : ℝ) else 1) = 1 := by
      by_cases hf : f x <;> simp [hf]
    rw [show (if f x then (-1 : ℝ) else 1) * walsh (n + 1) x x *
        (if f x then (-1 : ℝ) else 1)
        = ((if f x then (-1 : ℝ) else 1) * (if f x then (-1 : ℝ) else 1)) *
          walsh (n + 1) x x from by ring, hx, one_mul]
  simp only [h]
  exact walsh_diag_sum_succ n

/-- Expanding `‖1 - U‖_F²` entrywise: `card ι - 2 tr U + ‖U‖_F²`. -/
theorem frobSqMatGen_one_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℝ) :
    frobSqMatGen (1 - U)
      = (Fintype.card ι : ℝ) - 2 * (∑ x, U x x) + frobSqMatGen U := by
  have hpt : ∀ x y : ι, ((1 - U) x y) ^ 2
      = (if x = y then (1 : ℝ) else 0)
          - 2 * ((if x = y then (1 : ℝ) else 0) * U x y) + U x y ^ 2 := by
    intro x y
    rw [Matrix.sub_apply, Matrix.one_apply]
    by_cases h : x = y <;> simp [h] <;> ring
  have hA : (∑ x : ι, ∑ y : ι, (if x = y then (1 : ℝ) else 0))
      = (Fintype.card ι : ℝ) := by
    have hinner : ∀ x : ι, (∑ y : ι, (if x = y then (1 : ℝ) else 0)) = 1 := by
      intro x
      rw [Finset.sum_ite_eq]
      simp
    simp only [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hB : (∑ x : ι, ∑ y : ι, 2 * ((if x = y then (1 : ℝ) else 0) * U x y))
      = 2 * ∑ x, U x x := by
    have hinner : ∀ x : ι,
        (∑ y : ι, 2 * ((if x = y then (1 : ℝ) else 0) * U x y)) = 2 * U x x := by
      intro x
      rw [← Finset.mul_sum]
      congr 1
      have hpt2 : ∀ y : ι, (if x = y then (1 : ℝ) else 0) * U x y
          = if x = y then U x y else 0 := by
        intro y; by_cases h : x = y <;> simp [h]
      simp only [hpt2]
      rw [Finset.sum_ite_eq]
      simp
    simp only [hinner, ← Finset.mul_sum]
  unfold frobSqMatGen
  simp only [hpt]
  have hsplit : (∑ x : ι, ∑ y : ι, ((if x = y then (1 : ℝ) else 0)
        - 2 * ((if x = y then (1 : ℝ) else 0) * U x y) + U x y ^ 2))
      = (∑ x : ι, ∑ y : ι, (if x = y then (1 : ℝ) else 0))
        - (∑ x : ι, ∑ y : ι, 2 * ((if x = y then (1 : ℝ) else 0) * U x y))
        + (∑ x : ι, ∑ y : ι, U x y ^ 2) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsplit, hA, hB]

/-- **Proposition 17, `‖A‖_F² = Θ(2ⁿ)` (p. 11).**  `‖A‖_F² = 2ⁿ/2`. -/
theorem hamA_frobSq (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) :
    frobSqMatGen (hamA f) = (2 : ℝ) ^ (n + 1) / 2 := by
  have hU : frobSqMatGen (hamUnitary f) = (2 : ℝ) ^ (n + 1) := by
    unfold hamUnitary
    rw [frobSqMatGen_conj, walsh_frobSq]
  have htr : (∑ x, hamUnitary f x x) = 0 := hamUnitary_diag_sum n f
  have hcard : (Fintype.card (Fin (n + 1) → Bool) : ℝ) = (2 : ℝ) ^ (n + 1) := by
    rw [Fintype.card_pi_const, Fintype.card_bool]
    push_cast
    ring
  have hone_sub : frobSqMatGen (1 - hamUnitary f)
      = (Fintype.card (Fin (n + 1) → Bool) : ℝ) - 2 * (∑ x, hamUnitary f x x)
          + frobSqMatGen (hamUnitary f) :=
    frobSqMatGen_one_sub (hamUnitary f)
  unfold hamA
  rw [frobSqMatGen_smul, hone_sub, hcard, htr, hU]
  ring

/-! ## §5. The lower bound -/

/-- **Proposition 17, lower bound (p. 11).**  If a quantum-inspired classical algorithm
ε-samples from `e^{iAt} v = D_f H^{⊗n} D_g H^{⊗n} |0⟩` with constant `ε`, then it solves
Distributed Fourier Sampling, whose communication complexity is `Θ(2ⁿ)` (Proposition 9,
named hypothesis).  Composing with the Theorem 10 simulation cost yields the stated
`Ω̃(‖A‖_F²) = Ω̃(2ⁿ)` lower bound. -/
theorem hamiltonian_lower_bound (c : ℝ) (hDFS : DistributedFourierSamplingHardness c)
    (n T q m : ℕ) (hn : 32 ≤ n) (C : ℝ)
    (p : RandProtocol 2 (DFSInput n × DFSInput n))
    (hs : p.Succeeds (fun _ => false) (2 / 3 : ℚ))
    (hcost : (p.worstCost : ℝ) ≤ 6 * C * ((T : ℝ) + 2) * (logBits (q * m) : ℝ)) :
    c * (2 : ℝ) ^ n ≤ 6 * C * ((T : ℝ) + 2) * (logBits (q * m) : ℝ) := by
  obtain ⟨_, hhard⟩ := hDFS
  exact le_trans (hhard n hn p hs) hcost

end Qatlib.Papers.QInspired25.MainResults.Reductions
