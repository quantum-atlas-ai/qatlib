/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnitaryLearn09.MainResults.ChoiFidelity

set_option backward.isDefEq.respectTransparency false

/-!
# UnitaryLearn09 — tensor-power goal function for `M` output copies

Fixed source: Bisio–Chiribella–D'Ariano–Facchini–Perinotti,
*Optimal quantum learning of a unitary transformation*, arXiv:0903.0543v2
(PDF SHA-256 7740f8bf94c88b19a046c4c627cda8edf148bf92fe178c381fd20bceede57048),
Section III B.2 (global fidelity, after Theorem 1) and Section IV (inversion).

For `M > 1` output copies the paper replaces the target `U` by `U^{⊗M}` and
states that optimal learning is equivalent to optimal estimation maximizing the
expectation of the goal function
`f_M(U, Û) = (‖Tr[U† Û]‖/d)^{2M}`
(Sec. III B.2).  Section IV observes that inversion is obtained by the
substitution `U → U†`, so the inversion goal function is the same scalar with
`U, Û` replaced by their adjoints.

This file proves the two scalar identities for the unitary channel fidelity of
`ChoiFidelity.lean`: the `M`-copy fidelity is the `M`-th power of the
single-copy fidelity, the goal function agrees with it, and passing to
adjoints (the inversion task) leaves the fidelity unchanged.  The optimization
over storing boards and retrieving channels is *not* formalized here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Papers.UnitaryLearn09.MainResults

/-- Index type of the `M`-fold tensor power of a `d`-dimensional register. -/
def kronIdx (d : ℕ) : ℕ → Type
  | 0 => PUnit
  | n + 1 => kronIdx d n × Fin d

/-- Finiteness of the `n`-fold index type, by recursion on `n`. -/
@[reducible] def kronIdxFintype (d : ℕ) : (n : ℕ) → Fintype (kronIdx d n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => @instFintypeProd (kronIdx d n) (Fin d) (kronIdxFintype d n) inferInstance

/-- Decidable equality of the `n`-fold index type, by recursion on `n`. -/
@[reducible] def kronIdxDecidableEq (d : ℕ) : (n : ℕ) → DecidableEq (kronIdx d n)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | n + 1 =>
      @instDecidableEqProd (kronIdx d n) (Fin d) (kronIdxDecidableEq d n) inferInstance

/-- The `n`-fold index type is finite for every `n`. -/
instance (d n : ℕ) : Fintype (kronIdx d n) := kronIdxFintype d n

/-- The `n`-fold index type has decidable equality for every `n`. -/
instance (d n : ℕ) : DecidableEq (kronIdx d n) := kronIdxDecidableEq d n

/-- The `M`-fold Kronecker power of a square matrix. -/
noncomputable def kronPow (d : ℕ) : (n : ℕ) → Matrix (Fin d) (Fin d) ℂ →
    Matrix (kronIdx d n) (kronIdx d n) ℂ
  | 0, _ => 1
  | n + 1, A => kronPow d n A ⊗ₖ A

/-- The dimension of the `M`-fold register is `d ^ M`. -/
theorem card_kronIdx (d : ℕ) : ∀ n : ℕ, Fintype.card (kronIdx d n) = d ^ n
  | 0 => by change Fintype.card PUnit = 1; simp
  | n + 1 => by
      change Fintype.card (kronIdx d n × Fin d) = d ^ (n + 1)
      rw [Fintype.card_prod, card_kronIdx d n, Fintype.card_fin, pow_succ]

/-- The trace of an `M`-fold Kronecker power is the `M`-th power of the trace. -/
theorem trace_kronPow (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    ∀ n : ℕ, (kronPow d n A).trace = A.trace ^ n
  | 0 => by
      change (1 : Matrix (kronIdx d 0) (kronIdx d 0) ℂ).trace = A.trace ^ 0
      rw [Matrix.trace_one, card_kronIdx]
      simp
  | n + 1 => by
      change (kronPow d n A ⊗ₖ A).trace = A.trace ^ (n + 1)
      rw [Matrix.trace_kronecker, trace_kronPow d A n, pow_succ]

/-- Kronecker powers are multiplicative. -/
theorem kronPow_mul (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) :
    ∀ n : ℕ, kronPow d n (A * B) = kronPow d n A * kronPow d n B
  | 0 => by simp [kronPow]
  | n + 1 => by
      change kronPow d n (A * B) ⊗ₖ (A * B) =
        (kronPow d n A ⊗ₖ A) * (kronPow d n B ⊗ₖ B)
      rw [kronPow_mul d A B n, Matrix.mul_kronecker_mul]

/-- Kronecker powers commute with the adjoint. -/
theorem kronPow_conjTranspose (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    ∀ n : ℕ, (kronPow d n A)ᴴ = kronPow d n Aᴴ
  | 0 => by simp [kronPow]
  | n + 1 => by
      change (kronPow d n A ⊗ₖ A)ᴴ = kronPow d n Aᴴ ⊗ₖ Aᴴ
      rw [Matrix.conjTranspose_kronecker, kronPow_conjTranspose d A n]

/-- The Kronecker power of the identity is the identity. -/
theorem kronPow_one (d : ℕ) : ∀ n : ℕ, kronPow d n (1 : Matrix (Fin d) (Fin d) ℂ) = 1
  | 0 => rfl
  | n + 1 => by
      change kronPow d n (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ 1 = 1
      rw [kronPow_one d n]
      exact Matrix.one_kronecker_one

/-- The Kronecker power of a unitary matrix is unitary. -/
theorem kronPow_mem_unitaryGroup {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ) (n : ℕ) :
    kronPow d n A ∈ Matrix.unitaryGroup (kronIdx d n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, kronPow_conjTranspose,
    ← kronPow_mul]
  have hAA : Aᴴ * A = 1 := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hA
    exact hA
  rw [hAA, kronPow_one]

/-- `M`-copy global fidelity is the `M`-th power of the single-copy unitary
channel fidelity; this is the tensor-power content of the paper's goal function
`f_M(U,Û) = (‖Tr[U†Û]‖/d)^{2M}`. -/
theorem unitaryChannelFidelity_kronPow {d M : ℕ} (hd : 0 < d)
    (U V : Matrix (Fin d) (Fin d) ℂ) :
    (unitaryChannelFidelity (I := kronIdx d M) (kronPow d M U) (kronPow d M V)) =
      (unitaryChannelFidelity (I := Fin d) U V) ^ M := by
  have hdtrace : ((kronPow d M U)ᴴ * kronPow d M V).trace = ((Uᴴ * V).trace) ^ M := by
    rw [kronPow_conjTranspose, ← kronPow_mul, trace_kronPow]
  have hcard : Fintype.card (kronIdx d M) = d ^ M := card_kronIdx d M
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdM : ((d : ℝ) ^ M) ≠ 0 := pow_ne_zero _ hdR.ne'
  rw [unitaryChannelFidelity, hdtrace, Complex.norm_pow]
  rw [hcard]
  push_cast
  have h1 : (‖(Uᴴ * V).trace‖ ^ M) ^ 2 = (‖(Uᴴ * V).trace‖ ^ 2) ^ M := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have h2 : ((d : ℝ) ^ M) ^ 2 = ((d : ℝ) ^ 2) ^ M := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [h1, h2, ← div_pow, unitaryChannelFidelity]
  simp only [Fintype.card_fin]

/-- Paper Sec. III B.2: the goal function of `M`-copy learning,
`f_M(U,Û) = (‖Tr[U†Û]‖/d)^{2M}`. -/
def globalGoal (d M : ℕ) (U V : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (‖(Uᴴ * V).trace‖ / (d : ℝ)) ^ (2 * M)

/-- The goal function is the `M`-th power of the unitary channel fidelity. -/
theorem globalGoal_eq_pow {d M : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ) :
    globalGoal d M U V = (unitaryChannelFidelity (I := Fin d) U V) ^ M := by
  rw [globalGoal, unitaryChannelFidelity]
  simp only [Fintype.card_fin]
  rw [← div_pow, ← pow_mul, div_pow]

/-- Cyclicity of the trace and conjugation: `Tr[U V†] = conj Tr[U† V]`. -/
theorem trace_mul_conjTranspose {d : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ) :
    (U * Vᴴ).trace = star ((Uᴴ * V).trace) := by
  have hconj : Vᴴ * U = (Uᴴ * V)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.trace_mul_comm U Vᴴ, hconj, Matrix.trace_conjTranspose]

/-- Passing to adjoints — the inversion task of Sec. IV — leaves the unitary
channel fidelity unchanged. -/
theorem unitaryChannelFidelity_adjoint {d : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ) :
    unitaryChannelFidelity (I := Fin d) Uᴴ Vᴴ =
      unitaryChannelFidelity (I := Fin d) U V := by
  unfold unitaryChannelFidelity
  simp only [Matrix.conjTranspose_conjTranspose]
  rw [trace_mul_conjTranspose, norm_star]

/-- The `M`-copy inversion goal function is the `M`-copy learning goal
function: Sec. IV's substitution `U → U†` does not change the fidelity. -/
theorem globalGoal_adjoint {d M : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ) :
    globalGoal d M Uᴴ Vᴴ = globalGoal d M U V := by
  unfold globalGoal
  simp only [Matrix.conjTranspose_conjTranspose]
  rw [trace_mul_conjTranspose, norm_star]

end Qatlib.Papers.UnitaryLearn09.MainResults
