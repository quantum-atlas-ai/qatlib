/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Block
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

set_option backward.isDefEq.respectTransparency false

/-!
# Readout — c006 of SteadyState20

Fixed source: arXiv:2008.07133v2 (Quantum **5**, 420 (2021)), Section 4, p. 8,
Eqs. (14), (15), (16), and (17):

* Eq. (14): `Tr(Ô ρ̂_ss) = ⟨I|O|ρ_ss⟩ = ⟨ρ_ss|O|I⟩`, where `O = I ⊗ Ô` is the
  superoperator acting on the vectorized density matrix.
* Eq. (15): the Hermitian readout operator `Q = X ⊗ O = [[0, O], [O, 0]]` acting on the
  `(2N+1)`-qubit second register.
* Eq. (16): `Tr(Ô ρ̂_ss) = ⟨η₀|Q|η₁⟩ = ⟨η₁|Q|η₀⟩` and `⟨η₀|Q|η₀⟩ = ⟨η₁|Q|η₁⟩ = 0`.
* Eq. (17): `⟨ψ₃|I ⊗ Q|ψ₃⟩ = c₁ Tr(Ô ρ̂_ss) + (spurious terms)`.

Formalisation (the vectorized inner product is represented by the Hilbert–Schmidt
pairing `⟨A|B⟩ = Tr(A† B)`):

* `hsInner` is `⟨A|B⟩ = Tr(A† B)`, the vectorized inner product of the matrix
  representations; the superoperator `O = I ⊗ Ô` acts by left multiplication
  `X ↦ Ô * X`.  Eq. (14) is `trace_eq_hsInner`.
* Block vectors are represented as pairs of matrices; `Q` swaps the two blocks and
  applies `O` (`Q`, Eq. (15)).
* `eta0_Q_eta1` and `eta1_Q_eta0` prove the two equalities of Eq. (16); the diagonal
  vanishing `⟨η₀|Q|η₀⟩ = ⟨η₁|Q|η₁⟩ = 0` is `eta0_Q_eta0`, `eta1_Q_eta1`.
* `Q_expectation_no_spurious` proves the exact Eq. (17) coefficient structure without
  the spurious terms: for `v = a|η₀⟩ + b|η₁⟩`,
  `⟨v|Q|v⟩ = (ā b + b̄ a) Tr(Ô ρ̂_ss)`.  With the paper's normalisation `a = 1/√2`,
  `b = c₁/√2` and real `c₁`, this is `c₁ Tr(Ô ρ̂_ss)`, matching the leading term of
  Eq. (17).

The spurious terms of Eq. (17) are the `O(|α₀^(j)|)` and `O(|α₀^(j)|²)` remainders whose
decay in `t` is established separately in `MainResults.PhaseEstimationError`
(claim c004); they are not part of this file's statements.

Shared interface: expectation-value measurement of Hermitian observables on a quantum
state is the province of `QuantumAlgorithm.MeasureStats.PauliShadows` (Frozen v2.0.2);
this file contributes the algebraic readout identities that make that measurement
applicable to the NESS state.
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix BigOperators

namespace Qatlib.Papers.SteadyState20.MainResults.Readout

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Hilbert–Schmidt inner product of the vectorized matrices `A` and `B`:
`⟨A|B⟩ = Tr(A† B)`, i.e. the vectorized inner product of `|A⟩` and `|B⟩`. -/
def hsInner (A B : Matrix ι ι ℂ) : ℂ := (Aᴴ * B).trace

/-- `⟨I|B⟩ = Tr(B)`: the bra `⟨I|` of Eq. (14). -/
theorem hsInner_one_left (B : Matrix ι ι ℂ) : hsInner 1 B = B.trace := by
  simp [hsInner]

/-- `⟨0|B⟩ = 0`. -/
theorem hsInner_zero_left (B : Matrix ι ι ℂ) : hsInner 0 B = 0 := by
  simp [hsInner]

/-- `⟨A|0⟩ = 0`. -/
theorem hsInner_zero_right (A : Matrix ι ι ℂ) : hsInner A 0 = 0 := by
  simp [hsInner]

/-- Paper Eq. (14) (arXiv:2008.07133v2, Sec. 4, p. 8): the trace average
`Tr(Ô ρ̂_ss)` equals the vectorized matrix element `⟨I| I⊗Ô |ρ̂_ss⟩`.  The superoperator
`O = I ⊗ Ô` acts on vectorized density matrices by left multiplication `X ↦ Ô * X`. -/
theorem trace_eq_hsInner (O ρ : Matrix ι ι ℂ) :
    hsInner 1 (O * ρ) = (O * ρ).trace :=
  hsInner_one_left _

/-- A block vector `(A, B)` in the `|0⟩`/`|1⟩` block space, i.e. `|0⟩|A⟩ + |1⟩|B⟩`
(the paper's `|η⟩ = |0⟩|a⟩ + |1⟩|b⟩`). -/
abbrev BlockVec (ι : Type*) := Matrix ι ι ℂ × Matrix ι ι ℂ

/-- Paper Sec. 2, p. 4: `|η₀⟩ = |0⟩|I⟩`. -/
def eta0 : BlockVec ι := (1, 0)

/-- Paper Sec. 2, p. 4: `|η₁⟩ = |1⟩|ρ̂_ss⟩`. -/
def eta1 (ρ : Matrix ι ι ℂ) : BlockVec ι := (0, ρ)

/-- Paper Eq. (15) (Sec. 4, p. 8): `Q = X ⊗ O` acts on block vectors by swapping the
two `|0⟩`/`|1⟩` blocks and applying the superoperator `O = I ⊗ Ô` to the block. -/
def Q (O : Matrix ι ι ℂ) (v : BlockVec ι) : BlockVec ι := (O * v.2, O * v.1)

/-- The block inner product `⟨A,B|C,D⟩ = ⟨A|C⟩ + ⟨B|D⟩` on `H ⊕ H`. -/
def blockInner (v w : BlockVec ι) : ℂ := hsInner v.1 w.1 + hsInner v.2 w.2

/-- Paper Eq. (16), first equality (Sec. 4, p. 8): `Tr(Ôρ̂_ss) = ⟨η₀|Q|η₁⟩`. -/
theorem eta0_Q_eta1 (O ρ : Matrix ι ι ℂ) :
    blockInner eta0 (Q O (eta1 ρ)) = (O * ρ).trace := by
  simp [blockInner, eta0, eta1, Q, hsInner_one_left, hsInner_zero_left]

/-- Paper Eq. (16), second equality (Sec. 4, p. 8): `⟨η₀|Q|η₁⟩ = ⟨η₁|Q|η₀⟩`; the
right-hand side reduces to `Tr(ρ̂_ss Ô) = Tr(Ô ρ̂_ss)` by cyclicity of the trace, using
Hermiticity of the density matrix. -/
theorem eta1_Q_eta0 (O ρ : Matrix ι ι ℂ) (hρ : ρᴴ = ρ) :
    blockInner (eta1 ρ) (Q O eta0) = (O * ρ).trace := by
  simp only [blockInner, eta1, eta0, Q, Matrix.mul_zero, Matrix.mul_one,
    hsInner_zero_left, zero_add]
  rw [hsInner, hρ, Matrix.trace_mul_comm ρ O]

/-- Paper Eq. (16), p. 8: `⟨η₀|Q|η₀⟩ = 0`, one of the two diagonal vanishing
relations following from the block structure of `Q`. -/
theorem eta0_Q_eta0 (O : Matrix ι ι ℂ) : blockInner eta0 (Q O eta0) = 0 := by
  simp [blockInner, eta0, Q, hsInner_zero_left, hsInner_zero_right]

/-- Paper Eq. (16), p. 8: `⟨η₁|Q|η₁⟩ = 0`. -/
theorem eta1_Q_eta1 (O ρ : Matrix ι ι ℂ) : blockInner (eta1 ρ) (Q O (eta1 ρ)) = 0 := by
  simp [blockInner, eta1, Q, hsInner_zero_left, hsInner_zero_right]

/-- Bilinearity of the Hilbert–Schmidt pairing under scalar multiples:
`⟨a A|b B⟩ = ā b ⟨A|B⟩`. -/
theorem hsInner_smul_smul (a b : ℂ) (A B : Matrix ι ι ℂ) :
    hsInner (a • A) (b • B) = star a * b * hsInner A B := by
  unfold hsInner
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_smul, smul_eq_mul]

/-- Paper Eq. (17) (Sec. 4, p. 8), spurious-free part: for
`|v⟩ = a|η₀⟩ + b|η₁⟩`, the expectation of `Q` is
`⟨v|Q|v⟩ = (ā b + b̄ a) Tr(Ô ρ̂_ss)`.

With the paper's normalisation `a = b = 1/√2` and real `c₁` (`b = c₁/√2`), and a real
trace average, the scalar prefactor is `c₁`, giving the leading term `c₁ Tr(Ô ρ̂_ss)` of
Eq. (17).  The remaining, spurious contributions of Eq. (17) involve the QPE amplitudes
`α₀^(j)` and are treated in claim c004. -/
theorem Q_expectation_no_spurious (O ρ : Matrix ι ι ℂ) (hρ : ρᴴ = ρ) (a b : ℂ) :
    blockInner (a • eta0 + b • eta1 ρ) (Q O (a • eta0 + b • eta1 ρ))
      = (star a * b + star b * a) * (O * ρ).trace := by
  have hQ : Q O (a • eta0 + b • eta1 ρ) = (b • (O * ρ), a • O) := by
    apply Prod.ext
    · simp [Q, eta0, eta1]
    · simp [Q, eta0, eta1]
  have hsum : a • eta0 + b • eta1 ρ = (a • (1 : Matrix ι ι ℂ), b • ρ) := by
    apply Prod.ext <;> simp [eta0, eta1]
  rw [hQ, hsum]
  simp only [blockInner]
  have h2 : hsInner ρ O = (O * ρ).trace := by
    rw [hsInner, hρ, Matrix.trace_mul_comm ρ O]
  rw [hsInner_smul_smul, hsInner_smul_smul, hsInner_one_left, h2]
  ring

end Qatlib.Papers.SteadyState20.MainResults.Readout
