/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-! Bell-basis orthogonality for
"Hamiltonian Decoded Quantum Interferometry"
(arXiv:2510.07913, 2025), Lemma 46.

The paper's Lemma 46 shows that the Weyl (generalized Pauli) operators
`W_a` map the maximally entangled state `|Φ_d⟩ = d^{-1/2} ∑ᵢ |i⟩|i⟩`
to an orthonormal family of Bell states: the inner product of two Bell
states is the normalized Hilbert–Schmidt inner product of the
operators, and the Weyl operators satisfy the Frobenius orthogonality
`⟨W_a, W_b⟩_HS = d δ_{a,b}` (non-identity Pauli operators are
traceless, so distinct Weyl operators are orthogonal). Here the
tensor-product space is flattened to functions on `Fin d × Fin d`, and
the Frobenius orthogonality enters as a hypothesis; the abstract
identification of `(ℂ^d)^{⊗ 2n}` with `(ℂ^d) ⊗ (ℂ^d)` is the only
bridging step left implicit.

- `invSqrt` is the normalization constant `d^{-1/2}`.
- `bellPhi` is the maximally entangled state `|Φ_d⟩`.
- `tensorLeft` is the matrix of `A ⊗ I` on the first factor.
- `bellState` is the Bell state `(A ⊗ I)|Φ_d⟩`.
- `bellState_apply` computes the entries of a Bell state.
- `bell_inner` reduces Bell-state inner products to normalized
  Hilbert–Schmidt inner products of the operators.
- `bell_orthonormal` is Lemma 46: Frobenius-orthogonal operator
  families give orthonormal Bell families.

These are algebraic identities; no circuit synthesis or gate bound is proved. -/
set_option autoImplicit false

namespace Qatlib.Papers.HamDecodedQI25.MainResults.BellBasis

variable {d : ℕ}

/-- The normalization constant `d^{-1/2} = 1/√d` as a complex number. -/
noncomputable def invSqrt (d : ℕ) : ℂ := (Complex.ofReal (Real.sqrt d))⁻¹

/-- The maximally entangled state `|Φ_d⟩ = d^{-1/2} ∑ᵢ |i⟩ ⊗ |i⟩` as a
function on the flattened index `Fin d × Fin d`. -/
noncomputable def bellPhi (d : ℕ) : Fin d × Fin d → ℂ :=
  fun p => if p.1 = p.2 then invSqrt d else 0

/-- The matrix of the operator `A ⊗ I` acting on the first tensor
factor, with flattened row and column indices in `Fin d × Fin d`. -/
def tensorLeft (A : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun p q => A p.1 q.1 * (if p.2 = q.2 then (1 : ℂ) else 0)

/-- The Bell state associated with an operator `A`, i.e. the vector
`(A ⊗ I)|Φ_d⟩` in flattened tensor-product coordinates. -/
noncomputable def bellState (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) : Fin d × Fin d → ℂ :=
  (tensorLeft A).mulVec (bellPhi d)

/-- The normalization constant is real, hence fixed by conjugation. -/
theorem conj_invSqrt (d : ℕ) : starRingEnd ℂ (invSqrt d) = invSqrt d := by
  simp only [invSqrt, map_inv₀]
  simp

/-- The squared normalization constant equals `d⁻¹` for every `d`
(both sides are `0` when `d = 0`). -/
theorem invSqrt_sq (d : ℕ) : invSqrt d * invSqrt d = (d : ℂ)⁻¹ := by
  by_cases hd : d = 0
  · subst hd
    simp [invSqrt]
  · have hs : Complex.ofReal (Real.sqrt d) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr
        ((Real.sqrt_ne_zero (by positivity)).mpr (Nat.cast_ne_zero.mpr hd))
    have h1 : Complex.ofReal (Real.sqrt d) * Complex.ofReal (Real.sqrt d) = (d : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      rfl
    simp only [invSqrt]
    rw [← mul_inv, h1]

/-- Entrywise description of a Bell state: the `(i, k)` entry of the
vector `(A ⊗ I)|Φ_d⟩` is `A i k * d^{-1/2}`. -/
theorem bellState_apply (A : Matrix (Fin d) (Fin d) ℂ) (i k : Fin d) :
    bellState d A (i, k) = A i k * invSqrt d := by
  classical
  simp only [bellState, Matrix.mulVec, dotProduct, tensorLeft, bellPhi]
  rw [Finset.sum_eq_single (k, k)]
  · simp
  · intro q _ hq
    by_cases h2 : k = q.2
    · have h1 : q.1 ≠ q.2 := by
        intro he
        exact hq (Prod.ext_iff.mpr ⟨he.trans h2.symm, h2.symm⟩)
      rw [if_pos h2, if_neg h1, mul_zero]
    · rw [if_neg h2]
      simp
  · simp

/-- Inner products of Bell states are normalized Hilbert–Schmidt inner
products of the operators:
`⟨(A ⊗ I)Φ, (B ⊗ I)Φ⟩ = d⁻¹ ⟨A, B⟩_HS`. -/
theorem bell_inner (A B : Matrix (Fin d) (Fin d) ℂ) :
    ∑ p : Fin d × Fin d, starRingEnd ℂ (bellState d A p) * bellState d B p
      = (d : ℂ)⁻¹ * ∑ p : Fin d × Fin d, starRingEnd ℂ (A p.1 p.2) * B p.1 p.2 := by
  have hterm : ∀ p : Fin d × Fin d,
      starRingEnd ℂ (bellState d A p) * bellState d B p
        = invSqrt d * invSqrt d * (starRingEnd ℂ (A p.1 p.2) * B p.1 p.2) := by
    intro p
    rw [bellState_apply, bellState_apply, map_mul, conj_invSqrt]
    ring
  rw [Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.mul_sum, invSqrt_sq]

/-- **Lemma 46 (Bell orthonormality)**: an operator family whose
Frobenius inner products satisfy `⟨W_a, W_b⟩_HS = d δ_{a,b}` (as the
Weyl operators do, since non-identity Paulis are traceless and distinct
Weyl operators are orthogonal) yields an orthonormal Bell family
`((W_a ⊗ I)|Φ_d⟩)_a`. -/
theorem bell_orthonormal {ι : Type*} [DecidableEq ι] (hd : d ≠ 0)
    (W : ι → Matrix (Fin d) (Fin d) ℂ)
    (hW : ∀ a b, ∑ p : Fin d × Fin d, starRingEnd ℂ (W a p.1 p.2) * W b p.1 p.2
      = if a = b then (d : ℂ) else 0) (a b : ι) :
    ∑ p : Fin d × Fin d, starRingEnd ℂ (bellState d (W a) p) * bellState d (W b) p
      = if a = b then 1 else 0 := by
  rw [bell_inner, hW a b]
  by_cases hab : a = b
  · subst hab
    simp [inv_mul_cancel₀ (show (d : ℂ) ≠ 0 by exact_mod_cast hd)]
  · simp [hab]

end Qatlib.Papers.HamDecodedQI25.MainResults.BellBasis
