/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

open Matrix Finset BigOperators
set_option autoImplicit false

/-!
# Permutation operators and block tensor products for `SpoofedXEB24`

The paper (Tanggara–Gu–Bharti, arXiv:2405.00789v2, §3.2 and Appendix F) expands mQSVT
output probabilities in Pauli paths and evaluates Haar averages through Weingarten
functions.  The trace factors there are of the shape

`Tr (W_π (Q_1 ⊗ ⋯ ⊗ Q_k))`,

where `W_π` is the permutation operator of `π ∈ S_k` acting on `k` two-qubit registers
and the `Q_i` are two-qubit Paulis.  This module fixes that object in the
`(Fin k → d)`-basis representation: `permOp σ` is the permutation matrix of `σ` and
`tensorAll Q` is the block tensor product, so that the trace becomes the Pauli-path sum
`∑ x, ∏ i, Q i (x (σ⁻¹ i)) (x i)`.

The combinatorial content of Lemma 1 — the factorisation of this trace over the cyclic
partitions of `π` — is recorded separately in the `LemmaOne` module once available; this
module only provides the representation and the trace rewrite.
-/

namespace Qatlib.Papers.SpoofedXEB24.MainResults

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The multi-register tensor product `Q 0 ⊗ ⋯ ⊗ Q (k-1)` in the basis `Fin k → d`. -/
def tensorAll {k : ℕ} (Q : Fin k → Matrix d d ℂ) : Matrix (Fin k → d) (Fin k → d) ℂ :=
  fun x y => ∏ i, Q i (x i) (y i)

/-- The permutation operator `W_σ` acting on `Fin k → d`. -/
def permOp {k : ℕ} (σ : Equiv.Perm (Fin k)) : Matrix (Fin k → d) (Fin k → d) ℂ :=
  fun x y => if y = x ∘ σ.symm then 1 else 0

/-- The `(x, y)` entry of `W_σ · (Q 0 ⊗ ⋯ ⊗ Q (k-1))` is the tensor-product entry at
`(x ∘ σ⁻¹, y)`. -/
lemma permOp_mul_tensorAll_apply {k : ℕ} (σ : Equiv.Perm (Fin k))
    (Q : Fin k → Matrix d d ℂ) (x y : Fin k → d) :
    ((permOp (d := d) σ * tensorAll Q : Matrix (Fin k → d) (Fin k → d) ℂ)) x y
      = tensorAll Q (x ∘ σ.symm) y := by
  conv_lhs => rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (x ∘ σ.symm)]
  · simp [permOp]
  · intro z _ hz
    simp [permOp, hz]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The trace as a Pauli-path sum**: `Tr (W_σ (Q 0 ⊗ ⋯ ⊗ Q (k-1)))` is the sum over
assignments `x` of the product of the matrix entries along the permutation `σ`. -/
theorem trace_permOp_mul_tensorAll {k : ℕ} (σ : Equiv.Perm (Fin k))
    (Q : Fin k → Matrix d d ℂ) :
    ((permOp (d := d) σ * tensorAll Q : Matrix (Fin k → d) (Fin k → d) ℂ)).trace
      = ∑ x : Fin k → d, ∏ i, Q i (x (σ.symm i)) (x i) := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply, permOp_mul_tensorAll_apply]
  simp [tensorAll, Function.comp]

/-- **Trace of the permutation operator**: `Tr W_σ` counts the assignments fixed by `σ`,
i.e. the functions constant on the cycles of `σ`.  In particular `Tr W_π = d^{c_π}` for a
permutation with `c_π` cycles. -/
theorem trace_permOp {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    (permOp (d := d) σ).trace
      = ((Finset.univ.filter fun x : Fin k → d => x = x ∘ σ.symm).card : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show permOp (d := d) σ x x = (if x = x ∘ σ.symm then (1:ℂ) else 0) from rfl]


/-- **Factorisation of a product-sum over a finite function type.**  This is the
combinatorial step behind the cycle-factorisation of Lemma 1: the sum over assignments of a
product of per-coordinate factors splits into the product of the per-coordinate sums. -/
lemma sum_fin_pi_prod {k : ℕ} (β : Fin k → Type*) [∀ i, Fintype (β i)]
    (g : ∀ i, β i → ℂ) :
    (∑ x : (∀ i, β i), ∏ i, g i (x i)) = ∏ i, ∑ a, g i a := by
  induction k with
  | zero =>
      haveI : Subsingleton ((i : Fin 0) → β i) := ⟨fun f g => funext fun i => i.elim0⟩
      simp
  | succ k ih =>
      rw [Fintype.sum_equiv (Fin.consEquiv (n := k) β).symm
        (fun x : (i : Fin (k+1)) → β i => ∏ i, g i (x i))
        (fun p : β 0 × ((i : Fin k) → β i.succ) =>
          ∏ i, g i ((Fin.consEquiv β p) i))]
      · rw [Fintype.sum_prod_type]
        simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        rw [ih (fun i => β i.succ) (fun i a => g i.succ a)]
      · intro x
        simp

omit [DecidableEq d] in
/-- **The trace of a block tensor product is the product of the traces.**  This is the
`π = id` case of the cyclic-partition formula (every block is its own singleton cycle). -/
theorem trace_tensorAll {k : ℕ} (Q : Fin k → Matrix d d ℂ) :
    (tensorAll Q).trace = ∏ i, (Q i).trace := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, tensorAll]
  rw [sum_fin_pi_prod (fun _ : Fin k => d) (fun i a => Q i a a)]
  rfl

omit [Fintype d] in
/-- The permutation operator of the identity permutation is the identity matrix. -/
lemma permOp_one {k : ℕ} : permOp (d := d) (1 : Equiv.Perm (Fin k)) = 1 := by
  ext x y
  show (if y = x ∘ ⇑(Equiv.refl (Fin k)) then (1:ℂ) else 0)
    = (1 : Matrix (Fin k → d) (Fin k → d) ℂ) x y
  rw [Equiv.coe_refl, Function.comp_id]
  simp only [Matrix.one_apply]
  by_cases h : y = x
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]

/-- **Lemma 1 at the identity permutation**: `Tr (W_1 (Q 0 ⊗ ⋯ ⊗ Q (k-1)))` is the product
of the traces. -/
theorem trace_permOp_one_mul_tensorAll {k : ℕ} (Q : Fin k → Matrix d d ℂ) :
    ((permOp (d := d) (1 : Equiv.Perm (Fin k)) * tensorAll Q :
      Matrix (Fin k → d) (Fin k → d) ℂ)).trace = ∏ i, (Q i).trace := by
  rw [permOp_one, Matrix.one_mul, trace_tensorAll]

/-- **Lemma 1 at a transposition**: for two-block permutations,
`Tr (W_(0 1) (A ⊗ B)) = Tr (A B)`, the `l = 2` instance of equation (41) of the paper. -/
theorem trace_permOp_swap_mul_tensorAll (A B : Matrix d d ℂ) :
    ((permOp (d := d) (Equiv.swap (0 : Fin 2) 1) * tensorAll ![A, B] :
      Matrix (Fin 2 → d) (Fin 2 → d) ℂ)).trace = (A * B).trace := by
  rw [trace_permOp_mul_tensorAll]
  have hprod : ∀ x : Fin 2 → d,
      (∏ i : Fin 2, ![A, B] i (x ((Equiv.swap (0 : Fin 2) 1).symm i)) (x i))
        = A (x 1) (x 0) * B (x 0) (x 1) := by
    intro x
    rw [Fin.prod_univ_two]
    simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  simp only [hprod]
  rw [Fintype.sum_equiv (finTwoArrowEquiv d) _
    (fun p : d × d => A p.2 p.1 * B p.1 p.2)]
  · rw [Fintype.sum_prod_type]
    rw [Matrix.trace_mul_comm A B, Matrix.trace]
    simp only [Matrix.diag_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  · intro x
    simp [finTwoArrowEquiv]

end Qatlib.Papers.SpoofedXEB24.MainResults
