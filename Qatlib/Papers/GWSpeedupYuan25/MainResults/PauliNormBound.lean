/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GWSpeedupYuan25.MainResults.Definitions
public import Qatlib.Concepts.PauliClifford.PauliBasis

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# GWSpeedupYuan25 — the operator norm of a Pauli expansion is bounded by its Pauli `ℓ1` norm

Paper: [arXiv:2510.08292v1](https://arxiv.org/abs/2510.08292v1), Appendix B, proof of
Theorem 32, Eq. (B5)–(B7); the Pauli `ℓ1` norm is Definition 3 (§II D, Eq. (16)) and
Definition 31 (Eq. (B2)).

The paper bounds the operator norm of a Pauli expansion `C = ∑_p c_p P_p` by its Pauli `ℓ1`
norm `‖C‖_{P,ℓ1} = ∑_p |c_p|`: each `P_p` is a unitary, hence has operator norm one, and the
triangle inequality gives `‖C‖ ≤ ‖C‖_{P,ℓ1}`. This is the finite-dimensional step that turns
the sparsified approximation `‖C − C̃‖ ≤ ε` of Eq. (B7) into an error on the value of the
QUBO and unnormalised Goemans–Williamson programs, and it is the inequality
`‖X‖ ≤ ‖C‖_{P,ℓ1}` used in the same proof.

The proof reuses the tensor-product Pauli basis of
`Qatlib.Concepts.PauliClifford.PauliBasis`: the paper's Pauli string
`Qatlib.Papers.GWSpeedupYuan25.MainResults.pauliOp` is identified with the Pauli word matrix
`Qatlib.Concepts.PauliClifford.PauliBasis.pauliWord` through the four-valued letter encoding
`pauliLetter`; `pauliWord` is unitary by `word_unitary`, and a unitary matrix has operator
norm one by `CStarRing.norm_of_mem_unitary`.

## Main statements

* `pauliOp_opNorm_eq_one`: every Pauli string in the paper's `(x,z)` labelling has operator
  norm one.
* `pauliExpand_opNorm_le_pauliL1`: `‖pauliExpand c‖ ≤ pauliL1 c`.

Boundary: the inequality is proved for the paper's own concrete matrix model on
`Reg n = Fin n → Bool` with the `ℓ²` operator norm. The sampling distribution of Proposition 8,
its `2/3` success probability, and the passage from an operator-norm error to a value error of
`GW` or `QUBO` are outside this module.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GWSpeedupYuan25.MainResults

open Matrix
open Qatlib.Papers.GWSpeedupYuan25.MainResults
open Qatlib.Concepts.PauliClifford.PauliBasis
open Qatlib.Concepts.GateVocabulary.GateVocab
open scoped BigOperators Matrix.Norms.L2Operator

/-- The four-valued Pauli letter of a single-site label `(x,z)`, numbered as in
`pauliBool`: `0` is the identity, `1` is `X`, `2` is `Y` and `3` is `Z`. The paper's label
`(x,z)` stands for `X^x Z^z` up to the phase `i^{xz}`, so `(true, true)` is `Y`. -/
def pauliLetter (x z : Bool) : Fin 4 :=
  if x then (if z then 2 else 1) else (if z then 3 else 0)

/-- The paper's single-site Pauli matrix `pauli1Mat` is the shared Pauli family `pauliBool`
at the letter `pauliLetter`; this is the identification of the two letter encodings. -/
theorem pauli1Mat_eq_pauliBool (x z : Bool) :
    pauli1Mat x z = pauliBool (pauliLetter x z) := by
  cases x <;> cases z <;>
    ext a b <;> cases a <;> cases b <;>
      norm_num [pauli1Mat, pauliLetter, pauliBool, pauliYBool,
        Qatlib.Foundations.PureStateMath.PauliX, Qatlib.Foundations.PureStateMath.PauliZ,
        Qatlib.Foundations.PureStateMath.permMatrix, Matrix.diagonal_apply,
        Matrix.one_apply, Complex.I_sq]

/-- The `n`-qubit Pauli string `pauliOp n p` is the tensor-product Pauli word matrix of the
letter family `pauliLetter` applied site by site. -/
theorem pauliOp_eq_pauliWord (n : ℕ) (p : PauliIndex n) :
    pauliOp n p = pauliWord (fun k => pauliLetter (p.1 k) (p.2 k)) := by
  ext i j
  simp only [pauliOp, pauliWord]
  refine Finset.prod_congr rfl ?_
  intro k _
  rw [pauli1Mat_eq_pauliBool]

/-- Every Pauli string `pauliOp n p` is a unitary matrix. -/
theorem pauliOp_mem_unitaryGroup (n : ℕ) (p : PauliIndex n) :
    pauliOp n p ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [pauliOp_eq_pauliWord]
  exact word_unitary _

/-- Every Pauli string in the paper's `(x,z)` labelling has `ℓ²` operator norm one. -/
theorem pauliOp_opNorm_eq_one (n : ℕ) (p : PauliIndex n) : ‖pauliOp n p‖ = 1 :=
  CStarRing.norm_of_mem_unitary (pauliOp_mem_unitaryGroup n p)

/-- The norm of a single scaled Pauli string is the absolute value of its coefficient. -/
theorem norm_smul_pauliOp (n : ℕ) (c : PauliIndex n → ℝ) (p : PauliIndex n) :
    ‖(c p : ℂ) • pauliOp n p‖ = |c p| := by
  rw [norm_smul, pauliOp_opNorm_eq_one, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- Definition 3 / Definition 31, Appendix B Eq. (B5)–(B7): the operator norm of the Pauli
expansion `pauliExpand c` is at most the Pauli `ℓ1` norm `pauliL1 c = ∑_p |c_p|`. -/
theorem pauliExpand_opNorm_le_pauliL1 (n : ℕ) (c : PauliIndex n → ℝ) :
    ‖pauliExpand c‖ ≤ pauliL1 c := by
  calc
    ‖pauliExpand c‖ = ‖∑ p, (c p : ℂ) • pauliOp n p‖ := rfl
    _ ≤ ∑ p, ‖(c p : ℂ) • pauliOp n p‖ := norm_sum_le _ _
    _ = ∑ p, |c p| := Finset.sum_congr rfl (fun p _ => norm_smul_pauliOp n c p)
    _ = pauliL1 c := rfl

/-- The Pauli expansion is additive in the coefficient function. -/
theorem pauliExpand_sub (n : ℕ) (c d : PauliIndex n → ℝ) :
    pauliExpand (fun p => c p - d p) = pauliExpand c - pauliExpand d := by
  simp [pauliExpand, Finset.sum_sub_distrib, sub_smul]

/-- Appendix B Eq. (B7) in operator-norm form: the operator norm of the difference of two Pauli
expansions is at most the Pauli `ℓ1` norm of the coefficient difference. A sparsified
approximation `C̃` with `pauliL1 (c − c̃) ≤ ε` therefore satisfies `‖C − C̃‖ ≤ ε`. -/
theorem pauliExpand_sub_opNorm_le_pauliL1 (n : ℕ) (c d : PauliIndex n → ℝ) :
    ‖pauliExpand c - pauliExpand d‖ ≤ pauliL1 (fun p => c p - d p) := by
  rw [← pauliExpand_sub]
  exact pauliExpand_opNorm_le_pauliL1 n _

end Qatlib.Papers.GWSpeedupYuan25.MainResults
