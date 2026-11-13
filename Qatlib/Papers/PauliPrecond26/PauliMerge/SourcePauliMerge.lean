/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Real.Basic
import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs

set_option backward.isDefEq.respectTransparency false

/-!
# PauliPrecond26 / PauliMerge — Proposition 6 and Theorem 13

Source: H. Nie, Z. Lai, D. An, *Pauli-structured preconditioning for quantum
linear system solvers*, arXiv:2606.01733v1 (2026-06-01), Proposition 6
(pp. 6--7) and Theorem 13 (pp. 8--9).

The paper writes the system matrix and the preconditioner in the Pauli basis,
`A = ∑_ℓ a_ℓ A_ℓ` and `P = ∑_m β_m P_m`, and defines the Pauli coefficient
weights `w(A) = ∑_ℓ |a_ℓ|`, `w(P) = ∑_m |β_m|`.  This file formalises:

* the product expansion of two finite Pauli sums, with the term-count bounds
  `J_L ≤ L M` and `J_S ≤ L M²` (Proposition 6 items 1 and 2);
* the coefficient-weight bounds `w(PA) ≤ w(P)w(A)` and
  `w(PAPᴴ) ≤ w(P)²w(A)` via the triangle inequality;
* the real-coefficient refinement when `PA` (respectively `PAPᴴ`) is
  Hermitian: pairwise averaging with the adjoint makes every coefficient
  real without increasing the weight;
* the Neumann-series part of Theorem 13: `‖I - PA‖ ≤ η < 1` implies that
  `PA` is invertible, that `σ_min(PA) ≥ 1 - η`, and hence the structural
  depth proxy `D_RQLS(PA) = (w(PA)/σ_min(PA))²` is bounded by
  `(w(P)w(A)/(1-η))²`.

The Pauli algebra (words, phases, `op`, multiplicativity and Hermiticity) is
reused from
`Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs`.
Scope note: this file proves the algebraic and structural bounds above.  The
asymptotic `Õ` depth expression (23) and the state-preparation and sampling-cost
clauses of Theorem 13 are algorithmic claims outside the scope of this file;
the depth estimate below takes the solver's complexity bound as a hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.PauliPrecond26.PauliMerge

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Foundations.PureStateMath

variable {n : ℕ}

/-- A finite Pauli expansion `∑_j c_j • op p_j`, stored as a list of
coefficient/Pauli-element pairs.  This is the paper's Pauli input model (1),
(2) with an arbitrary finite list of terms. -/
abbrev PauliSum (n : ℕ) : Type := List (ℂ × PauliElem n)

/-- A finite Pauli expansion whose coefficients are real and whose terms are
phase-free Pauli words (the Hermitian Pauli basis `V_n` of the paper). -/
abbrev RealPauliSum (n : ℕ) : Type := List (ℝ × PauliWord n)

/-- Evaluation of a Pauli sum as a matrix over the `n`-qubit register. -/
def evalSum {n : ℕ} (s : PauliSum n) : Matrix (Reg n) (Reg n) ℂ :=
  (s.map fun cq => cq.1 • op cq.2).sum

/-- Evaluation of a real, phase-free Pauli sum. -/
def evalRealSum {n : ℕ} (s : RealPauliSum n) : Matrix (Reg n) (Reg n) ℂ :=
  (s.map fun rw => (rw.1 : ℂ) • pauliWordOp n rw.2).sum

/-- The Pauli coefficient weight `w(·) = ∑_j |c_j|` of a Pauli sum. -/
def coeffWeight {n : ℕ} (s : PauliSum n) : ℝ :=
  (s.map fun cq => ‖cq.1‖).sum

/-- The Pauli coefficient weight of a real, phase-free Pauli sum. -/
def realWeight {n : ℕ} (s : RealPauliSum n) : ℝ :=
  (s.map fun rw => |rw.1|).sum

/-- Product expansion of two Pauli sums, term by term.  The product of the
Pauli elements is the phase-aware product `PauliElem.mul`; the scalar
coefficient multiplies.  No regrouping of equal words is performed. -/
def mulSum {n : ℕ} (s t : PauliSum n) : PauliSum n :=
  s.flatMap fun cq => t.map fun dr => (cq.1 * dr.1, PauliElem.mul cq.2 dr.2)

/-- Term-wise adjoint of a Pauli sum: conjugates coefficients and negates
phases, so that `evalSum (adjSum s) = (evalSum s)ᴴ`. -/
def adjSum {n : ℕ} (s : PauliSum n) : PauliSum n :=
  s.map fun cq => (star cq.1, ⟨cq.2.word, -cq.2.phase⟩)

/-- The symmetrised real Pauli expansion of a complex Pauli sum: each term
`z • op p` is replaced by `Re (z * i^{phase})` acting on the phase-free Pauli
word.  For a Hermitian target, `½(s + sᴴ)` equals this real expansion, and
its coefficient weight is at most the original weight because
`|Re z| ≤ |z|`. -/
def realSymm {n : ℕ} (s : PauliSum n) : RealPauliSum n :=
  s.map fun cq =>
    (Complex.re (cq.1 * (Complex.I ^ cq.2.phase.val)), cq.2.word)

/-- Evaluation is additive under list concatenation. -/
theorem evalSum_append {n : ℕ} (s t : PauliSum n) :
    evalSum (s ++ t) = evalSum s + evalSum t := by
  simp [evalSum, List.map_append, List.sum_append]

/-- Evaluation of a cons is the head term plus the tail evaluation. -/
theorem evalSum_cons {n : ℕ} (cq : ℂ × PauliElem n) (t : PauliSum n) :
    evalSum (cq :: t) = cq.1 • op cq.2 + evalSum t := by
  simp [evalSum]

/-- Coefficient weight is additive under list concatenation. -/
theorem coeffWeight_append {n : ℕ} (s t : PauliSum n) :
    coeffWeight (s ++ t) = coeffWeight s + coeffWeight t := by
  simp [coeffWeight, List.map_append, List.sum_append]

/-- Coefficient weight of a cons. -/
theorem coeffWeight_cons {n : ℕ} (cq : ℂ × PauliElem n) (t : PauliSum n) :
    coeffWeight (cq :: t) = ‖cq.1‖ + coeffWeight t := by
  simp [coeffWeight]

/-- Term count of the product expansion is the product of the term counts. -/
theorem length_mulSum {n : ℕ} (s t : PauliSum n) :
    (mulSum s t).length = s.length * t.length := by
  induction s with
  | nil => simp [mulSum]
  | cons hd tl ih =>
    rw [show mulSum (hd :: tl) t =
        (t.map fun dr => (hd.1 * dr.1, PauliElem.mul hd.2 dr.2)) ++ mulSum tl t
        from rfl]
    rw [List.length_append, List.length_map, ih, List.length_cons]
    ring

/-- Multiplying a Pauli sum on the left by one Pauli term `A = c • op p`
preserves evaluation as left multiplication by `A`. -/
theorem evalSum_map_mul_left {n : ℕ} (c : ℂ) (p : PauliElem n) (t : PauliSum n) :
    evalSum (t.map fun dr => (c * dr.1, PauliElem.mul p dr.2)) =
      (c • op p) * evalSum t := by
  induction t with
  | nil => simp [evalSum]
  | cons hd tl ih =>
    rw [List.map_cons, evalSum_cons, ih, evalSum_cons, op_mul, Matrix.mul_add,
      smul_mul_smul' c hd.1 (op p) (op hd.2)]

/-- The coefficient weight of that left-multiplied list is `‖c‖` times the
original weight. -/
theorem coeffWeight_map_mul_left {n : ℕ} (c : ℂ) (p : PauliElem n) (t : PauliSum n) :
    coeffWeight (t.map fun dr => (c * dr.1, PauliElem.mul p dr.2)) =
      ‖c‖ * coeffWeight t := by
  induction t with
  | nil => simp [coeffWeight]
  | cons hd tl ih =>
    rw [List.map_cons, coeffWeight_cons, ih, coeffWeight_cons, norm_mul]
    ring

/-- **c003, Proposition 6, product expansion.**  The product of two finite
Pauli expansions is again a finite Pauli expansion with at most `L M` terms
and with evaluation equal to the matrix product.  This is the unregrouped
form; regrouping equal Pauli words can only reduce the number of terms.

Source: Proposition 6, p. 7, proof sentence "The product of Pauli words is a
phase times a Pauli word.  Thus every term `P_m A_ℓ` ... can be rewritten as a
scalar multiple of a Pauli word." -/
theorem evalSum_mulSum {n : ℕ} (s t : PauliSum n) :
    evalSum (mulSum s t) = evalSum s * evalSum t := by
  induction s with
  | nil => simp [mulSum, evalSum]
  | cons hd tl ih =>
    rw [show mulSum (hd :: tl) t =
        (t.map fun dr => (hd.1 * dr.1, PauliElem.mul hd.2 dr.2)) ++ mulSum tl t
        from rfl]
    rw [evalSum_append, evalSum_map_mul_left, ih, evalSum_cons, Matrix.add_mul]

/-- **c003, Proposition 6, weight bound.**  The coefficient weight of the
product expansion is the product of the coefficient weights; by the triangle
inequality, the regrouped weight is at most this value.

Source: Proposition 6, p. 7:
`w(PA) ≤ ∑_{m,ℓ} |β_m| |a_ℓ| = w(P)w(A)`. -/
theorem coeffWeight_mulSum {n : ℕ} (s t : PauliSum n) :
    coeffWeight (mulSum s t) = coeffWeight s * coeffWeight t := by
  induction s with
  | nil => simp [mulSum, coeffWeight]
  | cons hd tl ih =>
    rw [show mulSum (hd :: tl) t =
        (t.map fun dr => (hd.1 * dr.1, PauliElem.mul hd.2 dr.2)) ++ mulSum tl t
        from rfl]
    rw [coeffWeight_append, coeffWeight_map_mul_left, ih, coeffWeight_cons]
    ring

/-- Conjugate transpose of a list sum is the sum of the conjugate transposes. -/
theorem conjTranspose_list_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : List (Matrix ι ι ℂ)) :
    (l.sum)ᴴ = (l.map fun M => Mᴴ).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp [Matrix.conjTranspose_add, ih]

/-- Evaluation of the term-wise adjoint is the conjugate transpose. -/
theorem evalSum_adjSum {n : ℕ} (s : PauliSum n) :
    evalSum (adjSum s) = (evalSum s)ᴴ := by
  unfold evalSum adjSum
  rw [conjTranspose_list_sum, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro cq _
  simp only [Function.comp_apply, Matrix.conjTranspose_smul, op_conjTranspose]

/-- The coefficient weight is unchanged by taking the term-wise adjoint. -/
theorem coeffWeight_adjSum {n : ℕ} (s : PauliSum n) :
    coeffWeight (adjSum s) = coeffWeight s := by
  unfold coeffWeight adjSum
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro cq _
  simp only [Function.comp_apply]
  exact norm_star cq.1

/-- The conjugate of `I ^ k.val` is `I ^ (-k).val`, used to identify the
adjoint phase coefficient in the symmetrisation lemma. -/
theorem star_I_pow_phase (k : ZMod 4) :
    star ((Complex.I : ℂ) ^ k.val) = (Complex.I : ℂ) ^ (-k).val := by
  have h1 : star ((Complex.I : ℂ) ^ k.val) * (Complex.I : ℂ) ^ k.val = 1 :=
    star_I_pow_mul_self k.val
  have h2 : (Complex.I : ℂ) ^ (-k).val * (Complex.I : ℂ) ^ k.val = 1 := by
    rw [← I_pow_val_add, neg_add_cancel k]
    simp
  have hne : ((Complex.I : ℂ) ^ k.val) ≠ 0 := pow_ne_zero _ (by simp)
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

/-- The norm of any power of `I` appearing as a Pauli phase is one. -/
theorem norm_I_pow_phase (k : ZMod 4) :
    ‖(Complex.I : ℂ) ^ k.val‖ = 1 := by
  rw [norm_pow, Complex.norm_I, one_pow]

/-- Term-level symmetrisation identity: averaging one Pauli term with its
adjoint produces the real part of its phase-free coefficient times the
Hermitian Pauli word matrix. -/
theorem realSymm_term {n : ℕ} (c : ℂ) (p : PauliElem n) :
    (2 : ℂ)⁻¹ • ((c • op p) + (c • op p)ᴴ) =
      (Complex.re (c * (Complex.I : ℂ) ^ p.phase.val) : ℂ) •
        pauliWordOp n p.word := by
  set W : Matrix (Reg n) (Reg n) ℂ := pauliWordOp n p.word with hW
  have ha : c • op p = (c * (Complex.I : ℂ) ^ p.phase.val) • W := by
    rw [op, smul_smul']
  have hb : (c • op p)ᴴ =
      (star c * (Complex.I : ℂ) ^ (-p.phase).val) • W := by
    rw [Matrix.conjTranspose_smul, op_conjTranspose, op, smul_smul']
  have hstar : star c * (Complex.I : ℂ) ^ (-p.phase).val =
      star (c * (Complex.I : ℂ) ^ p.phase.val) := by
    rw [star_mul, star_I_pow_phase, mul_comm]
  have hcoeff :
      (2 : ℂ)⁻¹ * ((c * (Complex.I : ℂ) ^ p.phase.val) +
        (star c * (Complex.I : ℂ) ^ (-p.phase).val)) =
      (Complex.re (c * (Complex.I : ℂ) ^ p.phase.val) : ℂ) := by
    have h := Complex.re_eq_add_conj (c * (Complex.I : ℂ) ^ p.phase.val)
    rw [hstar]
    simpa only [Complex.star_def, div_eq_mul_inv, mul_comm] using h.symm
  calc
    (2 : ℂ)⁻¹ • ((c • op p) + (c • op p)ᴴ)
        = (2 : ℂ)⁻¹ •
            (((c * (Complex.I : ℂ) ^ p.phase.val) • W) +
              ((star c * (Complex.I : ℂ) ^ (-p.phase).val) • W)) := by
          nth_rewrite 1 [ha]
          rw [hb]
    _ = (2 : ℂ)⁻¹ •
          (((c * (Complex.I : ℂ) ^ p.phase.val) +
            (star c * (Complex.I : ℂ) ^ (-p.phase).val)) • W) := by
          rw [add_smul]
    _ = ((2 : ℂ)⁻¹ *
          ((c * (Complex.I : ℂ) ^ p.phase.val) +
            (star c * (Complex.I : ℂ) ^ (-p.phase).val))) • W := by
          rw [smul_smul']
    _ = (Complex.re (c * (Complex.I : ℂ) ^ p.phase.val) : ℂ) • W := by
          rw [hcoeff]

/-- The real symmetrisation evaluates to half the sum of the Pauli sum and
its adjoint.  For a Hermitian target the right-hand side is the matrix
itself. -/
theorem evalRealSum_realSymm {n : ℕ} (s : PauliSum n) :
    evalRealSum (realSymm s) =
      (2 : ℂ)⁻¹ • (evalSum s + (evalSum s)ᴴ) := by
  induction s with
  | nil => simp [evalRealSum, realSymm, evalSum]
  | cons hd tl ih =>
    have hhead : evalRealSum (realSymm (hd :: tl)) =
        (Complex.re (hd.1 * (Complex.I : ℂ) ^ hd.2.phase.val) : ℂ) •
          pauliWordOp n hd.2.word + evalRealSum (realSymm tl) := rfl
    have hsum : evalSum (hd :: tl) = hd.1 • op hd.2 + evalSum tl := by
      simp [evalSum]
    rw [hhead, hsum, ih, Matrix.conjTranspose_add,
      ← realSymm_term (c := hd.1) (p := hd.2)]
    simp only [smul_add]
    abel

/-- The real weight of the symmetrisation is at most the complex weight. -/
theorem realWeight_realSymm_le {n : ℕ} (s : PauliSum n) :
    realWeight (realSymm s) ≤ coeffWeight s := by
  induction s with
  | nil => simp [realWeight, realSymm, coeffWeight]
  | cons hd tl ih =>
    simp only [realSymm, List.map_cons, realWeight, coeffWeight, List.sum_cons]
    change |Complex.re (hd.1 * (Complex.I : ℂ) ^ hd.2.phase.val)|
        + realWeight (realSymm tl) ≤ ‖hd.1‖ + coeffWeight tl
    have hterm : |Complex.re (hd.1 * (Complex.I : ℂ) ^ hd.2.phase.val)| ≤ ‖hd.1‖ := by
      calc
        |Complex.re (hd.1 * (Complex.I : ℂ) ^ hd.2.phase.val)|
            ≤ ‖hd.1 * (Complex.I : ℂ) ^ hd.2.phase.val‖ := Complex.abs_re_le_norm _
        _ = ‖hd.1‖ := by
          rw [norm_mul, norm_I_pow_phase, mul_one]
    linarith [ih, hterm]

/-- The length of the term-wise adjoint equals the length of the original sum. -/
theorem adjSum_length {n : ℕ} (s : PauliSum n) : (adjSum s).length = s.length := by
  simp [adjSum]

/-- The length of the real symmetrisation equals the length of the original sum. -/
theorem realSymm_length {n : ℕ} (s : PauliSum n) : (realSymm s).length = s.length := by
  simp [realSymm]

/-- Scalar cancellation for matrices: `½ • (X + X) = X`. -/
theorem half_smul_add_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) : (2 : ℂ)⁻¹ • (X + X) = X := by
  ext i j
  simp [Matrix.smul_apply, Matrix.add_apply]
  ring

/-- **c003, Proposition 6(1).**  Let `s` be the Pauli expansion (1) of the system
matrix `A` (`L = s.length` terms) and `t` that of the preconditioner `P`
(`M = t.length` terms).  If the classical product `P A` is Hermitian, then it has
a real, phase-free Pauli expansion with at most `L M` terms whose coefficient
weight is at most `w(P)w(A)`.

Source: Proposition 6, item 1, p. 7 (displayed expansion
`P A = ∑_j μ_j^{(L)} Q_j^{(L)}`, `J_L ≤ L M`, `w(P A) ≤ w(P)w(A)`).
The construction is term-by-term: `P A = ∑_m ∑_ℓ β_m a_ℓ P_m A_ℓ`, and each
`P_m A_ℓ` is a phase times a Pauli word; the pairing `½(X + Xᴴ)` makes the
coefficients real without increasing the weight. -/
theorem prop6_left_expansion {n : ℕ} (s t : PauliSum n)
    (hHerm : evalSum (mulSum t s) = (evalSum (mulSum t s))ᴴ) :
    ∃ r : RealPauliSum n,
      r.length ≤ s.length * t.length ∧
      evalRealSum r = evalSum t * evalSum s ∧
      realWeight r ≤ coeffWeight s * coeffWeight t := by
  refine ⟨realSymm (mulSum t s), ?_, ?_, ?_⟩
  · rw [realSymm_length, length_mulSum]
    exact Nat.mul_comm _ _ ▸ le_rfl
  · have hX : evalSum (mulSum t s) = evalSum t * evalSum s := evalSum_mulSum t s
    have hH : (evalSum t * evalSum s)ᴴ = evalSum t * evalSum s := by
      rw [← hX]
      exact hHerm.symm
    rw [evalRealSum_realSymm, hX, hH]
    exact half_smul_add_self _
  · calc realWeight (realSymm (mulSum t s))
        ≤ coeffWeight (mulSum t s) := realWeight_realSymm_le _
      _ = coeffWeight t * coeffWeight s := coeffWeight_mulSum t s
      _ = coeffWeight s * coeffWeight t := mul_comm _ _

/-- **c003, Proposition 6(2).**  For the symmetric product `P A Pᴴ`, the real
Pauli expansion has at most `L M²` terms and coefficient weight at most
`w(P)² w(A)`; it is real when `P A Pᴴ` is Hermitian.

Source: Proposition 6, item 2, p. 7 (displayed expansion
`P A Pᴴ = ∑_j μ_j^{(S)} Q_j^{(S)}`, `J_S ≤ L M²`, `w(P A Pᴴ) ≤ w(P)² w(A)`).
Here `P A Pᴴ = mulSum (mulSum t s) (adjSum t)` and the weight of the unregrouped
product is exactly `w(P) w(A) w(P)`. -/
theorem prop6_symm_expansion {n : ℕ} (s t : PauliSum n)
    (hHerm : evalSum (mulSum (mulSum t s) (adjSum t)) =
      (evalSum (mulSum (mulSum t s) (adjSum t)))ᴴ) :
    ∃ r : RealPauliSum n,
      r.length ≤ s.length * t.length * t.length ∧
      evalRealSum r = evalSum t * evalSum s * (evalSum t)ᴴ ∧
      realWeight r ≤ coeffWeight s * coeffWeight t * coeffWeight t := by
  refine ⟨realSymm (mulSum (mulSum t s) (adjSum t)), ?_, ?_, ?_⟩
  · apply le_of_eq
    rw [realSymm_length, length_mulSum, length_mulSum, adjSum_length]
    ring
  · have hY : evalSum (mulSum (mulSum t s) (adjSum t))
        = evalSum t * evalSum s * (evalSum t)ᴴ := by
      rw [evalSum_mulSum, evalSum_mulSum, evalSum_adjSum]
    have hYH : (evalSum t * evalSum s * (evalSum t)ᴴ)ᴴ =
        evalSum t * evalSum s * (evalSum t)ᴴ := by
      rw [← hY]
      exact hHerm.symm
    rw [evalRealSum_realSymm, hY, hYH]
    exact half_smul_add_self _
  · calc realWeight (realSymm (mulSum (mulSum t s) (adjSum t)))
        ≤ coeffWeight (mulSum (mulSum t s) (adjSum t)) := realWeight_realSymm_le _
      _ = coeffWeight t * coeffWeight s * coeffWeight t := by
            rw [coeffWeight_mulSum, coeffWeight_mulSum, coeffWeight_adjSum]
      _ = coeffWeight s * coeffWeight t * coeffWeight t := by ring

/-- **c003, Proposition 6 (combined form).**  Both parts of Proposition 6, with
the term-count and coefficient-weight bounds, as a single statement.

Source: Proposition 6, p. 7. -/
theorem proposition6 {n : ℕ} (s t : PauliSum n)
    (hHermL : evalSum (mulSum t s) = (evalSum (mulSum t s))ᴴ)
    (hHermS : evalSum (mulSum (mulSum t s) (adjSum t)) =
      (evalSum (mulSum (mulSum t s) (adjSum t)))ᴴ) :
    (∃ r : RealPauliSum n,
        r.length ≤ s.length * t.length ∧
        evalRealSum r = evalSum t * evalSum s ∧
        realWeight r ≤ coeffWeight s * coeffWeight t) ∧
      (∃ r : RealPauliSum n,
        r.length ≤ s.length * t.length * t.length ∧
        evalRealSum r = evalSum t * evalSum s * (evalSum t)ᴴ ∧
        realWeight r ≤ coeffWeight s * coeffWeight t * coeffWeight t) :=
  ⟨prop6_left_expansion s t hHermL, prop6_symm_expansion s t hHermS⟩

/-! ### Theorem 13: Neumann-series and structural depth bounds -/

section Neumann

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- The smallest singular value of an invertible matrix, represented as
`‖M⁻¹‖⁻¹`.  For invertible `M` this coincides with `σ_min(M)`; the paper's
`+∞` convention for singular `M` is handled separately (see
`EncodingObstr.kappaEff`).  Source: Theorem 13, p. 9, and eq. (5), p. 4. -/
def sigmaMin (M : Matrix (Fin N) (Fin N) ℂ) : ℝ := ‖M⁻¹‖⁻¹

omit [NeZero N] in
/-- The scale-invariant structural per-sample depth proxy (21) of the randomized
QLS solver, `D_RQLS(H) = (w(H)/σ_min(H))²`, where `w` is the Pauli coefficient
weight.  Source: eq. (21), p. 8. -/
def dRQLS (w : ℝ) (M : Matrix (Fin N) (Fin N) ℂ) : ℝ := (w / sigmaMin M) ^ 2

/-- **c006, Theorem 13 (Neumann-series step).**  If `‖1 - M‖ ≤ η < 1`, then `M`
is invertible and `‖M⁻¹‖ ≤ (1 - η)⁻¹`.

Source: Theorem 13, p. 9, proof of (24): with `E := I - PA`,
`(PA)⁻¹ = (I - E)⁻¹ = ∑_k E^k` and `‖(PA)⁻¹‖ ≤ 1/(1-η)`.  This is the
`geometric series` bound for the Neumann expansion, formalised with
`isUnit_one_sub_of_norm_lt_one`, `geom_series_eq_inverse` and the
`tsum` norm estimates. -/
theorem neumann_inverse_norm_le {M : Matrix (Fin N) (Fin N) ℂ} {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hE : ‖1 - M‖ ≤ η) :
    IsUnit M ∧ ‖M⁻¹‖ ≤ (1 - η)⁻¹ := by
  have hlt : ‖1 - M‖ < 1 := lt_of_le_of_lt hE hη1
  have hunit : IsUnit M := by
    have h' : IsUnit (1 - (1 - M)) := isUnit_one_sub_of_norm_lt_one hlt
    rwa [sub_sub_cancel 1 M] at h'
  refine ⟨hunit, ?_⟩
  have hsum : Summable fun k : ℕ => (1 - M) ^ k := summable_geometric_of_norm_lt_one hlt
  have hnorm_sum : Summable fun k : ℕ => ‖(1 - M) ^ k‖ := hsum.norm
  have hgeom : Summable fun k : ℕ => η ^ k := summable_geometric_of_lt_one hη0 hη1
  have hbound : ∀ k : ℕ, ‖(1 - M) ^ k‖ ≤ η ^ k := by
    intro k
    cases k with
    | zero => simp
    | succ m =>
        calc ‖(1 - M) ^ (m + 1)‖ ≤ ‖1 - M‖ ^ (m + 1) := norm_pow_le' _ (Nat.succ_pos m)
          _ ≤ η ^ (m + 1) := pow_le_pow_left₀ (norm_nonneg _) hE _
  have hEq : ∑' k : ℕ, (1 - M) ^ k = Ring.inverse M := by
    have h := geom_series_eq_inverse (1 - M) hlt
    rwa [sub_sub_cancel 1 M] at h
  calc ‖M⁻¹‖ = ‖Ring.inverse M‖ := by rw [Matrix.nonsing_inv_eq_ringInverse]
    _ = ‖∑' k : ℕ, (1 - M) ^ k‖ := by rw [← hEq]
    _ ≤ ∑' k : ℕ, ‖(1 - M) ^ k‖ := norm_tsum_le_tsum_norm hnorm_sum
    _ ≤ ∑' k : ℕ, η ^ k := hnorm_sum.tsum_le_tsum hbound hgeom
    _ = (1 - η)⁻¹ := tsum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hη0])

/-- **c006, Theorem 13 (singular-value consequence).**  Under `‖1 - M‖ ≤ η < 1`
the smallest singular value satisfies `σ_min(M) ≥ 1 - η`.

Source: Theorem 13, p. 9: "Hence `σ_min(PA) ≥ 1 - η`". -/
theorem neumann_sigmaMin_ge {M : Matrix (Fin N) (Fin N) ℂ} {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hE : ‖1 - M‖ ≤ η) :
    1 - η ≤ sigmaMin M := by
  obtain ⟨hunit, hnorm⟩ := neumann_inverse_norm_le hη0 hη1 hE
  have hdet : IsUnit M.det := (isUnit_iff_isUnit_det (A := M)).mp hunit
  have hmul : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet
  have hpos : 0 < ‖M⁻¹‖ := by
    rcases lt_or_eq_of_le (norm_nonneg M⁻¹) with h | h
    · exact h
    · exfalso
      have hz : M⁻¹ = 0 := norm_eq_zero.mp h.symm
      have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
        rw [← hmul, hz, Matrix.mul_zero]
      exact one_ne_zero h1
  unfold sigmaMin
  have hδ : 0 < 1 - η := by linarith
  have := (inv_le_inv₀ (inv_pos.mpr hδ) hpos).mpr hnorm
  rwa [inv_inv] at this

omit [NeZero N] in
/-- The proxy `D_RQLS(w, M)` is monotone in the Pauli coefficient weight `w`.
Used to pass from `w(PA)` to its upper bound `w(P)w(A)`. -/
theorem dRQLS_le_of_le {M : Matrix (Fin N) (Fin N) ℂ} {w₁ w₂ : ℝ}
    (hw : w₁ ≤ w₂) (hw1 : 0 ≤ w₁) (hσ : 0 < sigmaMin M) :
    dRQLS w₁ M ≤ dRQLS w₂ M := by
  unfold dRQLS
  have h1 : 0 ≤ w₁ / sigmaMin M := div_nonneg hw1 (le_of_lt hσ)
  have h2 : w₁ / sigmaMin M ≤ w₂ / sigmaMin M :=
    div_le_div_of_nonneg_right hw (le_of_lt hσ)
  exact pow_le_pow_left₀ h1 h2 2

/-- **c006, Theorem 13 (structural bound).**  If `‖1 - M‖ ≤ η < 1`, then the
structural per-sample depth proxy of `M` with the weight bound `w(P)w(A)` obeys
`D_RQLS(w(P)w(A), M) ≤ (w(P)w(A)/(1-η))²`, i.e. the right-hand side of (24).

Source: Theorem 13, p. 9: combining `σ_min(PA) ≥ 1 - η` with
`w(PA) ≤ w(P)w(A)`. -/
theorem theorem13_structural_bound {M : Matrix (Fin N) (Fin N) ℂ} {wP wA η : ℝ}
    (hwP : 0 ≤ wP) (hwA : 0 ≤ wA)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hE : ‖1 - M‖ ≤ η) :
    dRQLS (wP * wA) M ≤ (wP * wA / (1 - η)) ^ 2 := by
  unfold dRQLS
  have hσ : 1 - η ≤ sigmaMin M := neumann_sigmaMin_ge hη0 hη1 hE
  have hδ : 0 < 1 - η := by linarith
  have hσpos : 0 < sigmaMin M := lt_of_lt_of_le hδ hσ
  have hw : wP * wA / sigmaMin M ≤ wP * wA / (1 - η) :=
    div_le_div_of_nonneg_left (mul_nonneg hwP hwA) hδ hσ
  exact pow_le_pow_left₀ (div_nonneg (mul_nonneg hwP hwA) (le_of_lt hσpos)) hw 2

/-- **c006, Theorem 13 (Neumann-series clause).**  Combining the invertibility,
the singular-value bound and the structural proxy bound under
`‖1 - PA‖ ≤ η < 1`.

Source: Theorem 13, p. 9, the sentence "the sufficient condition
`‖I - PA‖ ≤ η < 1` implies that `PA` is invertible, `σ_min(PA) ≥ 1 - η`,
and ...". -/
theorem theorem13_neumann {M : Matrix (Fin N) (Fin N) ℂ} {wP wA η : ℝ}
    (hwP : 0 ≤ wP) (hwA : 0 ≤ wA)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hE : ‖1 - M‖ ≤ η) :
    IsUnit M ∧ 1 - η ≤ sigmaMin M ∧
      dRQLS (wP * wA) M ≤ (wP * wA / (1 - η)) ^ 2 :=
  ⟨(neumann_inverse_norm_le hη0 hη1 hE).1,
   neumann_sigmaMin_ge hη0 hη1 hE,
   theorem13_structural_bound hwP hwA hη0 hη1 hE⟩

/-- **c006, Theorem 13, Eq. (24) — per-sample depth bound after preconditioning.**
Given the randomized QLS per-sample depth bound for `M` in the form
`C_depth(M; ε) ≤ K · D_RQLS(w, M) · log(1/ε)` (the structural bound (23) of the
paper, whose solver-internal derivation is external), and given the Pauli weight
bound `w ≤ w(P)w(A)`, the Neumann condition `‖1 - M‖ ≤ η < 1` yields the
preconditioned bound
`C_depth(M; ε) ≤ K · (w(P)w(A)/(1-η))² · log(1/ε)`.

Source: Theorem 13, p. 9, displayed equation (24).  The paper's proof is:
apply the [42] randomized complexity bound to `PA`, then substitute
`w(PA) ≤ w(P)w(A)` and `σ_min(PA) ≥ 1 - η`. -/
theorem theorem13_neumann_depth_bound {M : Matrix (Fin N) (Fin N) ℂ}
    {w wP wA η ε K : ℝ}
    (Cdepth : Matrix (Fin N) (Fin N) ℂ → ℝ → ℝ)
    (hK : 0 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hSolver : Cdepth M ε ≤ K * dRQLS w M * Real.log (1 / ε))
    (hw : 0 ≤ w) (hwle : w ≤ wP * wA) (hwP : 0 ≤ wP) (hwA : 0 ≤ wA)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hE : ‖1 - M‖ ≤ η) :
    Cdepth M ε ≤ K * ((wP * wA) / (1 - η)) ^ 2 * Real.log (1 / ε) := by
  have hσ : 1 - η ≤ sigmaMin M := neumann_sigmaMin_ge hη0 hη1 hE
  have hδ : 0 < 1 - η := by linarith
  have hσpos : 0 < sigmaMin M := lt_of_lt_of_le hδ hσ
  have hstruct : dRQLS w M ≤ ((wP * wA) / (1 - η)) ^ 2 :=
    (dRQLS_le_of_le hwle hw hσpos).trans (theorem13_structural_bound hwP hwA hη0 hη1 hE)
  have hlog : 0 ≤ Real.log (1 / ε) := by
    apply Real.log_nonneg
    rw [one_div]
    exact (one_le_inv₀ hε).mpr hε1
  calc Cdepth M ε ≤ K * dRQLS w M * Real.log (1 / ε) := hSolver
    _ ≤ K * ((wP * wA) / (1 - η)) ^ 2 * Real.log (1 / ε) := by
        have h1 : K * dRQLS w M ≤ K * ((wP * wA) / (1 - η)) ^ 2 :=
          mul_le_mul_of_nonneg_left hstruct hK
        exact mul_le_mul_of_nonneg_right h1 hlog

end Neumann

end Qatlib.Papers.PauliPrecond26.PauliMerge
