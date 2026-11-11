/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Annihilating polynomial of the reference block (Lemma 4.6)

Shen--Wu--Yuan--Zhang, fixed arXiv:2610.05362v1, Lemma 4.6, page 30.
The reference diagonal block of the local transducer is `A₀ := i (I - P) O`,
where `O` is an involution (`O² = 1`) and `P` is a projection (`P² = P`) with
`P O P = 0`.  The Lemma asserts `A₀⁴ + A₀² = 0`, so that `p(z) = (z² + z⁴)/2`
annihilates every reference diagonal block.

The proof follows the source: `Q := P + O P O` is again a projection and
`A₀² = Q - I`, hence `A₀⁴ = (I - Q)² = I - Q` and the two powers cancel.
-/

open Matrix

namespace Qatlib.Papers.ShallowLind26.ShallowSim.AnnihilatorPolynomial

set_option autoImplicit false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The reference block `A₀ = i (I - P) O` of the local transducer. -/
noncomputable def referenceBlock (O P : Matrix n n ℂ) : Matrix n n ℂ :=
  Complex.I • ((1 - P) * O)

/-- **Lemma 4.6, projection part.**  If `O O = 1`, `P P = P` and `P O P = 0`,
then `Q = P + O P O` is a projection. -/
theorem referenceBlock_Q_projection (O P : Matrix n n ℂ)
    (hO : O * O = 1) (hP : P * P = P) (hPOP : P * O * P = 0) :
    (P + O * P * O) * (P + O * P * O) = P + O * P * O := by
  have hA : P * (O * P * O) = 0 := by
    rw [show P * (O * P * O) = (P * O * P) * O from by noncomm_ring, hPOP,
      Matrix.zero_mul]
  have hB : (O * P * O) * P = 0 := by
    rw [show (O * P * O) * P = O * (P * O * P) from by noncomm_ring, hPOP,
      Matrix.mul_zero]
  have hC : (O * P * O) * (O * P * O) = O * P * O := by
    calc (O * P * O) * (O * P * O) = O * P * (O * O) * (P * O) := by noncomm_ring
      _ = O * P * (P * O) := by rw [hO, Matrix.mul_one]
      _ = O * (P * P) * O := by noncomm_ring
      _ = O * P * O := by rw [hP]
  calc (P + O * P * O) * (P + O * P * O)
      = P * P + P * (O * P * O) + (O * P * O) * P
          + (O * P * O) * (O * P * O) := by noncomm_ring
    _ = P + O * P * O := by rw [hP, hA, hB, hC]; abel

/-- **Lemma 4.6.**  For `O O = 1`, `P P = P` and `P O P = 0`, the reference
block `A₀ = i (I - P) O` satisfies `A₀⁴ + A₀² = 0`. -/
theorem annihilator_polynomial (O P : Matrix n n ℂ)
    (hO : O * O = 1) (hP : P * P = P) (hPOP : P * O * P = 0) :
    referenceBlock O P ^ 4 + referenceBlock O P ^ 2 = 0 := by
  set Q : Matrix n n ℂ := P + O * P * O with hQdef
  have hQ : Q * Q = Q :=
    referenceBlock_Q_projection O P hO hP hPOP
  have hPOPO : P * (O * P * O) = 0 := by
    rw [show P * (O * P * O) = (P * O * P) * O from by noncomm_ring, hPOP,
      Matrix.zero_mul]
  have hA1 : O * ((1 - P) * O) = 1 - O * P * O := by
    rw [show O * ((1 - P) * O) = (O * (1 - P)) * O from by noncomm_ring]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hO]
  have hXX : ((1 - P) * O) * ((1 - P) * O) = 1 - Q := by
    calc ((1 - P) * O) * ((1 - P) * O)
        = (1 - P) * (O * ((1 - P) * O)) := by noncomm_ring
      _ = (1 - P) * (1 - O * P * O) := by rw [hA1]
      _ = (1 - P) - (1 - P) * (O * P * O) := by rw [Matrix.mul_sub, Matrix.mul_one]
      _ = (1 - P) - O * P * O := by
            rw [Matrix.sub_mul, Matrix.one_mul, hPOPO, sub_zero]
      _ = 1 - Q := by rw [hQdef]; abel
  have hsq : referenceBlock O P ^ 2 = Q - 1 := by
    rw [referenceBlock, pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.I_mul_I, neg_one_smul, hXX]
    abel
  have hfour : referenceBlock O P ^ 4 = (referenceBlock O P ^ 2) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
  have hcalc : (Q - 1) * (Q - 1) = -(Q - 1) := by
    have e : (Q - 1) * (Q - 1) = 1 - Q - Q + Q * Q := by noncomm_ring
    rw [e, hQ]
    abel
  rw [hfour, hsq, pow_two, hcalc]
  abel

/-- **Lemma 4.6, polynomial consequence.**  With `p(z) = (z² + z⁴)/2`, the
reference diagonal block is annihilated by `p`: `p(A₀) = 0`. -/
theorem polynomial_annihilates (O P : Matrix n n ℂ)
    (hO : O * O = 1) (hP : P * P = P) (hPOP : P * O * P = 0) :
    (2 : ℂ)⁻¹ • (referenceBlock O P ^ 2 + referenceBlock O P ^ 4) = 0 := by
  have h := annihilator_polynomial O P hO hP hPOP
  rw [add_comm, h]
  simp

end Qatlib.Papers.ShallowLind26.ShallowSim.AnnihilatorPolynomial
