/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Papers.PrecondQLS20.MainResults.Foundation.PrecondModel

set_option backward.isDefEq.respectTransparency false

/-!
# PrecondQLS20 — Lemma 11 (condition number of `W = I + A⁻¹B`)

Fixed source: arXiv:2008.13295v2, **Lemma 11, p. 15** (Section 3.1,
"Preconditioning the linear system").

Printed statement.  Define `W = I + A⁻¹B`.  Then the smallest and largest
singular values of `W` satisfy

```
1/σ_min ≤ 1 + ‖(A+B)⁻¹‖‖B‖ =: C_AB ,      σ_max ≤ 1 + ‖A⁻¹‖‖B‖ =: C'_AB ,
```

hence `κ(W) ≤ C_AB · C'_AB` (printed Eq. (15), p. 15).

Printed proof route (p. 15).  Write `W|x⟩ = |y⟩`.  Then `(A+B)|x⟩ = A|y⟩`,
hence `(A+B)(|x⟩−|y⟩) = −B|y⟩` and `A(|x⟩−|y⟩) = −B|x⟩`, which give

```
‖x‖ ≤ ‖y‖ + ‖x−y‖ ≤ (1 + ‖(A+B)⁻¹‖‖B‖)‖y‖ ,
‖y‖ ≤ ‖x‖ + ‖x−y‖ ≤ (1 + ‖A⁻¹‖‖B‖)‖x‖ .
```

Formalisation notes.  Vectors are elements of `EuclideanSpace ℂ (Fin n)`, on
which `clm M` — the library's `Matrix.toEuclideanCLM` — is a star-algebra
isometry, so multiplication, addition, negation and the identity move through it
by `map_*`.  Invertibility of `A`, `A+B` and `W` is passed as the two-sided
inverse equations (`M * M⁻¹ = 1`, `M⁻¹ * M = 1`), the paper's "`A` and `A + B`
invertible" written out.

No `sorry` in this file.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PrecondQLS20.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

/-- The matrix-vector action as a continuous linear map. -/
noncomputable def clm (M : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M

/-- `clm` sends matrix addition to addition of continuous linear maps. -/
@[simp] theorem clm_add (M N : Matrix (Fin n) (Fin n) ℂ) :
    clm (M + N) = clm M + clm N :=
  map_add (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) M N

/-- `clm` sends matrix multiplication to composition of continuous linear maps. -/
@[simp] theorem clm_mul (M N : Matrix (Fin n) (Fin n) ℂ) :
    clm (M * N) = clm M * clm N :=
  map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) M N

/-- `clm` sends the identity matrix to the identity map. -/
@[simp] theorem clm_one : clm (1 : Matrix (Fin n) (Fin n) ℂ) = 1 :=
  map_one (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n))

/-- `clm` commutes with negation. -/
@[simp] theorem clm_neg (M : Matrix (Fin n) (Fin n) ℂ) : clm (-M) = -clm M :=
  map_neg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) M

/-- `clm` commutes with subtraction. -/
@[simp] theorem clm_sub (M N : Matrix (Fin n) (Fin n) ℂ) :
    clm (M - N) = clm M - clm N :=
  map_sub (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) M N

/-- The operator norm of `clm M` equals the spectral norm of `M`. -/
theorem clm_norm (M : Matrix (Fin n) (Fin n) ℂ) : ‖clm M‖ = ‖M‖ :=
  Matrix.l2_opNorm_toEuclideanCLM M

/-- Matrix-vector action, written as application of `clm`. -/
noncomputable def act (M : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) :=
  clm M x

/-- Matrix-vector action is additive in the matrix. -/
@[simp] theorem act_add (M N : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    act (M + N) x = act M x + act N x := by
  simp [act]

/-- Matrix-vector action composes matrix multiplication. -/
@[simp] theorem act_mul (M N : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    act (M * N) x = act M (act N x) := by
  simp [act]

/-- The identity matrix acts as the identity. -/
@[simp] theorem act_one (x : EuclideanSpace ℂ (Fin n)) : act 1 x = x := by
  simp [act]

/-- Matrix-vector action commutes with negation. -/
@[simp] theorem act_neg (M : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    act (-M) x = - act M x := by
  simp [act]

/-- Matrix-vector action commutes with subtraction. -/
@[simp] theorem act_sub (M N : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    act (M - N) x = act M x - act N x := by
  simp [act]

/-- Linearity in the *vector* argument: `act M (x - y) = act M x - act M y`. -/
@[simp] theorem act_vec_sub (M : Matrix (Fin n) (Fin n) ℂ)
    (x y : EuclideanSpace ℂ (Fin n)) : act M (x - y) = act M x - act M y := by
  unfold act
  exact map_sub (clm M) x y

/-- The matrix-vector action is contractive in the spectral norm. -/
theorem norm_act_le (M : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    ‖act M x‖ ≤ ‖M‖ * ‖x‖ := by
  have := ContinuousLinearMap.le_opNorm (clm M) x
  rwa [clm_norm] at this

/-- The spectral norm of the identity is at most one. -/
theorem norm_one_matrix : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 :=
  Qatlib.Concepts.BlockEncoding.Encoding.matrix_one_norm_le

/-- Pointwise bounds turn into an operator-norm bound. -/
theorem opNorm_le_of_act_le (M : Matrix (Fin n) (Fin n) ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖act M x‖ ≤ C * ‖x‖) : ‖M‖ ≤ C := by
  have hf : ‖clm M‖ ≤ C := ContinuousLinearMap.opNorm_le_bound _ hC h
  rwa [clm_norm] at hf

/-! ## The two singular-value bounds -/

/-- **Lemma 11, lower bound** (p. 15): `1/σ_min ≤ 1 + ‖(A+B)⁻¹‖‖B‖`.

In the form "`W` expands": for every `y`, `‖y‖ ≤ (1 + ‖(A+B)⁻¹‖‖B‖)‖W y‖`. -/
theorem lemma11_lower
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA_left : A * A⁻¹ = 1) (hA_right : A⁻¹ * A = 1)
    (hAB_left : (A + B) * (A + B)⁻¹ = 1) (hAB_right : (A + B)⁻¹ * (A + B) = 1) :
    ∀ x : EuclideanSpace ℂ (Fin n),
      ‖x‖ ≤ (1 + ‖(A + B)⁻¹‖ * ‖B‖) * ‖act (1 + A⁻¹ * B) x‖ := by
  intro x
  set W : Matrix (Fin n) (Fin n) ℂ := 1 + A⁻¹ * B with hWdef
  -- `A * W = A + B`
  have hAW : A * W = A + B := by
    rw [hWdef]
    calc
      A * (1 + A⁻¹ * B) = A + (A * A⁻¹) * B := by
            rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc]
      _ = A + 1 * B := by rw [hA_left]
      _ = A + B := by rw [Matrix.one_mul]
  -- Step 1: `A y = (A+B) x` where `y = W x`.
  have hAy : act A (act W x) = act (A + B) x := by
    rw [← act_mul, hAW]
  -- Step 2: `(A+B)(x−y) = −B y`.
  have hdiff : act (A + B) (x - act W x) = - act B (act W x) := by
    have h1 : act (A + B) (x - act W x)
        = act (A + B) x - act (A + B) (act W x) := act_vec_sub _ _ _
    have h2 : act (A + B) (act W x)
        = act A (act W x) + act B (act W x) := act_add _ _ _
    have h3 : act (A + B) x = act A (act W x) := hAy.symm
    rw [h1, h2, h3]
    abel
  -- Step 3: `x − y = (A+B)⁻¹ (−B y)`.
  have hxsub : x - act W x = act ((A + B)⁻¹) (- act B (act W x)) := by
    rw [← hdiff, ← act_mul, hAB_right, act_one]
  -- Step 4: bound.
  have hxsub_le : ‖x - act W x‖ ≤ ‖(A + B)⁻¹‖ * (‖B‖ * ‖act W x‖) := by
    rw [hxsub]
    calc
      ‖act ((A + B)⁻¹) (- act B (act W x))‖
          ≤ ‖(A + B)⁻¹‖ * ‖- act B (act W x)‖ := norm_act_le _ _
      _ = ‖(A + B)⁻¹‖ * ‖act B (act W x)‖ := by rw [norm_neg]
      _ ≤ ‖(A + B)⁻¹‖ * (‖B‖ * ‖act W x‖) := by
            gcongr
            exact norm_act_le B _
  have hsplit : ‖x‖ ≤ ‖act W x‖ + ‖x - act W x‖ := by
    calc
      ‖x‖ = ‖act W x + (x - act W x)‖ := by
              congr 1
              abel
      _ ≤ ‖act W x‖ + ‖x - act W x‖ := norm_add_le _ _
  calc
    ‖x‖ ≤ ‖act W x‖ + ‖(A + B)⁻¹‖ * (‖B‖ * ‖act W x‖) :=
          hsplit.trans (by linarith [hxsub_le])
    _ = (1 + ‖(A + B)⁻¹‖ * ‖B‖) * ‖act W x‖ := by ring

/-- **Lemma 11, upper bound** (p. 15): `σ_max ≤ 1 + ‖A⁻¹‖‖B‖`,
in the form `‖W x‖ ≤ (1 + ‖A⁻¹‖‖B‖)‖x‖`. -/
theorem lemma11_upper (A B : Matrix (Fin n) (Fin n) ℂ) :
    ∀ x : EuclideanSpace ℂ (Fin n),
      ‖act (1 + A⁻¹ * B) x‖ ≤ (1 + ‖A⁻¹‖ * ‖B‖) * ‖x‖ := by
  intro x
  have hWnorm : ‖(1 + A⁻¹ * B : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 + ‖A⁻¹‖ * ‖B‖ := by
    calc
      ‖(1 + A⁻¹ * B : Matrix (Fin n) (Fin n) ℂ)‖ ≤
          ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖A⁻¹ * B‖ := norm_add_le _ _
      _ ≤ 1 + ‖A⁻¹‖ * ‖B‖ := by
            gcongr
            · exact norm_one_matrix
            · exact Matrix.l2_opNorm_mul _ _
  calc
    ‖act (1 + A⁻¹ * B) x‖ ≤ ‖(1 + A⁻¹ * B : Matrix (Fin n) (Fin n) ℂ)‖ * ‖x‖ := norm_act_le _ _
    _ ≤ (1 + ‖A⁻¹‖ * ‖B‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right hWnorm (norm_nonneg x)

/-! ## The condition-number product (printed Eq. (15)) -/

/-- **Lemma 11, condition-number bound** (printed Eq. (15), p. 15):

`κ(W) = ‖W‖‖W⁻¹‖ ≤ (1 + ‖(A+B)⁻¹‖‖B‖)(1 + ‖A⁻¹‖‖B‖)`. -/
theorem lemma11_conditionNumber
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA_left : A * A⁻¹ = 1) (hA_right : A⁻¹ * A = 1)
    (hAB_left : (A + B) * (A + B)⁻¹ = 1) (hAB_right : (A + B)⁻¹ * (A + B) = 1)
    (hW_left : (1 + A⁻¹ * B) * (1 + A⁻¹ * B)⁻¹ = 1) :
    ‖(1 + A⁻¹ * B : Matrix (Fin n) (Fin n) ℂ)‖ *
        ‖(1 + A⁻¹ * B : Matrix (Fin n) (Fin n) ℂ)⁻¹‖ ≤
      (1 + ‖(A + B)⁻¹‖ * ‖B‖) * (1 + ‖A⁻¹‖ * ‖B‖) := by
  set W : Matrix (Fin n) (Fin n) ℂ := 1 + A⁻¹ * B with hWdef
  set C : ℝ := 1 + ‖(A + B)⁻¹‖ * ‖B‖ with hCdef
  set Cp : ℝ := 1 + ‖A⁻¹‖ * ‖B‖ with hCpdef
  have hCpos : 0 ≤ C := by rw [hCdef]; positivity
  have hlower : ∀ x : EuclideanSpace ℂ (Fin n), ‖x‖ ≤ C * ‖act W x‖ := by
    intro x
    have := lemma11_lower (n := n) A B hA_left hA_right hAB_left hAB_right x
    rw [← hWdef, ← hCdef] at this
    exact this
  have hinv : ‖W⁻¹‖ ≤ C := by
    apply opNorm_le_of_act_le _ hCpos
    intro y
    have hxy : act W (act W⁻¹ y) = y := by
      rw [← act_mul, hW_left, act_one]
    calc
      ‖act W⁻¹ y‖ ≤ C * ‖act W (act W⁻¹ y)‖ := hlower _
      _ = C * ‖y‖ := by rw [hxy]
  have hupper : ‖W‖ ≤ Cp := by
    rw [hWdef, hCpdef]
    apply opNorm_le_of_act_le _ (by positivity)
    intro x
    exact lemma11_upper A B x
  calc
    ‖W‖ * ‖W⁻¹‖ ≤ Cp * C := mul_le_mul hupper hinv (by positivity) (by positivity)
    _ = C * Cp := mul_comm _ _
    _ = (1 + ‖(A + B)⁻¹‖ * ‖B‖) * (1 + ‖A⁻¹‖ * ‖B‖) := by rw [hCdef, hCpdef]

/-- **Lemma 11** (p. 15), packaged: both singular-value bounds and the
condition-number product, in the paper's notation `C_AB`, `C'_AB`. -/
theorem lemma11
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA_left : A * A⁻¹ = 1) (hA_right : A⁻¹ * A = 1)
    (hAB_left : (A + B) * (A + B)⁻¹ = 1) (hAB_right : (A + B)⁻¹ * (A + B) = 1)
    (hW_left : (1 + A⁻¹ * B) * (1 + A⁻¹ * B)⁻¹ = 1) :
    (∀ x : EuclideanSpace ℂ (Fin n),
        ‖x‖ ≤ (1 + ‖(A + B)⁻¹‖ * ‖B‖) * ‖act (1 + A⁻¹ * B) x‖) ∧
    (∀ x : EuclideanSpace ℂ (Fin n),
        ‖act (1 + A⁻¹ * B) x‖ ≤ (1 + ‖A⁻¹‖ * ‖B‖) * ‖x‖) ∧
    ‖(1 + A⁻¹ * B : Matrix (Fin n) (Fin n) ℂ)‖ *
        ‖(1 + A⁻¹ * B : Matrix (Fin n) (Fin n) ℂ)⁻¹‖ ≤
      (1 + ‖(A + B)⁻¹‖ * ‖B‖) * (1 + ‖A⁻¹‖ * ‖B‖) :=
  ⟨lemma11_lower A B hA_left hA_right hAB_left hAB_right,
   lemma11_upper A B,
   lemma11_conditionNumber A B hA_left hA_right hAB_left hAB_right hW_left⟩

/-- `σ̃_min = 1/(1 + ‖(A+B)⁻¹‖‖B‖)` is a valid lower bound for the smallest
singular value of `W`, in the operational form used by Theorem 13: `W` expands
by the factor `σ̃_min`.  (Restatement of `lemma11_lower` after division.) -/
theorem lemma11_sigmaMinValue
    (A B : Matrix (Fin n) (Fin n) ℂ) (hC : 0 < 1 + ‖(A + B)⁻¹‖ * ‖B‖)
    (hA_left : A * A⁻¹ = 1) (hA_right : A⁻¹ * A = 1)
    (hAB_left : (A + B) * (A + B)⁻¹ = 1) (hAB_right : (A + B)⁻¹ * (A + B) = 1) :
    ∀ x : EuclideanSpace ℂ (Fin n),
      (1 / (1 + ‖(A + B)⁻¹‖ * ‖B‖)) * ‖x‖ ≤ ‖act (1 + A⁻¹ * B) x‖ := by
  intro x
  have h := lemma11_lower (n := n) A B hA_left hA_right hAB_left hAB_right x
  have hle : ‖x‖ / (1 + ‖(A + B)⁻¹‖ * ‖B‖) ≤ ‖act (1 + A⁻¹ * B) x‖ := by
    rw [div_le_iff₀ hC]
    rw [mul_comm]
    exact h
  have heq : ‖x‖ / (1 + ‖(A + B)⁻¹‖ * ‖B‖) =
      (1 / (1 + ‖(A + B)⁻¹‖ * ‖B‖)) * ‖x‖ := by
    rw [one_div, div_eq_inv_mul]
  rwa [heq] at hle

end Qatlib.Papers.PrecondQLS20.MainResults
