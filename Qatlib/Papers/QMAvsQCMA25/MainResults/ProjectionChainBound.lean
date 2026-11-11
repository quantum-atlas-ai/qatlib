/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Nat.Choose.Sum

set_option backward.isDefEq.respectTransparency false

/-!
# Recursive odd-occupancy bound along a chain of projectors (Lemma 13.8)

Source: J. Bostanci, J. Haferkamp, C. Nirkhe, M. Zhandry, *Separating QMA from QCMA with a
classical oracle*, arXiv:2511.09551v2, Section 13.3, Lemma 13.8 and eqs. (204)–(208).

The paper's statement is: let `Π 0 ⪯ Π 1 ⪯ ⋯` be an increasing sequence of projectors on a Hilbert
space, let `A 1, …, A t` be operators with `‖A i‖ ≤ 1`, and suppose that for all integers `a, b ≥ 0`
one has `‖(id - Π (a+b)) * A i * Π a‖ ≤ ε ^ (b+1)`. Then for every `λ ≥ 0` and every state `ψ` with
`Π 0 ψ = ψ`,

  `‖(id - Π λ) A t ⋯ A 1 ψ‖ ≤ C(t + λ, t - 1) · ε ^ (λ + 1)`   (eq. (204)),

where `C(·,·)` is the binomial coefficient. The paper's proof (eqs. (205)–(208)) splits
`id = Π λ + (id - Π λ) = Σ_{j ≤ λ} Δ j + (id - Π λ)` with `Δ j = Π j - Π (j-1)` (and `Π (-1) = 0`),
bounds the `λ + 1` `Δ j`-terms by the induction hypothesis at level `j - 1`, and closes the
recursion with the hockey-stick identity `Σ_{j ≤ λ} C(t+j-1, t-1) = C(t+λ, t)` and Pascal's rule.

The formal statement follows the paper's hypotheses literally and replaces "projector" by the two
concrete properties used in the proof: idempotence (`Π * Π = Π`) and self-adjointness
(`adjoint Π = Π`), together with the containment `Π j * Π i = Π i` for `i ≤ j`. The paper states
eq. (204) for a normalised state; here the normalisation is kept as the explicit hypothesis
`‖ψ‖ ≤ 1` instead of inserting a factor `‖ψ‖` on the right-hand side. Nonnegativity of `ε` is not
assumed: it is derived inside the proof from the step hypothesis at `a = b = 0`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMAvsQCMA25.MainResults

open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Inner products against a self-adjoint idempotent -/

/-- For a self-adjoint idempotent `P`, the inner product `⟪P x, x⟫` is the real number `‖P x‖ ^ 2`. -/
lemma inner_proj_left [CompleteSpace H] (P : H →L[ℂ] H) (hidem : P * P = P)
    (hadj : ContinuousLinearMap.adjoint P = P) (x : H) :
    inner ℂ (P x) x = ((‖P x‖ ^ 2 : ℝ) : ℂ) := by
  have h : inner ℂ (P x) x = inner ℂ x (P x) := by
    rw [← ContinuousLinearMap.adjoint_inner_right (A := P) (x := x) (y := x), hadj]
  have h' : inner ℂ x (P x) = inner ℂ (P x) (P x) := by
    rw [← ContinuousLinearMap.adjoint_inner_right (A := P) (x := x) (y := P x), hadj,
      ← ContinuousLinearMap.mul_apply, hidem]
  rw [h, h', inner_self_eq_norm_sq_to_K]
  norm_num

/-- For a self-adjoint idempotent `P`, the inner product `⟪x, P x⟫` is the real number
`‖P x‖ ^ 2`. -/
lemma inner_proj_right [CompleteSpace H] (P : H →L[ℂ] H) (hidem : P * P = P)
    (hadj : ContinuousLinearMap.adjoint P = P) (x : H) :
    inner ℂ x (P x) = ((‖P x‖ ^ 2 : ℝ) : ℂ) := by
  have h' : inner ℂ x (P x) = inner ℂ (P x) (P x) := by
    rw [← ContinuousLinearMap.adjoint_inner_right (A := P) (x := x) (y := P x), hadj,
      ← ContinuousLinearMap.mul_apply, hidem]
  rw [h', inner_self_eq_norm_sq_to_K]
  norm_num

/-- For a self-adjoint idempotent `P`, the inner product `⟪P x, P x⟫` is the real number
`‖P x‖ ^ 2`. -/
lemma inner_proj_self (P : H →L[ℂ] H) (x : H) :
    inner ℂ (P x) (P x) = ((‖P x‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  norm_num

/-! ### Contractions from idempotent self-adjoint operators -/

/-- An idempotent self-adjoint continuous linear operator is a contraction. This is the operator
norm fact used in eq. (206a) of the paper, where the projector factors are dropped from the norm
bound. -/
lemma norm_le_one_of_idem_selfAdjoint [CompleteSpace H] (Q : H →L[ℂ] H) (hidem : Q * Q = Q)
    (hadj : ContinuousLinearMap.adjoint Q = Q) : ‖Q‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound Q zero_le_one fun x => ?_
  have hreal : inner ℂ x (Q x) = ((‖Q x‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : inner ℂ x (Q x) = inner ℂ (Q x) (Q x) := by
      rw [← ContinuousLinearMap.adjoint_inner_right (A := Q) (x := x) (y := Q x), hadj,
        ← ContinuousLinearMap.mul_apply, hidem]
    rw [h1, inner_self_eq_norm_sq_to_K]
    norm_num
  have hCS : ‖Q x‖ ^ 2 ≤ ‖x‖ * ‖Q x‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) x (Q x)
    rw [hreal, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h
    exact h
  have hsq : ‖Q x‖ * ‖Q x‖ ≤ ‖x‖ * ‖Q x‖ := by
    simpa [sq] using hCS
  have hle : ‖Q x‖ ≤ ‖x‖ := by
    by_contra h
    have hlt : ‖x‖ < ‖Q x‖ := not_le.mp h
    nlinarith [hsq, norm_nonneg (Q x), norm_nonneg x]
  simpa using hle

/-- The complementary operator `id - P` of an orthogonal projector `P` is a contraction, so the
factor `id - Π λ` may be dropped from the operator norm bound (eq. (206a)). -/
lemma norm_one_sub_of_idem_selfAdjoint [CompleteSpace H] (P : H →L[ℂ] H) (hidem : P * P = P)
    (hadj : ContinuousLinearMap.adjoint P = P) : ‖1 - P‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound (1 - P) zero_le_one fun x => ?_
  have hxx : inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_num
  have hexp : inner ℂ (x - P x) (x - P x) = ((‖x‖ ^ 2 - ‖P x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      inner_proj_self P x, inner_proj_left P hidem hadj x, inner_proj_right P hidem hadj x, hxx]
    push_cast
    ring
  have hnorm : inner ℂ (x - P x) (x - P x) = ((‖x - P x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_num
  have hsq : ‖x - P x‖ ^ 2 = ‖x‖ ^ 2 - ‖P x‖ ^ 2 :=
    RCLike.ofReal_inj.mp (hnorm.symm.trans hexp)
  have hle : ‖x - P x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hsq]
    have : (0 : ℝ) ≤ ‖P x‖ ^ 2 := by positivity
    linarith
  have hnorm' := le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (norm_nonneg x) hle
  simpa using hnorm'

/-! ### The difference operators `Δ j = Π j - Π (j-1)` -/

/-- The complementary projector `Q j := id - Π (j-1)`, with the paper's convention `Π (-1) = 0`, so
that `Q 0 = id`. This is the factor isolated in eq. (207a). -/
def projComplement (P : ℕ → H →L[ℂ] H) : ℕ → H →L[ℂ] H
  | 0 => 1
  | (j + 1) => 1 - P j

/-- The increment `Δ j := Π j - Π (j-1)`, with `Π (-1) = 0`, i.e. `Δ 0 = Π 0`. These are the
operators summed in eq. (205). -/
def projDelta (P : ℕ → H →L[ℂ] H) : ℕ → H →L[ℂ] H
  | 0 => P 0
  | (j + 1) => P (j + 1) - P j

/-- The compatibility convention `Π (-1) = 0` makes `Q 0` the identity. -/
@[simp] lemma projComplement_zero (P : ℕ → H →L[ℂ] H) : projComplement P 0 = 1 := rfl

/-- Unfolding `Q (j+1) = id - Π j`. -/
@[simp] lemma projComplement_succ (P : ℕ → H →L[ℂ] H) (j : ℕ) :
    projComplement P (j + 1) = 1 - P j := rfl

/-- The convention `Π (-1) = 0` makes `Δ 0` equal to `Π 0`. -/
@[simp] lemma projDelta_zero (P : ℕ → H →L[ℂ] H) : projDelta P 0 = P 0 := rfl

/-- Unfolding `Δ (j+1) = Π (j+1) - Π j`. -/
@[simp] lemma projDelta_succ (P : ℕ → H →L[ℂ] H) (j : ℕ) :
    projDelta P (j + 1) = P (j + 1) - P j := rfl

/-- `Δ j = Π j * (id - Π (j-1))`: containment of the projectors turns the difference into a
product (step (207a) of the paper). -/
lemma projDelta_eq_mul (P : ℕ → H →L[ℂ] H)
    (hPmono : ∀ i j : ℕ, i ≤ j → P j * P i = P i) (j : ℕ) :
    projDelta P j = P j * projComplement P j := by
  cases j with
  | zero => simp
  | succ j =>
    have h := hPmono j (j + 1) (Nat.le_succ j)
    simp only [projDelta_succ, projComplement_succ]
    rw [show P (j + 1) * (1 - P j) = P (j + 1) - P j by rw [mul_sub, mul_one, h]]

/-- Telescoping `Σ_{j ≤ λ} Δ j = Π λ`, the identity that makes `Σ_{j ≤ λ} Δ j + (id - Π λ) = id`
in eq. (205). -/
lemma sum_projDelta (P : ℕ → H →L[ℂ] H) (lam : ℕ) :
    ∑ j ∈ Finset.range (lam + 1), projDelta P j = P lam := by
  induction lam with
  | zero => simp
  | succ lam ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [projDelta_succ]
    abel

/-! ### The hockey-stick count of eq. (207d) -/

/-- Hockey-stick identity in the shape used by the paper: `Σ_{j ≤ λ} C(t+j-1, t-1) = C(t+λ, t)`
(eq. (207d)), proved by induction using Pascal's rule. -/
lemma sum_range_choose_shift (t lam : ℕ) (ht : 1 ≤ t) :
    ∑ j ∈ Finset.range (lam + 1), (t + j - 1).choose (t - 1) = (t + lam).choose t := by
  induction lam with
  | zero =>
    simp [Nat.choose_self]
  | succ lam ih =>
    rw [Finset.sum_range_succ, ih]
    have harg : t + (lam + 1) - 1 = t + lam := by omega
    rw [harg]
    have hpascal := Nat.choose_succ_succ (t + lam) (t - 1)
    rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, Nat.sub_add_cancel ht] at hpascal
    have htop : t + (lam + 1) = t + lam + 1 := by omega
    rw [htop, hpascal, add_comm]

/-! ### The chain of query operators -/

/-- The ordered product `A t * ⋯ * A 1` of the query operators appearing in eq. (204). -/
def chainProd (A : ℕ → H →L[ℂ] H) : ℕ → H →L[ℂ] H
  | 0 => 1
  | (t + 1) => A (t + 1) * chainProd A t

/-- The empty product in the chain is the identity. -/
@[simp] lemma chainProd_zero (A : ℕ → H →L[ℂ] H) : chainProd A 0 = 1 := rfl

/-- The chain is built by prepending `A (t+1)` to the chain of length `t`, matching the ordering
`A t ⋯ A 1` of eq. (204). -/
@[simp] lemma chainProd_succ (A : ℕ → H →L[ℂ] H) (t : ℕ) :
    chainProd A (t + 1) = A (t + 1) * chainProd A t := rfl

/-- Contractive queries keep the state inside the unit ball along the whole chain. -/
lemma norm_chainProd_apply_le (A : ℕ → H →L[ℂ] H) (hA : ∀ i : ℕ, ‖A i‖ ≤ 1) (t : ℕ)
    (ψ : H) : ‖chainProd A t ψ‖ ≤ ‖ψ‖ := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [chainProd_succ, ContinuousLinearMap.mul_apply]
    calc ‖A (t + 1) (chainProd A t ψ)‖ ≤ ‖A (t + 1)‖ * ‖chainProd A t ψ‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖ψ‖ := mul_le_mul (hA (t + 1)) ih (norm_nonneg _) zero_le_one
      _ = ‖ψ‖ := one_mul _

/-! ### Lemma 13.8 -/

/-- **Lemma 13.8** of the paper (eq. (204)): a chain of `t` contractive operators can raise the
projector index from `0` to `λ` with norm at most `C(t+λ, t-1) ε^{λ+1}`, provided each step raises
the index by `b` only at the price of a factor `ε^{b+1}`.

The paper's inductive proof is followed line by line: eq. (205) splits off the `λ + 1`
`Δ j`-terms, eq. (206) handles the `id - Π λ` remainder using contractivity (here
`norm_one_sub_of_idem_selfAdjoint`), eq. (207) applies the induction hypothesis at the shifted
level `j - 1`, and the sum is closed by `sum_range_choose_shift` and Pascal's rule in place of
eq. (208). -/
theorem projectionChain_bound [CompleteSpace H] (P : ℕ → H →L[ℂ] H) (A : ℕ → H →L[ℂ] H)
    (hPidem : ∀ i : ℕ, P i * P i = P i)
    (hPadj : ∀ i : ℕ, ContinuousLinearMap.adjoint (P i) = P i)
    (hPmono : ∀ i j : ℕ, i ≤ j → P j * P i = P i)
    (hA : ∀ i : ℕ, ‖A i‖ ≤ 1) (ε : ℝ)
    (hstep : ∀ (i a b : ℕ), ‖(1 - P (a + b)) * A i * P a‖ ≤ ε ^ (b + 1)) :
    ∀ (t : ℕ), 1 ≤ t → ∀ (lam : ℕ) (ψ : H), ‖ψ‖ ≤ 1 → P 0 ψ = ψ →
      ‖((1 - P lam) * chainProd A t) ψ‖ ≤ ((t + lam).choose (t - 1) : ℝ) * ε ^ (lam + 1) := by
  intro t ht
  -- `ε ≥ 0` is forced by the step hypothesis at `a = b = 0`, so it is not an extra assumption.
  have hε : 0 ≤ ε := by
    have h := hstep 0 0 0
    simp only [Nat.zero_add, pow_one] at h
    exact le_trans (norm_nonneg _) h
  induction t, ht using Nat.le_induction with
  | base =>
    intro lam ψ hψ hψ0
    calc ‖((1 - P lam) * chainProd A 1) ψ‖
        = ‖((1 - P (0 + lam)) * A 1 * P 0) ψ‖ := by
          rw [Nat.zero_add, chainProd_succ, chainProd_zero]
          simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, hψ0]
      _ ≤ ‖(1 - P (0 + lam)) * A 1 * P 0‖ * ‖ψ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε ^ (lam + 1) * 1 :=
          mul_le_mul (hstep 1 0 lam) hψ (norm_nonneg _) (pow_nonneg hε _)
      _ = ((1 + lam).choose (1 - 1) : ℝ) * ε ^ (lam + 1) := by
          rw [Nat.choose_zero_right]
          ring
  | succ t ht ih =>
    intro lam ψ hψ hψ0
    set v : H := chainProd A t ψ with hv
    have hvnorm : ‖v‖ ≤ 1 := le_trans (norm_chainProd_apply_le A hA t ψ) hψ
    -- Eq. (205): split `id = Σ_{j ≤ λ} Δ j + (id - Π λ)`.
    have hsplit : v = (∑ j ∈ Finset.range (lam + 1), (projDelta P j) v) + (1 - P lam) v := by
      rw [← ContinuousLinearMap.sum_apply, ← ContinuousLinearMap.add_apply,
        ← sum_projDelta P lam]
      simp
    have hexp : (1 - P lam) (A (t + 1) v)
        = (∑ j ∈ Finset.range (lam + 1), (1 - P lam) (A (t + 1) ((projDelta P j) v)))
          + (1 - P lam) (A (t + 1) ((1 - P lam) v)) := by
      conv_lhs => rw [hsplit]
      simp only [map_add, map_sum]
    -- Eq. (207): the `Δ j`-terms.
    have hterm : ∀ j ∈ Finset.range (lam + 1),
        ‖(1 - P lam) (A (t + 1) (projDelta P j v))‖
          ≤ ((t + j - 1).choose (t - 1) : ℝ) * ε ^ (lam + 1) := by
      intro j hj
      have hjle : j ≤ lam := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hdelta : projDelta P j = P j * projComplement P j := projDelta_eq_mul P hPmono j
      have hstepj : ‖(1 - P lam) * A (t + 1) * P j‖ ≤ ε ^ (lam - j + 1) := by
        have h := hstep (t + 1) j (lam - j)
        rwa [show j + (lam - j) = lam by omega] at h
      have hQ : ‖projComplement P j v‖ ≤ ((t + j - 1).choose (t - 1) : ℝ) * ε ^ j := by
        rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · subst hj0
          simp only [projComplement_zero, ContinuousLinearMap.one_apply]
          have h1 : ((t + 0 - 1).choose (t - 1) : ℝ) * ε ^ 0 = 1 := by
            rw [Nat.add_zero, Nat.choose_self, pow_zero, mul_one]
            norm_num
          rw [h1]
          exact hvnorm
        · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hjpos)
          have h := ih j' ψ hψ hψ0
          have harg : t + (j' + 1) - 1 = t + j' := by omega
          simpa only [projComplement_succ, ContinuousLinearMap.mul_apply, ← hv, harg] using h
      have hle : ‖(1 - P lam) (A (t + 1) (projDelta P j v))‖
          ≤ ε ^ (lam - j + 1) * (((t + j - 1).choose (t - 1) : ℝ) * ε ^ j) := by
        rw [hdelta]
        calc ‖(1 - P lam) (A (t + 1) ((P j * projComplement P j) v))‖
            = ‖((1 - P lam) * A (t + 1) * P j) (projComplement P j v)‖ := by
              simp only [ContinuousLinearMap.mul_apply]
          _ ≤ ‖(1 - P lam) * A (t + 1) * P j‖ * ‖projComplement P j v‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ ε ^ (lam - j + 1) * (((t + j - 1).choose (t - 1) : ℝ) * ε ^ j) :=
              mul_le_mul hstepj hQ (norm_nonneg _) (pow_nonneg hε _)
      have hexp_eq : ε ^ (lam - j + 1) * (((t + j - 1).choose (t - 1) : ℝ) * ε ^ j)
          = ((t + j - 1).choose (t - 1) : ℝ) * ε ^ (lam + 1) := by
        rw [← mul_assoc, mul_comm (ε ^ (lam - j + 1)) (((t + j - 1).choose (t - 1) : ℝ)),
          mul_assoc, ← pow_add]
        have hidx : lam - j + 1 + j = lam + 1 := by omega
        rw [hidx]
      rw [hexp_eq] at hle
      exact hle
    -- Eq. (206): the `(id - Π λ)` remainder.
    have hB : ‖(1 - P lam) (A (t + 1) ((1 - P lam) v))‖
        ≤ ((t + lam).choose (t - 1) : ℝ) * ε ^ (lam + 1) := by
      have hcontract : ‖(1 - P lam) * A (t + 1)‖ ≤ 1 := by
        refine le_trans (norm_mul_le _ _) ?_
        calc ‖1 - P lam‖ * ‖A (t + 1)‖ ≤ 1 * 1 :=
              mul_le_mul (norm_one_sub_of_idem_selfAdjoint (P lam) (hPidem lam) (hPadj lam))
                (hA (t + 1)) (norm_nonneg _) zero_le_one
          _ = 1 := by norm_num
      have h := ih lam ψ hψ hψ0
      calc ‖(1 - P lam) (A (t + 1) ((1 - P lam) v))‖
          = ‖((1 - P lam) * A (t + 1)) ((1 - P lam) v)‖ := by
            simp only [ContinuousLinearMap.mul_apply]
        _ ≤ ‖(1 - P lam) * A (t + 1)‖ * ‖(1 - P lam) v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * (((t + lam).choose (t - 1) : ℝ) * ε ^ (lam + 1)) := by
            refine mul_le_mul hcontract ?_ (norm_nonneg _) zero_le_one
            simpa only [← hv, ContinuousLinearMap.mul_apply] using h
        _ = ((t + lam).choose (t - 1) : ℝ) * ε ^ (lam + 1) := one_mul _
    have hsum : ∑ j ∈ Finset.range (lam + 1),
          ‖(1 - P lam) (A (t + 1) (projDelta P j v))‖ ≤ ε ^ (lam + 1) * ((t + lam).choose t : ℝ) := by
      calc ∑ j ∈ Finset.range (lam + 1), ‖(1 - P lam) (A (t + 1) (projDelta P j v))‖
          ≤ ∑ j ∈ Finset.range (lam + 1), ((t + j - 1).choose (t - 1) : ℝ) * ε ^ (lam + 1) :=
            Finset.sum_le_sum hterm
        _ = (∑ j ∈ Finset.range (lam + 1), ((t + j - 1).choose (t - 1) : ℝ)) * ε ^ (lam + 1) := by
            rw [Finset.sum_mul]
        _ = ε ^ (lam + 1) * ((t + lam).choose t : ℝ) := by
            rw [← Nat.cast_sum, sum_range_choose_shift t lam ht, mul_comm]
    -- Assemble eq. (208).
    have hnorm : ‖(1 - P lam) (A (t + 1) v)‖
        ≤ (∑ j ∈ Finset.range (lam + 1), ‖(1 - P lam) (A (t + 1) (projDelta P j v))‖)
          + ‖(1 - P lam) (A (t + 1) ((1 - P lam) v))‖ := by
      rw [hexp]
      exact le_trans (norm_add_le _ _) (add_le_add (norm_sum_le _ _) le_rfl)
    have hmain := le_trans hnorm (add_le_add hsum hB)
    have hpascal := Nat.choose_succ_succ (t + lam) (t - 1)
    rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, Nat.sub_add_cancel ht] at hpascal
    have hcoef : ((t + 1 + lam).choose t : ℝ)
        = ((t + lam).choose t : ℝ) + ((t + lam).choose (t - 1) : ℝ) := by
      have htop : t + 1 + lam = t + lam + 1 := by omega
      rw [htop, hpascal]
      push_cast
      ring
    calc ‖((1 - P lam) * chainProd A (t + 1)) ψ‖
        = ‖(1 - P lam) (A (t + 1) v)‖ := by
          rw [chainProd_succ]
          simp only [ContinuousLinearMap.mul_apply]
          rw [← hv]
      _ ≤ ε ^ (lam + 1) * ((t + lam).choose t : ℝ)
            + ((t + lam).choose (t - 1) : ℝ) * ε ^ (lam + 1) := hmain
      _ = ((t + 1 + lam).choose t : ℝ) * ε ^ (lam + 1) := by
          rw [hcoef]
          ring

end Qatlib.Papers.QMAvsQCMA25.MainResults
