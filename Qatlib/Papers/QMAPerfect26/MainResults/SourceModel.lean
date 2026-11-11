/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Complex.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# QMAPerfect26 — shared mathematical model

Fixed paper: Grewal–Rudolph, *QMA has perfect completeness*, arXiv:2609.13032v1 (2026-09-11).

This module fixes the objects used across every claim file of the paper layer:

* `Idx m = Fin m → Bool`, the computational-basis index set `{0,1}^m`;
* `ProofMat m = Matrix (Idx m) (Idx m) ℝ`, the (real-symmetrised) proof-space operator;
* `ket z`, the basis vector `|z⟩`;
* `IsDyadicMat h E`, the paper's "`2^h E` is an integer matrix" dyadic-denominator
  predicate (Cor. 3.2, p.7);
* `Gamma A ℓ z = (A^ℓ)_{zz} = ⟨z|A^ℓ|z⟩`, the diagonal entry used in Lemma 3.3;
* `histVec A ℓ z` and `cyclicOp A ℓ z Γ`, the history vector `|Ω_z⟩` and cyclic
  operator `C_{z,Γ}` of Lemma 3.4, Eq. (3), p.8;
* a minimal `InQMA` promise-verifier model used by the class-level claims.

The whole layer works over `ℝ`, exactly as the paper reduces to: Lemma 3.1 (real
simulation, p.7) produces real gate matrices, so the acceptance operator `E` and
`A = 2E` are real symmetric matrices. Mathematical state/output semantics are kept;
arbitrary program uniformity and gate-set membership are represented by the explicit
`UsesGateSet`/dyadic predicates below rather than by an unstated polynomial-time oracle.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QMAPerfect26.MainResults

/-- Computational-basis index `{0,1}^m`, represented as `Fin m → Bool`. -/
abbrev Idx (m : ℕ) : Type := Fin m → Bool

/-- An operator on the `m`-qubit proof register, taken real (Lemma 3.1's real
simulation makes the acceptance operator real symmetric). -/
abbrev ProofMat (m : ℕ) : Type := Matrix (Idx m) (Idx m) ℝ

/-- The clock–proof register `ℂℓ ⊗ ℙ` of Lemma 3.4: clock values `0,…,ℓ`. -/
abbrev ClockProof (ℓ m : ℕ) : Type := Fin (ℓ + 1) × Idx m

/-- The computational-basis ket `|z⟩`. -/
def ket {m : ℕ} (z : Idx m) : Idx m → ℝ := Pi.single z 1

/-- Unit norm of a computational basis ket. -/
@[simp] lemma ket_norm {m : ℕ} (z : Idx m) : ‖ket z‖ = 1 := by
  simp [ket, Pi.norm_single]

/-- `|z⟩` has entry `1` at `z`. -/
@[simp] lemma ket_self {m : ℕ} (z : Idx m) : ket z z = 1 := by
  simp [ket]

/-- `|z⟩` has entry `0` away from `z`. -/
lemma ket_of_ne {m : ℕ} {z z' : Idx m} (h : z' ≠ z) : ket z z' = 0 := by
  simp [ket, Pi.single_apply, h]

/-- `M` has all entries in the image of `ℤ → ℝ`, i.e. `M` is an integer matrix. -/
def IsIntegerMat {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ i j, ∃ k : ℤ, M i j = (k : ℝ)

/-- The identity matrix is an integer matrix. -/
lemma IsIntegerMat.one {ι : Type} [Fintype ι] [DecidableEq ι] :
    IsIntegerMat (1 : Matrix ι ι ℝ) := by
  intro i j
  by_cases h : i = j
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [Matrix.one_apply, h]⟩

/-- The zero matrix is an integer matrix. -/
lemma IsIntegerMat.zero {ι : Type} [Fintype ι] : IsIntegerMat (0 : Matrix ι ι ℝ) :=
  fun i j => ⟨0, by simp⟩

/-- Integer matrices are closed under addition. -/
lemma IsIntegerMat.add {ι : Type} [Fintype ι] {M N : Matrix ι ι ℝ}
    (hM : IsIntegerMat M) (hN : IsIntegerMat N) : IsIntegerMat (M + N) := by
  intro i j
  obtain ⟨a, ha⟩ := hM i j
  obtain ⟨b, hb⟩ := hN i j
  exact ⟨a + b, by rw [Matrix.add_apply, ha, hb, Int.cast_add]⟩

/-- Integer matrices are closed under negation. -/
lemma IsIntegerMat.neg {ι : Type} [Fintype ι] {M : Matrix ι ι ℝ}
    (hM : IsIntegerMat M) : IsIntegerMat (-M) := by
  intro i j
  obtain ⟨a, ha⟩ := hM i j
  exact ⟨-a, by rw [Matrix.neg_apply, ha, Int.cast_neg]⟩

/-- Integer matrices are closed under multiplication (entry expansion of the product sum). -/
lemma IsIntegerMat.mul {ι : Type} [Fintype ι] {M N : Matrix ι ι ℝ}
    (hM : IsIntegerMat M) (hN : IsIntegerMat N) : IsIntegerMat (M * N) := by
  intro i j
  choose a ha using fun k => hM i k
  choose b hb using fun k => hN k j
  refine ⟨∑ k, a k * b k, ?_⟩
  rw [Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [ha k, hb k]

/-- Integer matrices are closed under powers (induction on `pow_succ'`). -/
lemma IsIntegerMat.pow {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ}
    (hM : IsIntegerMat M) : ∀ n : ℕ, IsIntegerMat (M ^ n)
  | 0 => by simpa using IsIntegerMat.one
  | n + 1 => by
    rw [pow_succ']
    exact hM.mul (IsIntegerMat.pow hM n)

/-- Integer matrices are closed under integer scaling. -/
lemma IsIntegerMat.smul_int {ι : Type} [Fintype ι] {M : Matrix ι ι ℝ}
    (hM : IsIntegerMat M) (c : ℤ) : IsIntegerMat ((c : ℝ) • M) := by
  intro i j
  obtain ⟨a, ha⟩ := hM i j
  exact ⟨c * a, by rw [Matrix.smul_apply, ha, smul_eq_mul, Int.cast_mul]⟩

/-- `2^h E` is an integer matrix — the dyadic-denominator property of Cor. 3.2. -/
def IsDyadicMat {ι : Type} [Fintype ι] (h : ℕ) (E : Matrix ι ι ℝ) : Prop :=
  IsIntegerMat ((2 : ℝ) ^ h • E)

/-- Unfolding: dyadicity is integrality of `2^h • E`. -/
lemma IsDyadicMat.integer {ι : Type} [Fintype ι] {h : ℕ} {E : Matrix ι ι ℝ}
    (hE : IsDyadicMat h E) : IsIntegerMat ((2 : ℝ) ^ h • E) := hE

/-! ## `Γ_z` and Lemma 3.3 arithmetic

`Γ_z = ⟨z|A^ℓ|z⟩ = (A^ℓ)_{zz}` (the `(z,z)` diagonal entry), for `A = 2E`.
-/

/-- `Γ_z = ⟨z|A^ℓ|z⟩`, defined as the `(z,z)` diagonal entry of `A^ℓ`. -/
def Gamma {m : ℕ} (A : ProofMat m) (ℓ : ℕ) (z : Idx m) : ℝ := (A ^ ℓ) z z

/-- `Γ_z` equals the quadratic form `⟨z|A^ℓ|z⟩` used in the paper. -/
lemma Gamma_eq_quadForm {m : ℕ} (A : ProofMat m) (ℓ : ℕ) (z : Idx m) :
    Gamma A ℓ z = ket z ⬝ᵥ ((A ^ ℓ) *ᵥ ket z) := by
  rw [Gamma, dotProduct]
  simp only [ket, Pi.single_apply]
  -- `∑ w, (if z = w then 1 else 0) * (A^ℓ *ᵥ ket z) w = (A^ℓ *ᵥ ket z) z`
  rw [Finset.sum_eq_single z]
  · simp
  · intro b _ hb; simp [hb]
  · intro hz; simp at hz

/-- Lemma 3.3, nonnegativity: `0 ≤ Γ_z`. -/
theorem Gamma_nonneg {m : ℕ} (A : ProofMat m) (ℓ : ℕ) (z : Idx m)
    (hA : A.PosSemidef) : 0 ≤ Gamma A ℓ z :=
  (hA.pow ℓ).diag_nonneg

/-- Scalar (operator) norm bound `‖A v‖ ≤ 2‖v‖` propagated to powers. -/
lemma norm_pow_mulVec_le {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : ∀ v : ι → ℝ, ‖A *ᵥ v‖ ≤ 2 * ‖v‖) :
    ∀ (ℓ : ℕ) (v : ι → ℝ), ‖(A ^ ℓ) *ᵥ v‖ ≤ 2 ^ ℓ * ‖v‖
  | 0, v => by
    simp only [pow_zero, one_mulVec]
    rw [one_mul]
  | ℓ + 1, v => by
    rw [pow_succ', ← mulVec_mulVec]
    calc ‖A *ᵥ (A ^ ℓ *ᵥ v)‖ ≤ 2 * ‖A ^ ℓ *ᵥ v‖ := hA _
      _ ≤ 2 * (2 ^ ℓ * ‖v‖) := by
        exact mul_le_mul_of_nonneg_left (norm_pow_mulVec_le A hA ℓ v) (by norm_num)
      _ = 2 ^ (ℓ + 1) * ‖v‖ := by ring

/-- Lemma 3.3, upper bound: `Γ_z ≤ 2^ℓ` from `‖A‖ ≤ 2` (`A` acts as a contraction
with constant `2`, i.e. `A ⪯ 2·I` in operator-norm form). -/
theorem Gamma_le {m : ℕ} (A : ProofMat m) (ℓ : ℕ) (z : Idx m)
    (hbound : ∀ v : Idx m → ℝ, ‖A *ᵥ v‖ ≤ 2 * ‖v‖) :
    Gamma A ℓ z ≤ 2 ^ ℓ := by
  have hz : Gamma A ℓ z = ((A ^ ℓ) *ᵥ ket z) z := by
    rw [Gamma, Matrix.mulVec, dotProduct]
    simp only [ket, Pi.single_apply]
    rw [Finset.sum_eq_single z]
    · simp
    · intro b _ hb; simp [hb]
    · intro hz0; simp at hz0
  have hle : ‖Gamma A ℓ z‖ ≤ ‖(A ^ ℓ) *ᵥ ket z‖ := by
    rw [hz]; exact norm_le_pi_norm _ _
  have hbound' : ‖(A ^ ℓ) *ᵥ ket z‖ ≤ 2 ^ ℓ * ‖ket z‖ := norm_pow_mulVec_le A hbound ℓ (ket z)
  have : Gamma A ℓ z ≤ ‖Gamma A ℓ z‖ := le_abs_self _
  calc Gamma A ℓ z ≤ ‖Gamma A ℓ z‖ := this
    _ ≤ ‖(A ^ ℓ) *ᵥ ket z‖ := hle
    _ ≤ 2 ^ ℓ * ‖ket z‖ := hbound'
    _ = 2 ^ ℓ := by rw [ket_norm, mul_one]

/-- Lemma 3.3, integrality: if `2^h E` is an integer matrix and `A = 2E`, then
`2^{h·ℓ} Γ_z ∈ ℤ`. -/
theorem Gamma_integer {m : ℕ} (E : ProofMat m) (h ℓ : ℕ) (z : Idx m)
    (hint : IsDyadicMat h E) :
    ∃ k : ℤ, (2 : ℝ) ^ (h * ℓ) * Gamma ((2 : ℝ) • E) ℓ z = (k : ℝ) := by
  -- `2^{hℓ} (2E)^ℓ = 2^ℓ · (2^h E)^ℓ`, and `(2^h E)^ℓ` is an integer matrix.
  have hsmul : (2 : ℝ) ^ (h * ℓ) • ((2 : ℝ) • E) ^ ℓ
      = (2 : ℝ) ^ ℓ • ((2 : ℝ) ^ h • E) ^ ℓ := by
    rw [smul_pow, smul_pow, smul_smul, smul_smul, ← pow_mul, mul_comm h ℓ, mul_comm]
  have hint' : IsIntegerMat ((2 : ℝ) ^ (h * ℓ) • ((2 : ℝ) • E) ^ ℓ) := by
    rw [hsmul]
    have hz := IsIntegerMat.smul_int (IsIntegerMat.pow hint ℓ) ((2 : ℤ) ^ ℓ)
    simpa [Int.cast_pow] using hz
  obtain ⟨k, hk⟩ := hint' z z
  refine ⟨k, ?_⟩
  rw [← hk, Matrix.smul_apply, smul_eq_mul, Gamma]

/-- Lemma 3.3, YES-instance existence (paper's pigeonhole step): if the normalised trace
of `A^ℓ` exceeds `2^m · 2`, then some diagonal entry `Γ_z` is `> 2`. -/
theorem Gamma_yes_exists {m : ℕ} (A : ProofMat m) (ℓ : ℕ)
    (htrace : (2 : ℝ) ^ m * 2 < (A ^ ℓ).trace) :
    ∃ z : Idx m, 2 < Gamma A ℓ z := by
  by_contra h
  push_neg at h
  have hle : (A ^ ℓ).trace ≤ (2 : ℝ) ^ m * 2 := by
    rw [Matrix.trace]
    calc ∑ z, (A ^ ℓ) z z = ∑ z, Gamma A ℓ z := rfl
      _ ≤ ∑ _z : Idx m, 2 := Finset.sum_le_sum (fun z _ => h z)
      _ = (Fintype.card (Idx m) : ℝ) * 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (2 : ℝ) ^ m * 2 := by rw [Fintype.card_fun]; simp [Idx]
  linarith

/-! ## The cyclic operator `C_{z,Γ}` and history vector `|Ω_z⟩` (Lemma 3.4) -/

/-- History vector `|Ω_z⟩ = ∑_{t=0}^ℓ |t⟩ ⊗ A^t|z⟩` (Lemma 3.4, Eq. (3)). -/
def histVec {m : ℕ} (A : ProofMat m) (ℓ : ℕ) (z : Idx m) : ClockProof ℓ m → ℝ :=
  fun p => ((A ^ p.1.val) *ᵥ ket z) p.2

/-- The history vector is nonzero: its clock-`0` component is `|z⟩ ≠ 0`. -/
lemma histVec_ne_zero {m : ℕ} (A : ProofMat m) (ℓ : ℕ) (z : Idx m) :
    histVec A ℓ z ≠ 0 := by
  intro h
  have := congrFun h (⟨0, Nat.succ_pos ℓ⟩, z)
  simp [histVec, ket] at this

/-- Cyclic operator `C_{z,Γ} = ∑_{t<ℓ}|t+1⟩⟨t|⊗A + |0⟩⟨ℓ|⊗Γ⁻¹|z⟩⟨z|` (Lemma 3.4, Eq. (3)).
The forward transitions are `A` on the proof register; the single closing transition is
`Γ⁻¹|z⟩⟨z|` from clock `ℓ` back to clock `0`. -/
def cyclicOp {m : ℕ} (A : ProofMat m) (ℓ : ℕ) (z : Idx m) (Γ : ℝ) :
    Matrix (ClockProof ℓ m) (ClockProof ℓ m) ℝ :=
  fun p q =>
    (if p.1.val = q.1.val + 1 then A p.2 q.2 else 0) +
    (if p.1.val = 0 ∧ q.1.val = ℓ then Γ⁻¹ * ket z p.2 * ket z q.2 else 0)

/-- General fact behind Lemma 3.4(i): a vector fixed by `C` lies in the kernel of
`I − C` (and a nonzero fixed vector exhibits a nontrivial kernel element). -/
theorem fixedPoint_iff_kernel {α : Type} [Fintype α] [DecidableEq α] (C : Matrix α α ℝ) (ω : α → ℝ)
    (hfix : C *ᵥ ω = ω) : ((1 - C) *ᵥ ω = 0) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfix, sub_self]

/-! ## Lemma 3.4 fixed-point and contraction cores -/

/-- Lemma 3.4(i), the cyclic fixed point: with `Γ = Γ_z`, the history vector `|Ω_z⟩`
satisfies `C_{z,Γ}|Ω_z⟩ = |Ω_z⟩`. This is the paper's "the operator cyclically permutes
the summands of `|Ω_z⟩`, leaving their sum fixed" (Lemma 3.4 proof, p.8): the forward
transition sends the `t`-th summand `|t⟩⊗A^t|z⟩` to `|t+1⟩⊗A^{t+1}|z⟩`, and the
closing transition sends `|ℓ⟩⊗A^ℓ|z⟩` to `Γ_z^{-1}|z⟩⟨z|A^ℓ|z⟩ = |z⟩`. -/
theorem cyclicOp_fixes_histVec {m : ℕ} (A : ProofMat m) (ℓ : ℕ) (z : Idx m) (Γ : ℝ)
    (hΓ : Γ = Gamma A ℓ z) (hΓ0 : Γ ≠ 0) :
    cyclicOp A ℓ z Γ *ᵥ histVec A ℓ z = histVec A ℓ z := by
  funext p
  obtain ⟨⟨tval, hval⟩, w⟩ := p
  show ∑ q : ClockProof ℓ m, cyclicOp A ℓ z Γ (⟨tval, hval⟩, w) q * histVec A ℓ z q
      = histVec A ℓ z (⟨tval, hval⟩, w)
  rw [Fintype.sum_prod_type]
  simp only [cyclicOp, histVec]
  have hdot : ∑ w' : Idx m, ket z w' * ((A ^ ℓ) *ᵥ ket z) w'
      = ket z ⬝ᵥ ((A ^ ℓ) *ᵥ ket z) := rfl
  rcases tval with _ | k
  · -- Clock slot `0`: only the closing transition from clock `ℓ` contributes.
    rw [Finset.sum_eq_single (Fin.last ℓ)]
    · have e1 : Γ⁻¹ * (ket z w * Γ) = ket z w := by
        rw [mul_comm (ket z w) Γ, ← mul_assoc]
        first
          | rw [inv_mul_cancel Γ, one_mul]
          | rw [inv_mul_cancel₀ hΓ0, one_mul]
      simp only [Fin.val_last, if_neg (by omega : ¬ (0 : ℕ) = ℓ + 1),
        if_pos (show (True ∧ (ℓ = ℓ)) by simp), if_pos (show (0 = 0 ∧ ℓ = ℓ) by simp),
        if_pos (show (True ∧ True) by simp), zero_add, mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum, hdot, ← Gamma_eq_quadForm, ← hΓ, pow_zero,
        one_mulVec]
      first
        | rw [e1]
        | rw [mul_assoc Γ⁻¹ (ket z w) Γ, e1]
    · intro b _hb hne
      have hbℓ : b.val ≠ ℓ := fun h => hne (Fin.ext h)
      simp [hbℓ]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- Clock slot `k+1`: only the forward transition from clock `k` contributes.
    have hk : k < ℓ + 1 := by omega
    rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin (ℓ + 1))]
    · simp only [if_pos (trivial : True), if_pos (show ((k + 1 : ℕ) = k + 1) by omega),
        if_neg (by simp [Nat.succ_ne_zero] : ¬ ((k + 1 : ℕ) = 0 ∧ k = ℓ)), add_zero]
      have h1 : ∑ w' : Idx m, A w w' * ((A ^ k) *ᵥ ket z) w'
          = (A *ᵥ ((A ^ k) *ᵥ ket z)) w := rfl
      rw [h1, mulVec_mulVec, ← pow_succ']
    · intro b _hb hne
      have hb' : b.val ≠ k := fun h => hne (Fin.ext h)
      have hf : ¬ ((k + 1 : ℕ) = b.val + 1) := by omega
      have hb2 : ¬ (k = b.val) := fun h => hb' h.symm
      simp [hf, hb2, Nat.succ_ne_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- Lemma 3.4(i): on a YES instance, if `Γ_z > 2` and `Γ = Γ_z`, then `|Ω_z⟩ ≠ 0` and
`(I − C_{z,Γ})|Ω_z⟩ = 0`. -/
theorem lemma34_yes {m : ℕ} (A : ProofMat m) (ℓ : ℕ) (z : Idx m) (Γ : ℝ)
    (hΓ : Γ = Gamma A ℓ z) (hpos : 0 < Γ) :
    histVec A ℓ z ≠ 0 ∧ (1 - cyclicOp A ℓ z Γ) *ᵥ histVec A ℓ z = 0 := by
  refine ⟨histVec_ne_zero A ℓ z, ?_⟩
  exact fixedPoint_iff_kernel _ _ (cyclicOp_fixes_histVec A ℓ z Γ hΓ hpos.ne')

/-- Lemma 3.4(ii), the operator-theoretic core: a contractive `C` (with constant `2/3`)
separates every vector from its image by at least `1/3` of the norm. -/
theorem contraction_separates {α : Type} [Fintype α] (C : Matrix α α ℝ)
    (hC : ∀ ψ : α → ℝ, ‖C *ᵥ ψ‖ ≤ (2 / 3) * ‖ψ‖) :
    ∀ ψ : α → ℝ, (1 / 3) * ‖ψ‖ ≤ ‖ψ - C *ᵥ ψ‖ := by
  intro ψ
  have hsplit : ‖ψ - C *ᵥ ψ‖ ≥ ‖ψ‖ - ‖C *ᵥ ψ‖ := by
    simpa using norm_sub_norm_le ψ (C *ᵥ ψ)
  have := hC ψ
  linarith

end Qatlib.Papers.QMAPerfect26.MainResults
