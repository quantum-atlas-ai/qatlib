/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Symmetrization of fine-grained unambiguous measurements for
Buzet--Chailloux, "Fine-Grained Unambiguous Measurements",
arXiv:2510.07298v2 (2025), §3.1.

This file formalizes the symmetrization machinery behind Proposition 7:

* the outcome translation `(H, y) ↦ (H, y + H a)` as a bijection
  (`Idx.translateEquiv`);
* the adjoint identity for the Euclidean inner product
  (`innerVec_mulVec`);
* `rho2Of`, the measurement quality evaluated only on `|ψ₀⟩`
  (Proposition 7);
* **Lemma 1** (`lemma1_rho_eq_rho2`): on symmetrized measurements of a
  symmetric state set, `ρ = ρ₂`;
* **Lemma 2** (`symmetrize_psd`, `symmetrize_isPOVM`,
  `symmetrize_unambiguous`, `symmetrize_isSymmetrized`): the twirled
  family `F̄_{H,y} = 2^{−n} ∑_a X_a F_{H,y+Ha} X_a` is again a
  fine-grained unambiguous measurement and is symmetrized;
* `rho2_symmetrize` / `rhoOf_symmetrize`: symmetrization preserves the
  measurement quality (the content of Proposition 7; the paper's
  `max` over `Γs(S)` is restated through these witnesses since the
  existence of the maximum is not formalized here).
-/
import Qatlib.Papers.UnambigMeas25.MainResults.Preliminaries
import Mathlib.Data.Complex.BigOperators

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped BigOperators
open Matrix

namespace Qatlib.Papers.UnambigMeas25.MainResults

/-! ### Outcome translation -/

/-- Translation of parity values: `(H, y) ↦ (H, y + H a)`. -/
def Idx.translate {n : ℕ} (a : F2Vec n) (idx : Idx n) : Idx n :=
  ⟨idx.k, idx.H, fun r => idx.y r + ∑ s, idx.H r s * a s⟩

/-- Doubling vanishes in `F₂` (scalar version). -/
lemma zmod_add_self (z : ZMod 2) : z + z = 0 := by
  fin_cases z <;> rfl

/-- Translation is an involution on outcomes, hence a bijection. -/
def Idx.translateEquiv {n : ℕ} (a : F2Vec n) : Idx n ≃ Idx n where
  toFun := Idx.translate a
  invFun := Idx.translate a
  left_inv idx := by
    rcases idx with ⟨k, H, y⟩
    show (⟨k, H, fun r => (y r + ∑ s, H r s * a s) + ∑ s, H r s * a s⟩ : Idx n)
      = ⟨k, H, y⟩
    congr 1
    funext r
    rw [add_assoc, zmod_add_self, add_zero]
  right_inv idx := by
    rcases idx with ⟨k, H, y⟩
    show (⟨k, H, fun r => (y r + ∑ s, H r s * a s) + ∑ s, H r s * a s⟩ : Idx n)
      = ⟨k, H, y⟩
    congr 1
    funext r
    rw [add_assoc, zmod_add_self, add_zero]

/-- Translations compose by adding the shifts. -/
lemma Idx.translate_translate {n : ℕ} (a b : F2Vec n) (idx : Idx n) :
    Idx.translate a (Idx.translate b idx) = Idx.translate (a + b) idx := by
  rcases idx with ⟨k, H, y⟩
  show (⟨k, H, fun r => (y r + ∑ s, H r s * b s) + ∑ s, H r s * a s⟩ : Idx n)
      = ⟨k, H, fun r => y r + ∑ s, H r s * (a + b) s⟩
  congr 1
  funext r
  have hexp : ∑ s, H r s * (a + b) s
      = (∑ s, H r s * a s) + ∑ s, H r s * b s := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hexp, add_assoc (y r) (∑ s, H r s * b s) (∑ s, H r s * a s),
    add_comm (∑ s, H r s * b s) (∑ s, H r s * a s)]

/-- Correctness of a translated outcome: `H (x + a) = y + H a` iff
`H x = y`. -/
lemma holds_translate {n : ℕ} (idx : Idx n) (a x : F2Vec n) :
    (Idx.translate a idx).holds (x + a) ↔ idx.holds x := by
  constructor
  · intro h r
    have hr := h r
    simp only [Idx.translate, Pi.add_apply, mul_add, Finset.sum_add_distrib] at hr
    exact add_right_cancel hr
  · intro h r
    have hr := h r
    simp only [Idx.translate, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hr]

/-! ### Adjoint identity for the inner product -/

/-- Generic `star` on `ℂ` is complex conjugation. -/
lemma star_eq_conj (z : ℂ) : Star.star z = starRingEnd ℂ z := by
  rw [Complex.star_def]

/-- The adjoint identity: `⟨A u | v⟩ = ⟨u | Aᴴ v⟩`. -/
lemma innerVec_mulVec {n : ℕ} (A : Matrix (F2Vec n) (F2Vec n) ℂ)
    (u v : F2Vec n → ℂ) :
    innerVec (A *ᵥ u) v = innerVec u ((Aᴴ) *ᵥ v) := by
  simp only [innerVec, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    map_sum, map_mul, star_eq_conj]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_mul _ _ _), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The adjoint identity in the other direction: `⟨u | A v⟩ = ⟨Aᴴ u | v⟩`. -/
lemma innerVec_mulVec' {n : ℕ} (A : Matrix (F2Vec n) (F2Vec n) ℂ)
    (u v : F2Vec n → ℂ) :
    innerVec u (A *ᵥ v) = innerVec ((Aᴴ) *ᵥ u) v := by
  rw [innerVec_mulVec, Matrix.conjTranspose_conjTranspose]

/-- Conjugating a quadratic form by a shift moves the shift to the
vector arguments. -/
lemma inner_conj_shiftX {n : ℕ} (M : Matrix (F2Vec n) (F2Vec n) ℂ)
    (a : F2Vec n) (u : F2Vec n → ℂ) :
    innerVec u ((shiftX a * M * shiftX a) *ᵥ u)
      = innerVec (shiftX a *ᵥ u) (M *ᵥ (shiftX a *ᵥ u)) := by
  rw [← Matrix.mulVec_mulVec u (shiftX a * M) (shiftX a),
    ← Matrix.mulVec_mulVec (shiftX a *ᵥ u) (shiftX a) M, innerVec_mulVec',
    shiftX_conjTranspose]

/-! ### Sums against vectors -/

/-- Matrix sums act pointwise on vectors. -/
lemma sum_mulVec {n : ℕ} (Ms : F2Vec n → Matrix (F2Vec n) (F2Vec n) ℂ)
    (u : F2Vec n → ℂ) :
    (∑ a, Ms a) *ᵥ u = ∑ a, (Ms a *ᵥ u) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_mul _ _ _), Finset.sum_comm]

/-- Inner products split over matrix sums. -/
lemma innerVec_sum_mulVec {n : ℕ} (Ms : F2Vec n → Matrix (F2Vec n) (F2Vec n) ℂ)
    (u : F2Vec n → ℂ) :
    innerVec u ((∑ a, Ms a) *ᵥ u) = ∑ a, innerVec u (Ms a *ᵥ u) := by
  rw [sum_mulVec]
  simp only [innerVec, Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun i _ => Finset.mul_sum _ _ _), Finset.sum_comm]

/-- Inner products pull out scalars. -/
lemma innerVec_smul {n : ℕ} (c : ℂ) (u w : F2Vec n → ℂ) :
    innerVec u (c • w) = c * innerVec u w := by
  simp only [innerVec, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ => ?_), Finset.mul_sum]
  rw [← mul_assoc, mul_comm (starRingEnd ℂ (u i)) c, mul_assoc]

/-- Scalar multiples act uniformly on quadratic forms. -/
lemma innerVec_smul_mulVec {n : ℕ} (c : ℂ) (M : Matrix (F2Vec n) (F2Vec n) ℂ)
    (u : F2Vec n → ℂ) :
    innerVec u ((c • M) *ᵥ u) = c * innerVec u (M *ᵥ u) := by
  rw [Matrix.smul_mulVec, innerVec_smul]

/-- Conjugate transpose is additive. -/
lemma conjTranspose_sum {n : ℕ} (Ms : F2Vec n → Matrix (F2Vec n) (F2Vec n) ℂ) :
    (∑ a, Ms a)ᴴ = ∑ a, (Ms a)ᴴ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.sum_apply, star_eq_conj, map_sum]

/-- Real part of a product with a real scalar. -/
lemma re_mul_of_conj_eq {c z : ℂ} (hc : starRingEnd ℂ c = c) :
    (c * z).re = c.re * z.re := by
  have him : c.im = 0 := by
    have h := congrArg Complex.im hc
    simp only [Complex.conj_im] at h
    linarith
  rw [Complex.mul_re, him, zero_mul, sub_zero]

/-! ### `ρ₂` and Lemma 1 -/

/-- The quality evaluated only on `|ψ₀⟩` (Proposition 7). -/
noncomputable def rho2Of {n : ℕ} (C : Fin (n + 1) → ℝ)
    (F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ) (ψ : F2Vec n → F2Vec n → ℂ) : ℝ :=
  ∑ idx, C idx.k * (innerVec (ψ 0) (F idx *ᵥ ψ 0)).re

/-- The diagonal quadratic form of a symmetric set translates the
outcome label (Lemma 1, pointwise). -/
lemma inner_diag_translate {n : ℕ} {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ}
    {ψ : F2Vec n → F2Vec n → ℂ} (hsym : IsSymmetricSet ψ)
    (hsymm : IsSymmetrized F) (x : F2Vec n) (idx : Idx n) :
    innerVec (ψ x) (F idx *ᵥ ψ x)
      = innerVec (ψ 0) (F (Idx.translate x idx) *ᵥ ψ 0) := by
  have heq : shiftX x * F idx * shiftX x = F (Idx.translate x idx) :=
    Matrix.ext fun i j => hsymm idx x i j
  rw [hsym x, ← inner_conj_shiftX (F idx) x (ψ 0), heq]

/-- The average over `F₂ⁿ` of a constant. -/
lemma sum_univ_const_real {n : ℕ} (T : ℝ) :
    ∑ _x : F2Vec n, T = ((2 ^ n : ℕ) : ℝ) * T := by
  have hone : ∑ x : F2Vec n, (1 : ℝ) = ((2 ^ n : ℕ) : ℝ) := by simp
  calc ∑ x : F2Vec n, T = ∑ x : F2Vec n, (1 : ℝ) * T :=
        Finset.sum_congr rfl (fun x _ => (one_mul T).symm)
    _ = (∑ x : F2Vec n, (1 : ℝ)) * T := (Finset.sum_mul _ _ _).symm
    _ = ((2 ^ n : ℕ) : ℝ) * T := by rw [hone]

/-- **Lemma 1** (arXiv:2510.07298v2, §3.1.1): for a symmetrized
measurement on a symmetric state set, `ρ(S, {F}) = ρ₂(S, {F})`. -/
theorem lemma1_rho_eq_rho2 {n : ℕ} {C : Fin (n + 1) → ℝ}
    {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ}
    {ψ : F2Vec n → F2Vec n → ℂ} (hsym : IsSymmetricSet ψ)
    (hsymm : IsSymmetrized F) :
    rhoOf C F ψ = rho2Of C F ψ := by
  have hdiag : ∀ (x : F2Vec n) (idx : Idx n),
      C idx.k * (innerVec (ψ x) (F idx *ᵥ ψ x)).re
      = C idx.k * (innerVec (ψ 0) (F (Idx.translate x idx) *ᵥ ψ 0)).re :=
    fun x idx => by rw [inner_diag_translate hsym hsymm x idx]
  have hstep : ∀ x : F2Vec n,
      (∑ idx : Idx n, C idx.k * (innerVec (ψ x) (F idx *ᵥ ψ x)).re)
      = ∑ idx : Idx n, C idx.k * (innerVec (ψ 0) (F idx *ᵥ ψ 0)).re := by
    intro x
    rw [Finset.sum_congr rfl (fun idx _ => hdiag x idx)]
    exact Equiv.sum_comp (Idx.translateEquiv x)
      (fun idx => C idx.k * (innerVec (ψ 0) (F idx *ᵥ ψ 0)).re)
  have hcast : ((2 ^ n : ℕ) : ℝ) = ((2 : ℝ) ^ n) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
  show (2 ^ n : ℝ)⁻¹ * (∑ x : F2Vec n, ∑ idx : Idx n,
        C idx.k * (innerVec (ψ x) (F idx *ᵥ ψ x)).re)
    = ∑ idx : Idx n, C idx.k * (innerVec (ψ 0) (F idx *ᵥ ψ 0)).re
  rw [Finset.sum_congr rfl (fun x _ => hstep x), sum_univ_const_real, hcast,
    ← mul_assoc, inv_mul_cancel₀ (by positivity : ((2 : ℝ) ^ n) ≠ 0), one_mul]

/-! ### Lemma 2: the symmetrized family -/

/-- The twirled measurement of Lemma 2:
`F̄_{H,y} = 2^{−n} ∑_a X_a F_{H, y + Ha} X_a`. -/
noncomputable def symmetrize {n : ℕ} (F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ) :
    Idx n → Matrix (F2Vec n) (F2Vec n) ℂ :=
  fun idx => (((2 ^ n : ℕ) : ℂ)⁻¹) • ∑ a, shiftX a * F (Idx.translate a idx) * shiftX a

/-- The symmetrization prefactor is fixed by conjugation. -/
lemma conj_inv_two_pow (n : ℕ) :
    starRingEnd ℂ (((2 ^ n : ℕ) : ℂ)⁻¹) = ((2 ^ n : ℕ) : ℂ)⁻¹ := by
  rw [Complex.conj_inv, Complex.conj_natCast]

/-- Real part of the symmetrization prefactor. -/
lemma re_inv_two_pow (n : ℕ) :
    (((2 ^ n : ℕ) : ℂ)⁻¹).re = ((2 ^ n : ℕ) : ℝ)⁻¹ := by
  have hn : (((2 ^ n : ℕ) : ℝ) : ℂ) = ((2 ^ n : ℕ) : ℂ) := Complex.ofReal_natCast _
  rw [← hn, ← Complex.ofReal_inv, Complex.ofReal_re]

/-- **Lemma 2, positivity**: `F̄_{H,y}` is positive semidefinite. -/
theorem symmetrize_psd {n : ℕ} {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ}
    (hpsd : ∀ idx, IsPSD (F idx)) (idx : Idx n) :
    IsPSD (symmetrize F idx) := by
  have hsa : (∑ a, shiftX a * F (Idx.translate a idx) * shiftX a)ᴴ
      = ∑ a, shiftX a * F (Idx.translate a idx) * shiftX a := by
    rw [conjTranspose_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      shiftX_conjTranspose, ← (hpsd _).1, ← Matrix.mul_assoc]
  constructor
  · simp only [symmetrize]
    rw [Matrix.conjTranspose_smul, star_eq_conj, Complex.conj_inv,
      Complex.conj_natCast, hsa]
  · intro u
    have h1 : innerVec u (symmetrize F idx *ᵥ u)
        = (((2 ^ n : ℕ) : ℂ)⁻¹)
          * ∑ a, innerVec u ((shiftX a * F (Idx.translate a idx) * shiftX a) *ᵥ u) := by
      rw [symmetrize, innerVec_smul_mulVec, innerVec_sum_mulVec]
    rw [h1, re_mul_of_conj_eq (conj_inv_two_pow n), re_inv_two_pow, Complex.re_sum]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun a _ => ?_))
    rw [inner_conj_shiftX]
    exact (hpsd _).2 _

/-- The POVM elements of `F` sum to the identity, as a matrix identity. -/
lemma povm_sum {n : ℕ} {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ}
    (h : IsPOVMOverIdx F) : ∑ idx, F idx = 1 := by
  ext x y
  rw [Matrix.sum_apply, h.2 x y, Matrix.one_apply]

/-- **Lemma 2, normalization**: the twirled family still sums to the
identity. -/
theorem symmetrize_isPOVM {n : ℕ} {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ}
    (hpovm : IsPOVMOverIdx F) : IsPOVMOverIdx (symmetrize F) := by
  constructor
  · exact fun idx => symmetrize_psd hpovm.1 idx
  · intro x y
    have hma : ∀ a : F2Vec n,
        (∑ idx : Idx n, shiftX a * F (Idx.translate a idx) * shiftX a)
          = shiftX a * (∑ idx : Idx n, F (Idx.translate a idx)) * shiftX a := by
      intro a
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    have htr : ∀ a : F2Vec n,
        (∑ idx : Idx n, F (Idx.translate a idx)) = ∑ idx : Idx n, F idx :=
      fun a => Equiv.sum_comp (Idx.translateEquiv a) F
    have htot : (∑ idx : Idx n, symmetrize F idx)
        = (((2 ^ n : ℕ) : ℂ)⁻¹) • ∑ a : F2Vec n, (1 : Matrix (F2Vec n) (F2Vec n) ℂ) := by
      calc (∑ idx : Idx n, symmetrize F idx)
          = (((2 ^ n : ℕ) : ℂ)⁻¹) • ∑ idx : Idx n, ∑ a : F2Vec n,
              shiftX a * F (Idx.translate a idx) * shiftX a := by
            simp only [symmetrize]
            exact Finset.smul_sum.symm
        _ = (((2 ^ n : ℕ) : ℂ)⁻¹) • ∑ a : F2Vec n, ∑ idx : Idx n,
              shiftX a * F (Idx.translate a idx) * shiftX a := by
            rw [Finset.sum_comm]
        _ = (((2 ^ n : ℕ) : ℂ)⁻¹) • ∑ a : F2Vec n,
              (1 : Matrix (F2Vec n) (F2Vec n) ℂ) := by
            refine congrArg _ (Finset.sum_congr rfl (fun a _ => ?_))
            rw [hma a, htr a, povm_sum hpovm, mul_one, shiftX_mul_self]
    rw [← Matrix.sum_apply, htot, Matrix.smul_apply, Matrix.sum_apply]
    by_cases hij : x = y
    · subst hij
      have h1ii : ((1 : Matrix (F2Vec n) (F2Vec n) ℂ) x x) = 1 := by simp
      rw [h1ii]
      simp
    · have h0 : ((1 : Matrix (F2Vec n) (F2Vec n) ℂ) x y) = 0 := by
        rw [Matrix.one_apply, if_neg hij]
      rw [h0, if_neg hij]
      simp

/-- Shifts act on symmetric state families by relabeling. -/
lemma shiftX_apply_psi {n : ℕ} {ψ : F2Vec n → F2Vec n → ℂ}
    (hsym : IsSymmetricSet ψ) (a x : F2Vec n) :
    shiftX a *ᵥ ψ x = ψ (x + a) := by
  rw [add_comm x a, hsym (a + x), ← shiftX_mul_shiftX a x, ← Matrix.mulVec_mulVec,
    hsym x]

/-- **Lemma 2, unambiguity**: twirling preserves the unambiguity
condition on symmetric state sets. -/
theorem symmetrize_unambiguous {n : ℕ} {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ}
    {ψ : F2Vec n → F2Vec n → ℂ} (hsym : IsSymmetricSet ψ)
    (hunamb : IsUnambiguous F ψ) : IsUnambiguous (symmetrize F) ψ := by
  intro idx x hx
  have h1 : innerVec (ψ x) (symmetrize F idx *ᵥ ψ x)
      = (((2 ^ n : ℕ) : ℂ)⁻¹)
        * ∑ a, innerVec (ψ (x + a)) (F (Idx.translate a idx) *ᵥ ψ (x + a)) := by
    rw [symmetrize, innerVec_smul_mulVec, innerVec_sum_mulVec]
    refine congrArg ((((2 ^ n : ℕ) : ℂ)⁻¹) * ·) (Finset.sum_congr rfl (fun a _ => ?_))
    rw [inner_conj_shiftX, ← shiftX_apply_psi hsym a x]
  have hz : ∀ a : F2Vec n,
      innerVec (ψ (x + a)) (F (Idx.translate a idx) *ᵥ ψ (x + a)) = 0 :=
    fun a => hunamb _ _ (fun hh => hx ((holds_translate idx a x).mp hh))
  rw [h1, Finset.sum_eq_zero (fun a _ => hz a), mul_zero]

/-- Conjugating `X_q M X_q` by `X_p` shifts the labels by `p` on the
left and by `q + p` on the right. -/
lemma shiftX_mul_mid {n : ℕ} (p q : F2Vec n)
    (M : Matrix (F2Vec n) (F2Vec n) ℂ) :
    shiftX p * (shiftX q * M * shiftX q) * shiftX p
      = shiftX (p + q) * M * shiftX (q + p) := by
  rw [← Matrix.mul_assoc (shiftX p) (shiftX q * M) (shiftX q),
    ← Matrix.mul_assoc (shiftX p) (shiftX q) M, shiftX_mul_shiftX p q,
    Matrix.mul_assoc (shiftX (p + q) * M) (shiftX q) (shiftX p),
    shiftX_mul_shiftX q p]

/-- **Lemma 2, covariance**: the twirled family is symmetrized. -/
theorem symmetrize_isSymmetrized {n : ℕ} (F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ) :
    IsSymmetrized (symmetrize F) := by
  intro idx b i j
  have hab : ∀ a : F2Vec n, (a + b) + b = a := by
    intro a
    rw [add_assoc, addSelf_zero, add_zero]
  have hba : ∀ a : F2Vec n, b + (a + b) = a := by
    intro a
    rw [← add_assoc, add_comm b a, add_assoc, addSelf_zero, add_zero]
  have hmid : shiftX b * symmetrize F idx * shiftX b
      = (((2 ^ n : ℕ) : ℂ)⁻¹)
        • ∑ a, shiftX (b + a) * F (Idx.translate a idx) * shiftX (a + b) := by
    rw [symmetrize, mul_smul_comm, smul_mul_assoc, Finset.mul_sum,
      Finset.sum_mul]
    exact congrArg _ (Finset.sum_congr rfl (fun a _ => shiftX_mul_mid b a _))
  have hin : ∑ a, shiftX (b + a) * F (Idx.translate a idx) * shiftX (a + b)
      = ∑ a, shiftX a * F (Idx.translate a (Idx.translate b idx)) * shiftX a := by
    have hper : ∀ a : F2Vec n,
        shiftX (b + a) * F (Idx.translate a idx) * shiftX (a + b)
          = shiftX (a + b) * F (Idx.translate (a + b) (Idx.translate b idx))
              * shiftX (a + b) := by
      intro a
      have htra : Idx.translate a idx = Idx.translate ((a + b) + b) idx := by
        rw [hab a]
      rw [add_comm b a, htra, ← Idx.translate_translate (a + b) b idx]
    calc ∑ a, shiftX (b + a) * F (Idx.translate a idx) * shiftX (a + b)
        = ∑ a, shiftX (a + b) * F (Idx.translate (a + b) (Idx.translate b idx))
            * shiftX (a + b) :=
          Finset.sum_congr rfl (fun a _ => hper a)
      _ = ∑ a, shiftX a * F (Idx.translate a (Idx.translate b idx)) * shiftX a :=
          Equiv.sum_comp
            { toFun := fun a => a + b
              invFun := fun a => a + b
              left_inv := by
                intro a
                show (a + b) + b = a
                rw [hab a]
              right_inv := by
                intro a
                show (a + b) + b = a
                rw [hab a] }
            (fun a => shiftX a * F (Idx.translate a (Idx.translate b idx)) * shiftX a)
  show (shiftX b * symmetrize F idx * shiftX b) i j
      = symmetrize F (Idx.translate b idx) i j
  rw [hmid, hin, symmetrize]

/-- **Lemma 2** (arXiv:2510.07298v2, §3.1.1): for a fine-grained
unambiguous measurement on a symmetric state set, the twirled family
`{F̄}` is a fine-grained unambiguous measurement and is symmetrized. -/
theorem lemma2_symmetrize_mem {n : ℕ} {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ}
    {ψ : F2Vec n → F2Vec n → ℂ} (hF : IsFGUM F ψ) (hsym : IsSymmetricSet ψ) :
    IsFGUM (symmetrize F) ψ ∧ IsSymmetrized (symmetrize F) :=
  ⟨⟨symmetrize_isPOVM hF.1, symmetrize_unambiguous hsym hF.2⟩,
    symmetrize_isSymmetrized F⟩

/-! ### Quality preservation -/

/-- The `ρ₂`-value of the twirled family equals the `ρ`-value of the
original one (the computation behind Proposition 7). -/
theorem rho2_symmetrize {n : ℕ} {C : Fin (n + 1) → ℝ}
    {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ} {ψ : F2Vec n → F2Vec n → ℂ}
    (hsym : IsSymmetricSet ψ) :
    rho2Of C (symmetrize F) ψ = rhoOf C F ψ := by
  have h1 : ∀ idx : Idx n, innerVec (ψ 0) (symmetrize F idx *ᵥ ψ 0)
      = (((2 ^ n : ℕ) : ℂ)⁻¹)
        * ∑ a, innerVec (ψ a) (F (Idx.translate a idx) *ᵥ ψ a) := by
    intro idx
    rw [symmetrize, innerVec_smul_mulVec, innerVec_sum_mulVec]
    refine congrArg ((((2 ^ n : ℕ) : ℂ)⁻¹) * ·) (Finset.sum_congr rfl (fun a _ => ?_))
    have hψ : shiftX a *ᵥ ψ 0 = ψ a := by
      rw [shiftX_apply_psi hsym a 0, zero_add]
    rw [inner_conj_shiftX, hψ]
  have hre : ((2 ^ n : ℕ) : ℝ)⁻¹ = (2 ^ n : ℝ)⁻¹ := by
    have hcast : ((2 ^ n : ℕ) : ℝ) = ((2 : ℝ) ^ n) := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    rw [hcast]
  show (∑ idx : Idx n, C idx.k * (innerVec (ψ 0) (symmetrize F idx *ᵥ ψ 0)).re)
    = (2 ^ n : ℝ)⁻¹ * (∑ x : F2Vec n, ∑ idx : Idx n,
        C idx.k * (innerVec (ψ x) (F idx *ᵥ ψ x)).re)
  have hterm : ∀ idx : Idx n,
      C idx.k * (innerVec (ψ 0) (symmetrize F idx *ᵥ ψ 0)).re
      = C idx.k * (((2 ^ n : ℕ) : ℝ)⁻¹
        * ∑ a, (innerVec (ψ a) (F (Idx.translate a idx) *ᵥ ψ a)).re) := by
    intro idx
    rw [h1 idx, re_mul_of_conj_eq (conj_inv_two_pow n), re_inv_two_pow,
      Complex.re_sum]
  calc (∑ idx : Idx n, C idx.k * (innerVec (ψ 0) (symmetrize F idx *ᵥ ψ 0)).re)
      = ∑ idx : Idx n, C idx.k * (((2 ^ n : ℕ) : ℝ)⁻¹
          * ∑ a, (innerVec (ψ a) (F (Idx.translate a idx) *ᵥ ψ a)).re) :=
        Finset.sum_congr rfl (fun idx _ => hterm idx)
    _ = ((2 ^ n : ℕ) : ℝ)⁻¹ * ∑ idx : Idx n, ∑ a : F2Vec n,
          C idx.k * (innerVec (ψ a) (F (Idx.translate a idx) *ᵥ ψ a)).re := by
        have hpull : ∀ idx : Idx n,
            C idx.k * (((2 ^ n : ℕ) : ℝ)⁻¹
              * ∑ a, (innerVec (ψ a) (F (Idx.translate a idx) *ᵥ ψ a)).re)
            = ((2 ^ n : ℕ) : ℝ)⁻¹ * ∑ a : F2Vec n,
              C idx.k * (innerVec (ψ a) (F (Idx.translate a idx) *ᵥ ψ a)).re := by
          intro idx
          calc C idx.k * (((2 ^ n : ℕ) : ℝ)⁻¹
                * ∑ a, (innerVec (ψ a) (F (Idx.translate a idx) *ᵥ ψ a)).re)
              = ((2 ^ n : ℕ) : ℝ)⁻¹ * (C idx.k
                * ∑ a, (innerVec (ψ a) (F (Idx.translate a idx) *ᵥ ψ a)).re) := by ring
            _ = ((2 ^ n : ℕ) : ℝ)⁻¹ * ∑ a : F2Vec n,
                C idx.k * (innerVec (ψ a) (F (Idx.translate a idx) *ᵥ ψ a)).re := by
              rw [Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun idx _ => hpull idx)]
        exact (Finset.mul_sum Finset.univ
          (fun idx : Idx n => ∑ a : F2Vec n,
            C idx.k * (innerVec (ψ a) (F (Idx.translate a idx) *ᵥ ψ a)).re)
          (((2 ^ n : ℕ) : ℝ)⁻¹)).symm
    _ = ((2 ^ n : ℕ) : ℝ)⁻¹ * ∑ a : F2Vec n, ∑ idx : Idx n,
          C idx.k * (innerVec (ψ a) (F (Idx.translate a idx) *ᵥ ψ a)).re := by
        rw [Finset.sum_comm]
    _ = ((2 ^ n : ℕ) : ℝ)⁻¹ * ∑ a : F2Vec n, ∑ idx : Idx n,
          C idx.k * (innerVec (ψ a) (F idx *ᵥ ψ a)).re := by
        refine congrArg _ (Finset.sum_congr rfl (fun a _ => ?_))
        exact Equiv.sum_comp (Idx.translateEquiv a)
          (fun idx => C idx.k * (innerVec (ψ a) (F idx *ᵥ ψ a)).re)
    _ = (2 ^ n : ℝ)⁻¹ * (∑ x : F2Vec n, ∑ idx : Idx n,
          C idx.k * (innerVec (ψ x) (F idx *ᵥ ψ x)).re) := by
        rw [hre]

/-- Symmetrization preserves the measurement quality (Proposition 7,
witness form). -/
theorem rhoOf_symmetrize {n : ℕ} {C : Fin (n + 1) → ℝ}
    {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ} {ψ : F2Vec n → F2Vec n → ℂ}
    (hsym : IsSymmetricSet ψ) :
    rhoOf C (symmetrize F) ψ = rhoOf C F ψ := by
  rw [lemma1_rho_eq_rho2 hsym (symmetrize_isSymmetrized F), rho2_symmetrize hsym]

/-- **Proposition 7** (arXiv:2510.07298v2, §3.1.1), witness form: every
fine-grained unambiguous measurement on a symmetric state set is
`ρ`-matched by a symmetrized one, on which `ρ = ρ₂` (Lemma 1).  The
paper's `max` over `Γ_s(S)` is equivalent to these two facts together
with `Γ_s(S) ⊆ Γ(S)`; the existence of the maximum itself is not
formalized. -/
theorem prop7_symmetrized_witness {n : ℕ} {C : Fin (n + 1) → ℝ}
    {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ} {ψ : F2Vec n → F2Vec n → ℂ}
    (hF : IsFGUM F ψ) (hsym : IsSymmetricSet ψ) :
    IsFGUM (symmetrize F) ψ ∧ IsSymmetrized (symmetrize F)
      ∧ rhoOf C (symmetrize F) ψ = rhoOf C F ψ :=
  ⟨(lemma2_symmetrize_mem hF hsym).1, (lemma2_symmetrize_mem hF hsym).2,
    rhoOf_symmetrize hsym⟩

end Qatlib.Papers.UnambigMeas25.MainResults
