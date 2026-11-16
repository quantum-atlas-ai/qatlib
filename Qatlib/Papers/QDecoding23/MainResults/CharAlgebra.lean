/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QDecoding23.MainResults.Measurement
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

@[expose] public section


/-!
# QDecoding23 — character, Fourier and shift-operator claims

Source: Chailloux--Tillich, *The Quantum Decoding Problem*, fixed arXiv:2310.20651v1
(2023-10-31). Character and shift identities from Prop. 9 and Prop. 10.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QDecoding23.MainResults

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QDecoding23.MainResults
open Qatlib.Foundations.PureStateMath.Reflection

attribute [local instance] Classical.propDecidable

/-! ## §1. Proposition 9: the characters `χ_y` (p.17) -/

section CharacterAlgebra

variable {𝔽 : Type} [Field 𝔽] [Fintype 𝔽]
variable {ψ : AddChar 𝔽 ℂ}

/-- Prop. 9(1), p.17: `χ_y` is a group homomorphism `(F_q^n, +) → (ℂ, ·)`, i.e.
`χ_y(x + x') = χ_y(x)·χ_y(x')`. -/
theorem charFun_add {n : ℕ} (x x' y : FVec 𝔽 n) :
    charFun ψ (x + x') y = charFun ψ x y * charFun ψ x' y := by
  unfold charFun
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Prop. 9(2), p.17: symmetry `χ_y(x) = χ_x(y)`. -/
theorem charFun_comm {n : ℕ} (x y : FVec 𝔽 n) : charFun ψ x y = charFun ψ y x := by
  unfold charFun
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm (x i) (y i)

/-- Prop. 9(1), p.17, in subtraction form: `χ_x(y - b) = χ_x(y)·χ_x(-b)`. -/
theorem charFun_sub {n : ℕ} (x y b : FVec 𝔽 n) :
    charFun ψ x (y - b) = charFun ψ x y * charFun ψ x (-b) := by
  have hb : charFun ψ b x * charFun ψ (-b) x = 1 := by
    rw [← charFun_add, add_neg_cancel]
    simp [charFun]
  have h := charFun_add (ψ := ψ) (x := y - b) (x' := b) (y := x)
  rw [sub_add_cancel] at h
  rw [charFun_comm (ψ := ψ) x (y - b), charFun_comm (ψ := ψ) x y,
    charFun_comm (ψ := ψ) x (-b), h, mul_assoc, hb, mul_one]

/-- The conjugate of a character value is the value at the negative argument,
`conj(ψ a) = ψ(-a)`, because the target is `ℂ` and `ringChar 𝔽 > 0`. -/
theorem conj_char (a : 𝔽) : (starRingEnd ℂ) (ψ a) = ψ (-a) := by
  have hR : 0 < ringChar 𝔽 := (CharP.prime_ringChar (R := 𝔽)).pos
  rw [AddChar.starComp_apply (φ := ψ) hR a, AddChar.inv_apply]

/-- The linear functional `y ↦ ∑ᵢ zᵢ·yᵢ`, i.e. the pairing `⟨z, ·⟩`. -/
def dotLM {n : ℕ} (z : FVec 𝔽 n) : (FVec 𝔽 n) →ₗ[𝔽] 𝔽 where
  toFun y := ∑ i, z i * y i
  map_add' y y' := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a y := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [RingHom.id_apply]; ring

/-- The additive character `y ↦ ψ(⟨z,y⟩)` on `F_q^n`. -/
def gchar {n : ℕ} (z : FVec 𝔽 n) : AddChar (FVec 𝔽 n) ℂ :=
  ψ.compAddMonoidHom (dotLM (𝔽 := 𝔽) z).toAddMonoidHom

/-- `gchar` agrees with `charFun` on the first argument. -/
theorem gchar_apply {n : ℕ} (z y : FVec 𝔽 n) : gchar (ψ := ψ) z y = charFun ψ z y := rfl

omit [Fintype 𝔽] in
/-- The character `y ↦ ψ(⟨0,y⟩)` is trivial. -/
theorem gchar_zero {n : ℕ} : gchar (ψ := ψ) (0 : FVec 𝔽 n) = 0 := by
  ext y
  simp [gchar, dotLM]

/-- For `z ≠ 0` and primitive `ψ`, `y ↦ ψ(⟨z,y⟩)` is nontrivial. -/
theorem gchar_ne_zero {n : ℕ} (hψ : ψ.IsPrimitive) {z : FVec 𝔽 n} (hz : z ≠ 0) :
    gchar (ψ := ψ) z ≠ 0 := by
  classical
  rw [AddChar.ne_zero_iff]
  have hzj : ∃ j : Fin n, z j ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext fun j => h j)
  obtain ⟨j, hzj⟩ := hzj
  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.mp (hψ hzj)
  refine ⟨fun i => if i = j then t else 0, ?_⟩
  rw [gchar_apply, charFun]
  have hsum : (∑ i, z i * (if i = j then t else 0)) = z j * t := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; rw [ite_eq_right hij, mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [hsum]
  simpa [AddChar.mulShift_apply] using ht

/-- Prop. 9(3), p.17: character orthogonality
`∑_y χ_y(x) · conj(χ_y(x')) = q^n · δ_{x,x'}`.

The paper prints `∑_y χ_y(x)χ_y(x')`, but orthonormality of the characters requires the
complex conjugate on the second factor (as the paper's own `∑_y |χ_y(x)|² = q^n` clause
shows); we state the mathematically correct conjugated form. -/
theorem charFun_orthogonality {n : ℕ} (hψ : ψ.IsPrimitive) (x x' : FVec 𝔽 n) :
    (∑ z : FVec 𝔽 n, charFun ψ x z * (starRingEnd ℂ) (charFun ψ x' z))
      = (Fintype.card 𝔽 : ℂ) ^ n * (if x = x' then 1 else 0) := by
  classical
  have hterm : ∀ z, charFun ψ x z * (starRingEnd ℂ) (charFun ψ x' z)
      = charFun ψ (x - x') z := by
    intro z
    simp only [charFun]
    rw [conj_char (ψ := ψ) (∑ i, x' i * z i), ← AddChar.map_add_eq_mul, ← sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
  calc ∑ z, charFun ψ x z * (starRingEnd ℂ) (charFun ψ x' z)
      = ∑ z, gchar (ψ := ψ) (x - x') z := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [hterm z, gchar_apply]
    _ = (Fintype.card 𝔽 : ℂ) ^ n * (if x = x' then 1 else 0) := by
        rw [AddChar.sum_eq_ite]
        by_cases hz : x - x' = 0
        · have hgz : gchar (ψ := ψ) (x - x') = 0 := by rw [hz]; exact gchar_zero
          have hxx : x = x' := sub_eq_zero.mp hz
          rw [ite_eq_left hgz, ite_eq_left hxx, mul_one]
          simp [FVec, Nat.cast_pow]
        · have hgz : gchar (ψ := ψ) (x - x') ≠ 0 := gchar_ne_zero hψ hz
          have hxx : ¬ x = x' := fun h => hz (sub_eq_zero.mpr h)
          rw [ite_eq_right hgz, ite_eq_right hxx, mul_zero]

/-- Prop. 9, p.17, stated as one theorem (all three properties). -/
theorem prop9_characters {n : ℕ} (hψ : ψ.IsPrimitive) (x x' y : FVec 𝔽 n) :
    (charFun ψ (x + x') y = charFun ψ x y * charFun ψ x' y) ∧
    (charFun ψ x y = charFun ψ y x) ∧
    (∑ z : FVec 𝔽 n, charFun ψ x z * (starRingEnd ℂ) (charFun ψ x' z)
        = (Fintype.card 𝔽 : ℂ) ^ n * (if x = x' then 1 else 0)) :=
  ⟨charFun_add (ψ := ψ) x x' y, charFun_comm (ψ := ψ) x y,
    charFun_orthogonality (ψ := ψ) hψ x x'⟩

end CharacterAlgebra

/-! ## §2. Proposition 10: the Fourier basis and the shift/phase operators (p.19) -/

section FourierShift

variable {𝔽 : Type} [Field 𝔽] [Fintype 𝔽]
variable {ψ : AddChar 𝔽 ℂ}

/-- **Prop. 10, p.19** (eigenstate part): `|x̂⟩ = QFT|x⟩` is an eigenvector of the shift
`X_b` with eigenvalue `χ_x(-b)`.

Fixed version: arXiv:2310.20651v1 (2023-10-31), Prop. 10, p.19.
Proof key steps: `(QFT|x⟩)(y) = q^{-n/2}χ_x(y)`; hence `(X_b QFT|x⟩)(y) = q^{-n/2}χ_x(y-b)`,
and `χ_x(y-b) = χ_x(y)χ_x(-b)` by Prop. 9(1). -/
theorem prop10_eigenstate [DecidableEq 𝔽] {n : ℕ} (x b : FVec 𝔽 n) :
    shiftOp b (qft ψ (basisVec x)) = charFun ψ x (-b) • qft ψ (basisVec x) := by
  funext y
  simp only [shiftOp, qft, basisVec, Pi.smul_apply, smul_eq_mul]
  have hsum : ∀ z : FVec 𝔽 n,
      (∑ x' : FVec 𝔽 n, charFun ψ x' z * (if x' = x then (1 : ℂ) else 0))
        = charFun ψ x z := by
    intro z
    rw [Finset.sum_eq_single x]
    · simp
    · intro x' _ hx'; simp [hx']
    · intro h; exact absurd (Finset.mem_univ x) h
  rw [hsum (y - b), hsum y, charFun_sub]
  ring

/-- **Prop. 10, eq. (2), p.19**: `X_b · QFT = QFT · Z_{-b}`.

Fixed version: arXiv:2310.20651v1 (2023-10-31), eq. (2), p.19.
Proof key steps: expand `(X_b QFT g)(y) = q^{-n/2}∑_x χ_x(y-b)g(x)`, use `χ_x(y-b) =
χ_x(y)χ_x(-b)` and `(QFT Z_{-b} g)(y) = χ_y(-b)(QFT g)(y)`. -/
theorem prop10_shift_comp_qft {n : ℕ} (b : FVec 𝔽 n) (g : QState (FVec 𝔽 n)) :
    shiftOp b (qft ψ g) = qft ψ (phaseOp ψ (-b) g) := by
  funext y
  simp only [shiftOp, qft, phaseOp]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [charFun_sub]
  ring

/-- **Prop. 10, eq. (3), p.19**: `QFT · X_b = Z_b · QFT`.

Fixed version: arXiv:2310.20651v1 (2023-10-31), eq. (3), p.19.
Proof key steps: `(QFT (X_b g))(y) = q^{-n/2}∑_x χ_x(y)g(x-b)`; substitute `x = x' + b`
and use `χ_{x'+b}(y) = χ_{x'}(y)χ_b(y) = χ_{x'}(y)χ_y(b)`. -/
theorem prop10_qft_comp_shift {n : ℕ} (b : FVec 𝔽 n) (g : QState (FVec 𝔽 n)) :
    qft ψ (shiftOp b g) = phaseOp ψ b (qft ψ g) := by
  funext y
  simp only [qft, shiftOp, phaseOp]
  have hval : ∀ i : FVec 𝔽 n, (i + b) - b = i := fun i => add_sub_cancel_right i b
  have hS : (∑ i : FVec 𝔽 n, charFun ψ (i + b) y * g i)
      = ∑ x : FVec 𝔽 n, charFun ψ x y * g (x - b) := by
    simpa [hval] using Equiv.sum_comp (Equiv.addRight b)
      (fun x : FVec 𝔽 n => charFun ψ x y * g (x - b))
  rw [← hS]
  have hstep : (∑ a : FVec 𝔽 n, charFun ψ (a + b) y * g a)
      = charFun ψ y b * ∑ a : FVec 𝔽 n, charFun ψ a y * g a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [charFun_add, charFun_comm (ψ := ψ) b y]
    ring
  rw [hstep]
  ring

end FourierShift


end Qatlib.Papers.QDecoding23.MainResults
