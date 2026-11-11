/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnambigMeas25.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped BigOperators
open Matrix

namespace Qatlib.Papers.UnambigMeas25.MainResults

/-! ### Bilinearity and basic phase algebra -/

/-- The inner product is additive in the second argument. -/
lemma dotF2_add_right {n : ℕ} (v a b : F2Vec n) :
    dotF2 v (a + b) = dotF2 v a + dotF2 v b := by
  simp [dotF2, Finset.sum_add_distrib, mul_add]

/-- The inner product is additive in the first argument. -/
lemma dotF2_add_left {n : ℕ} (a b v : F2Vec n) :
    dotF2 (a + b) v = dotF2 a v + dotF2 b v := by
  simp [dotF2, Finset.sum_add_distrib, add_mul]

/-- The inner product is symmetric. -/
lemma dotF2_comm {n : ℕ} (a b : F2Vec n) : dotF2 a b = dotF2 b a := by
  simp [dotF2, mul_comm]

/-- The nonzero element of `F₂` is `1`. -/
lemma zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The phase function is multiplicative (F₂ addition is XOR). -/
lemma phase_mul (a b : ZMod 2) : phase (a + b) = phase a * phase b := by
  have h11 : (1 : ZMod 2) + (1 : ZMod 2) = 0 := by decide
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [phase, h11]

/-! ### Shift operators -/

/-- `X_0 = 1`. -/
theorem shiftX_zero {n : ℕ} : shiftX (0 : F2Vec n) = 1 := by
  ext x y
  simp [shiftX, Matrix.one_apply, add_zero]

/-- Shift operators compose by addition: `X_a X_b = X_{a+b}`. -/
theorem shiftX_mul_shiftX {n : ℕ} (a b : F2Vec n) :
    shiftX a * shiftX b = shiftX (a + b) := by
  ext x y
  rw [Matrix.mul_apply]
  simp only [shiftX]
  have hz : ∀ z : F2Vec n,
      (if x = z + a then (1 : ℂ) else 0) * (if z = y + b then (1 : ℂ) else 0)
      = if z = y + b then (if x = z + a then (1 : ℂ) else 0) else 0 := by
    intro z
    by_cases hzy : z = y + b <;> simp [hzy]
  rw [Finset.sum_congr rfl (fun z _ => hz z), Finset.sum_eq_single (y + b)]
  · have hyy : (y + b) + a = y + (a + b) := by rw [add_assoc, add_comm b a]
    rw [if_pos rfl, hyy]
  · intro z _ hzne
    rw [if_neg hzne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `X_a` is self-adjoint. -/
theorem shiftX_conjTranspose {n : ℕ} (a : F2Vec n) :
    (shiftX a)ᴴ = shiftX a := by
  ext x y
  rw [Matrix.conjTranspose_apply]
  simp only [shiftX]
  by_cases hy : y = x + a
  · have hx : x = y + a := by
      rw [hy, add_assoc, addSelf_zero, add_zero]
    rw [if_pos hy, if_pos hx]
    simp
  · have hx : ¬(x = y + a) := by
      intro h'
      apply hy
      rw [h', add_assoc, addSelf_zero, add_zero]
    rw [if_neg hy, if_neg hx]
    simp

/-- `X_a` is a unitary (an involution), since `X_a X_a = X_{a+a} = X_0`. -/
theorem shiftX_mul_self {n : ℕ} (a : F2Vec n) : shiftX a * shiftX a = 1 := by
  rw [shiftX_mul_shiftX, addSelf_zero, shiftX_zero]

/-! ### Proposition 5 (arXiv:2510.07298v2, §2.1): Weyl relations for the
Fourier transform. -/

/-- **Proposition 5, Eq. (5)**: `X_b H^{⊗n} = H^{⊗n} Z_b`. -/
theorem prop5_shift_qft {n : ℕ} (b : F2Vec n) :
    shiftX b * qftMat n = qftMat n * phaseZ b := by
  ext x y
  simp only [Matrix.mul_apply, shiftX, phaseZ, qftMat]
  have hl : ∀ z : F2Vec n,
      (if x = z + b then (1 : ℂ) else 0)
          * (((Real.sqrt 2)⁻¹ ^ n : ℝ) * phase (dotF2 z y))
      = if x = z + b then
          (((Real.sqrt 2)⁻¹ ^ n : ℝ) * phase (dotF2 z y)) else 0 := by
    intro z
    by_cases h : x = z + b <;> simp [h]
  rw [Finset.sum_congr rfl (fun z _ => hl z), Finset.sum_eq_single (x + b)]
  · have hxx : x = (x + b) + b := by
      rw [add_assoc, addSelf_zero, add_zero]
    rw [if_pos hxx]
    have hr : ∀ z : F2Vec n,
        (((Real.sqrt 2)⁻¹ ^ n : ℝ) * phase (dotF2 x z))
            * (if z = y then phase (dotF2 z b) else 0)
        = if z = y then
            (((Real.sqrt 2)⁻¹ ^ n : ℝ) * phase (dotF2 x z)) * phase (dotF2 z b)
          else 0 := by
      intro z
      by_cases h : z = y <;> simp [h]
    rw [Finset.sum_congr rfl (fun z _ => hr z), Finset.sum_eq_single y]
    · rw [if_pos rfl]
      have hd : dotF2 (x + b) y = dotF2 x y + dotF2 y b := by
        rw [dotF2_add_left, dotF2_comm b y]
      rw [hd, phase_mul]
      ring
    · intro z _ hzne
      rw [if_neg hzne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro z _ hzne
    have hxz : ¬(x = z + b) := by
      intro h
      apply hzne
      rw [h, add_assoc, addSelf_zero, add_zero]
    rw [if_neg hxz]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Proposition 5, Eq. (6)**: `H^{⊗n} X_b = Z_b H^{⊗n}`. -/
theorem prop5_qft_shift {n : ℕ} (b : F2Vec n) :
    qftMat n * shiftX b = phaseZ b * qftMat n := by
  ext x y
  simp only [Matrix.mul_apply, shiftX, phaseZ, qftMat]
  have hl : ∀ z : F2Vec n,
      (((Real.sqrt 2)⁻¹ ^ n : ℝ) * phase (dotF2 x z))
          * (if z = y + b then (1 : ℂ) else 0)
      = if z = y + b then
          (((Real.sqrt 2)⁻¹ ^ n : ℝ) * phase (dotF2 x z)) else 0 := by
    intro z
    by_cases h : z = y + b <;> simp [h]
  rw [Finset.sum_congr rfl (fun z _ => hl z), Finset.sum_eq_single (y + b)]
  · rw [if_pos rfl]
    have hr : ∀ z : F2Vec n,
        (if x = z then phase (dotF2 x b) else 0)
            * (((Real.sqrt 2)⁻¹ ^ n : ℝ) * phase (dotF2 z y))
        = if x = z then
            phase (dotF2 x b) * (((Real.sqrt 2)⁻¹ ^ n : ℝ) * phase (dotF2 z y))
          else 0 := by
      intro z
      by_cases h : x = z <;> simp [h]
    rw [Finset.sum_congr rfl (fun z _ => hr z), Finset.sum_eq_single x]
    · rw [if_pos rfl]
      have hd : dotF2 x (y + b) = dotF2 x y + dotF2 x b := dotF2_add_right x y b
      rw [hd, phase_mul]
      ring
    · intro z _ hzne
      rw [if_neg (fun h => hzne h.symm)]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro z _ hzne
    rw [if_neg hzne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### Proposition 6 (§2.2): character sums over binary linear codes. -/

/-- A binary linear code (§2.2): a subset of `F₂ⁿ` containing `0` and
closed under addition. -/
structure BinaryCode (n : ℕ) where
  /-- The set of codewords. -/
  carrier : Set (F2Vec n)
  /-- The zero word is a codeword. -/
  mem_zero : (0 : F2Vec n) ∈ carrier
  /-- Closed under addition. -/
  mem_add : ∀ ⦃a b : F2Vec n⦄, a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  /-- The code is finite (implicit). -/
  [fint : Fintype carrier]

/-- The carrier of a binary code has the finite type supplied by the code. -/
instance {n : ℕ} (C : BinaryCode n) : Fintype (C.carrier) := C.fint

/-- Membership coercion for codes. -/
lemma BinaryCode.mem_cast {n : ℕ} (C : BinaryCode n) (c : C.carrier) :
    (c : F2Vec n) ∈ C.carrier := c.2

/-- **Proposition 6, trivial-character case** (arXiv:2510.07298v2, §2.2):
if `v ∈ C^⊥` then `∑_{c ∈ C} (−1)^{v·c} = |C|`. -/
theorem prop6_char_sum_trivial {n : ℕ} (C : BinaryCode n) (v : F2Vec n)
    (hv : ∀ c ∈ C.carrier, dotF2 v c = 0) :
    ∑ c : C.carrier, phase (dotF2 v (c : F2Vec n)) = ((Fintype.card C.carrier : ℕ) : ℂ) := by
  rw [Finset.sum_congr rfl (fun c _ => by rw [hv _ c.2, phase_zero])]
  simp

/-- **Proposition 6, annihilated case** (arXiv:2510.07298v2, §2.2): if
some `c₀ ∈ C` pairs nontrivially with `v`, then
`∑_{c ∈ C} (−1)^{v·c} = 0`.  The proof pairs `c` with `c + c₀`. -/
theorem prop6_char_sum_zero {n : ℕ} (C : BinaryCode n) (v : F2Vec n)
    (c₀ : F2Vec n) (hc₀mem : c₀ ∈ C.carrier) (hc₀ne : dotF2 v c₀ ≠ 0) :
    ∑ c : C.carrier, phase (dotF2 v (c : F2Vec n)) = 0 := by
  have hc₀ph : phase (dotF2 v c₀) = -1 := by
    rcases zmod2_cases (dotF2 v c₀) with h | h
    · exact absurd h hc₀ne
    · rw [h, phase_one]
  -- the translation c ↦ c + c₀ is a self-equivalence of C
  have key : (∑ c : C.carrier, phase (dotF2 v (c : F2Vec n)))
      = -(∑ c : C.carrier, phase (dotF2 v (c : F2Vec n))) := by
    set e : C.carrier ≃ C.carrier :=
      { toFun := fun c => ⟨(c : F2Vec n) + c₀, C.mem_add c.2 hc₀mem⟩
        invFun := fun c => ⟨(c : F2Vec n) + c₀, C.mem_add c.2 hc₀mem⟩
        left_inv := by
          intro c
          apply Subtype.ext
          show ((c : F2Vec n) + c₀) + c₀ = (c : F2Vec n)
          rw [add_assoc, addSelf_zero, add_zero]
        right_inv := by
          intro c
          apply Subtype.ext
          show ((c : F2Vec n) + c₀) + c₀ = (c : F2Vec n)
          rw [add_assoc, addSelf_zero, add_zero] } with hedef
    calc (∑ c : C.carrier, phase (dotF2 v (c : F2Vec n)))
        = ∑ c : C.carrier, phase (dotF2 v ((c : F2Vec n) + c₀)) := by
          refine (Equiv.sum_comp e (fun c : C.carrier => phase (dotF2 v (c : F2Vec n)))).symm
      _ = ∑ c : C.carrier,
            phase (dotF2 v (c : F2Vec n)) * phase (dotF2 v c₀) := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [← phase_mul, dotF2_add_right]
      _ = (∑ c : C.carrier, phase (dotF2 v (c : F2Vec n)))
            * phase (dotF2 v c₀) :=
          (Finset.sum_mul _ _ _).symm
      _ = -(∑ c : C.carrier, phase (dotF2 v (c : F2Vec n))) := by
          rw [hc₀ph]
          ring
  have hss : (∑ c : C.carrier, phase (dotF2 v (c : F2Vec n)))
      + (∑ c : C.carrier, phase (dotF2 v (c : F2Vec n))) = 0 := by
    have h0 := congrArg (fun t => t + (∑ c : C.carrier, phase (dotF2 v (c : F2Vec n)))) key
    simp only [neg_add_cancel] at h0
    exact h0
  have h2S : (2 : ℂ) * (∑ c : C.carrier, phase (dotF2 v (c : F2Vec n))) = 0 := by
    rw [two_mul]
    exact hss
  exact ((mul_eq_zero.mp h2S).resolve_left two_ne_zero)

end Qatlib.Papers.UnambigMeas25.MainResults
