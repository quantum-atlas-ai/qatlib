/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Classical duals, Pauli actions, and coordinate projections

A binary linear code `C` has a classical dual `classicalDual C`, the set of words orthogonal to
every codeword under the binary pairing `bitDot`. The two component operators of the CSS model act
on an amplitude vector over `Fin n → ZMod 2` in a transparent way: the `X` operator translates
the register label and the `Z` operator multiplies by the character of the label. Those two
computations are the coordinate input for the projection statements of the correction block.

`projectOn E e` is the diagonal operator that keeps the computational basis states whose
coordinates on the support of `E` agree with `e`. It is the rank-one-per-coordinate projector used
in the projection lemma of the fixed source; it is not the CSS syndrome projector of
`Qatlib.Concepts.CodingDecoding.CssTesters.cssSyndromeProjector`.

## Main statements

* `cssPauliX_mulVec_apply`: `cssPauliX` acts on amplitudes by translation.
* `cssPauliZ_mulVec_apply`: `cssPauliZ` acts on amplitudes diagonally.
* `projectOn_mulVec_apply`: `projectOn` keeps exactly the patterns matching `e` on `E`.
* `classicalDual`: the classical dual code, with `mem_classicalDual` its characteristic property.

## References

* [Calderbank and Shor, 1996][CalderbankShor1996]
-/

namespace Qatlib.Papers.CssCodeCS96.Correction

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodingDecoding.CssTesters
open scoped Matrix
open scoped Classical

variable {n : ℕ}

/-- Over the binary field every element is zero or one. -/
theorem binary_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

/-- The classical dual of a binary linear code: the words orthogonal to every codeword. This is the
dual code of the fixed source, written as a submodule of `Fin n → ZMod 2` so that the projection
and counting statements can quantify over its words directly. -/
def classicalDual (C : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {w | ∀ v ∈ C, bitDot v w = 0}
  zero_mem' := by
    intro v _
    simp only [bitDot_zero_right]
  add_mem' := by
    intro a b ha hb v hv
    have h : bitDot v (a + b) = bitDot v a + bitDot v b := by
      simp only [bitDot, dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [h, ha v hv, hb v hv, add_zero]
  smul_mem' := by
    intro c a ha v hv
    have hmul : bitDot v (c • a) = c * bitDot v a := by
      simp only [bitDot, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hmul, ha v hv, mul_zero]

/-- A word lies in the classical dual exactly when it pairs to zero with every codeword. -/
@[simp] theorem mem_classicalDual {C : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {w : Fin n → ZMod 2} : w ∈ classicalDual C ↔ ∀ v ∈ C, bitDot v w = 0 := Iff.rfl

/-- The dual construction is antitone on submodules. -/
theorem classicalDual_anti {C D : Submodule (ZMod 2) (Fin n → ZMod 2)} (h : C ≤ D) :
    classicalDual D ≤ classicalDual C := by
  intro w hw v hv
  exact hw v (h hv)

/-- The `X` component operator translates the register label: an amplitude at `a` moves to the
amplitude at `a + x`. Only the binary right action of the translation is used, so the statement is
independent of the rank or structure of any code. -/
theorem cssPauliX_mulVec_apply (x : Fin n → ZMod 2) (ψ : (Fin n → ZMod 2) → ℂ)
    (a : Fin n → ZMod 2) : (cssPauliX x *ᵥ ψ) a = ψ (a + x) := by
  classical
  have hkey : ∀ j : Fin n → ZMod 2, a = j + x → j = a + x := by
    intro j hj
    have h : a + x = j + x + x := by rw [hj]
    rw [add_assoc, binary_add_self, add_zero] at h
    exact h.symm
  rw [Matrix.mulVec, dotProduct]
  refine (Finset.sum_eq_single (a + x) ?_ ?_).trans ?_
  · intro b _ hb
    simp only [cssPauliX, Matrix.of_apply]
    rw [ite_eq_right (fun h => hb (hkey b h)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (a + x)) h
  · simp only [cssPauliX, Matrix.of_apply]
    rw [ite_eq_left (by rw [add_assoc, binary_add_self, add_zero]), one_mul]

/-- The `Z` component operator acts diagonally, multiplying the amplitude at `a` by the character
of `a` against the label `z`. -/
theorem cssPauliZ_mulVec_apply (z : Fin n → ZMod 2) (ψ : (Fin n → ZMod 2) → ℂ)
    (a : Fin n → ZMod 2) : (cssPauliZ z *ᵥ ψ) a = phaseOfBit (bitDot z a) * ψ a := by
  classical
  rw [Matrix.mulVec, dotProduct, cssPauliZ]
  refine (Finset.sum_eq_single a ?_ ?_).trans ?_
  · intro b _ hb
    simp only [Matrix.diagonal_apply]
    rw [ite_eq_right (Ne.symm hb), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h
  · simp only [Matrix.diagonal_apply, ite_true]

/-- The coordinate projection onto the pattern `e` on the support of `E`. Its diagonal entry at the
basis state `a` is one exactly when `a` agrees with `e` wherever `E` is nonzero. -/
noncomputable def projectOn (E e : Fin n → ZMod 2) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ := by
  classical
  exact Matrix.diagonal fun a => if ∀ i, E i ≠ 0 → a i = e i then 1 else 0

/-- The projection keeps an amplitude exactly when the pattern agrees with `e` on the support of
`E`. -/
theorem projectOn_mulVec_apply (E e : Fin n → ZMod 2) (ψ : (Fin n → ZMod 2) → ℂ)
    (a : Fin n → ZMod 2) :
    (projectOn E e *ᵥ ψ) a = (if ∀ i, E i ≠ 0 → a i = e i then 1 else 0) * ψ a := by
  classical
  rw [Matrix.mulVec, dotProduct, projectOn]
  refine (Finset.sum_eq_single a ?_ ?_).trans ?_
  · intro b _ hb
    simp only [Matrix.diagonal_apply]
    rw [ite_eq_right (Ne.symm hb), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h
  · simp only [Matrix.diagonal_apply, ite_true]

/-- The projection with a zero support pattern is the identity operator. -/
theorem projectOn_zero (e : Fin n → ZMod 2) : projectOn (0 : Fin n → ZMod 2) e = 1 := by
  ext a b
  classical
  rw [projectOn, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp
  · rw [ite_eq_right h, ite_eq_right h]

/-- The number of words of a binary code, counted as a finite set of coordinate labels. -/
noncomputable def codeSize (C : Submodule (ZMod 2) (Fin n → ZMod 2)) : ℕ := by
  classical
  exact (Finset.univ.filter fun a => a ∈ C).card

/-- The normalizing scalar `(√|C|)⁻¹` of a character state of the code `C`. -/
noncomputable def charStateNorm (C : Submodule (ZMod 2) (Fin n → ZMod 2)) : ℂ :=
  ((Real.sqrt (codeSize C) : ℝ) : ℂ)⁻¹

/-- The character state of a binary code attached to the cocharacter `w`: the normalized
superposition `2^(-k/2) ∑ c ∈ C, (-1)^(c ⬝ w) |c⟩` of source Eq. (2). The normalization uses the
code size, which equals `2 ^ k` for a `k`-dimensional code. -/
noncomputable def charState (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (w : Fin n → ZMod 2) :
    (Fin n → ZMod 2) → ℂ := by
  classical
  exact fun a => if a ∈ C then charStateNorm C * phaseOfBit (bitDot a w) else 0

/-- A character state vanishes outside its code. -/
theorem charState_eq_zero_of_notMem {C : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {w : Fin n → ZMod 2} {a : Fin n → ZMod 2} (h : a ∉ C) : charState C w a = 0 := by
  classical
  simp only [charState]
  rw [ite_eq_right h]

/-- The bra-ket pairing of two amplitude vectors over the register. -/
noncomputable def ampInner (φ ψ : (Fin n → ZMod 2) → ℂ) : ℂ := ∑ a, star (φ a) * ψ a

/-- The binary code is nonempty, so its character-state normalization is available. -/
theorem codeSize_pos (C : Submodule (ZMod 2) (Fin n → ZMod 2)) : 0 < codeSize C := by
  classical
  refine Finset.card_pos.mpr ⟨0, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Submodule.zero_mem C

/-- The character-state normalization is a positive real number, so complex conjugation fixes
it. -/
theorem star_charStateNorm (C : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    star (charStateNorm C) = charStateNorm C := by
  have hs : star ((Real.sqrt (codeSize C) : ℝ) : ℂ) = ((Real.sqrt (codeSize C) : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [charStateNorm, star_inv₀, hs]

/-- Squaring the character-state normalization and multiplying by the code size gives one. -/
theorem star_charStateNorm_mul (C : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    star (charStateNorm C) * charStateNorm C * (codeSize C : ℂ) = 1 := by
  have hN : (codeSize C : ℂ) ≠ 0 := by
    have h1 : codeSize C ≠ 0 := Nat.ne_of_gt (codeSize_pos C)
    exact Nat.cast_ne_zero.mpr h1
  have hsq : ((Real.sqrt (codeSize C) : ℝ) : ℂ) * ((Real.sqrt (codeSize C) : ℝ) : ℂ)
      = (codeSize C : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    push_cast
    ring
  rw [star_charStateNorm C, charStateNorm, ← mul_inv, hsq, inv_mul_cancel₀ hN]

/-- The character sum of a binary code: the sum of the characters of its words is the code size
when the label lies in the classical dual and vanishes otherwise. -/
theorem sum_phaseOfBit_bitDot (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (z : Fin n → ZMod 2) :
    (∑ a ∈ Finset.univ.filter (fun a => a ∈ C), phaseOfBit (bitDot a z)) =
      if z ∈ classicalDual C then (codeSize C : ℂ) else 0 := by
  classical
  by_cases hz : z ∈ classicalDual C
  · rw [ite_eq_left hz]
    have hone : ∀ a ∈ Finset.univ.filter (fun a => a ∈ C), phaseOfBit (bitDot a z) = 1 := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rw [mem_classicalDual] at hz
      rw [hz a ha.2, phaseOfBit_zero]
    rw [Finset.sum_congr rfl hone, Finset.sum_const]
    simp [codeSize]
  · rw [ite_eq_right hz]
    have hex : ∃ a ∈ C, bitDot a z ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (by rw [mem_classicalDual]; exact h)
    obtain ⟨a₀, ha₀, hne⟩ := hex
    have ha₁ : bitDot a₀ z = 1 := (binary_eq_zero_or_one _).resolve_left hne
    have hbij : (∑ a ∈ Finset.univ.filter (fun a => a ∈ C),
          phaseOfBit (bitDot (a + a₀) z))
        = ∑ a ∈ Finset.univ.filter (fun a => a ∈ C), phaseOfBit (bitDot a z) := by
      refine Finset.sum_bij (fun a _ => a + a₀) ?_ ?_ ?_ ?_
      · intro a ha
        rw [Finset.mem_filter] at ha ⊢
        exact ⟨Finset.mem_univ _, C.add_mem ha.2 ha₀⟩
      · intro a₁ _ a₂ _ h
        exact add_right_cancel h
      · intro b hb
        rw [Finset.mem_filter] at hb
        refine ⟨b + a₀, ?_, ?_⟩
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, C.add_mem hb.2 ha₀⟩
        · show b + a₀ + a₀ = b
          rw [add_assoc, binary_add_self, add_zero]
      · intro a _
        rfl
    have hstep : ∀ a, phaseOfBit (bitDot (a + a₀) z) = - phaseOfBit (bitDot a z) := by
      intro a
      rw [bitDot_add_left, phaseOfBit_add, ha₁, phaseOfBit_one]
      ring
    rw [Finset.sum_congr rfl (fun a _ => hstep a), Finset.sum_neg_distrib] at hbij
    have hneg : -(∑ a ∈ Finset.univ.filter (fun a => a ∈ C), phaseOfBit (bitDot a z))
        = ∑ a ∈ Finset.univ.filter (fun a => a ∈ C), phaseOfBit (bitDot a z) := hbij
    have hzero : (2 : ℂ) * (∑ a ∈ Finset.univ.filter (fun a => a ∈ C),
        phaseOfBit (bitDot a z)) = 0 := by
      have hsum : (∑ a ∈ Finset.univ.filter (fun a => a ∈ C), phaseOfBit (bitDot a z))
          + (∑ a ∈ Finset.univ.filter (fun a => a ∈ C), phaseOfBit (bitDot a z)) = 0 := by
        nth_rewrite 2 [← hneg]
        exact add_neg_cancel _
      calc (2 : ℂ) * (∑ a ∈ Finset.univ.filter (fun a => a ∈ C), phaseOfBit (bitDot a z))
          = _ + _ := by ring
        _ = 0 := hsum
    exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)

/-- Character states of a binary code with labels summing into the classical dual coincide up to
sign, and character states with labels in distinct cosets of the dual are orthogonal. This is the
orthonormal character basis of source Eq. (2). -/
theorem charState_inner (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (w₁ w₂ : Fin n → ZMod 2) :
    ampInner (charState C w₁) (charState C w₂) =
      if w₁ + w₂ ∈ classicalDual C then 1 else 0 := by
  classical
  have hμ : star (charStateNorm C) = charStateNorm C := star_charStateNorm C
  have hterm : ∀ a, star (charState C w₁ a) * charState C w₂ a
      = (star (charStateNorm C) * charStateNorm C) *
        (if a ∈ C then phaseOfBit (bitDot a w₁) * phaseOfBit (bitDot a w₂) else 0) := by
    intro a
    by_cases ha : a ∈ C
    · simp only [charState, ite_eq_left ha, star_mul, hμ, phaseOfBit_star]
      ring
    · simp only [charState, ite_eq_right ha, star_zero, mul_zero]
  have hsum : ampInner (charState C w₁) (charState C w₂)
      = (star (charStateNorm C) * charStateNorm C) *
        ∑ a ∈ Finset.univ.filter (fun a => a ∈ C),
          phaseOfBit (bitDot a w₁) * phaseOfBit (bitDot a w₂) := by
    rw [ampInner, Finset.sum_congr rfl (fun a _ => hterm a), ← Finset.mul_sum,
      ← Finset.sum_filter]
  have hphase : (∑ a ∈ Finset.univ.filter (fun a => a ∈ C),
        phaseOfBit (bitDot a w₁) * phaseOfBit (bitDot a w₂))
      = ∑ a ∈ Finset.univ.filter (fun a => a ∈ C), phaseOfBit (bitDot a (w₁ + w₂)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← phaseOfBit_add, ← bitDot_add_right]
  rw [hsum, hphase, sum_phaseOfBit_bitDot]
  by_cases h : w₁ + w₂ ∈ classicalDual C
  · rw [ite_eq_left h, ite_eq_left h]
    exact star_charStateNorm_mul C
  · rw [ite_eq_right h, ite_eq_right h, mul_zero]

end Qatlib.Papers.CssCodeCS96.Correction
