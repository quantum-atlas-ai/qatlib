/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SoftDecoder24.MainResults.Basic
import Qatlib.Papers.SoftDecoder24.MainResults.Characters.SourceCharacters

set_option backward.isDefEq.respectTransparency false

/-!
# Selective Quantum Fourier Transform on Code-Periodic States

This module proves Proposition 3: applying the normalized Fourier transform `dft` over
`(ZMod q)^n` to the code-periodic amplitude `periodicAmp C F v` restricts its support
to the dual coset `-v + C^⊥` (`dualCoset C v`), scaling the Fourier amplitudes `dft F y`
on that coset by `|C|`.

## Main statements

* `source_proposition3`: `dft (periodicAmp C F v) y = |C| * dft F y` on `dualCoset C v` and `0` outside.
* `source_proposition3_support`: `dft (periodicAmp C F v)` vanishes outside `dualCoset C v`.

## References

* [Chailloux and Tillich, 2024][ChaillouxTillich2024], Proposition 3, Section 2.2, p. 11.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Classical
open Finset

namespace Qatlib.Papers.SoftDecoder24.MainResults.SelectiveQFT

open Qatlib.Papers.SoftDecoder24.MainResults.Basic

variable {q : ℕ} [NeZero q] {n : ℕ}

private lemma vchar_eq_stdAddChar_dot (y x : Fin n → ZMod q) :
    vchar y x = ZMod.stdAddChar (dot y x) := by
  unfold vchar char dot
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, AddChar.map_add_eq_mul, ih,
      mul_comm (x i)]

private lemma dot_comm (a b : Fin n → ZMod q) : dot a b = dot b a := by
  simp only [dot, mul_comm]

private lemma stdAddChar_eq_one_iff (t : ZMod q) :
    ZMod.stdAddChar t = 1 ↔ t = 0 := by
  rw [← (ZMod.stdAddChar (N := q)).map_zero_eq_one, ZMod.injective_stdAddChar.eq_iff]

private lemma sum_code_stdAddChar
    (C : Submodule (ZMod q) (Fin n → ZMod q)) (w : Fin n → ZMod q) :
    (∑ c ∈ codeSum C, ZMod.stdAddChar (dot w c)) =
      if w ∈ dual C then ((codeSum C).card : ℂ) else 0 := by
  let ψ : AddChar C ℂ :=
    { toFun := fun c => ZMod.stdAddChar (dot w c.val)
      map_zero_eq_one' := by simp [dot]
      map_add_eq_mul' := by
        intro a b
        change ZMod.stdAddChar (dot w (a.val + b.val)) =
          ZMod.stdAddChar (dot w a.val) * ZMod.stdAddChar (dot w b.val)
        rw [dot_comm w, dot_add, dot_comm a.val, dot_comm b.val,
          AddChar.map_add_eq_mul] }
  by_cases hw : w ∈ dual C
  · simp only [hw, ite_true]
    calc
      _ = ∑ _c ∈ codeSum C, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro c hc
        have hcC : c ∈ C := by simpa [codeSum] using hc
        rw [show dot w c = 0 from hw c hcC, AddChar.map_zero_eq_one]
      _ = _ := by simp
  · simp only [hw, ite_false]
    have hψ : ψ ≠ 1 := by
      intro hψ
      apply hw
      change ∀ c ∈ C, dot w c = 0
      intro c hc
      apply (stdAddChar_eq_one_iff _).mp
      have h := DFunLike.congr_fun hψ (⟨c, hc⟩ : C)
      simpa [ψ] using h
    have hsum : (∑ c ∈ codeSum C, ZMod.stdAddChar (dot w c)) = ∑ c : C, ψ c :=
      Finset.sum_subtype (codeSum C) (fun c => by simp [codeSum]) _
    rw [hsum]
    exact AddChar.sum_eq_zero_of_ne_one hψ

private lemma dft_periodicAmp_factor
    (C : Submodule (ZMod q) (Fin n → ZMod q)) (F : (Fin n → ZMod q) → ℂ)
    (v y : Fin n → ZMod q) :
    dft (periodicAmp C F v) y =
      (∑ c ∈ codeSum C, ZMod.stdAddChar (dot (y + v) c)) * dft F y := by
  have hshift (c : Fin n → ZMod q) :
      (∑ x, vchar y x * (F (x - c) * vchar c v)) =
        (∑ e, vchar y e * F e) * ZMod.stdAddChar (dot (y + v) c) := by
    calc
      _ = ∑ e, vchar y (e + c) * (F e * vchar c v) := by
        exact (Fintype.sum_equiv (Equiv.addRight c) _ _ (fun e => by simp)).symm
      _ = ∑ e, (vchar y e * F e) * ZMod.stdAddChar (dot (y + v) c) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [Characters.source_proposition2_hom, vchar_eq_stdAddChar_dot y c,
          vchar_eq_stdAddChar_dot c v, dot_comm c v, dot_add, AddChar.map_add_eq_mul]
        ring
      _ = _ := (Finset.sum_mul _ _ _).symm
  calc
    _ = (dftNorm q) ^ n *
        ∑ c ∈ codeSum C, ∑ x, vchar y x * (F (x - c) * vchar c v) := by
      unfold dft periodicAmp
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = (dftNorm q) ^ n *
        ∑ c ∈ codeSum C, (∑ e, vchar y e * F e) *
          ZMod.stdAddChar (dot (y + v) c) := by simp_rw [hshift]
    _ = _ := by
      rw [← Finset.mul_sum]
      unfold dft
      ring

/-- **Proposition 3** (selective QFT on a code-periodic state): the normalized Fourier
transform of `periodicAmp C F v` is supported on `dualCoset C v`, where it equals
`((codeSum C).card : ℂ) * dft F y`. -/
theorem source_proposition3
    (C : Submodule (ZMod q) (Fin n → ZMod q)) (F : (Fin n → ZMod q) → ℂ)
    (v : Fin n → ZMod q) :
    dft (periodicAmp C F v) = fun y =>
      ((codeSum C).card : ℂ) * (if y ∈ dualCoset C v then dft F y else 0) := by
  funext y
  rw [dft_periodicAmp_factor, sum_code_stdAddChar]
  by_cases hy : y + v ∈ dual C <;> simp [dualCoset, hy]

/-- Corollary of Proposition 3: the Fourier-transformed state vanishes outside `dualCoset C v`. -/
theorem source_proposition3_support
    (C : Submodule (ZMod q) (Fin n → ZMod q)) (F : (Fin n → ZMod q) → ℂ)
    (v y : Fin n → ZMod q) (hy : y ∉ dualCoset C v) :
    dft (periodicAmp C F v) y = 0 := by
  rw [source_proposition3 C F v]
  simp [hy]

end Qatlib.Papers.SoftDecoder24.MainResults.SelectiveQFT
