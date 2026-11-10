/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.StateConversionDefs
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.NumericalWord.MixedWordError.FixedGateSynthesis
import Mathlib.Data.Nat.Bitwise
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QlsReadoutSpec.Amplification


namespace Qatlib.Concepts.ConversionCore.WitnessCompile

open Qatlib
open Matrix
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib
open Qatlib
open Qatlib.Concepts.NumericalWord.MixedWordError
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

structure RationalRectInstance (R S : Type) (n : ℕ) where

  A : Matrix R S ℚ

  Z : Fin n → Matrix R S ℚ

def rectComplex {R S : Type} (A : Matrix R S ℚ) : Matrix R S ℂ := fun r s => (A r s : ℂ)

def rectComplexZ {R S : Type} {n : ℕ} (Z : Fin n → Matrix R S ℚ) : Fin n → Matrix R S ℂ :=
  fun j => rectComplex (Z j)

structure RationalRectFactorization {R S : Type} (n m : ℕ)
    (A : Matrix R S ℚ) (Z : Fin n → Matrix R S ℚ) where

  u : Fin n → R → Fin m → ℚ

  v : Fin n → S → Fin m → ℚ

  budget : ℚ

namespace RationalRectFactorization

variable {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable {n m : ℕ} {A : Matrix R S ℚ} {Z : Fin n → Matrix R S ℚ}

def massU (F : RationalRectFactorization n m A Z) (r : R) : ℝ :=
  ∑ j, ∑ q, ((F.u j r q * F.u j r q : ℚ) : ℝ)

def massV (F : RationalRectFactorization n m A Z) (s : S) : ℝ :=
  ∑ j, ∑ q, ((F.v j s q * F.v j s q : ℚ) : ℝ)

def residual (F : RationalRectFactorization n m A Z) (r : R) (s : S) : ℂ :=
  ((A r s : ℚ) : ℂ) - ∑ j, ((Z j r s : ℚ) : ℂ) *
    ∑ k, ((F.u j r k * F.v j s k : ℚ) : ℂ)

def certValid (F : RationalRectFactorization n m A Z) : Prop :=
  (∀ r, massU F r ≤ (F.budget : ℝ)) ∧ (∀ s, massV F s ≤ (F.budget : ℝ)) ∧
    (∀ r s, residual F r s = 0)

def certValidDecidable (F : RationalRectFactorization n m A Z) : Decidable (certValid F) := by
  unfold certValid
  infer_instance

def massQRational (F : RationalRectFactorization n m A Z) (r : R) : ℚ :=
  ∑ j, ∑ q, F.u j r q * F.u j r q

def massVRational (F : RationalRectFactorization n m A Z) (s : S) : ℚ :=
  ∑ j, ∑ q, F.v j s q * F.v j s q

def rationalResidual (F : RationalRectFactorization n m A Z) (r : R) (s : S) : ℚ :=
  A r s - ∑ j, Z j r s * ∑ q, F.u j r q * F.v j s q

def rationalCertValid (F : RationalRectFactorization n m A Z) : Prop :=
  (∀ r, massQRational F r ≤ F.budget) ∧ (∀ s, massVRational F s ≤ F.budget) ∧
    (∀ r s, rationalResidual F r s = 0)

instance rationalCertValidDecidable (F : RationalRectFactorization n m A Z) :
    Decidable (rationalCertValid F) := by
  unfold rationalCertValid
  infer_instance

end RationalRectFactorization

def diagonalRectInstance {X : Type} [Fintype X] [DecidableEq X] (a : X → ℚ) :
    RationalRectInstance X X 1 where
  A := Matrix.diagonal a
  Z := fun _ => 1

def diagonalScaleReal {X : Type} [Fintype X] [DecidableEq X] (a : X → ℚ) : ℝ :=
  ‖(fun r => (a r : ℂ))‖

def diagonalRectFactorization {X : Type} [Fintype X] [DecidableEq X]
    (a : X → ℚ) (t : ℚ) : RationalRectFactorization 1 1
      (diagonalRectInstance a).A (diagonalRectInstance a).Z where
  u := fun _ r _ => a r / t
  v := fun _ _ _ => t
  budget := t * t

def diagonalWitnessSlots {X : Type} [Fintype X] : ℕ :=
  2 * Fintype.card X + 1

theorem diagonalWitnessSlots_eq {X : Type} [Fintype X] :
    diagonalWitnessSlots (X := X) = 2 * Fintype.card X + 1 := rfl

def synthWordNativeProgram (p : SynthWord) : SourceNativeProgram where
  width := p.width
  steps := p.letters.map (fun g => SourceNativeStep.local g)

theorem isFixedPrimitive_iff_sourceFixedGate {w : ℕ} (g : LocalQFTGate w) :
    IsFixedPrimitive g ↔ sourceFixedGate g := by
  cases g <;> simp [IsFixedPrimitive, sourceFixedGate]

def nativeTagWire (d : SourceRationalProblem) : ℕ :=
  sourceAddressBits d + sourceValueBits d

def nativeFrameWidth (d : SourceRationalProblem) : ℕ :=
  sourceAddressBits d + sourceValueBits d + 1 + Nat.clog 2 (d.dimension + 1)

def nativeFlipWord (w a : ℕ) (ha : a < w) : List (LocalQFTGate w) :=
  [.h ⟨a, ha⟩, .cp ⟨a, ha⟩ ⟨a, ha⟩ 1 true, .h ⟨a, ha⟩]

def rationalToNativeProgram (d : SourceRationalProblem) (k : ℕ) : SourceNativeProgram where
  width := nativeFrameWidth d + k
  steps := (nativeFlipWord (nativeFrameWidth d + k) (nativeTagWire d) (by
      simp [nativeTagWire, nativeFrameWidth]
      omega)).map
    (fun g => SourceNativeStep.local g)

structure PartialPermutation (R S : Type) [Fintype R] [DecidableEq R] where

  col : R → S

  support : Finset R

namespace PartialPermutation

variable {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]

def matrix (P : PartialPermutation R S) : Matrix R S ℚ := fun r s =>
  if r ∈ P.support ∧ P.col r = s then 1 else 0

def complexMatrix (P : PartialPermutation R S) : Matrix R S ℂ := fun r s =>
  if r ∈ P.support ∧ P.col r = s then 1 else 0

def monomial (P : PartialPermutation R S) (amp : R → ℚ) : Matrix R S ℚ := fun r s =>
  if r ∈ P.support ∧ P.col r = s then amp r else 0

def complexMonomial (P : PartialPermutation R S) (amp : R → ℂ) : Matrix R S ℂ := fun r s =>
  if r ∈ P.support ∧ P.col r = s then amp r else 0

end PartialPermutation

def monomialRectInstance {R S : Type} [Fintype R] [DecidableEq R] [Fintype S]
    [DecidableEq S] (P : PartialPermutation R S) (amp : R → ℚ) :
    RationalRectInstance R S 1 where
  A := P.monomial amp
  Z := fun _ => P.matrix

def monomialRectFactorization {R S : Type} [Fintype R] [DecidableEq R] [Fintype S]
    [DecidableEq S] (P : PartialPermutation R S) (amp : R → ℚ) (t : ℚ) :
    RationalRectFactorization 1 1 (monomialRectInstance P amp).A
      (monomialRectInstance P amp).Z where
  u := fun _ r _ => if r ∈ P.support then amp r / t else 0
  v := fun _ _ _ => t
  budget := t * t

def monomialScaleReal {R S : Type} [Fintype R] [DecidableEq R] (P : PartialPermutation R S)
    (amp : R → ℚ) : ℝ := ‖(fun r => if r ∈ P.support then (amp r : ℂ) else 0)‖

theorem sourceCoordinateAfter_pair {d : SourceRealProblem} {x : Fin d.count}
    {h : Fin d.dimension} {target : Bool} {r t : ℕ}
    (hc : sourceCoordinateAfter d x h target r t) :
    ∃ a b : ℚ,
      ‖((a : ℂ) + (b : ℂ) * Complex.I) - (if target then d.target x h else d.start x h)‖
        ≤ (1 / 2 : ℝ) ^ r := by
  obtain ⟨cfg, a, b, h1, h2, h3, h4⟩ := hc
  exact ⟨a, b, h4⟩

def realCoordinateApprox (d : SourceRealProblem) (hacc : sourceRealAccess d)
    (x : Fin d.count) (h : Fin d.dimension) (target : Bool) (r : ℕ) : ℚ × ℚ :=
  let ht : sourceCoordinateAfter d x h target r (Classical.choose (hacc x h target r)) :=
    Classical.choose_spec (hacc x h target r)
  let hab : ∃ _ : ℚ, ∃ _ : ℚ, _ := sourceCoordinateAfter_pair ht
  (Classical.choose hab, Classical.choose (Classical.choose_spec hab))

def rationalizeReal (d : SourceRealProblem) (hacc : sourceRealAccess d) (R : ℕ) :
    SourceRationalProblem where
  count := d.count
  dimension := d.dimension
  addresses := d.addresses
  alphabet := d.alphabet
  input := d.input
  start := fun x h => realCoordinateApprox d hacc x h false R
  target := fun x h => realCoordinateApprox d hacc x h true R

def realToNativeProgram (d : SourceRealProblem) (hacc : sourceRealAccess d) (k : ℕ) :
    SourceNativeProgram :=
  rationalToNativeProgram (rationalizeReal d hacc k) k

def rationalGram (d : SourceRealProblem) (hacc : sourceRealAccess d) (R : ℕ) :
    Matrix (Fin d.count) (Fin d.count) ℚ :=
  fun x y => Finset.univ.sum (fun h : Fin d.dimension =>
    ((rationalizeReal d hacc R).start x h).1 * ((rationalizeReal d hacc R).start y h).1
      + ((rationalizeReal d hacc R).start x h).2 * ((rationalizeReal d hacc R).start y h).2)

def rationalGramInstance (d : SourceRealProblem) (hacc : sourceRealAccess d) (R : ℕ) :
    RationalRectInstance (Fin d.count) (Fin d.count) 1 where
  A := rationalGram d hacc R
  Z := fun _ => 1

theorem pow_dvd_pow (i m : ℕ) (h : i ≤ m) : 2 ^ i ∣ 2 ^ m := by
  obtain ⟨r, rfl⟩ : ∃ r, m = i + r := ⟨m - i, by omega⟩
  refine ⟨2 ^ r, ?_⟩
  rw [Nat.pow_add]

theorem pow_div_pow (i m : ℕ) (h : i ≤ m) : 2 ^ m / 2 ^ i = 2 ^ (m - i) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = i + r := ⟨m - i, by omega⟩
  have h1 : 2 ^ (i + r) / 2 ^ i = 2 ^ r := by
    rw [Nat.pow_add]
    exact Nat.mul_div_cancel_left (2 ^ r) (by positivity : 0 < 2 ^ i)
  rw [h1, Nat.add_sub_cancel_left]

theorem pow_two_mod_two (m : ℕ) (hm : 0 < m) : 2 ^ m % 2 = 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  rw [Nat.pow_add, Nat.mul_mod, Nat.mul_mod]
  simp

theorem testBit_mul_pow_two (n k j : ℕ) :
    (n * 2 ^ k).testBit j = if j < k then false else n.testBit (j - k) := by
  by_cases hjk : j < k
  · have hquot : n * 2 ^ k / 2 ^ j = n * 2 ^ (k - j) := by
      have hdiv : 2 ^ j ∣ 2 ^ k := pow_dvd_pow j k (by omega)
      rw [Nat.mul_div_assoc n hdiv, pow_div_pow j k (by omega)]
    have hshift : (n * 2 ^ k).testBit j = (n * 2 ^ k / 2 ^ j).testBit 0 := by
      calc (n * 2 ^ k).testBit j = (n * 2 ^ k).testBit (0 + j) := by rw [Nat.zero_add]
        _ = (n * 2 ^ k / 2 ^ j).testBit 0 := Nat.testBit_add (n * 2 ^ k) 0 j
    rw [hshift, hquot, if_pos hjk]
    rw [Nat.testBit_zero]
    show decide ((n * 2 ^ (k - j)) % 2 = 1) = false
    have hmod : n * 2 ^ (k - j) % 2 = 0 := by
      rw [Nat.mul_mod, Nat.mul_mod, pow_two_mod_two (k - j) (by omega)]
      simp
    rw [hmod]
    rfl
  · have hshift : (n * 2 ^ k).testBit j = (n * 2 ^ k / 2 ^ k).testBit (j - k) := by
      have h1 : (j - k) + k = j := Nat.sub_add_cancel (by omega)
      have h2 : (n * 2 ^ k).testBit j = (n * 2 ^ k).testBit ((j - k) + k) := by
        rw [h1]
      calc (n * 2 ^ k).testBit j = (n * 2 ^ k).testBit ((j - k) + k) := h2
        _ = (n * 2 ^ k / 2 ^ k).testBit (j - k) := Nat.testBit_add (n * 2 ^ k) (j - k) k
    have hquot : n * 2 ^ k / 2 ^ k = n := by
      rw [Nat.mul_comm, Nat.mul_div_cancel_left n (by positivity : 0 < 2 ^ k)]
    rw [hshift, hquot, if_neg hjk]

theorem testBit_two_mul_add_one (h j : ℕ) :
    (2 * h + 1).testBit j = if j = 0 then true else h.testBit (j - 1) := by
  by_cases hj : j = 0
  · subst hj
    rw [Nat.testBit_zero]
    show decide ((2 * h + 1) % 2 = 1) = true
    have hmod : (2 * h + 1) % 2 = 1 := by omega
    rw [hmod]
    rfl
  · have hshift : (2 * h + 1).testBit j = ((2 * h + 1) / 2).testBit (j - 1) := by
      have hj' : j = (j - 1) + 1 := by omega
      rw [hj']
      exact Nat.testBit_add (2 * h + 1) (j - 1) 1
    have hquot : (2 * h + 1) / 2 = h := by omega
    rw [hshift, hquot, if_neg hj]

def frameFalseN (a h : ℕ) : ℕ := h * 2 ^ (a + 1)

def frameTrueN (a h : ℕ) : ℕ := 2 ^ a + h * 2 ^ (a + 1)

theorem frameTrueN_eq (a h : ℕ) : frameTrueN a h = (1 + 2 * h) * 2 ^ a := by
  rw [frameTrueN, Nat.pow_succ]
  ring

theorem testBit_frameFalseN (a h : ℕ) : (frameFalseN a h).testBit a = false := by
  rw [frameFalseN, testBit_mul_pow_two h (a + 1) a]
  simp [not_lt.2 (by omega : ¬ a < a + 1)]

theorem testBit_frameTrueN (a h : ℕ) : (frameTrueN a h).testBit a = true := by
  rw [frameTrueN_eq, Nat.testBit_eq_decide_div_mod_eq]
  have hdiv : 2 ^ a * (1 + 2 * h) / 2 ^ a = 1 + 2 * h := by
    exact Nat.mul_div_cancel_left (1 + 2 * h) (by positivity : 0 < 2 ^ a)
  rw [Nat.mul_comm (1 + 2 * h) (2 ^ a), hdiv]
  show decide ((1 + 2 * h) % 2 = 1) = true
  have hmod : (1 + 2 * h) % 2 = 1 := by omega
  rw [hmod]
  rfl

theorem testBit_frame_off (a h i : ℕ) (hi : i ≠ a) :
    (frameTrueN a h).testBit i = (frameFalseN a h).testBit i := by
  by_cases hia : i < a
  · have hX : (frameFalseN a h).testBit i = false := by
      have hshift : (frameFalseN a h).testBit i
          = (frameFalseN a h / 2 ^ i).testBit 0 := by
        calc (frameFalseN a h).testBit i = (frameFalseN a h).testBit (0 + i) := by
              rw [Nat.zero_add]
          _ = (frameFalseN a h / 2 ^ i).testBit 0 := Nat.testBit_add (frameFalseN a h) 0 i
      have hquot : frameFalseN a h / 2 ^ i = h * 2 ^ (a + 1 - i) := by
        have hdiv : 2 ^ i ∣ 2 ^ (a + 1) := pow_dvd_pow i (a + 1) (by omega)
        rw [frameFalseN, Nat.mul_div_assoc h hdiv, pow_div_pow i (a + 1) (by omega)]
      rw [hshift, hquot, Nat.testBit_zero]
      show decide ((h * 2 ^ (a + 1 - i)) % 2 = 1) = false
      have hmod : h * 2 ^ (a + 1 - i) % 2 = 0 := by
        rw [Nat.mul_mod, Nat.mul_mod, pow_two_mod_two (a + 1 - i) (by omega)]
        simp
      rw [hmod]
      rfl
    have hY : (frameTrueN a h).testBit i = false := by
      have hshift : (frameTrueN a h).testBit i
          = (frameTrueN a h / 2 ^ i).testBit 0 := by
        calc (frameTrueN a h).testBit i = (frameTrueN a h).testBit (0 + i) := by
              rw [Nat.zero_add]
          _ = (frameTrueN a h / 2 ^ i).testBit 0 := Nat.testBit_add (frameTrueN a h) 0 i
      have hquot : frameTrueN a h / 2 ^ i = (1 + 2 * h) * 2 ^ (a - i) := by
        have hdiv : 2 ^ i ∣ 2 ^ a := pow_dvd_pow i a (by omega)
        rw [frameTrueN_eq, Nat.mul_div_assoc (1 + 2 * h) hdiv,
          pow_div_pow i a (by omega)]
      rw [hshift, hquot, Nat.testBit_zero]
      show decide (((1 + 2 * h) * 2 ^ (a - i)) % 2 = 1) = false
      have hmod : (1 + 2 * h) * 2 ^ (a - i) % 2 = 0 := by
        rw [Nat.mul_mod, Nat.mul_mod, pow_two_mod_two (a - i) (by omega)]
        simp
      rw [hmod]
      rfl
    rw [hX, hY]
  · have hX : (frameFalseN a h).testBit i = h.testBit (i - (a + 1)) := by
      have hshift : (frameFalseN a h).testBit i
          = (frameFalseN a h / 2 ^ (a + 1)).testBit (i - (a + 1)) := by
        have h1 : (i - (a + 1)) + (a + 1) = i := Nat.sub_add_cancel (by omega)
        have h2 : (frameFalseN a h).testBit i
            = (frameFalseN a h).testBit ((i - (a + 1)) + (a + 1)) := by
          rw [h1]
        calc (frameFalseN a h).testBit i
            = (frameFalseN a h).testBit ((i - (a + 1)) + (a + 1)) := h2
          _ = (frameFalseN a h / 2 ^ (a + 1)).testBit (i - (a + 1)) :=
            Nat.testBit_add (frameFalseN a h) (i - (a + 1)) (a + 1)
      have hquot : frameFalseN a h / 2 ^ (a + 1) = h := by
        rw [frameFalseN, Nat.mul_comm,
          Nat.mul_div_cancel_left h (by positivity : 0 < 2 ^ (a + 1))]
      rw [hshift, hquot]
    have hY : (frameTrueN a h).testBit i = h.testBit (i - (a + 1)) := by
      have hshift : (frameTrueN a h).testBit i
          = (frameTrueN a h / 2 ^ a).testBit (i - a) := by
        have h1 : (i - a) + a = i := Nat.sub_add_cancel (by omega)
        have h2 : (frameTrueN a h).testBit i = (frameTrueN a h).testBit ((i - a) + a) := by
          rw [h1]
        calc (frameTrueN a h).testBit i = (frameTrueN a h).testBit ((i - a) + a) := h2
          _ = (frameTrueN a h / 2 ^ a).testBit (i - a) := Nat.testBit_add (frameTrueN a h) (i - a) a
      have hquot : frameTrueN a h / 2 ^ a = 1 + 2 * h := by
        rw [frameTrueN_eq, Nat.mul_comm,
          Nat.mul_div_cancel_left (1 + 2 * h) (by positivity : 0 < 2 ^ a)]
      rw [hshift, hquot, show (1 + 2 * h) = 2 * h + 1 by omega,
        testBit_two_mul_add_one h (i - a)]
      have hEq : i - a - 1 = i - (a + 1) := by omega
      rw [if_neg (by omega : i - a ≠ 0), hEq]
    rw [hX, hY]

def flipBit {w : ℕ} (a : Fin w) (y : Reg w) : Reg w :=
  fun i => if i = a then !y i else y i

theorem flipBit_apply_self {w : ℕ} (a : Fin w) (y : Reg w) : flipBit a y a = !y a := by
  simp [flipBit]

theorem flipBit_apply_of_ne {w : ℕ} (a i : Fin w) (y : Reg w) (h : i ≠ a) :
    flipBit a y i = y i := by
  simp [flipBit, h]

theorem flipBit_involutive {w : ℕ} (a : Fin w) (y : Reg w) : flipBit a (flipBit a y) = y := by
  funext i
  by_cases hi : i = a
  · subst hi
    simp [flipBit]
  · simp [flipBit, hi]

theorem flipBit_ne_self {w : ℕ} (a : Fin w) (y : Reg w) : flipBit a y ≠ y := by
  intro h
  have h1 : y a = !y a := by
    have h2 : y a = flipBit a y a := congrFun h.symm a
    rw [flipBit_apply_self] at h2
    exact h2
  cases hy : y a <;> simp at h1

def agreeOff {w : ℕ} (a : Fin w) (p q : Reg w) : Prop :=
  ∀ i : Fin w, i ≠ a → p i = q i

theorem agreeOff_symm {w : ℕ} (a : Fin w) {p q : Reg w} (h : agreeOff a p q) :
    agreeOff a q p := by
  intro i hi
  exact (h i hi).symm

theorem agreeOff_trans {w : ℕ} (a : Fin w) {p q r : Reg w} (h₁ : agreeOff a p q)
    (h₂ : agreeOff a q r) : agreeOff a p r := by
  intro i hi
  exact (h₁ i hi).trans (h₂ i hi)

theorem eq_flipBit_of_agreeOff {w : ℕ} (a : Fin w) {q y : Reg w}
    (h : agreeOff a q y) (hbit : q a = !y a) : q = flipBit a y := by
  funext i
  by_cases hi : i = a
  · subst hi
    simp [flipBit, hbit]
  · have h1 := h i hi
    have h2 := flipBit_apply_of_ne a i y hi
    simp [flipBit, hi, h1]

theorem agreeOff_iff {w : ℕ} (a : Fin w) (q y : Reg w) :
    agreeOff a q y ↔ y = q ∨ y = flipBit a q := by
  constructor
  · intro h
    by_cases hy : y a = q a
    · left
      funext i
      by_cases hi : i = a
      · subst hi
        exact hy
      · exact (h i hi).symm
    · right
      apply eq_flipBit_of_agreeOff (a := a) (q := y) (y := q)
      · exact agreeOff_symm a h
      · have hbit : y a = !q a := by
          cases hyy : y a <;> cases hqq : q a <;> simp_all
        exact hbit
  · rintro (rfl | rfl)
    · intro i _
      rfl
    · intro i hi
      simp [flipBit, hi]

theorem sum_indicator_single {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : ι) (f : ι → ℂ) :
    (∑ r : ι, f r * (if r = P then 1 else 0)) = f P := by
  classical
  rw [Finset.sum_eq_single P]
  · simp
  · intro r _ hne
    simp [hne]
  · intro hP
    exact absurd (Finset.mem_univ P) hP

theorem fiber_sum {w : ℕ} (a : Fin w) (q : Reg w) (c : Bool → ℂ) :
    (∑ r : Reg w, if agreeOff a q r then c (r a) else 0) = c (q a) + c (! q a) := by
  classical
  have hset : (Finset.univ.filter (fun r : Reg w => agreeOff a q r) : Finset (Reg w))
      = {q, flipBit a q} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact agreeOff_iff a q r
  rw [← Finset.sum_filter (fun r : Reg w => agreeOff a q r) (fun r : Reg w => c (r a))]
  rw [hset]
  rw [Finset.sum_pair ((flipBit_ne_self a q).symm), flipBit_apply_self]

theorem fiber_sum2 {w : ℕ} (a : Fin w) (q y : Reg w) (c : Bool → ℂ) :
    (∑ r : Reg w, if agreeOff a q r ∧ agreeOff a r y then c (r a) else 0)
      = (if agreeOff a q y then c (q a) + c (! q a) else 0) := by
  classical
  by_cases hy : agreeOff a q y
  · have hkey : ∀ r : Reg w, (agreeOff a q r ∧ agreeOff a r y) ↔ agreeOff a q r := by
      intro r
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, fun i hi => (h i hi).symm.trans (hy i hi)⟩
    have hsum : (∑ r : Reg w, if agreeOff a q r ∧ agreeOff a r y then c (r a) else 0)
        = (∑ r : Reg w, if agreeOff a q r then c (r a) else 0) := by
      apply Finset.sum_congr rfl
      intro r _
      simp [hkey r]
    rw [hsum, fiber_sum]
    simp [hy]
  · have hnone : ∀ r : Reg w, ¬ (agreeOff a q r ∧ agreeOff a r y) := by
      intro r h
      exact hy (agreeOff_trans a h.1 h.2)
    have hsum : (∑ r : Reg w, if agreeOff a q r ∧ agreeOff a r y then c (r a) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      simp [hnone r]
    rw [hsum]
    simp [hy]

def tagWire (d : SourceRationalProblem) : ℕ :=
  sourceAddressBits d + sourceValueBits d

def framePos (d : SourceRationalProblem) (w : ℕ) (tag : Bool) (h : Fin d.dimension) : Reg w :=
  sourceRegBits w ((if tag then 1 else 0) * 2 ^ (tagWire d) + h.val * 2 ^ (tagWire d + 1))

theorem framePos_false (d : SourceRationalProblem) (w : ℕ) (h : Fin d.dimension) :
    framePos d w false h = sourceRegBits w (frameFalseN (tagWire d) h.val) := by
  simp [framePos, frameFalseN, tagWire]

theorem framePos_true (d : SourceRationalProblem) (w : ℕ) (h : Fin d.dimension) :
    framePos d w true h = sourceRegBits w (frameTrueN (tagWire d) h.val) := by
  simp [framePos, frameTrueN, tagWire]

theorem framePos_flip (d : SourceRationalProblem) (w : ℕ) (hw : tagWire d < w)
    (h : Fin d.dimension) :
    flipBit ⟨tagWire d, hw⟩ (framePos d w false h) = framePos d w true h := by
  funext i
  rw [framePos_false, framePos_true]
  by_cases hi : i = ⟨tagWire d, hw⟩
  · subst hi
    simp only [flipBit, sourceRegBits]
    rw [testBit_frameFalseN, testBit_frameTrueN]
    rfl
  · have hival : i.val ≠ tagWire d := by
      intro hh
      exact hi (Fin.ext hh)
    simp only [flipBit, sourceRegBits, if_neg hi]
    rw [testBit_frame_off (tagWire d) h.val i.val hival]

theorem sourceNativeClean_eq (d : SourceRationalProblem) (w : ℕ) (tag : Bool)
    (ψ : QState (Fin d.dimension)) (q : Reg w) :
    sourceNativeClean d w tag ψ q
      = ∑ h : Fin d.dimension, (if q = framePos d w tag h then 1 else 0) * ψ h := by
  unfold sourceNativeClean
  rw [Matrix.mulVec, dotProduct]
  have hframe : ∀ t : Bool × Fin d.dimension,
      sourceNativeFrame d w q t
        = (if q = framePos d w t.1 t.2 then 1 else 0) := by
    intro t
    show (if q = sourceRegBits w ((if t.1 then 1 else 0) * 2 ^ (sourceAddressBits d + sourceValueBits d)
        + t.2.val * 2 ^ (sourceAddressBits d + sourceValueBits d + 1)) then 1 else 0)
        = (if q = framePos d w t.1 t.2 then 1 else 0)
    rfl
  have key : (∑ t : Bool × Fin d.dimension,
        sourceNativeFrame d w q t * (if t.1 = tag then ψ t.2 else 0))
      = ∑ t : Bool × Fin d.dimension,
        (if q = framePos d w t.1 t.2 then 1 else 0) * (if t.1 = tag then ψ t.2 else 0) := by
    apply Finset.sum_congr rfl
    intro t _
    rw [hframe t]
  rw [key]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_bool]
  cases tag with
  | true =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    simp
  | false =>
    simp only [Bool.true_eq_false, ↓reduceIte]
    simp

theorem sourceRegBits_injective {w : ℕ} {v1 v2 : ℕ} (h1 : v1 < 2 ^ w) (h2 : v2 < 2 ^ w)
    (h : sourceRegBits w v1 = sourceRegBits w v2) : v1 = v2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < w
  · exact congrFun h ⟨i, hi⟩
  · rw [Nat.testBit_eq_false_of_lt (by
        have h2w : 2 ^ w ≤ 2 ^ i := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
        omega),
      Nat.testBit_eq_false_of_lt (by
        have h2w : 2 ^ w ≤ 2 ^ i := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
        omega)]

theorem frameFalseN_ne {a h1 h2 : ℕ} (h : h1 ≠ h2) : frameFalseN a h1 ≠ frameFalseN a h2 := by
  intro heq
  have h' : h1 * 2 ^ (a + 1) = h2 * 2 ^ (a + 1) := by simpa [frameFalseN] using! heq
  exact h (Nat.mul_right_cancel (by positivity) h')

theorem frameTrueN_ne {a h1 h2 : ℕ} (h : h1 ≠ h2) : frameTrueN a h1 ≠ frameTrueN a h2 := by
  intro heq
  rw [frameTrueN_eq, frameTrueN_eq] at heq
  have h' : (1 + 2 * h1) * 2 ^ a = (1 + 2 * h2) * 2 ^ a := heq
  have h'' : 1 + 2 * h1 = 1 + 2 * h2 := Nat.mul_right_cancel (by positivity) h'
  omega

theorem frameFalseN_ne_frameTrueN {a h1 h2 : ℕ} : frameFalseN a h1 ≠ frameTrueN a h2 := by
  intro heq
  rw [frameFalseN, frameTrueN_eq, Nat.pow_succ] at heq
  have h' : h1 * 2 * 2 ^ a = (1 + 2 * h2) * 2 ^ a := by
    calc h1 * 2 * 2 ^ a = h1 * (2 ^ a * 2) := by
          rw [Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]
      _ = (1 + 2 * h2) * 2 ^ a := heq
  have h'' : h1 * 2 = 1 + 2 * h2 := Nat.mul_right_cancel (by positivity) h'
  omega

def frameFaithful (d : SourceRationalProblem) (w : ℕ) : Prop :=
  tagWire d + 1 + Nat.clog 2 (d.dimension + 1) ≤ w

theorem frameFaithful_clog (d : SourceRationalProblem) :
    d.dimension + 1 ≤ 2 ^ Nat.clog 2 (d.dimension + 1) := by
  exact (Nat.clog_le_iff_le_pow (by norm_num : (1 : ℕ) < 2)).mp (le_refl _)

theorem frameFalseN_lt {d : SourceRationalProblem} {w : ℕ} (hw : frameFaithful d w)
    (h : Fin d.dimension) : frameFalseN (tagWire d) h.val < 2 ^ w := by
  have hc := frameFaithful_clog d
  have hlt : h.val < d.dimension := h.isLt
  have h2 : h.val * 2 ^ (tagWire d + 1) < (d.dimension + 1) * 2 ^ (tagWire d + 1) := by
    rw [Nat.mul_lt_mul_right (by simp : (0 : ℕ) < 2 ^ (tagWire d + 1))]
    omega
  have h3 : (d.dimension + 1) * 2 ^ (tagWire d + 1)
      ≤ 2 ^ Nat.clog 2 (d.dimension + 1) * 2 ^ (tagWire d + 1) :=
    Nat.mul_le_mul_right (2 ^ (tagWire d + 1)) hc
  have h4 : 2 ^ Nat.clog 2 (d.dimension + 1) * 2 ^ (tagWire d + 1)
      = 2 ^ (tagWire d + 1 + Nat.clog 2 (d.dimension + 1)) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have h5 : tagWire d + 1 + Nat.clog 2 (d.dimension + 1) ≤ w := hw
  calc frameFalseN (tagWire d) h.val = h.val * 2 ^ (tagWire d + 1) := rfl
    _ < (d.dimension + 1) * 2 ^ (tagWire d + 1) := h2
    _ ≤ 2 ^ Nat.clog 2 (d.dimension + 1) * 2 ^ (tagWire d + 1) := h3
    _ = 2 ^ (tagWire d + 1 + Nat.clog 2 (d.dimension + 1)) := h4
    _ ≤ 2 ^ w := Nat.pow_le_pow_right Nat.zero_lt_two h5

theorem frameTrueN_lt {d : SourceRationalProblem} {w : ℕ} (hw : frameFaithful d w)
    (h : Fin d.dimension) : frameTrueN (tagWire d) h.val < 2 ^ w := by
  have hc := frameFaithful_clog d
  have hlt : h.val < d.dimension := h.isLt
  have h2 : 1 + 2 * h.val < 2 * (d.dimension + 1) := by
    have hh : 2 * h.val < 2 * d.dimension := by
      have h2' : h.val * 2 < d.dimension * 2 :=
        Nat.mul_lt_mul_of_pos_right hlt (by norm_num : (0 : ℕ) < 2)
      omega
    omega
  have h3 : 2 * (d.dimension + 1) ≤ 2 * 2 ^ Nat.clog 2 (d.dimension + 1) := by
    have hh : (d.dimension + 1) * 2 ≤ 2 ^ Nat.clog 2 (d.dimension + 1) * 2 :=
      Nat.mul_le_mul_right 2 hc
    omega
  have h4 : 2 * 2 ^ Nat.clog 2 (d.dimension + 1)
      = 2 ^ (Nat.clog 2 (d.dimension + 1) + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have h5 : tagWire d + 1 + Nat.clog 2 (d.dimension + 1) ≤ w := hw
  calc frameTrueN (tagWire d) h.val = (1 + 2 * h.val) * 2 ^ tagWire d := frameTrueN_eq _ _
    _ < (2 * (d.dimension + 1)) * 2 ^ tagWire d := by
        rw [Nat.mul_lt_mul_right (by simp : (0 : ℕ) < 2 ^ tagWire d)]
        omega
    _ ≤ (2 * 2 ^ Nat.clog 2 (d.dimension + 1)) * 2 ^ tagWire d := by
        exact Nat.mul_le_mul_right (2 ^ tagWire d) h3
    _ = 2 ^ (Nat.clog 2 (d.dimension + 1) + 1) * 2 ^ tagWire d := by rw [h4]
    _ = 2 ^ (tagWire d + 1 + Nat.clog 2 (d.dimension + 1)) := by
        rw [← Nat.pow_add]
        congr 1
        omega
    _ ≤ 2 ^ w := Nat.pow_le_pow_right Nat.zero_lt_two h5

theorem frameFaithful_native (d : SourceRationalProblem) (k : ℕ) :
    frameFaithful d (nativeFrameWidth d + k) := by
  unfold frameFaithful nativeFrameWidth tagWire
  omega

theorem framePos_injective {d : SourceRationalProblem} {w : ℕ} {tag : Bool}
    {h1 h2 : Fin d.dimension} (hw : frameFaithful d w)
    (h : framePos d w tag h1 = framePos d w tag h2) : h1 = h2 := by
  cases tag with
  | false =>
      rw [framePos_false, framePos_false] at h
      have hv := sourceRegBits_injective (frameFalseN_lt hw h1) (frameFalseN_lt hw h2) h
      have hne := frameFalseN_ne (a := tagWire d) (h1 := h1.val) (h2 := h2.val)
      have hval : h1.val = h2.val := by
        by_contra hc
        exact hne hc (by simpa [frameFalseN] using! hv)
      exact Fin.ext hval
  | true =>
      rw [framePos_true, framePos_true] at h
      have hv := sourceRegBits_injective (frameTrueN_lt hw h1) (frameTrueN_lt hw h2) h
      have hne := frameTrueN_ne (a := tagWire d) (h1 := h1.val) (h2 := h2.val)
      have hval : h1.val = h2.val := by
        by_contra hc
        exact hne hc (by simpa [frameTrueN, frameTrueN_eq] using! hv)
      exact Fin.ext hval

theorem framePos_injective' {d : SourceRationalProblem} {w : ℕ} {tag : Bool}
    (hw : frameFaithful d w) : Function.Injective (framePos d w tag) := by
  intro h1 h2 h
  exact framePos_injective hw h

theorem framePos_tag_ne {d : SourceRationalProblem} {w : ℕ} {h1 h2 : Fin d.dimension}
    (hw : frameFaithful d w) : framePos d w false h1 ≠ framePos d w true h2 := by
  rw [framePos_false, framePos_true]
  intro heq
  have hv := sourceRegBits_injective (frameFalseN_lt hw h1) (frameTrueN_lt hw h2) heq
  exact frameFalseN_ne_frameTrueN (a := tagWire d) (by simpa [frameFalseN] using! hv)

theorem flipBit_iff {w : ℕ} (a : Fin w) (q y : Reg w) :
    q = flipBit a y ↔ (agreeOff a q y ∧ q a = !y a) := by
  constructor
  · intro h
    subst h
    refine ⟨fun i hi => flipBit_apply_of_ne a i y hi, flipBit_apply_self a y⟩
  · intro h
    exact eq_flipBit_of_agreeOff a h.1 h.2

theorem framePos_false_bit (d : SourceRationalProblem) (w : ℕ) (hw : tagWire d < w)
    (h : Fin d.dimension) :
    (framePos d w false h) ⟨tagWire d, hw⟩ = false := by
  rw [framePos_false, sourceRegBits]
  exact testBit_frameFalseN _ _

theorem framePos_true_agree_false (d : SourceRationalProblem) (w : ℕ) (hw : tagWire d < w)
    (h : Fin d.dimension) :
    agreeOff ⟨tagWire d, hw⟩ (framePos d w true h) (framePos d w false h) := by
  intro i hi
  have hflip : flipBit ⟨tagWire d, hw⟩ (framePos d w false h) = framePos d w true h :=
    framePos_flip d w hw h
  rw [← hflip]
  exact flipBit_apply_of_ne ⟨tagWire d, hw⟩ i (framePos d w false h) hi

theorem framePos_true_bit (d : SourceRationalProblem) (w : ℕ) (hw : tagWire d < w)
    (h : Fin d.dimension) :
    (framePos d w true h) ⟨tagWire d, hw⟩ = true := by
  rw [framePos_true, sourceRegBits]
  exact testBit_frameTrueN _ _

theorem eq_framePos_true_iff (d : SourceRationalProblem) (w : ℕ) (hw : tagWire d < w)
    (h : Fin d.dimension) (q : Reg w) :
    q = framePos d w true h ↔
      (agreeOff ⟨tagWire d, hw⟩ q (framePos d w false h) ∧ q ⟨tagWire d, hw⟩) := by
  rw [← framePos_flip d w hw h, flipBit_iff]
  have hPa : (framePos d w false h) ⟨tagWire d, hw⟩ = false :=
    framePos_false_bit d w hw h
  constructor
  · intro h
    exact ⟨h.1, by simpa [hPa] using! h.2⟩
  · intro h
    exact ⟨h.1, by simpa [hPa] using! h.2⟩

theorem hadamard_mulVec {w : ℕ} (a : Fin w) (u : Reg w → ℂ) (q : Reg w) :
    (localGateMatrix (.h a) *ᵥ u) q
      = ∑ r : Reg w, (if agreeOff a q r then Hadamard (q a) (r a) else 0) * u r := by
  classical
  rw [Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hc : ∀ k : Fin w, k ≠ a → q k = r k
  · simp [localGateMatrix_h, agreeOff]
  · simp [localGateMatrix_h, agreeOff]

theorem sum_ite_single {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι) (b : ι → ℂ) :
    (∑ r : ι, if r = P then b r else 0) = b P := by
  classical
  have h1 : (∑ r : ι, if r = P then b r else 0)
      = (∑ r ∈ (Finset.univ : Finset ι), if r = P then b r else 0) := rfl
  rw [h1, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]

theorem sum_swap3 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (f : γ → α → β → ℂ) :
    (∑ q : γ, ∑ x : α, ∑ y : β, f q x y) = ∑ x : α, ∑ y : β, ∑ q : γ, f q x y := by
  classical
  calc (∑ q : γ, ∑ x : α, ∑ y : β, f q x y)
      = ∑ x : α, ∑ q : γ, ∑ y : β, f q x y := by
          rw [Finset.sum_comm]
    _ = ∑ x : α, ∑ y : β, ∑ q : γ, f q x y := by
          apply Finset.sum_congr rfl
          intro x _
          exact Finset.sum_comm

theorem sum_frame_overlap {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {P : ι → κ} (hP : Function.Injective P) (ρ σ : ι → ℂ) :
    (∑ q : κ, (∑ h : ι, if q = P h then ρ h else 0) *
        (∑ h' : ι, if q = P h' then σ h' else 0))
      = ∑ h : ι, ρ h * σ h := by
  classical
  have key : ∀ h h' : ι,
      (∑ q : κ, (if q = P h then ρ h else 0) * (if q = P h' then σ h' else 0))
        = if h = h' then ρ h * σ h else 0 := by
    intro h h'
    by_cases heq : h = h'
    · subst heq
      have hq : ∀ q : κ, (if q = P h then ρ h else 0) * (if q = P h then σ h else 0)
          = if q = P h then ρ h * σ h else 0 := by
        intro q
        by_cases hcond : q = P h
        · simp only [if_pos hcond]
        · simp only [if_neg hcond, zero_mul]
      rw [Finset.sum_congr rfl (fun q _ => hq q)]
      rw [sum_ite_single]
      simp only [if_true]
    · have hz : ∀ q : κ, (if q = P h then ρ h else 0) * (if q = P h' then σ h' else 0) = 0 := by
        intro q
        by_cases h1 : q = P h
        · by_cases h2 : q = P h'
          · exfalso
            exact heq (hP (h1.symm.trans h2))
          · simp only [if_pos h1, if_neg h2, mul_zero]
        · simp only [if_neg h1, zero_mul]
      rw [Finset.sum_congr rfl (fun q _ => hz q)]
      rw [if_neg heq]
      simp only [Finset.sum_const_zero]
  calc (∑ q : κ, (∑ h : ι, if q = P h then ρ h else 0) *
        (∑ h' : ι, if q = P h' then σ h' else 0))
      = ∑ q : κ, ∑ h : ι, ∑ h' : ι,
          (if q = P h then ρ h else 0) * (if q = P h' then σ h' else 0) := by
          apply Finset.sum_congr rfl
          intro q _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro h _
          rw [Finset.mul_sum]
      _ = ∑ h : ι, ∑ h' : ι, ∑ q : κ,
          (if q = P h then ρ h else 0) * (if q = P h' then σ h' else 0) := sum_swap3 _
      _ = ∑ h : ι, ∑ h' : ι, (if h = h' then ρ h * σ h else 0) := by
          apply Finset.sum_congr rfl
          intro h _
          apply Finset.sum_congr rfl
          intro h' _
          rw [key]
      _ = ∑ h : ι, ρ h * σ h := by
          apply Finset.sum_congr rfl
          intro h _
          have heq : (∑ h' : ι, if h = h' then ρ h * σ h else 0)
              = ∑ h' : ι, if h' = h then ρ h * σ h else 0 := by
            apply Finset.sum_congr rfl
            intro h' _
            by_cases hc : h = h'
            · simp only [if_pos hc, if_pos hc.symm]
            · simp only [if_neg hc, if_neg (Ne.symm hc)]
          rw [heq, sum_ite_single]

theorem sum_frame_overlap_diff {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {P Q : ι → κ} (hPQ : ∀ h h', P h ≠ Q h') (ρ σ : ι → ℂ) :
    (∑ q : κ, (∑ h : ι, if q = P h then ρ h else 0) *
        (∑ h' : ι, if q = Q h' then σ h' else 0)) = 0 := by
  classical
  have key : ∀ h h' : ι,
      (∑ q : κ, (if q = P h then ρ h else 0) * (if q = Q h' then σ h' else 0)) = 0 := by
    intro h h'
    have hz : ∀ q : κ, (if q = P h then ρ h else 0) * (if q = Q h' then σ h' else 0) = 0 := by
      intro q
      by_cases h1 : q = P h
      · by_cases h2 : q = Q h'
        · exfalso
          exact hPQ h h' (h1.symm.trans h2)
        · simp only [if_pos h1, if_neg h2, mul_zero]
      · simp only [if_neg h1, zero_mul]
    rw [Finset.sum_congr rfl (fun q _ => hz q)]
    simp only [Finset.sum_const_zero]
  calc (∑ q : κ, (∑ h : ι, if q = P h then ρ h else 0) *
        (∑ h' : ι, if q = Q h' then σ h' else 0))
      = ∑ q : κ, ∑ h : ι, ∑ h' : ι,
          (if q = P h then ρ h else 0) * (if q = Q h' then σ h' else 0) := by
          apply Finset.sum_congr rfl
          intro q _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro h _
          rw [Finset.mul_sum]
      _ = ∑ h : ι, ∑ h' : ι, ∑ q : κ,
          (if q = P h then ρ h else 0) * (if q = Q h' then σ h' else 0) := sum_swap3 _
      _ = ∑ h : ι, ∑ h' : ι, (0 : ℂ) := by
          apply Finset.sum_congr rfl
          intro h _
          apply Finset.sum_congr rfl
          intro h' _
          rw [key]
      _ = 0 := by simp

theorem sourceNativeClean_eq' (d : SourceRationalProblem) (w : ℕ) (tag : Bool)
    (ψ : QState (Fin d.dimension)) (q : Reg w) :
    sourceNativeClean d w tag ψ q
      = ∑ h : Fin d.dimension, if q = framePos d w tag h then ψ h else 0 := by
  rw [sourceNativeClean_eq]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hc : q = framePos d w tag h
  · rw [if_pos hc, if_pos hc, one_mul]
  · rw [if_neg hc, if_neg hc, zero_mul]

theorem star_sum_frame {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {P : ι → κ} (f : ι → ℂ) (q : κ) :
    star (∑ h : ι, if q = P h then f h else 0)
      = ∑ h : ι, if q = P h then star (f h) else 0 := by
  have hstar : ∀ (g : ι → ℂ), star (∑ h : ι, g h) = ∑ h : ι, star (g h) := by
    intro g
    simp
  rw [hstar]
  refine Fintype.sum_congr _ _ (fun h => ?_)
  by_cases hc : q = P h
  · simp only [if_pos hc]
  · simp only [if_neg hc, star_zero]

theorem clean_overlap_same {d : SourceRationalProblem} {w : ℕ} (hw : frameFaithful d w)
    (ρ σ : QState (Fin d.dimension)) :
    (∑ q, star (sourceNativeClean d w true ρ q) * sourceNativeClean d w true σ q)
      = ∑ h, star (ρ h) * σ h := by
  classical
  calc (∑ q, star (sourceNativeClean d w true ρ q) * sourceNativeClean d w true σ q)
      = ∑ q, (∑ h : Fin d.dimension, if q = framePos d w true h then star (ρ h) else 0) *
              (∑ h' : Fin d.dimension, if q = framePos d w true h' then σ h' else 0) := by
          apply Finset.sum_congr rfl
          intro q _
          rw [sourceNativeClean_eq', sourceNativeClean_eq']
          rw [star_sum_frame]
      _ = ∑ h, star (ρ h) * σ h :=
          sum_frame_overlap (P := framePos d w true) (framePos_injective' (tag := true) hw)
            (fun h => star (ρ h)) σ

theorem clean_overlap_diff {d : SourceRationalProblem} {w : ℕ} (hw : frameFaithful d w)
    (ρ σ : QState (Fin d.dimension)) :
    (∑ q, star (sourceNativeClean d w false ρ q) * sourceNativeClean d w true σ q) = 0 := by
  classical
  calc (∑ q, star (sourceNativeClean d w false ρ q) * sourceNativeClean d w true σ q)
      = ∑ q, (∑ h : Fin d.dimension, if q = framePos d w false h then star (ρ h) else 0) *
              (∑ h' : Fin d.dimension, if q = framePos d w true h' then σ h' else 0) := by
          apply Finset.sum_congr rfl
          intro q _
          rw [sourceNativeClean_eq', sourceNativeClean_eq']
          rw [star_sum_frame]
      _ = 0 :=
          sum_frame_overlap_diff (P := framePos d w false) (Q := framePos d w true)
            (fun h h' => framePos_tag_ne hw) (fun h => star (ρ h)) σ

theorem exp_dyadicPhaseAngle_one_neg :
    Complex.exp (dyadicPhaseAngle 1 true * Complex.I) = -1 := by
  have h1 : dyadicPhaseAngle 1 true = -(Real.pi : ℝ) := by
    simp [dyadicPhaseAngle]
  rw [h1]
  rw [Complex.exp_mul_I]
  apply Complex.ext
  · rw [Complex.add_re, Complex.cos_ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.sin_ofReal_re, Complex.I_im, Complex.sin_ofReal_im]
    simp [Real.cos_neg, Real.cos_pi]
  · rw [Complex.add_im, Complex.cos_ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.sin_ofReal_re, Complex.I_re]
    simp [Real.sin_neg, Real.sin_pi]

theorem zgate_diag {w : ℕ} (a : Fin w) (q : Reg w) :
    localGateMatrix (.cp a a 1 true) q q = (if q a then -1 else 1) := by
  rw [localGateMatrix_cp, if_pos rfl, Bool.and_self]
  rw [exp_dyadicPhaseAngle_one_neg]

theorem zgate_offdiag {w : ℕ} (a : Fin w) (q r : Reg w) (hqr : q ≠ r) :
    localGateMatrix (.cp a a 1 true) q r = 0 := by
  simp only [localGateMatrix_cp, if_neg hqr]

theorem zgate_mulVec {w : ℕ} (a : Fin w) (u : Reg w → ℂ) (q : Reg w) :
    (localGateMatrix (.cp a a 1 true) *ᵥ u) q = (if q a then -1 else 1) * u q := by
  rw [Matrix.mulVec, dotProduct]
  have hkey : ∀ r : Reg w, localGateMatrix (.cp a a 1 true) q r * u r
      = (if r = q then (if q a then -1 else 1) * u q else 0) := by
    intro r
    by_cases hqr : r = q
    · rw [hqr, zgate_diag]
      by_cases hqa : q a
      · simp [hqa]
      · simp [hqa]
    · rw [zgate_offdiag a q r (Ne.symm hqr)]
      simp [hqr]
  have hreplace : (∑ r : Reg w, localGateMatrix (.cp a a 1 true) q r * u r)
      = (∑ r : Reg w, (if r = q then (if q a then -1 else 1) * u q else 0)) :=
    Finset.sum_congr rfl (fun r _ => hkey r)
  rw [hreplace]
  rw [sum_ite_single q (fun _ => (if q a then -1 else 1) * u q)]

theorem hadamard_entry (p q : Bool) :
    Hadamard p q = (Real.sqrt 2 : ℂ)⁻¹ * (if p && q then -1 else 1) := rfl

theorem hadamard_b_false (b : Bool) : Hadamard b false = (Real.sqrt 2 : ℂ)⁻¹ := by
  rw [hadamard_entry]
  cases b <;> simp

theorem inv_sqrt2_sq : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
  calc ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 := by ring
    _ = ((Real.sqrt 2 : ℂ) ^ 2)⁻¹ := by rw [inv_pow]
    _ = (2 : ℂ)⁻¹ := by rw [sqrt2_sq]

theorem c_value (qa b : Bool) :
    Hadamard qa b * ((if b then -1 else 1) * Hadamard b false)
      = (2 : ℂ)⁻¹ * ((if qa && b then -1 else 1) * (if b then -1 else 1)) := by
  rw [hadamard_entry, hadamard_b_false]
  calc (Real.sqrt 2 : ℂ)⁻¹ * (if qa && b then -1 else 1)
        * ((if b then -1 else 1) * (Real.sqrt 2 : ℂ)⁻¹)
      = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹)
        * ((if qa && b then -1 else 1) * (if b then -1 else 1)) := by ring
    _ = _ := by rw [inv_sqrt2_sq]

theorem zbracket {w : ℕ} (a : Fin w) (q : Reg w) :
    (Hadamard (q a) (q a) * ((if q a then -1 else 1) * Hadamard (q a) false)
      + Hadamard (q a) (!q a) * ((if !q a then -1 else 1) * Hadamard (!q a) false))
      = (if q a then 1 else 0) := by
  by_cases hqa : q a = true
  · rw [hqa]
    rw [c_value, c_value]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Bool.and_true, Bool.and_false]
    ring_nf
  · have hqa' : q a = false := by cases h : q a <;> simp_all
    rw [hqa']
    rw [c_value, c_value]
    simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte,
      Bool.and_true, Bool.and_false]
    ring_nf

theorem hadamard_clean (d : SourceRationalProblem) (w : ℕ) (hw : tagWire d < w)
    (ψ : QState (Fin d.dimension)) (q : Reg w) :
    (localGateMatrix (.h ⟨tagWire d, hw⟩) *ᵥ (sourceNativeClean d w false ψ)) q
      = ∑ h : Fin d.dimension,
          (if agreeOff ⟨tagWire d, hw⟩ q (framePos d w false h)
            then Hadamard (q ⟨tagWire d, hw⟩) false else 0) * ψ h := by
  classical
  rw [hadamard_mulVec]
  have key : ∀ r : Reg w, sourceNativeClean d w false ψ r
      = ∑ h : Fin d.dimension, (if r = framePos d w false h then 1 else 0) * ψ h :=
    fun r => sourceNativeClean_eq d w false ψ r
  have hreplace : (∑ r : Reg w,
        (if agreeOff ⟨tagWire d, hw⟩ q r
            then Hadamard (q ⟨tagWire d, hw⟩) (r ⟨tagWire d, hw⟩) else 0) *
          (sourceNativeClean d w false ψ) r)
      = (∑ r : Reg w,
        (if agreeOff ⟨tagWire d, hw⟩ q r
            then Hadamard (q ⟨tagWire d, hw⟩) (r ⟨tagWire d, hw⟩) else 0) *
          (∑ h : Fin d.dimension, (if r = framePos d w false h then 1 else 0) * ψ h)) :=
    Finset.sum_congr rfl (fun r _ => by rw [key r])
  rw [hreplace]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  have hinner : (∑ r : Reg w,
        (if agreeOff ⟨tagWire d, hw⟩ q r
            then Hadamard (q ⟨tagWire d, hw⟩) (r ⟨tagWire d, hw⟩) else 0) *
          ((if r = framePos d w false h then 1 else 0) * ψ h))
      = (if agreeOff ⟨tagWire d, hw⟩ q (framePos d w false h)
          then Hadamard (q ⟨tagWire d, hw⟩) false else 0) * ψ h := by
    calc (∑ r : Reg w,
          (if agreeOff ⟨tagWire d, hw⟩ q r
              then Hadamard (q ⟨tagWire d, hw⟩) (r ⟨tagWire d, hw⟩) else 0) *
            ((if r = framePos d w false h then 1 else 0) * ψ h))
        = ψ h * (∑ r : Reg w,
            (if agreeOff ⟨tagWire d, hw⟩ q r
                then Hadamard (q ⟨tagWire d, hw⟩) (r ⟨tagWire d, hw⟩) else 0) *
              (if r = framePos d w false h then 1 else 0)) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
        _ = ψ h * (if agreeOff ⟨tagWire d, hw⟩ q (framePos d w false h)
              then Hadamard (q ⟨tagWire d, hw⟩)
                (framePos d w false h ⟨tagWire d, hw⟩) else 0) := by
          rw [sum_indicator_single]
        _ = (if agreeOff ⟨tagWire d, hw⟩ q (framePos d w false h)
              then Hadamard (q ⟨tagWire d, hw⟩) false else 0) * ψ h := by
          have hbit : (framePos d w false h) ⟨tagWire d, hw⟩ = false :=
            framePos_false_bit d w hw h
          rw [hbit]
          ring
  rw [hinner]

theorem nativeTagFlip_frame (d : SourceRationalProblem) (w : ℕ) (hw : tagWire d < w)
    (ψ : QState (Fin d.dimension)) :
    (localGateMatrix (.h ⟨tagWire d, hw⟩) * localGateMatrix (.cp ⟨tagWire d, hw⟩ ⟨tagWire d, hw⟩ 1 true) *
      localGateMatrix (.h ⟨tagWire d, hw⟩)) *ᵥ (sourceNativeClean d w false ψ)
      = sourceNativeClean d w true ψ := by
  classical
  funext q
  have hmv : (localGateMatrix (.h ⟨tagWire d, hw⟩) *
        localGateMatrix (.cp ⟨tagWire d, hw⟩ ⟨tagWire d, hw⟩ 1 true) *
        localGateMatrix (.h ⟨tagWire d, hw⟩)) *ᵥ (sourceNativeClean d w false ψ)
      = localGateMatrix (.h ⟨tagWire d, hw⟩) *ᵥ
        (localGateMatrix (.cp ⟨tagWire d, hw⟩ ⟨tagWire d, hw⟩ 1 true) *ᵥ
          (localGateMatrix (.h ⟨tagWire d, hw⟩) *ᵥ (sourceNativeClean d w false ψ))) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hmv]
  rw [hadamard_mulVec]
  have hHz : ∀ (r : Reg w),
      (localGateMatrix (.cp ⟨tagWire d, hw⟩ ⟨tagWire d, hw⟩ 1 true) *ᵥ
        (localGateMatrix (.h ⟨tagWire d, hw⟩) *ᵥ (sourceNativeClean d w false ψ))) r
        = (if r ⟨tagWire d, hw⟩ then -1 else 1) *
          ∑ h : Fin d.dimension,
            (if agreeOff ⟨tagWire d, hw⟩ r (framePos d w false h)
              then Hadamard (r ⟨tagWire d, hw⟩) false else 0) * ψ h := by
    intro r
    rw [zgate_mulVec]
    rw [hadamard_clean d w hw ψ r]
  have hreplace : (∑ r : Reg w,
        (if agreeOff ⟨tagWire d, hw⟩ q r
            then Hadamard (q ⟨tagWire d, hw⟩) (r ⟨tagWire d, hw⟩) else 0) *
          (localGateMatrix (.cp ⟨tagWire d, hw⟩ ⟨tagWire d, hw⟩ 1 true) *ᵥ
            (localGateMatrix (.h ⟨tagWire d, hw⟩) *ᵥ (sourceNativeClean d w false ψ))) r)
      = (∑ r : Reg w,
        (if agreeOff ⟨tagWire d, hw⟩ q r
            then Hadamard (q ⟨tagWire d, hw⟩) (r ⟨tagWire d, hw⟩) else 0) *
          ((if r ⟨tagWire d, hw⟩ then -1 else 1) *
            ∑ h : Fin d.dimension,
              (if agreeOff ⟨tagWire d, hw⟩ r (framePos d w false h)
                then Hadamard (r ⟨tagWire d, hw⟩) false else 0) * ψ h)) :=
    Finset.sum_congr rfl (fun r _ => by rw [hHz r])
  rw [hreplace]
  have hinner : ∀ (P : Reg w),
      (∑ r : Reg w,
        (if agreeOff ⟨tagWire d, hw⟩ q r
            then Hadamard (q ⟨tagWire d, hw⟩) (r ⟨tagWire d, hw⟩) else 0) *
          ((if r ⟨tagWire d, hw⟩ then -1 else 1) *
            (if agreeOff ⟨tagWire d, hw⟩ r P
              then Hadamard (r ⟨tagWire d, hw⟩) false else 0)))
        = (if agreeOff ⟨tagWire d, hw⟩ q P
            then (Hadamard (q ⟨tagWire d, hw⟩) (q ⟨tagWire d, hw⟩) *
                ((if q ⟨tagWire d, hw⟩ then -1 else 1) *
                  Hadamard (q ⟨tagWire d, hw⟩) false)
              + Hadamard (q ⟨tagWire d, hw⟩) (!q ⟨tagWire d, hw⟩) *
                ((if !q ⟨tagWire d, hw⟩ then -1 else 1) *
                  Hadamard (!q ⟨tagWire d, hw⟩) false))
            else 0) := by
    intro P
    have hconv : ∀ r : Reg w,
        (if agreeOff ⟨tagWire d, hw⟩ q r
            then Hadamard (q ⟨tagWire d, hw⟩) (r ⟨tagWire d, hw⟩) else 0) *
          ((if r ⟨tagWire d, hw⟩ then -1 else 1) *
            (if agreeOff ⟨tagWire d, hw⟩ r P
              then Hadamard (r ⟨tagWire d, hw⟩) false else 0))
          = (if agreeOff ⟨tagWire d, hw⟩ q r ∧ agreeOff ⟨tagWire d, hw⟩ r P then
              (Hadamard (q ⟨tagWire d, hw⟩) (r ⟨tagWire d, hw⟩) *
                ((if r ⟨tagWire d, hw⟩ then -1 else 1) *
                  Hadamard (r ⟨tagWire d, hw⟩) false)) else 0) := by
      intro r
      by_cases h1 : agreeOff ⟨tagWire d, hw⟩ q r
      · by_cases h2 : agreeOff ⟨tagWire d, hw⟩ r P
        · simp only [h1, h2, and_self, ↓reduceIte]
        · simp only [h1, h2, and_false, ↓reduceIte, mul_zero]
      · simp only [h1, false_and, ↓reduceIte, zero_mul]
    have hreplace2 : (∑ r : Reg w,
          (if agreeOff ⟨tagWire d, hw⟩ q r
              then Hadamard (q ⟨tagWire d, hw⟩) (r ⟨tagWire d, hw⟩) else 0) *
            ((if r ⟨tagWire d, hw⟩ then -1 else 1) *
              (if agreeOff ⟨tagWire d, hw⟩ r P
                then Hadamard (r ⟨tagWire d, hw⟩) false else 0)))
        = (∑ r : Reg w,
          (if agreeOff ⟨tagWire d, hw⟩ q r ∧ agreeOff ⟨tagWire d, hw⟩ r P then
            (Hadamard (q ⟨tagWire d, hw⟩) (r ⟨tagWire d, hw⟩) *
              ((if r ⟨tagWire d, hw⟩ then -1 else 1) *
                Hadamard (r ⟨tagWire d, hw⟩) false)) else 0)) :=
      Finset.sum_congr rfl (fun r _ => hconv r)
    rw [hreplace2]
    have hfs := fiber_sum2 (a := ⟨tagWire d, hw⟩) (q := q) (y := P)
      (c := fun b => Hadamard (q ⟨tagWire d, hw⟩) b *
        ((if b then -1 else 1) * Hadamard b false))
    rw [hfs]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [sourceNativeClean_eq d w true ψ q]
  apply Finset.sum_congr rfl
  intro h _
  have hsplit : (∑ x : Reg w,
        (if agreeOff ⟨tagWire d, hw⟩ q x
            then Hadamard (q ⟨tagWire d, hw⟩) (x ⟨tagWire d, hw⟩) else 0) *
          ((if x ⟨tagWire d, hw⟩ then -1 else 1) *
            ((if agreeOff ⟨tagWire d, hw⟩ x (framePos d w false h)
              then Hadamard (x ⟨tagWire d, hw⟩) false else 0) * ψ h)))
        = ψ h * (∑ x : Reg w,
        (if agreeOff ⟨tagWire d, hw⟩ q x
            then Hadamard (q ⟨tagWire d, hw⟩) (x ⟨tagWire d, hw⟩) else 0) *
          ((if x ⟨tagWire d, hw⟩ then -1 else 1) *
            (if agreeOff ⟨tagWire d, hw⟩ x (framePos d w false h)
              then Hadamard (x ⟨tagWire d, hw⟩) false else 0))) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hsplit]
  rw [hinner (framePos d w false h)]
  rw [zbracket]
  by_cases h1 : agreeOff ⟨tagWire d, hw⟩ q (framePos d w false h)
  · by_cases h2 : q ⟨tagWire d, hw⟩
    · have hkey : q = framePos d w true h :=
        (eq_framePos_true_iff d w hw h q).mpr ⟨h1, h2⟩
      rw [hkey]
      simp [framePos_true_agree_false d w hw h, framePos_true_bit d w hw h]
    · have hkey : q ≠ framePos d w true h := by
        intro hcon
        exact h2 ((eq_framePos_true_iff d w hw h q).mp hcon).2
      simp [hkey, h1, h2]
  · have hkey : q ≠ framePos d w true h := by
      intro hcon
      exact h1 ((eq_framePos_true_iff d w hw h q).mp hcon).1
    simp [hkey, h1]

end Qatlib.Concepts.ConversionCore.WitnessCompile
