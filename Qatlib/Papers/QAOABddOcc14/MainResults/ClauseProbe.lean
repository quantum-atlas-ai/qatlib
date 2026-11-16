/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAOABddOcc14.MainResults.StateModel
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section


/-! # A concrete counterexample to the archived clause identity
The actual three-bit amplitudes and the archived functional are evaluated at
exact angles; no scalar expectation identity is supplied as a premise.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QAOABddOcc14.MainResults.ClauseProbe

open scoped BigOperators
open Qatlib.Papers.QAOABddOcc14.MainResults

/-- The sole ordered triple of three bits. -/
def tri : Triple 3 := ⟨(0, 1, 2), by decide⟩

/-- There is only one strictly increasing triple of indices in Fin3. -/
theorem triUnique (p : Triple 3) : p = tri := by
  rcases p with ⟨⟨a, b, c⟩, hab, hbc⟩
  change a < b at hab
  change b < c at hbc
  have ha : a = 0 := by
    apply Fin.ext
    change a.val = 0
    omega
  have hb : b = 1 := by
    apply Fin.ext
    change b.val = 1
    omega
  have hc : c = 2 := by
    apply Fin.ext
    change c.val = 2
    omega
  subst a
  subst b
  subst c
  rfl

instance : Unique (Triple 3) where
  default := tri
  uniq := triUnique

/-- Any inherited inhabitant instance chooses the same sole triple. -/
@[simp] theorem triDefault : (default : Triple 3) = tri := triUnique _

/-- A genuine instance with its sole clause positive. -/
def sole : E3Instance 3 where
  d _ := 1
  dval _ := Or.inr (Or.inr rfl)

/-- The explicit coordinate equivalence used to expand the finite state sums. -/
def cube3 : Basis 3 ≃ Bool × Bool × Bool where
  toFun z := (z 0, z 1, z 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv z := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨a, b, c⟩
    rfl

/-- A sum over the eight actual basis states is a triple Boolean sum. -/
theorem sum3 {α : Type*} [AddCommMonoid α] (f : Basis 3 → α) :
    (∑ z : Basis 3, f z) =
      ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, f ![a, b, c] := by
  calc
    (∑ z : Basis 3, f z) =
        ∑ p : Bool × Bool × Bool, f (cube3.symm p) := by
      apply Fintype.sum_equiv cube3
      intro z
      simp
    _ = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, f ![a, b, c] := by
      simp only [Fintype.sum_prod_type]
      rfl

/-- Every sum over the actual ordered triples of three bits has exactly one term. -/
theorem sumTri {α : Type*} [AddCommMonoid α] (f : Triple 3 → α) :
    (∑ p : Triple 3, f p) = f tri := by
  apply Finset.sum_eq_single tri
  · intro p _ hp
    exact (hp (triUnique p)).elim
  · simp

/-- The shared exact trigonometric value at pi/4. -/
def s : ℝ := Real.sqrt 2 / 2

/-- Its square is one half. -/
theorem sSq : s ^ 2 = (1 / 2 : ℝ) := by
  unfold s
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The corresponding fifth complex power simplifies without numerical approximation. -/
theorem sFifth : (s : ℂ) ^ 5 = (s : ℂ) / 4 := by
  have hs : (s : ℂ) ^ 2 = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_pow, sSq]
    norm_num
  calc
    (s : ℂ) ^ 5 = ((s : ℂ) ^ 2) ^ 2 * (s : ℂ) := by ring
    _ = (s : ℂ) / 4 := by rw [hs]; ring

/-- The actual register-size square root is reduced exactly. -/
theorem sqrtEight : Real.sqrt ((2 : ℝ) ^ 3) = 2 * Real.sqrt 2 := by
  rw [show (2 : ℝ) ^ 3 = 4 * 2 by norm_num,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have hfour : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hfour]

/-- The actual uniform-start amplitude for three bits is s/2. -/
theorem plusAt : plusAmp 3 = ((s / 2 : ℝ) : ℂ) := by
  unfold plusAmp
  apply congrArg (fun x : ℝ => (x : ℂ))
  rw [sqrtEight]
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  unfold s
  field_simp [hn]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Exact phase of the positive half-valued objective. -/
theorem phaseMinus :
    Complex.exp (-(Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (1 / 2 : ℂ)) =
      (s : ℂ) - Complex.I * (s : ℂ) := by
  have harg : -(Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (1 / 2 : ℂ) =
      -(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [harg]
  apply Complex.ext <;>
    simp [s, Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im,
      Real.cos_pi_div_four, Real.sin_pi_div_four]

/-- Exact phase of the negative half-valued objective. -/
theorem phasePlus :
    Complex.exp (-(Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (- (1 / 2 : ℂ))) =
      (s : ℂ) + Complex.I * (s : ℂ) := by
  have harg : -(Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (- (1 / 2 : ℂ)) =
      Complex.I * ((Real.pi / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg]
  apply Complex.ext <;>
    simp [s, Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im,
      Real.cos_pi_div_four, Real.sin_pi_div_four]

/-- The actual one-clause objective on a basis vector. -/
theorem objAt (a b c : Bool) :
    sole.objectiveValue ![a, b, c] =
      if Bool.xor a (Bool.xor b c) then (- (1 / 2 : ℝ)) else (1 / 2 : ℝ) := by
  unfold E3Instance.objectiveValue
  rw [sumTri]
  cases a <;> cases b <;> cases c <;>
    norm_num [sole, tri,
      Triple.first, Triple.second, Triple.third, bitSign]

/-- The actual phaseAmp is evaluated for every one of the eight input basis states. -/
theorem phaseAt (a b c : Bool) :
    phaseAmp sole (Real.pi / 2) ![a, b, c] =
      if Bool.xor a (Bool.xor b c)
      then (s : ℂ) + Complex.I * (s : ℂ)
      else (s : ℂ) - Complex.I * (s : ℂ) := by
  unfold phaseAmp
  rw [objAt]
  by_cases hp : Bool.xor a (Bool.xor b c) = true
  · simp only [ite_eq_left hp]
    convert phasePlus using 1; push_cast; ring
  · simp only [ite_eq_right hp]
    convert phaseMinus using 1; push_cast; ring

/-- The actual three-bit mixer is the product of its three displayed entries. -/
theorem mixAt (a b c x y z : Bool) :
    mixAmp (Real.pi / 4) ![a, b, c] ![x, y, z] =
      (if a = x then (s : ℂ) else -(Complex.I * (s : ℂ))) *
      (if b = y then (s : ℂ) else -(Complex.I * (s : ℂ))) *
      (if c = z then (s : ℂ) else -(Complex.I * (s : ℂ))) := by
  cases a <;> cases b <;> cases c <;> cases x <;> cases y <;> cases z <;>
    simp [mixAmp, Fin.prod_univ_succ, Real.cos_pi_div_four,
      Real.sin_pi_div_four, s, mul_assoc] <;> ring

/-- The fully evaluated actual QAOA amplitude vanishes on even parity and has the
displayed common amplitude on odd parity. No closed scalar expectation is assumed. -/
theorem ampAt (a b c : Bool) :
    qaoaAmp sole (Real.pi / 2) (Real.pi / 4) ![a, b, c] =
      if Bool.xor a (Bool.xor b c)
      then -(s : ℂ) / 2 * (1 + Complex.I) else 0 := by
  unfold qaoaAmp
  rw [sum3]
  simp_rw [mixAt, phaseAt, plusAt]
  simp only [Fintype.sum_bool]
  push_cast
  cases a <;> cases b <;> cases c <;>
    simp <;>
    ring_nf <;>
    norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four, sFifth] <;>
    ring

/-- Each nonzero actual amplitude has squared norm one quarter. -/
theorem oddNorm :
    Complex.normSq (-(s : ℂ) / 2 * (1 + Complex.I)) = (1 / 4 : ℝ) := by
  norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  nlinarith [sSq]

/-- The actual expectation at the test angles is negative one half. -/
theorem actualMean : qaoaExp sole (Real.pi / 2) (Real.pi / 4) = - (1 / 2 : ℝ) := by
  unfold qaoaExp
  rw [sum3]
  norm_num [Fintype.sum_bool, measWeight, ampAt, objAt, oddNorm]

/-- The actual archived clause functional is zero at the same test angle. -/
theorem actualForm : (∑ p : Triple 3, clauseExpr sole (Real.pi / 2) p) = 0 := by
  have hfour : (Real.pi / 2) * 4 = 2 * Real.pi := by ring
  rw [sumTri]
  unfold clauseExpr localCoeff
  simp only [sumTri]
  rw [sum3]
  norm_num [otherProd, Fintype.sum_bool, sole, tri, Triple.first, Triple.second, Triple.third,
    bitSign, hfour, Real.sin_two_pi]

/-- This refutes the full original state-to-clause identity in the actual migrated model. -/
theorem oldClauseFalse : ¬
    (∀ (n : ℕ) (I : E3Instance n) (γ : ℝ),
      qaoaExp I γ (Real.pi / 4) = ∑ p : Triple n, clauseExpr I γ p) := by
  intro h
  have hf := h 3 sole (Real.pi / 2)
  rw [actualMean, actualForm] at hf
  norm_num at hf

/-- The sole clause satisfies the literal D-plus-one occurrence promise even at D zero. -/
theorem soleBoundZero : sole.BoundedOccurrence 0 := by
  intro a
  calc
    (Finset.univ.filter (fun p : Triple 3 =>
      sole.d p ≠ 0 ∧ (a = p.first ∨ a = p.second ∨ a = p.third))).card ≤
        (Finset.univ : Finset (Triple 3)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ 0 + 1 := by simp

/-- The original Taylor contract is false at its admitted D-zero and k-zero boundary. -/
theorem oldTaylorFalse : ¬
    (∀ (n : ℕ) (I : E3Instance n) (D : ℕ), I.BoundedOccurrence D →
      ∀ k : ℕ, ∃ (P : Triple n → ℝ → ℝ) (c : Triple n → ℕ → ℝ),
        (∀ p j, c p j ≠ 0 → Odd j ∧ 3 ≤ j ∧ j ≤ k) ∧
        (∀ p γ, P p γ = ∑ j ∈ Finset.range (k + 1), c p j * γ ^ j) ∧
        (∀ p γ, I.d p ≠ 0 → |clauseExpr I γ p - γ / 2 - P p γ| ≤
          (9 * Real.sqrt (D : ℝ) * |γ|) ^ (k + 2))) := by
  intro h
  obtain ⟨P, c, hc, hP, hR⟩ := h 3 sole 0 soleBoundZero 0
  have hc0 : c tri 0 = 0 := by
    by_contra hn
    have hh := (hc tri 0 hn).2.1
    omega
  have hp0 : P tri (Real.pi / 2) = 0 := by
    simpa [hc0] using hP tri (Real.pi / 2)
  have hf0 : clauseExpr sole (Real.pi / 2) tri = 0 := by
    simpa only [sumTri] using actualForm
  have hr := hR tri (Real.pi / 2) (by norm_num [sole])
  rw [hf0, hp0] at hr
  norm_num [abs_div, abs_of_pos Real.pi_pos] at hr
  linarith [Real.pi_pos]

end Qatlib.Papers.QAOABddOcc14.MainResults.ClauseProbe
