/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AncilFreeClfT14.MainResults.LegacyGrid
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Logic.Encodable.Basic

@[expose] public section


/-! # Literal existential specifications with free cost fields
Classical truth-value selection, countable enumerations and pointwise constants
satisfy these archived contracts. No executable synthesis or cost claim follows.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.AncilFreeClfT14.MainResults.Legacy
open Qatlib.Papers.AncilFreeClfT14.MainResults

/-- Coefficient tuples give a countable carrier for the archived cyclotomic model. -/
theorem coeffInjective : Function.Injective (fun x : Zomega => (x.a, x.b, x.c, x.d)) := by
  intro x y h
  cases x
  cases y
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨ha, hb, hc, hd⟩
  subst ha
  subst hb
  subst hc
  subst hd
  rfl

local instance : Countable Zomega := coeffInjective.countable

/-- A predicate on a countable carrier admits a classical enumeration with assigned zero cost. -/
def freeEnum {α : Type} [Countable α] (P : α → Prop) : Enumeration P := by
  classical
  letI := Encodable.ofCountable {a : α // P a}
  refine ⟨fun n => (Encodable.decode n : Option {a : α // P a}).map Subtype.val,
    ?_, ?_, fun _ => 0⟩
  · intro n a h
    cases hd : (Encodable.decode n : Option {a : α // P a}) with
    | none => simp [hd] at h
    | some x =>
      have hx : x.val = a := by simpa [hd] using h
      exact hx ▸ x.property
  · intro a ha
    exact ⟨Encodable.encode (⟨a, ha⟩ : {a : α // P a}), by simp⟩

/-- The recorded cost is zero by assignment, independently of enumeration computation. -/
theorem freeEnumCost {α : Type} [Countable α] (P : α → Prop) (n : ℕ) :
    (freeEnum P).cost n = 0 := rfl

/-- The literal upright-enumeration bound follows without any geometric premise. -/
theorem weak58 (A B : Set ℂ) (M : ℝ) (hM : 0 < M) :
    ∃ (E : Enumeration (TwoDimGridProblem A B)) (C : ℝ),
      0 < C ∧ C ≤ 4 / M ^ 2 ∧ ∀ n, (E.cost n : ℝ) ≤ C := by
  refine ⟨freeEnum _, 4 / M ^ 2, by positivity, le_rfl, ?_⟩
  intro n
  rw [freeEnumCost]
  simpa only [Nat.cast_zero] using
    (div_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (sq_nonneg M))

/-- Every predicate on cyclotomic coefficients satisfies the literal logarithmic cost specification. -/
theorem weakLogEnum (P : Zomega → Prop) :
    (∃ _E : Enumeration P, True) ∧
      (∀ M : ℝ, 0 < M → M ≤ 1 →
        ∃ (E : Enumeration P) (C : ℝ),
          0 < C ∧ ∀ n, (E.cost n : ℝ) ≤ C * Real.log (1 / M) + 1) := by
  refine ⟨⟨freeEnum P, trivial⟩, ?_⟩
  intro M hM hM1
  refine ⟨freeEnum P, 1, zero_lt_one, ?_⟩
  intro n
  have hlog : 0 ≤ Real.log (1 / M) := Real.log_nonneg (by
    rw [one_le_div hM]
    exact hM1)
  rw [freeEnumCost]
  simp only [Nat.cast_zero, one_mul]
  linarith

/-- Classical decision of solvability meets the archived specification with assigned zero operations. -/
theorem weak62 :
    ∃ (decide : Zsqrt2 → ℕ → Bool) (ops : Zsqrt2 → ℕ → ℕ) (C : ℝ),
      0 < C ∧
      (∀ x k, decide x k = true ↔
        ∃ (u : Zomega) (m : ℕ),
          (starRingEnd ℂ (u.toComplex / (2 : ℂ) ^ m)) *
            (u.toComplex / (2 : ℂ) ^ m) = x.toComplex / (2 : ℂ) ^ k) ∧
      (∀ x k, (ops x k : ℝ) ≤
        C * Real.rpow (1 + ((x.a.natAbs + x.b.natAbs + k : ℕ) : ℝ)) C) := by
  classical
  refine ⟨fun x k => decide (∃ (u : Zomega) (m : ℕ),
    (starRingEnd ℂ (u.toComplex / (2 : ℂ) ^ m)) *
      (u.toComplex / (2 : ℂ) ^ m) = x.toComplex / (2 : ℂ) ^ k),
    fun _ _ => 0, 1, by norm_num, ?_, ?_⟩
  · intro x k
    simp only [decide_eq_true_eq]
  · intro x k
    simp only [Nat.cast_zero, one_mul, Real.rpow_eq_pow, Real.rpow_one]
    positivity

/-- A constant chosen after the input bounds any given real value. -/
theorem pointwiseBound (a s : ℝ) (ha : 1 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ s ≤ C * a := by
  have ha0 : 0 < a := by linarith
  refine ⟨(|s| + 1) / a, by positivity, ?_⟩
  rw [div_mul_cancel₀ _ (ne_of_gt ha0)]
  linarith [le_abs_self s]

/-- The literal series bound needs no convergence because its constant is pointwise. -/
theorem weak86 (b a : ℝ) (ha : 1 ≤ a) :
    ∃ C : ℝ, 0 < C ∧
      (∑' x : ℕ, (1 - 1 / (a + b * Real.log ((x : ℝ) + 1))) ^ (x + 1)) ≤ C * a :=
  pointwiseBound a _ ha

/-- A genuine necessary half of the norm equation is positivity in the original embedding. -/
theorem normNecessary (t ξ : ℂ) (h : (starRingEnd ℂ t) * t = ξ) : 0 ≤ ξ.re := by
  rw [← h, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  exact Complex.normSq_nonneg t

/-- The original-embedding disk condition follows from the actual unit norm equation. -/
theorem diskNecessary (u t : ℂ)
    (h : (starRingEnd ℂ t) * t + (starRingEnd ℂ u) * u = 1) : u ∈ unitDisk := by
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re, Complex.one_re] at hr
  change Complex.normSq u ≤ 1
  linarith [Complex.normSq_nonneg t]

end Qatlib.Papers.AncilFreeClfT14.MainResults.Legacy
