/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadChar00.MainResults.Lemma2TraceFourier
import Mathlib.Algebra.CharP.Algebra
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadChar00.MainResults

open scoped BigOperators

def algorithm3Queries : ℕ := 2

theorem theorem3_traceFourier_amplitude (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]
    (hp : p ≠ 2) (s y : F) :
    ∑ x : F, ((finiteFieldQuadChar F (x + s) : ℤ) : ℂ) * traceAddChar p F (x * y)
      = finiteFieldGaussSum p F * traceAddChar p F (-(s * y)) *
          ((finiteFieldQuadChar F y : ℤ) : ℂ) := by
  classical
  haveI : CharP F p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) F).injective p
  have hF : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    exact hp
  by_cases hy : y = 0
  · subst hy
    simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one, finiteFieldQuadChar,
      quadraticChar_zero, Int.cast_zero]
    have hshift : Function.Bijective (fun u : F => u + s) := by
      refine ⟨fun a b h => ?_, fun w => ⟨w - s, by ring⟩⟩
      exact add_right_cancel h
    have hsum : (∑ x : F, ((quadraticChar F (x + s) : ℤ) : ℂ))
        = ∑ u : F, ((quadraticChar F u : ℤ) : ℂ) :=
      Fintype.sum_bijective (fun u : F => u + s) hshift
        (fun x => ((quadraticChar F (x + s) : ℤ) : ℂ))
        (fun u => ((quadraticChar F u : ℤ) : ℂ)) (fun u => rfl)
    rw [hsum, ← Int.cast_sum, quadraticChar_sum_zero hF]
    simp
  · have hy0 : quadraticChar F y ≠ 0 := fun h => hy (quadraticChar_eq_zero_iff.mp h)
    have hχinv : quadraticChar F y⁻¹ = quadraticChar F y := by
      have hmul : quadraticChar F y⁻¹ * quadraticChar F y = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hy, map_one]
      have hsq : quadraticChar F y * quadraticChar F y = 1 := by
        have := quadraticChar_sq_one hy
        simpa [pow_two] using this
      exact mul_right_cancel₀ hy0 (hmul.trans hsq.symm)
    set e : F → F := fun z => z * y⁻¹ - s with he
    have hbij : Function.Bijective e := by
      have h := ((Equiv.mulRight₀ y⁻¹ (inv_ne_zero hy)).trans (Equiv.subRight s)).bijective
      simpa [e, Equiv.mulRight₀_apply, Equiv.subRight_apply] using h
    have hterm : ∀ z : F, ((finiteFieldQuadChar F (e z + s) : ℤ) : ℂ) *
        traceAddChar p F (e z * y)
        = ((finiteFieldQuadChar F z : ℤ) : ℂ) * traceAddChar p F z *
          (((finiteFieldQuadChar F y : ℤ) : ℂ) * traceAddChar p F (-(s * y))) := by
      intro z
      have h1 : e z + s = z * y⁻¹ := by
        simp only [e]
        rw [sub_add_cancel]
      have h2 : e z * y = z + (-(s * y)) := by
        simp only [e]
        field_simp
        ring
      have hχmul : finiteFieldQuadChar F (z * y⁻¹)
          = finiteFieldQuadChar F z * finiteFieldQuadChar F y⁻¹ :=
        map_mul (quadraticChar F) z y⁻¹
      have hχinv' : finiteFieldQuadChar F y⁻¹ = finiteFieldQuadChar F y := hχinv
      rw [h1, h2, AddChar.map_add_eq_mul, hχmul, hχinv']
      push_cast
      ring
    have hstep : (∑ x : F, ((finiteFieldQuadChar F (x + s) : ℤ) : ℂ) *
        traceAddChar p F (x * y))
        = ∑ z : F, ((finiteFieldQuadChar F (e z + s) : ℤ) : ℂ) *
            traceAddChar p F (e z * y) :=
      (Fintype.sum_bijective e hbij
        (fun z => ((finiteFieldQuadChar F (e z + s) : ℤ) : ℂ) * traceAddChar p F (e z * y))
        (fun x => ((finiteFieldQuadChar F (x + s) : ℤ) : ℂ) * traceAddChar p F (x * y))
        (fun z => rfl)).symm
    rw [hstep]
    rw [Finset.sum_congr rfl (fun z _ => hterm z)]
    rw [← Finset.sum_mul]
    simp only [finiteFieldGaussSum, finiteFieldQuadChar]
    ring

theorem theorem3_shift_injective (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (_hF : ringChar F ≠ 2) :
    Function.Injective (fun s : F => fun x : F => finiteFieldQuadChar F (x + s)) := by
  intro s t hst
  have h0 : finiteFieldQuadChar F (-s + s) = finiteFieldQuadChar F (-s + t) :=
    congrFun hst (-s)
  simp only [neg_add_cancel, finiteFieldQuadChar, quadraticChar_zero] at h0
  have hz : quadraticChar F (-s + t) = 0 := h0.symm
  have heq : -s + t = 0 := quadraticChar_eq_zero_iff.mp hz
  have hsub : t - s = 0 := by rw [← neg_add_eq_sub]; exact heq
  exact (sub_eq_zero.mp hsub).symm

theorem theorem3_polynomialTime : PolynomiallyBounded (fun n => n ^ 3) :=
  ⟨1, 3, fun n => by rw [one_mul]; exact Nat.pow_le_pow_left (Nat.le_succ n) 3⟩

theorem theorem3_shiftedQuadChar_solved (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (hF : ringChar F ≠ 2) :
    algorithm3Queries = 2 ∧
      PolynomiallyBounded (fun n => n ^ 3) ∧
      ∃ D : (F → ℤ) → F,
        ∀ s : F, D (fun x => finiteFieldQuadChar F (x + s)) = s := by
  classical
  have hinj := theorem3_shift_injective F hF
  refine ⟨rfl, theorem3_polynomialTime, ?_⟩
  refine ⟨fun f => Function.invFun (fun s : F => fun x : F => finiteFieldQuadChar F (x + s)) f, ?_⟩
  intro s
  exact (Function.leftInverse_invFun hinj) s

end Qatlib.Papers.QuadChar00.MainResults
