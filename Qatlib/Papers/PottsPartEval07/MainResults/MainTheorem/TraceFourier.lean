/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem.TraceClasses
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

@[expose] public section

/-!
# Actual trace-code weights as additive-character sums

Orthogonality over the prime field derives the character expression for the
Hamming weight of every actual trace word. This supplies the first half of
the McEliece reduction without assuming a weight formula.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

open scoped Classical BigOperators
open Qatlib.Papers.PottsPartEval07.ExactRecovery
open Qatlib.Papers.PottsPartEval07.CodeStructure

variable {F : Type*} [Field F]
  [Algebra (ZMod (ringChar F)) F] [NeZero (ringChar F)]
  {E : Type*} [Fintype E] [DecidableEq E]

/-- The actual additive character of the extension is composed with the actual field trace. -/
def traceAddChar (additive : AddChar (ZMod (ringChar F)) ℂ) : AddChar F ℂ :=
  additive.compAddMonoidHom (Algebra.trace (ZMod (ringChar F)) F).toAddMonoidHom

omit [Fintype E] [DecidableEq E] in
/-- Averaging the actual character over prime-field scalars detects a zero trace coordinate. -/
theorem trace_average (additive : AddChar (ZMod (ringChar F)) ℂ)
    (ha : additive.IsPrimitive) (g : E → F) (x : F) (e : E) :
    (∑ a : ZMod (ringChar F), traceAddChar additive
      (algebraMap (ZMod (ringChar F)) F a * (x * g e))) =
      if traceWord g x e = 0 then (ringChar F : ℂ) else 0 := by
  have hscalar : ∀ a : ZMod (ringChar F), traceAddChar additive
      (algebraMap (ZMod (ringChar F)) F a * (x * g e)) = additive (a * traceWord g x e) := by
    intro a
    change additive (Algebra.trace (ZMod (ringChar F)) F
      (algebraMap (ZMod (ringChar F)) F a * (x * g e))) = _
    rw [← Algebra.smul_def, map_smul]
    rfl
  simp_rw [hscalar]
  simpa only [ZMod.card, Nat.cast_ite, Nat.cast_zero] using
    AddChar.sum_mulShift (traceWord g x e) ha

omit [DecidableEq E] in
/-- The derived character average counts the actual zero coordinates of a trace word. -/
theorem trace_zero_sum (additive : AddChar (ZMod (ringChar F)) ℂ)
    (ha : additive.IsPrimitive) (g : E → F) (x : F) :
    (ringChar F : ℂ) * ((Fintype.card E - hammingWeight (traceWord g x) : ℕ) : ℂ) =
      ∑ e : E, ∑ a : ZMod (ringChar F), traceAddChar additive
        (algebraMap (ZMod (ringChar F)) F a * (x * g e)) := by
  rw [← card_zero_eq]
  simp_rw [trace_average additive ha g x]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]

omit [DecidableEq E] in
/-- Actual trace-code weight is determined by the nonzero-scalar additive periods. -/
theorem trace_weight_sum (additive : AddChar (ZMod (ringChar F)) ℂ)
    (ha : additive.IsPrimitive) (g : E → F) (x : F) :
    (ringChar F : ℂ) * (hammingWeight (traceWord g x) : ℂ) =
      ((ringChar F : ℂ) - 1) * Fintype.card E -
        ∑ a ∈ (Finset.univ : Finset (ZMod (ringChar F))).erase 0,
          ∑ e : E, traceAddChar additive
            (algebraMap (ZMod (ringChar F)) F a * (x * g e)) := by
  have hweight : hammingWeight (traceWord g x) ≤ Fintype.card E := by
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)
  have hmean := trace_zero_sum additive ha g x
  rw [Nat.cast_sub hweight, Finset.sum_comm] at hmean
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod (ringChar F)))] at hmean
  simp only [map_zero, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hmean
  linear_combination -hmean

end Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
