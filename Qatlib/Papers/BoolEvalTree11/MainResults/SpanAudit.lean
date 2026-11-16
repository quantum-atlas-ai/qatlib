/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolEvalTree11.MainResults.Models

@[expose] public section


/-! # Constant functions are admitted by the old span-program carrier

The actual old negative-witness infimum is zero at the all-available endpoint,
including when the witness set is empty. A one-dimensional zero-column program
represents the constant false function, so the whole old two-trivial-endpoint
existence target fails. This function is outside the source's intended pair of
opposite-output direct endpoints; the counterexample does not refute that source
statement.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolEvalTree11.MainResults.SpanAudit
open Models

/-- The real infimum of a set containing only zero is zero, including the empty set. -/
theorem infZero (s : Set ℝ) (hs : s⊆{0}) : sInf s=0 := by
  rcases s.eq_empty_or_nonempty with he|hn
  · simp [he]
  · have he : s={0} := by
      apply Set.Subset.antisymm hs
      intro x hx
      have hx0 : x=0 := by simpa using hx
      obtain ⟨a,ha⟩ := hn
      have ha0 : a=0 := by simpa using hs ha
      simpa [hx0,ha0] using ha
    simp [he]

/-- Every old false witness at the all-available endpoint has cost zero. -/
theorem falseAtOne {c : ℕ} (sp : DirectSpanProgram c) :
    sp.wsizeFalse sp.endpointOne=0 := by
  apply infZero
  rintro z ⟨w,hw,rfl⟩
  obtain ⟨α,_hα,_hrow,hzero⟩ := hw
  have hw0 : w=0 := by
    funext j
    exact hzero j (DirectSpanProgram.chi_endpointOne sp j)
  simp [DirectSpanProgram.witnessCost,hw0]

/-- A nonempty one-dimensional old program with one zero column. -/
def zeroSpan : DirectSpanProgram 1 where
  C := 1
  hC := by norm_num
  v := fun _ _ => 0
  flip := fun _ => false

/-- This legal old program represents the constant false function. -/
theorem zeroRep : zeroSpan.Represents (fun _ => false) := by
  intro x
  constructor
  · intro h; cases h
  · rintro ⟨a,_hz,hr⟩
    have hh := hr zeroSpan.target
    have hv (i : Fin zeroSpan.C) (j : Fin 1) : zeroSpan.v i j=0 := rfl
    simp only [hv,mul_zero,Finset.sum_const_zero,ite_true] at hh
    norm_num at hh

/-- The complete literal old two-trivial-endpoints target is false. -/
theorem endpointFalse :
    ¬(∀ {c : ℕ} (sp : DirectSpanProgram c) (f : (Fin c→Bool)→Bool)
      (_hrep : sp.Represents f),
      ∃ sp' : DirectSpanProgram c, sp'.Represents f ∧
        sp'.Trivial f sp'.endpointZero ∧ sp'.Trivial f sp'.endpointOne) := by
  intro h
  obtain ⟨sp',_hrep,_hzero,hone⟩ := h zeroSpan (fun _ => false) zeroRep
  simp [DirectSpanProgram.Trivial,DirectSpanProgram.witnessSize,falseAtOne] at hone

end Qatlib.Papers.BoolEvalTree11.MainResults.SpanAudit
