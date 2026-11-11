/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Defs
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Kraus
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Euler
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Tools
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Wire

/-!
# Kraus semantics of the six-wire CNOT gadget

This module evaluates the six-wire CNOT measurement pattern with a uniform four-qubit resource.
It expands the entangler into Boolean phase signs, reduces the register sum to two free internal
bits, and identifies the resulting core matrix with a signed quarter multiple of the encoded
CNOT.

After conjugation and summation over the auxiliary register, each fixed measurement history
gives one sixteenth of the CNOT conjugation. This is a concrete branch calculation for the
cluster-state gate construction of [RaussendorfBriegel2000].

## Main statements

* `cnotAux_cnot_core`: The corrected core is the encoded CNOT scaled by a measurement-dependent
  sign divided by four.
* `cnotAux_cnot_core_conj`: Core conjugation removes the global sign and yields the factor one
  sixteenth.
* `cnotAux_clause1b`: Summing the pattern's Kraus conjugations gives the uniformly weighted CNOT
  branch.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire1a
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open scoped BigOperators Classical

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open scoped BigOperators Classical
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire1a

/-- The five-edge graph on six physical wires used by the CNOT pattern. -/
def cnotAux_cnotE : Finset (Fin 6 × Fin 6) :=
  {(⟨0, by omega⟩, ⟨2, by omega⟩), (⟨0, by omega⟩, ⟨3, by omega⟩),
    (⟨1, by omega⟩, ⟨2, by omega⟩), (⟨2, by omega⟩, ⟨5, by omega⟩),
    (⟨3, by omega⟩, ⟨4, by omega⟩)}

/-- The CNOT pattern entangler factors into the frame matrix and controlled-Z matrix of its
six-wire graph. -/
theorem cnotAux_cnot_entangler :
    mpCnotPattern.entangler
      = Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix cnotAux_cnotE * Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix cnotAux_cnotE := by
  simp only [mpCnotPattern]
  exact Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse_eq_frame_cz _

/-- The graph frame contributes the product of the phase signs on wires three, four, and five. -/
theorem cnotAux_cnot_frame (x : Reg 6) :
    Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix cnotAux_cnotE x x
      = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 3) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 4)
          * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 5) := by
  rw [Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix, Matrix.diagonal_apply,
      if_pos (rfl : x = x)]
  rw [Qatlib.Concepts.ClusterPatterns.CnotPatterns.prod_fin6]
  have h0 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd cnotAux_cnotE 0 = false := by decide
  have h1 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd cnotAux_cnotE 1 = false := by decide
  have h2 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd cnotAux_cnotE 2 = false := by decide
  have h3 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd cnotAux_cnotE 3 = true := by decide
  have h4 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd cnotAux_cnotE 4 = true := by decide
  have h5 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd cnotAux_cnotE 5 = true := by decide
  rw [h0, h1, h2, h3, h4, h5]
  simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

/-- The controlled-Z diagonal entry is the product of the five edge phase signs of the CNOT
graph. -/
theorem cnotAux_cnot_cz (x : Reg 6) :
    Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix cnotAux_cnotE x x
      = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 0 && x 2) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 0 && x 3)
          * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 1 && x 2) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 2 && x 5)
          * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 3 && x 4) := by
  rw [Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix, Matrix.diagonal_apply, if_pos (rfl : x = x)]
  show (∏ e ∈ cnotAux_cnotE, if x e.1 && x e.2 then (-1 : ℂ) else 1) = _
  rw [cnotAux_cnotE]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

/-- The total diagonal phase of the six-wire CNOT resource entangler. -/
def cnotAux_cnotPhase (x : Reg 6) : ℂ :=
  (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 3) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 4)
      * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 5))
    * (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 0 && x 2) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 0 && x 3)
      * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 1 && x 2) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 2 && x 5)
      * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 3 && x 4))

/-- The CNOT entangler is diagonal with diagonal function `cnotAux_cnotPhase`. -/
theorem cnotAux_cnot_ent_diag (x y : Reg 6) :
    mpCnotPattern.entangler x y = if x = y then cnotAux_cnotPhase x else 0 := by
  rw [cnotAux_cnot_entangler]
  by_cases h : x = y
  · subst h
    rw [if_pos rfl]
    rw [Matrix.mul_apply, Finset.sum_eq_single x]
    · rw [cnotAux_cnot_frame, cnotAux_cnot_cz]
      rfl
    · intro k _ hk
      rw [Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix, Matrix.diagonal_apply, if_neg (Ne.symm hk),
        zero_mul]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [if_neg h]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = x
    · subst hk
      rw [Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix, Matrix.diagonal_apply, if_neg h, mul_zero]
    · rw [Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix, Matrix.diagonal_apply, if_neg (Ne.symm hk),
        zero_mul]

/-- The uniform state on four bits has amplitude one quarter at every register. -/
theorem cnotAux_uniform4 (x : Reg 4) : Uniform (Reg 4) x = (1 / 4 : ℂ) := by
  show ((Real.sqrt (Fintype.card (Reg 4)) : ℝ) : ℂ)⁻¹ = 1 / 4
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [card_reg]
  norm_num [h16]

/-- The CNOT loading matrix has amplitude one quarter exactly when its first two physical bits
match the input register. -/
theorem cnotAux_cnot_load (d : Reg 6) (y : Reg 2) :
    mpLoadMatrix mpCnotPattern (Uniform (Reg 4)) d y
      = if d 0 = y 0 ∧ d 1 = y 1 then (1 / 4 : ℂ) else 0 := by
  simp only [mpLoadMatrix, mpCnotPattern, Matrix.of_apply]
  by_cases h : ∀ i : Fin 2, d (Fin.castLE (by omega : (2:ℕ) ≤ 4 + 2) i) = y i
  · rw [if_pos h]
    have h0 : d 0 = y 0 := h ⟨0, by omega⟩
    have h1 : d 1 = y 1 := h ⟨1, by omega⟩
    rw [if_pos (And.intro h0 h1)]
    have hres : Uniform (Reg 4)
        (fun k : Fin 4 => d (Fin.cast (by omega) (Fin.natAdd 2 k))) = (1 / 4 : ℂ) :=
      cnotAux_uniform4 _
    rw [hres]
  · rw [if_neg h]
    have h0 : ¬ (d 0 = y 0 ∧ d 1 = y 1) := by
      intro hh
      apply h
      intro i
      fin_cases i
      · exact hh.1
      · exact hh.2
    rw [if_neg h0]

/-- Entangling the loaded CNOT resource gives one quarter of the resource phase on matching
input bits and zero otherwise. -/
theorem cnotAux_cnot_EL (d : Reg 6) (y : Reg 2) :
    (mpCnotPattern.entangler * mpLoadMatrix mpCnotPattern (Uniform (Reg 4))) d y
      = if d 0 = y 0 ∧ d 1 = y 1 then (1 / 4 : ℂ) * cnotAux_cnotPhase d else 0 := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single d]
  · rw [cnotAux_cnot_ent_diag, if_pos rfl, cnotAux_cnot_load]
    by_cases h : d 0 = y 0 ∧ d 1 = y 1
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h]
      ring
  · intro d' _ hdne
    rw [cnotAux_cnot_ent_diag, if_neg (Ne.symm hdne), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Every adaptive measurement angle of the CNOT pattern is zero. -/
theorem cnotAux_cnot_sv (s : Fin 4 → Bool) (j : Fin 4) :
    mpAdaptiveAngle mpCnotPattern s j = 0 := by
  simp only [mpAdaptiveAngle, mpCnotPattern, mpParity_empty]
  norm_num

/-- The X correction on output zero is the negation of measurement bit three. -/
theorem cnotAux_cnot_xCorr0 (s : Fin 4 → Bool) : mpCnotPattern.xCorr 0 s = !s 3 := by
  simp only [mpCnotPattern]
  rfl

/-- The X correction on output one is measurement bit two. -/
theorem cnotAux_cnot_xCorr1 (s : Fin 4 → Bool) : mpCnotPattern.xCorr 1 s = s 2 := by
  simp only [mpCnotPattern]
  rfl

/-- The Z correction on output zero is the negation of the parity of measurement bits zero and
one. -/
theorem cnotAux_cnot_zCorr0 (s : Fin 4 → Bool) : mpCnotPattern.zCorr 0 s = !(xor (s 0) (s 1)) := by
  simp only [mpCnotPattern]
  rfl

/-- The Z correction on output one is the negation of measurement bit one. -/
theorem cnotAux_cnot_zCorr1 (s : Fin 4 → Bool) : mpCnotPattern.zCorr 1 s = !s 1 := by
  simp only [mpCnotPattern]
  rfl

/-- The first corrected output bit is the decoded first bit XOR the negation of measurement bit
three. -/
theorem cnotAux_cnot_outBit0 (s : Fin 4 → Bool) (xp : Fin 4) :
    mpOutBit mpCnotPattern s xp 0 = xor (!s 3) ((bitVecEquiv 2).symm xp 0) := by
  rw [mpOutBit, cnotAux_cnot_xCorr0]

/-- The second corrected output bit is the decoded second bit XOR measurement bit two. -/
theorem cnotAux_cnot_outBit1 (s : Fin 4 → Bool) (xp : Fin 4) :
    mpOutBit mpCnotPattern s xp 1 = xor (s 2) ((bitVecEquiv 2).symm xp 1) := by
  rw [mpOutBit, cnotAux_cnot_xCorr1]

/-- The output-matching condition over `Fin 2` is equivalent to its two coordinate equalities on
physical wires four and five. -/
theorem cnotAux_cnot_delta_iff (s : Fin 4 → Bool) (xp : Fin 4) (c : Reg 6) :
    (∀ v : Fin 2, c (Fin.natAdd 4 v) = mpOutBit mpCnotPattern s xp v)
      ↔ (c 4 = mpOutBit mpCnotPattern s xp 0
        ∧ c 5 = mpOutBit mpCnotPattern s xp 1) := by
  constructor
  · intro h
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    refine ⟨?_, ?_⟩
    · simpa using h0
    · simpa using h1
  · intro h v
    fin_cases v
    · simpa using h.1
    · simpa using h.2

/-- The six-register summand combining measurement contractions, output matching, and the
entangled loading matrix for the CNOT core. -/
noncomputable def cnotAux_cnotSummand (s : Fin 4 → Bool) (xp : Fin 4) (y : Reg 2) : Reg 6 → ℂ :=
  fun c =>
    (∏ j : Fin 4, star (mpSVector (mpAdaptiveAngle mpCnotPattern s j) (s j)
        (c (Fin.castLE (by omega : 4 ≤ 4 + 2) j))))
      * (if ∀ v : Fin 2, c (Fin.natAdd 4 v) = mpOutBit mpCnotPattern s xp v then (1 : ℂ) else 0)
      * (mpCnotPattern.entangler * mpLoadMatrix mpCnotPattern (Uniform (Reg 4))) c y

/-- The CNOT pre-core entry is its output Z-correction sign times the sum of
`cnotAux_cnotSummand`. -/
theorem cnotAux_cnot_corePre_eq (s : Fin 4 → Bool) (xp : Fin 4) (y : Reg 2) :
    corePre mpCnotPattern (Uniform (Reg 4)) s xp y
      = (∏ k : Fin 2,
            if mpCnotPattern.zCorr k s && mpOutBit mpCnotPattern s xp k
            then (-1 : ℂ) else 1)
          * ∑ c : Reg 6, cnotAux_cnotSummand s xp y c := by
  simp only [corePre, Matrix.of_apply, cnotAux_cnotSummand]

/-- The CNOT summand expands into zero-angle measurement entries, output-bit constraints, and
the phased loading amplitude. -/
theorem cnotAux_cnot_summand_eq (s : Fin 4 → Bool) (xp : Fin 4) (y : Reg 2) (c : Reg 6) :
    cnotAux_cnotSummand s xp y c
      = (∏ j : Fin 4, star (mpSVector 0 (s j) (c (Fin.castLE (by omega : 4 ≤ 4 + 2) j))))
          * (if c 4 = mpOutBit mpCnotPattern s xp 0
              ∧ c 5 = mpOutBit mpCnotPattern s xp 1 then (1 : ℂ) else 0)
          * (if c 0 = y 0 ∧ c 1 = y 1 then (1 / 4 : ℂ) * cnotAux_cnotPhase c else 0) := by
  simp only [cnotAux_cnotSummand]
  rw [cnotAux_cnot_EL]
  simp only [cnotAux_cnot_sv]
  simp only [cnotAux_cnot_delta_iff]

/-- A sum over six-bit registers supported on four fixed coordinates reduces to a sum over the
two free bits. -/
theorem cnotAux_sum_reclause6_fix4 (f : Reg 6 → ℂ) (a0 a1 a4 a5 : Bool)
    (hvan : ∀ c : Reg 6, (c 0 ≠ a0 ∨ c 1 ≠ a1 ∨ c 4 ≠ a4 ∨ c 5 ≠ a5) → f c = 0) :
    ∑ c : Reg 6, f c
      = ∑ p : Bool, ∑ q : Bool, f (pin6 a0 a1 p q a4 a5) := by
  have hfilter :
      ∑ c : Reg 6, f c
        = ∑ c ∈ (Finset.univ.filter fun c : Reg 6 =>
            c 0 = a0 ∧ c 1 = a1 ∧ c 4 = a4 ∧ c 5 = a5), f c := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : c 0 = a0 ∧ c 1 = a1 ∧ c 4 = a4 ∧ c 5 = a5
    · rw [if_pos h]
    · rw [if_neg h]
      have h' : c 0 ≠ a0 ∨ c 1 ≠ a1 ∨ c 4 ≠ a4 ∨ c 5 ≠ a5 := by
        by_contra hc
        push Not at hc
        exact h hc
      exact hvan c h'
  have hprod :
      ∑ c ∈ (Finset.univ.filter fun c : Reg 6 =>
          c 0 = a0 ∧ c 1 = a1 ∧ c 4 = a4 ∧ c 5 = a5), f c
        = ∑ p : Bool × Bool, f (pin6 a0 a1 p.1 p.2 a4 a5) := by
    refine Finset.sum_bij (fun c _ => (c 2, c 3)) ?_ ?_ ?_ ?_
    · intro c _; simp
    · intro c1 hc1 c2 hc2 heq
      obtain ⟨h10, h11, h14, h15⟩ : c1 0 = a0 ∧ c1 1 = a1 ∧ c1 4 = a4 ∧ c1 5 = a5 := by
        simpa using (Finset.mem_filter.mp hc1).2
      obtain ⟨h20, h21, h24, h25⟩ : c2 0 = a0 ∧ c2 1 = a1 ∧ c2 4 = a4 ∧ c2 5 = a5 := by
        simpa using (Finset.mem_filter.mp hc2).2
      have hp : c1 2 = c2 2 := congrArg Prod.fst heq
      have hq : c1 3 = c2 3 := congrArg Prod.snd heq
      conv_lhs => rw [reg6_eq_pin6 c1]
      conv_rhs => rw [reg6_eq_pin6 c2]
      simp [h10, h11, h14, h15, h20, h21, h24, h25, hp, hq]
    · intro p _
      refine ⟨pin6 a0 a1 p.1 p.2 a4 a5, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simp [pin6_0, pin6_1, pin6_4, pin6_5]
      · obtain ⟨p, q⟩ := p
        rfl
    · intro c hc
      obtain ⟨h10, h11, h14, h15⟩ : c 0 = a0 ∧ c 1 = a1 ∧ c 4 = a4 ∧ c 5 = a5 := by
        simpa using (Finset.mem_filter.mp hc).2
      conv_lhs => rw [reg6_eq_pin6 c, h10, h11, h14, h15]
  rw [hfilter, hprod]
  exact Fintype.sum_prod_type _

/-- The CNOT summand sum reduces to the two free internal bits with input and corrected output
bits fixed. -/
theorem cnotAux_cnot_sum_eq (s : Fin 4 → Bool) (xp : Fin 4) (y : Reg 2) :
    ∑ c : Reg 6, cnotAux_cnotSummand s xp y c
      = ∑ p : Bool, ∑ q : Bool,
          cnotAux_cnotSummand s xp y
            (pin6 (y 0) (y 1) p q (mpOutBit mpCnotPattern s xp 0)
              (mpOutBit mpCnotPattern s xp 1)) := by
  rw [cnotAux_sum_reclause6_fix4 (cnotAux_cnotSummand s xp y) (y 0) (y 1)
    (mpOutBit mpCnotPattern s xp 0) (mpOutBit mpCnotPattern s xp 1) ?_]
  · intro c hc
    rw [cnotAux_cnot_summand_eq]
    by_cases h0 : c 0 = y 0
    · by_cases h1 : c 1 = y 1
      · by_cases h4 : c 4 = mpOutBit mpCnotPattern s xp 0
        · by_cases h5 : c 5 = mpOutBit mpCnotPattern s xp 1
          · rcases hc with hc | hc | hc | hc
            · exact absurd h0 hc
            · exact absurd h1 hc
            · exact absurd h4 hc
            · exact absurd h5 hc
          · have hne : ¬ (c 4 = mpOutBit mpCnotPattern s xp 0
                ∧ c 5 = mpOutBit mpCnotPattern s xp 1) := fun hh => h5 hh.2
            rw [if_neg hne, mul_zero, zero_mul]
        · have hne : ¬ (c 4 = mpOutBit mpCnotPattern s xp 0
              ∧ c 5 = mpOutBit mpCnotPattern s xp 1) := fun hh => h4 hh.1
          rw [if_neg hne, mul_zero, zero_mul]
      · have hne : ¬ (c 0 = y 0 ∧ c 1 = y 1) := fun hh => h1 hh.2
        rw [if_neg hne, mul_zero]
    · have hne : ¬ (c 0 = y 0 ∧ c 1 = y 1) := fun hh => h0 hh.1
      rw [if_neg hne, mul_zero]

/-- The fourth power of the complex embedding of `√2` is four. -/
theorem cnotAux_sqrt2_pow4 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = 4 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by rw [pow_two, cnotAux_sqrt2_sq]
  rw [show (4:ℕ) = 2 + 2 by norm_num, pow_add, h2]
  norm_num

/-- A conjugated zero-angle measurement entry is its Boolean phase sign times the inverse square
root of two. -/
theorem cnotAux_sv0_bp (o b : Bool) :
    star (mpSVector 0 o b)
      = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (o && b) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  rw [star_sv, cnotAux_sv0]
  rcases o with rfl | rfl <;> rcases b with rfl | rfl <;>
    simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

/-- Four inverse-square-root-normalized phase factors and a quarter-weight phase combine into
one sixteenth times their XOR phase. -/
theorem cnotAux_prod5 (a b c d e : Bool) :
    (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase a * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
        * (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase b * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
        * (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase c * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
        * (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase d * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
        * ((1 / 4 : ℂ) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase e)
      = (1 / 16 : ℂ) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (a ^^ b ^^ c ^^ d ^^ e) := by
  rcases Bool.eq_false_or_eq_true a with ha | ha <;>
    rcases Bool.eq_false_or_eq_true b with hb | hb <;>
    rcases Bool.eq_false_or_eq_true c with hc | hc <;>
    rcases Bool.eq_false_or_eq_true d with hd | hd <;>
    rcases Bool.eq_false_or_eq_true e with he | he
  all_goals simp only [ha, hb, hc, hd, he]
  all_goals norm_num [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]
  all_goals field_simp [cnotAux_sqrt2_sq]
  all_goals (try rw [cnotAux_sqrt2_pow4])
  all_goals norm_num

/-- The first corrected output bit expressed using the high bit of the integer output index. -/
def cnotAux_cnotOb0 (s : Fin 4 → Bool) (xp : Fin 4) : Bool :=
  xor (!s 3) (decide (2 ≤ (xp : ℕ)))

/-- The second corrected output bit expressed using the low bit of the integer output index. -/
def cnotAux_cnotOb1 (s : Fin 4 → Bool) (xp : Fin 4) : Bool :=
  xor (s 2) (decide ((xp : ℕ) % 2 = 1))

/-- The first output bit of the CNOT pattern equals `cnotAux_cnotOb0`. -/
theorem cnotAux_cnot_ob0 (s : Fin 4 → Bool) (xp : Fin 4) :
    mpOutBit mpCnotPattern s xp 0 = cnotAux_cnotOb0 s xp := by
  rw [cnotAux_cnot_outBit0, cnotAux_cnotOb0]
  rw [(cnotAux_bv2_bits xp).1]

/-- The second output bit of the CNOT pattern equals `cnotAux_cnotOb1`. -/
theorem cnotAux_cnot_ob1 (s : Fin 4 → Bool) (xp : Fin 4) :
    mpOutBit mpCnotPattern s xp 1 = cnotAux_cnotOb1 s xp := by
  rw [cnotAux_cnot_outBit1, cnotAux_cnotOb1]
  rw [(cnotAux_bv2_bits xp).2]

/-- The Boolean exponent of the CNOT resource phase in coordinates with fixed input and output
bits. -/
def cnotAux_cnotPhaseBit (y0 y1 p q ob0 ob1 : Bool) : Bool :=
  q ^^ ob0 ^^ ob1 ^^ (y0 && p) ^^ (y0 && q) ^^ (y1 && p) ^^ (p && ob1) ^^ (q && ob0)

/-- Evaluating the CNOT resource phase on `pin6` gives the phase sign of `cnotAux_cnotPhaseBit`. -/
theorem cnotAux_phase_pin6 (y0 y1 p q ob0 ob1 : Bool) :
    cnotAux_cnotPhase (pin6 y0 y1 p q ob0 ob1)
      = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotPhaseBit y0 y1 p q ob0 ob1) := by
  have h0 : pin6 y0 y1 p q ob0 ob1 0 = y0 := rfl
  have h1 : pin6 y0 y1 p q ob0 ob1 1 = y1 := rfl
  have h2 : pin6 y0 y1 p q ob0 ob1 2 = p := rfl
  have h3 : pin6 y0 y1 p q ob0 ob1 3 = q := rfl
  have h4 : pin6 y0 y1 p q ob0 ob1 4 = ob0 := rfl
  have h5 : pin6 y0 y1 p q ob0 ob1 5 = ob1 := rfl
  rw [cnotAux_cnotPhase, h0, h1, h2, h3, h4, h5, cnotAux_cnotPhaseBit]
  rcases Bool.eq_false_or_eq_true y0 with a | a <;>
    rcases Bool.eq_false_or_eq_true y1 with b | b <;>
    rcases Bool.eq_false_or_eq_true p with c | c <;>
    rcases Bool.eq_false_or_eq_true q with d | d <;>
    rcases Bool.eq_false_or_eq_true ob0 with e | e <;>
    rcases Bool.eq_false_or_eq_true ob1 with f | f
  all_goals simp only [a, b, c, d, e, f]
  all_goals norm_num [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

/-- The constant Boolean term of the CNOT summand exponent after fixing its input and output
bits. -/
def cnotAux_cnotExB0 (s : Fin 4 → Bool) (xp : Fin 4) (y : Reg 2) : Bool :=
  ((s 0) && (y 0)) ^^ ((s 1) && (y 1)) ^^ (cnotAux_cnotOb0 s xp) ^^ (cnotAux_cnotOb1 s xp)

/-- The coefficient of the first free internal bit in the CNOT summand's Boolean exponent. -/
def cnotAux_cnotExP (s : Fin 4 → Bool) (xp : Fin 4) (y : Reg 2) : Bool :=
  (s 2) ^^ (y 0) ^^ (y 1) ^^ (cnotAux_cnotOb1 s xp)

/-- The coefficient of the second free internal bit in the CNOT summand's Boolean exponent. -/
def cnotAux_cnotExQ (s : Fin 4 → Bool) (xp : Fin 4) (y : Reg 2) : Bool :=
  !((y 0) ^^ (s 3) ^^ (cnotAux_cnotOb0 s xp))

/-- The affine Boolean exponent formed from its constant term and the two free-bit coefficients. -/
def cnotAux_cnotEx (s : Fin 4 → Bool) (xp : Fin 4) (y : Reg 2) (p q : Bool) : Bool :=
  (cnotAux_cnotExB0 s xp y) ^^ (p && (cnotAux_cnotExP s xp y)) ^^ (q && (cnotAux_cnotExQ s xp y))

/-- The affine CNOT exponent equals the XOR of the four measurement contributions and the
resource phase exponent. -/
theorem cnotAux_cnotEx_eq (s : Fin 4 → Bool) (xp : Fin 4) (y : Reg 2) (p q : Bool) :
    cnotAux_cnotEx s xp y p q
      = (((s 0) && (y 0)) ^^ ((s 1) && (y 1)) ^^ ((s 2) && p) ^^ ((s 3) && q)
          ^^ (cnotAux_cnotPhaseBit (y 0) (y 1) p q (cnotAux_cnotOb0 s xp) (cnotAux_cnotOb1 s xp))) := by
  revert s xp y p q
  decide

/-- On a register with input and output bits fixed, the CNOT summand is the product of four
measurement contractions and the quarter-weight resource phase. -/
theorem cnotAux_cnot_summand_pin6 (s : Fin 4 → Bool) (xp : Fin 4) (y : Reg 2) (p q : Bool) :
    cnotAux_cnotSummand s xp y
        (pin6 (y 0) (y 1) p q (mpOutBit mpCnotPattern s xp 0)
          (mpOutBit mpCnotPattern s xp 1))
      = star (mpSVector 0 (s 0) (y 0)) * star (mpSVector 0 (s 1) (y 1))
          * star (mpSVector 0 (s 2) p) * star (mpSVector 0 (s 3) q)
          * ((1 / 4 : ℂ) * cnotAux_cnotPhase (pin6 (y 0) (y 1) p q
              (mpOutBit mpCnotPattern s xp 0) (mpOutBit mpCnotPattern s xp 1))) := by
  rw [cnotAux_cnot_summand_eq]
  have e0 : (pin6 (y 0) (y 1) p q (mpOutBit mpCnotPattern s xp 0)
      (mpOutBit mpCnotPattern s xp 1)) (Fin.castLE (by omega : 4 ≤ 4 + 2) (0 : Fin 4)) = y 0 := rfl
  have e1 : (pin6 (y 0) (y 1) p q (mpOutBit mpCnotPattern s xp 0)
      (mpOutBit mpCnotPattern s xp 1)) (Fin.castLE (by omega : 4 ≤ 4 + 2) (1 : Fin 4)) = y 1 := rfl
  have e2 : (pin6 (y 0) (y 1) p q (mpOutBit mpCnotPattern s xp 0)
      (mpOutBit mpCnotPattern s xp 1)) (Fin.castLE (by omega : 4 ≤ 4 + 2) (2 : Fin 4)) = p := rfl
  have e3 : (pin6 (y 0) (y 1) p q (mpOutBit mpCnotPattern s xp 0)
      (mpOutBit mpCnotPattern s xp 1)) (Fin.castLE (by omega : 4 ≤ 4 + 2) (3 : Fin 4)) = q := rfl
  have hprod : (∏ j : Fin 4,
        star (mpSVector 0 (s j)
          ((pin6 (y 0) (y 1) p q (mpOutBit mpCnotPattern s xp 0)
            (mpOutBit mpCnotPattern s xp 1))
            (Fin.castLE (by omega : 4 ≤ 4 + 2) j))))
      = star (mpSVector 0 (s 0) (y 0)) * star (mpSVector 0 (s 1) (y 1))
          * star (mpSVector 0 (s 2) p) * star (mpSVector 0 (s 3) q) := by
    rw [Fin.prod_univ_four, e0, e1, e2, e3]
  rw [hprod]
  have hA : (pin6 (y 0) (y 1) p q (mpOutBit mpCnotPattern s xp 0)
      (mpOutBit mpCnotPattern s xp 1)) 4 = mpOutBit mpCnotPattern s xp 0 := rfl
  have hB : (pin6 (y 0) (y 1) p q (mpOutBit mpCnotPattern s xp 0)
      (mpOutBit mpCnotPattern s xp 1)) 5 = mpOutBit mpCnotPattern s xp 1 := rfl
  have hC : (pin6 (y 0) (y 1) p q (mpOutBit mpCnotPattern s xp 0)
      (mpOutBit mpCnotPattern s xp 1)) 0 = y 0 := rfl
  have hD : (pin6 (y 0) (y 1) p q (mpOutBit mpCnotPattern s xp 0)
      (mpOutBit mpCnotPattern s xp 1)) 1 = y 1 := rfl
  rw [if_pos ⟨hA, hB⟩, if_pos ⟨hC, hD⟩]
  ring

/-- Each CNOT summand with fixed input and output bits is one sixteenth of its Boolean
exponent's phase sign. -/
theorem cnotAux_cnot_term (s : Fin 4 → Bool) (xp : Fin 4) (y : Reg 2) (p q : Bool) :
    cnotAux_cnotSummand s xp y
        (pin6 (y 0) (y 1) p q (mpOutBit mpCnotPattern s xp 0)
          (mpOutBit mpCnotPattern s xp 1))
      = (1 / 16 : ℂ) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotEx s xp y p q) := by
  rw [cnotAux_cnot_summand_pin6, cnotAux_cnot_ob0, cnotAux_cnot_ob1]
  simp only [cnotAux_sv0_bp]
  rw [cnotAux_phase_pin6]
  have h := cnotAux_prod5 ((s 0) && (y 0)) ((s 1) && (y 1)) ((s 2) && p) ((s 3) && q)
    (cnotAux_cnotPhaseBit (y 0) (y 1) p q (cnotAux_cnotOb0 s xp) (cnotAux_cnotOb1 s xp))
  rw [h]
  congr 1
  rw [← cnotAux_cnotEx_eq]

/-- Summing an affine Boolean phase over two bits factors into its constant sign and two factors
of the form `1 + bitPhase`. -/
theorem cnotAux_sum_bit (base A B : Bool) :
    (∑ p : Bool, ∑ q : Bool,
        Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (base ^^ (p && A) ^^ (q && B)))
      = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase base
          * (((1:ℂ) + Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase A)
            * ((1:ℂ) + Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase B)) := by
  rw [sum_bool_eq, sum_bool_eq]
  rcases Bool.eq_false_or_eq_true base with hb | hb <;>
    rcases Bool.eq_false_or_eq_true A with hA | hA <;>
    rcases Bool.eq_false_or_eq_true B with hB | hB
  all_goals simp only [hb, hA, hB]
  all_goals norm_num [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

/-- The product of two factors `1 + bitPhase` is four when both bits are false and zero
otherwise. -/
theorem cnotAux_bitPhase_add_pair (A B : Bool) :
    (((1:ℂ) + Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase A)
      * ((1:ℂ) + Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase B))
      = if A || B then (0:ℂ) else 4 := by
  rcases Bool.eq_false_or_eq_true A with hA | hA <;>
    rcases Bool.eq_false_or_eq_true B with hB | hB
  all_goals simp only [hA, hB]
  all_goals norm_num [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

/-- The measurement-dependent Boolean exponent of the global sign of the CNOT core. -/
def cnotAux_cnotPhi (s : Fin 4 → Bool) : Bool :=
  (s 0) ^^ (s 1) ^^ ((s 0) && (s 3)) ^^ ((s 1) && (s 2)) ^^ ((s 1) && (s 3))

/-- The Boolean support condition that the encoded output equals CNOT applied to the input
register. -/
def cnotAux_cnotSupp (xp : Fin 4) (y : Reg 2) : Bool :=
  ((y 0) == decide (2 ≤ (xp : ℕ)))
    && ((y 1) == (decide ((xp : ℕ) % 2 = 1) ^^ (y 0)))

/-- The Boolean exponent of the output Z-correction sign. -/
def cnotAux_cnotZBit (s : Fin 4 → Bool) (xp : Fin 4) : Bool :=
  ((!(xor (s 0) (s 1))) && (cnotAux_cnotOb0 s xp)) ^^ ((!(s 1)) && (cnotAux_cnotOb1 s xp))

/-- The product of output Z-correction signs equals the phase sign of `cnotAux_cnotZBit`. -/
theorem cnotAux_cnot_sign (s : Fin 4 → Bool) (xp : Fin 4) :
    (∏ k : Fin 2,
        if mpCnotPattern.zCorr k s && mpOutBit mpCnotPattern s xp k
        then (-1 : ℂ) else 1)
      = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotZBit s xp) := by
  rw [Fin.prod_univ_two, cnotAux_cnot_zCorr0, cnotAux_cnot_zCorr1, cnotAux_cnot_ob0,
      cnotAux_cnot_ob1]
  rw [cnotAux_bitPhase_and, cnotAux_bitPhase_and]
  rw [← Clause18Wire1a.bitPhase_xor]
  rfl

/-- The two free-bit exponent coefficients vanish exactly on the CNOT support condition. -/
theorem cnotAux_cnot_supp_iff (s : Fin 4 → Bool) (xp : Fin 4) (y : Reg 2) :
    (cnotAux_cnotExP s xp y = false ∧ cnotAux_cnotExQ s xp y = false)
      ↔ cnotAux_cnotSupp xp y = true := by
  revert s xp y
  decide

/-- On the CNOT support, combining the correction exponent and the constant summand exponent
gives `cnotAux_cnotPhi s`. -/
theorem cnotAux_cnot_sig (s : Fin 4 → Bool) (xp : Fin 4) (y : Reg 2) :
    cnotAux_cnotSupp xp y = true →
      (cnotAux_cnotZBit s xp ^^ cnotAux_cnotExB0 s xp y) = cnotAux_cnotPhi s := by
  revert s xp y
  decide

/-- If the disjunction of two Boolean values is not true, both values are false. -/
theorem cnotAux_bool_or_false {a b : Bool} (h : ¬ (a || b) = true) : a = false ∧ b = false := by
  rcases Bool.eq_false_or_eq_true a with ha | ha <;>
    rcases Bool.eq_false_or_eq_true b with hb | hb <;>
    simp only [ha, hb] at h ⊢
  all_goals simp at h ⊢

/-- The CNOT pre-core entry is its measurement-dependent sign divided by four on the CNOT
support and zero elsewhere. -/
theorem cnotAux_cnot_corePre_closed (s : Fin 4 → Bool) (xp : Fin 4) (y : Reg 2) :
    corePre mpCnotPattern (Uniform (Reg 4)) s xp y
      = (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotPhi s) / 4)
          * (if cnotAux_cnotSupp xp y then (1:ℂ) else 0) := by
  rw [cnotAux_cnot_corePre_eq, cnotAux_cnot_sum_eq]
  simp_rw [cnotAux_cnot_term]
  have h16 : (∑ p : Bool, ∑ q : Bool,
        (1 / 16 : ℂ) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotEx s xp y p q))
      = (1 / 16 : ℂ)
          * (∑ p : Bool, ∑ q : Bool,
              Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotEx s xp y p q)) := by
    simp_rw [sum_bool_eq]
    ring
  rw [h16, cnotAux_cnot_sign]
  simp only [cnotAux_cnotEx]
  rw [cnotAux_sum_bit]
  rw [cnotAux_bitPhase_add_pair]
  by_cases hp : cnotAux_cnotExP s xp y || cnotAux_cnotExQ s xp y
  · rw [if_pos hp, mul_zero, mul_zero, mul_zero]
    have hs : ¬ cnotAux_cnotSupp xp y = true := by
      intro hc
      have h1 := (cnotAux_cnot_supp_iff s xp y).mpr hc
      simp [h1.1, h1.2] at hp
    rw [if_neg hs, mul_zero]
  · rw [if_neg hp]
    have hppqq := cnotAux_bool_or_false hp
    have hpp : cnotAux_cnotExP s xp y = false := hppqq.1
    have hqq : cnotAux_cnotExQ s xp y = false := hppqq.2
    have hsupp : cnotAux_cnotSupp xp y = true :=
      (cnotAux_cnot_supp_iff s xp y).mp ⟨hpp, hqq⟩
    have hsig := cnotAux_cnot_sig s xp y hsupp
    have hz : Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotZBit s xp)
        * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotExB0 s xp y)
        = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotPhi s) := by
      rw [← Clause18Wire1a.bitPhase_xor, hsig]
    rw [if_pos hsupp, mul_one]
    have hcalc : Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotZBit s xp)
        * ((1 / 16 : ℂ) * (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotExB0 s xp y) * 4))
        = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotPhi s) / 4 := by
      rw [← hz]
      field_simp
      ring
    rw [hcalc]

/-- The encoded CNOT entry is one exactly when the decoded output equals the input with its
target XORed with its control. -/
theorem cnotAux_mpFinCnot_apply (xp yp : Fin 4) :
    mpFinCnot ⟨0, by omega⟩ ⟨1, by omega⟩ xp yp
      = if (bitVecEquiv 2).symm xp
          = Function.update ((bitVecEquiv 2).symm yp) (⟨1, by omega⟩ : Fin 2)
              (((bitVecEquiv 2).symm yp) (⟨1, by omega⟩ : Fin 2)
                ^^ ((bitVecEquiv 2).symm yp) (⟨0, by omega⟩ : Fin 2))
        then (1:ℂ) else 0 := by
  have hleg : (0 < 2 ∧ 1 < 2 ∧ (0:ℕ) ≠ 1) := ⟨by omega, by omega, by omega⟩
  simp only [mpFinCnot, mpFinGate, finiteCodeMatrix]
  rw [dif_pos hleg]
  simp only [cnotGate, permMatrix, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.refl_symm, Equiv.refl_apply, Fin.isValue]

/-- The two-bit CNOT register update is equivalent to preserving bit zero and replacing bit one
by its XOR with bit zero. -/
theorem cnotAux_update_iff (x y : Reg 2) :
    x = Function.update y (⟨1, by omega⟩ : Fin 2)
          (y (⟨1, by omega⟩ : Fin 2) ^^ y (⟨0, by omega⟩ : Fin 2))
      ↔ (x 0 = y 0 ∧ x 1 = (y 1 ^^ y 0)) := by
  revert x y
  decide

/-- The encoded CNOT matrix is the indicator of `cnotAux_cnotSupp` on decoded inputs. -/
theorem cnotAux_mpFinCnot_supp (xp yp : Fin 4) :
    mpFinCnot ⟨0, by omega⟩ ⟨1, by omega⟩ xp yp
      = if cnotAux_cnotSupp xp ((bitVecEquiv 2).symm yp) then (1:ℂ) else 0 := by
  rw [cnotAux_mpFinCnot_apply]
  by_cases h : (bitVecEquiv 2).symm xp
      = Function.update ((bitVecEquiv 2).symm yp) (⟨1, by omega⟩ : Fin 2)
          (((bitVecEquiv 2).symm yp) (⟨1, by omega⟩ : Fin 2)
            ^^ ((bitVecEquiv 2).symm yp) (⟨0, by omega⟩ : Fin 2))
  · rw [if_pos h]
    have hi := (cnotAux_update_iff _ _).mp h
    have hb := cnotAux_bv2_bits xp
    have e0 : ((bitVecEquiv 2).symm yp) 0 = ((bitVecEquiv 2).symm xp) 0 := hi.1.symm
    have e1 : ((bitVecEquiv 2).symm yp) 1
        = (((bitVecEquiv 2).symm xp) 1 ^^ ((bitVecEquiv 2).symm yp) 0) := by
      rw [hi.2, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
    have key : cnotAux_cnotSupp xp ((bitVecEquiv 2).symm yp) = true := by
      simp only [cnotAux_cnotSupp]
      rw [← hb.1, ← hb.2]
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨e0, e1⟩
    rw [key]
    rfl
  · rw [if_neg h]
    have hb := cnotAux_bv2_bits xp
    have hi : ¬ (((bitVecEquiv 2).symm xp) 0 = ((bitVecEquiv 2).symm yp) 0
        ∧ ((bitVecEquiv 2).symm xp) 1
            = (((bitVecEquiv 2).symm yp) 1 ^^ ((bitVecEquiv 2).symm yp) 0)) := by
      intro hh
      apply h
      exact (cnotAux_update_iff _ _).mpr hh
    have key : ¬ cnotAux_cnotSupp xp ((bitVecEquiv 2).symm yp) = true := by
      intro hc
      simp only [cnotAux_cnotSupp] at hc
      rw [← hb.1, ← hb.2] at hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact hi ⟨hc.1.symm, by rw [hc.2, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]⟩
    rw [if_neg key]

/-- For each measurement history, the CNOT core is the encoded CNOT matrix scaled by its global
sign divided by four. -/
theorem cnotAux_cnot_core (s : Fin 4 → Bool) :
    core mpCnotPattern (Uniform (Reg 4)) s
      = (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotPhi s) / 4)
          • mpFinCnot ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  ext xp yp
  simp only [core, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul,
    Equiv.refl_symm, Equiv.refl_apply]
  rw [cnotAux_cnot_corePre_closed, cnotAux_mpFinCnot_supp]

/-- Conjugation by a CNOT core equals one sixteenth of conjugation by the encoded CNOT matrix. -/
theorem cnotAux_cnot_core_conj (s : Fin 4 → Bool) (ρ : Operator 4) :
    core mpCnotPattern (Uniform (Reg 4)) s * ρ
        * (core mpCnotPattern (Uniform (Reg 4)) s).conjTranspose
      = (1 / 16 : ℂ)
          • (mpFinCnot ⟨0, by omega⟩ ⟨1, by omega⟩ * ρ
            * (mpFinCnot ⟨0, by omega⟩ ⟨1, by omega⟩).conjTranspose) := by
  rw [cnotAux_cnot_core]
  set c : ℂ := Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotPhi s) / 4 with hc
  have h1 : (c • mpFinCnot ⟨0, by omega⟩ ⟨1, by omega⟩) * ρ
      = c • (mpFinCnot ⟨0, by omega⟩ ⟨1, by omega⟩ * ρ) :=
    cnotAux_smul_mul c _ _
  rw [h1, Matrix.conjTranspose_smul, cnotAux_smul_mul_smul]
  have h3 : c * star c = (1 / 16 : ℂ) := by
    rw [hc]
    have hst : star (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotPhi s))
        = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotPhi s) :=
      cnotAux_star_bitPhase _
    rw [star_div₀, hst, star_ofNat]
    have hsqb : Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotPhi s)
        * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (cnotAux_cnotPhi s) = 1 :=
      Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase_sq _
    rw [div_mul_div_comm, hsqb]
    norm_num
  rw [h3]

/-- The squared measurement-vector product amplitudes of the CNOT pattern sum to one over the
auxiliary bit register. -/
theorem cnotAux_cnot_sv_sum (s : Fin 4 → Bool) :
    ∑ z : Fin 4 → Bool,
      (∏ j : Fin 4, mpSVector (mpAdaptiveAngle mpCnotPattern s j) (s j) (z j))
        * star (∏ j : Fin 4, mpSVector (mpAdaptiveAngle mpCnotPattern s j) (s j) (z j)) = 1 := by
  simp only [cnotAux_cnot_sv]
  have hz : ∀ z : Fin 4 → Bool,
      (∏ j : Fin 4, mpSVector 0 (s j) (z j))
          * star (∏ j : Fin 4, mpSVector 0 (s j) (z j)) = (1 / 16 : ℂ) := by
    intro z
    have hstar : star (∏ j : Fin 4, mpSVector 0 (s j) (z j))
        = ∏ j : Fin 4, star (mpSVector 0 (s j) (z j)) :=
      map_prod (starRingEnd ℂ) (fun j => mpSVector 0 (s j) (z j)) Finset.univ
    rw [hstar, Fin.prod_univ_four, Fin.prod_univ_four]
    have h1 : mpSVector 0 (s 0) (z 0) * star (mpSVector 0 (s 0) (z 0)) = (1 / 2 : ℂ) :=
      sv_zero_sq _ _
    have h2 : mpSVector 0 (s 1) (z 1) * star (mpSVector 0 (s 1) (z 1)) = (1 / 2 : ℂ) :=
      sv_zero_sq _ _
    have h3 : mpSVector 0 (s 2) (z 2) * star (mpSVector 0 (s 2) (z 2)) = (1 / 2 : ℂ) :=
      sv_zero_sq _ _
    have h4 : mpSVector 0 (s 3) (z 3) * star (mpSVector 0 (s 3) (z 3)) = (1 / 2 : ℂ) :=
      sv_zero_sq _ _
    have hmul : (mpSVector 0 (s 0) (z 0) * mpSVector 0 (s 1) (z 1)
          * mpSVector 0 (s 2) (z 2) * mpSVector 0 (s 3) (z 3))
        * (star (mpSVector 0 (s 0) (z 0)) * star (mpSVector 0 (s 1) (z 1))
          * star (mpSVector 0 (s 2) (z 2)) * star (mpSVector 0 (s 3) (z 3)))
        = (mpSVector 0 (s 0) (z 0) * star (mpSVector 0 (s 0) (z 0)))
          * (mpSVector 0 (s 1) (z 1) * star (mpSVector 0 (s 1) (z 1)))
          * (mpSVector 0 (s 2) (z 2) * star (mpSVector 0 (s 2) (z 2)))
          * (mpSVector 0 (s 3) (z 3) * star (mpSVector 0 (s 3) (z 3))) := by
      ring
    rw [hmul, h1, h2, h3, h4]
    norm_num
  simp_rw [hz]
  rw [Finset.sum_const, Finset.card_univ]
  rw [card_reg]
  norm_num

/-- For every measurement history, summing the CNOT pattern's Kraus conjugations over auxiliary
outcomes gives one sixteenth of the CNOT conjugation. -/
theorem cnotAux_clause1b : ∀ (s : Fin 4 → Bool) (ρ : Operator 4),
    ∑ z : Fin 4 → Bool,
        (mpPatternKraus mpCnotPattern (Uniform (Reg 4)) s z) * ρ
          * (mpPatternKraus mpCnotPattern (Uniform (Reg 4)) s z).conjTranspose
      = (1 / 16 : ℂ) •
          (mpFinCnot ⟨0, by omega⟩ ⟨1, by omega⟩ * ρ
            * (mpFinCnot ⟨0, by omega⟩ ⟨1, by omega⟩).conjTranspose) := by
  intro s ρ
  have hkey : ∀ z : Fin 4 → Bool,
      (mpPatternKraus mpCnotPattern (Uniform (Reg 4)) s z) * ρ
          * (mpPatternKraus mpCnotPattern (Uniform (Reg 4)) s z).conjTranspose
        = ((∏ j : Fin 4, mpSVector (mpAdaptiveAngle mpCnotPattern s j) (s j) (z j))
            * star (∏ j : Fin 4, mpSVector (mpAdaptiveAngle mpCnotPattern s j) (s j) (z j)))
            • (core mpCnotPattern (Uniform (Reg 4)) s * ρ
                * (core mpCnotPattern (Uniform (Reg 4)) s).conjTranspose) := by
    intro z
    rw [kraus_eq_smul_core, Matrix.conjTranspose_smul, cnotAux_smul_mul, cnotAux_smul_mul_smul]
  simp_rw [hkey]
  rw [← Finset.sum_smul, cnotAux_cnot_sv_sum, one_smul]
  exact cnotAux_cnot_core_conj s ρ
end Qatlib.Concepts.ClusterPatterns.CnotPatterns
