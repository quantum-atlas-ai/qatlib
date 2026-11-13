/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-!
# VariableTimeComplexity

The `_statement` definitions are unproved resource specifications requiring an
implementation relation. Numeric records alone do not certify execution or correctness.
No quantum circuit synthesis is proved here.
The remaining theorems prove only their displayed algebraic inequalities or identities.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.BlockEncMatPw18.MainResults.Amplification

/- ## c009 — Corollary 19 -/

/-- Corollary 19's cost from uses of the variable-time algorithm `A`:
`E·O(T_max + I/√p_succ)`. -/
def cor19Cost (E O Tmax I p : ℝ) : ℝ :=
  E * O * (Tmax + I / Real.sqrt p)

/-- Corollary 19's additional elementary-gate cost:
`E·G·O(T_max + I/√p_succ)`. -/
def cor19GateCost (E G O Tmax I p : ℝ) : ℝ :=
  E * G * O * (Tmax + I / Real.sqrt p)

/-- Monotonicity of the displayed cost expressions under a supplied bound on `I`.
No amplification algorithm or boundedness contract is constructed. -/
theorem cor19_complexity_bound (E G O Tmax psucc I t1 T2 : ℝ)
    (hE : 0 ≤ E) (hG : 0 ≤ G) (hO : 0 ≤ O)
    (hp : 0 < psucc) (_ht1 : 0 < t1) (_hT2 : 0 ≤ T2)
    (hI : I ≤ t1 + T2 * Real.sqrt (Real.log (Tmax / t1))) :
    cor19Cost E O Tmax I psucc ≤
        cor19Cost E O Tmax (t1 + T2 * Real.sqrt (Real.log (Tmax / t1))) psucc ∧
      cor19GateCost E G O Tmax I psucc ≤
        cor19GateCost E G O Tmax (t1 + T2 * Real.sqrt (Real.log (Tmax / t1))) psucc := by
  classical
  by_cases _htriv : (0 < t1 ∧ 0 ≤ T2)
  swap
  · exact False.elim (_htriv ⟨_ht1, _hT2⟩)
  have hsqrt : 0 < Real.sqrt psucc := Real.sqrt_pos.2 hp
  have hI' : I / Real.sqrt psucc ≤
      (t1 + T2 * Real.sqrt (Real.log (Tmax / t1))) / Real.sqrt psucc :=
    div_le_div_of_nonneg_right hI hsqrt.le
  have hinner : Tmax + I / Real.sqrt psucc ≤
      Tmax + (t1 + T2 * Real.sqrt (Real.log (Tmax / t1))) / Real.sqrt psucc := by
    linarith [hI']
  constructor
  · exact mul_le_mul_of_nonneg_left hinner (mul_nonneg hE hO)
  · exact mul_le_mul_of_nonneg_left hinner (mul_nonneg (mul_nonneg hE hG) hO)

/- ## c012 — Lemma 22 -/

/-- Lemma 22's query complexity:
`O(T_max √m + ‖T‖₂ √(log(2 T_max/t₁)) √m / √p_succ)`. -/
def lemma22Cost (Tmax Tm2 t1 m psucc : ℝ) : ℝ :=
  Tmax * Real.sqrt m +
    Tm2 * Real.sqrt (Real.log (2 * Tmax / t1)) * Real.sqrt m / Real.sqrt psucc

/-- Algebraic identity for `lemma22Cost`, using the constant one.
This proves no query complexity bound for an implemented algorithm. -/
theorem lemma22_query_complexity (Tmax Tm2 t1 m psucc : ℝ)
    (hTmax : 0 ≤ Tmax) (hTm2 : 0 ≤ Tm2) (ht1 : 0 < t1) (hm : 0 ≤ m)
    (hp : 0 < psucc) :
    ∃ (C : ℝ), 0 < C ∧
      lemma22Cost Tmax Tm2 t1 m psucc ≤
        C * (Tmax * Real.sqrt m +
          Tm2 * Real.sqrt (Real.log (2 * Tmax / t1)) * Real.sqrt m /
            Real.sqrt psucc) := by
  classical
  by_cases _htriv : (0 ≤ Tmax ∧ 0 ≤ Tm2 ∧ 0 < t1 ∧ 0 ≤ m ∧ 0 < psucc)
  swap
  · exact False.elim (_htriv ⟨hTmax, hTm2, ht1, hm, hp⟩)
  refine ⟨1, zero_lt_one, ?_⟩
  unfold lemma22Cost
  rw [one_mul]

/- ## c013 — Theorem 23 -/

/-- Theorem 23's query count
`Q = (T_max + (T_U + k)/√p_prep) √(log T_max')
 + ((‖T‖₂ + (T_U + k)/√p_prep) log T_max')/√p_succ`, with `T_max' = 2T_max/t₁`. -/
def thm23Q (Tmax t1 TU k pprep psucc Tm2 : ℝ) : ℝ :=
  let Tmax' := 2 * Tmax / t1
  (Tmax + (TU + k) / Real.sqrt pprep) * Real.sqrt (Real.log Tmax') +
    ((Tm2 + (TU + k) / Real.sqrt pprep) * Real.log Tmax') / Real.sqrt psucc

/-- Legacy numeric metadata for the Theorem 23 specification. No execution,
amplitude semantics or success event is contained in this record. -/
structure VTAAResult where
  successProb : ℝ
  amplitude : ℝ
  cost : ℝ
  classicalQuery : ℝ
  mindfulCost : ℝ
  error : ℝ

/-- **Statement only — not proved in Qatlib.** Resource specification for `theorem23_variable_time_amplification`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def theorem23_variable_time_amplification_statement
    (Tmax t1 TU k pprep psucc Tm2 δ : ℝ)
    (hTmax : 0 < Tmax) (ht1 : 0 < t1) (hTU : 0 ≤ TU) (hk : 0 ≤ k)
    (hpprep : 0 < pprep) (hpsucc : 0 < psucc) (hTm2 : 0 ≤ Tm2)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (Realizes : VTAAResult → Prop) : Prop :=
    ∃ (r : VTAAResult) (C : ℝ), Realizes r ∧ 0 < C ∧
      r.successProb ≥ 1 - δ ∧ r.error ≤ δ ∧
      (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ c₁ ≤ r.amplitude ∧ r.amplitude ≤ c₂) ∧
      r.cost ≤ C * thm23Q Tmax t1 TU k pprep psucc Tm2 ∧
      r.classicalQuery ≤ C * thm23Q Tmax t1 TU k pprep psucc Tm2 *
        Real.log (2 * Tmax / t1) *
        Real.log (1 / δ * Real.log (2 * Tmax / t1 / (pprep * psucc)))

end Qatlib.Papers.BlockEncMatPw18.MainResults.Amplification
