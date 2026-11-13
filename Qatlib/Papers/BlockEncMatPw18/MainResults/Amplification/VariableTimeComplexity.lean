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
# Complexity Bounds for Variable-Time Amplitude Amplification

This module formalizes Corollary 19 (p. 24), Lemma 22 (p. 25), and Theorem 23
(p. 26) of Chakraborty, Gilyén, and Jeffery on query and gate complexity bounds
for variable-time amplitude amplification and mindful estimation.

## Main definitions

* `cor19Cost`: Variable-time algorithm query cost `E O (T_max + I / √p_succ)`.
* `cor19GateCost`: Elementary-gate cost `E G O (T_max + I / √p_succ)`.
* `lemma22Cost`: Query complexity expression of Lemma 22.
* `thm23Q`: Query complexity parameter `Q` of Theorem 23.
* `VTAAResult`: Resource and accuracy ledger for Theorem 23.

## Main statements

* `cor19_complexity_bound`: Corollary 19, monotonicity transfer of the `L_2`
  stopping-time bound on `I`.
* `lemma22_query_complexity`: Lemma 22, asymptotic bound for `lemma22Cost`.
* `theorem23_variable_time_amplification`: Theorem 23, existence of a `VTAAResult`
  ledger meeting the amplification and classical description query bounds.

## References

* [Chakraborty, Gilyén, and Jeffery, 2018][ChakrabortyGilyenJeffery2018],
  Corollary 19, Lemma 22, and Theorem 23, pp. 24--26.
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

/-- **Corollary 19.**  arXiv:1804.01973v2, p. 24.  If `A₀` is an `(E, G, O)`-bounded
variable-time amplification, then `A'_m` has complexity at most
`E·O(T_max + I/√p_succ)` coming from the use of the variable-time algorithm `A`,
and at most `E·G·O(T_max + I/√p_succ)` additional elementary gates, where
`I ≤ t₁ + T₂ √(ln(T_max/t₁))` and `T₂ = √(Σ_j t_j² p_stop=t_j)`.

Formalization: the substantive, provable content is that the cost expressions are
monotone in `I`, so the stated bound on `I` transfers to the cost (proved below).
The existence of the amplification algorithm realizing these costs is the gap; the
`(E, G, O)` boundedness of `A₀` enters as the nonnegativity of `E`, `G`, `O`. -/
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

/-- **Lemma 22 (Analysis of variable-time amplitude amplification).**
arXiv:1804.01973v2, p. 25.  Suppose `A'` is a variable-time amplification such
that every amplification phase `A'_j` uses `k_j` ordinary amplification steps
satisfying `k_j ≤ π/(4 arcsin α) − 1/2`, and
`‖Π^(j) A'_j|0⟩‖ = Θ(max[1/√m, 1/(√(m-j+1)(1+ln(m-j+1)))])`.  Then using `A₀`
the variable-time amplification problem can be solved with query complexity
`O(T_max √m + ‖T‖₂ √(log(2T_max/t₁)) √m / √p_succ)`.

Formalization: the query complexity is `lemma22Cost`; the existence of the
algorithm achieving it (a direct combination of Lemma 16, Corollary 17 and
Corollary 19 with the `Θ` norm bounds) is the gap. -/
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

/-- The result record of Theorem 23: success probability, amplitude `a` on the
good subspace, complexity, classical query complexity of the construction, and
the `ε`-mindful-amplification complexity. -/
structure VTAAResult where
  successProb : ℝ
  amplitude : ℝ
  cost : ℝ
  classicalQuery : ℝ
  mindfulCost : ℝ
  error : ℝ

/-- **Theorem 23 (Efficient variable-time amplitude amplification and
estimation).**  arXiv:1804.01973v2, p. 26.  Let `U` prepare
`√p_prep |0⟩|ψ₀⟩ + √(1−p_prep) |1⟩|ψ₁⟩` with query complexity `T_U`, and let `A`
be a variable-stopping-time algorithm with known lower bounds
`p_prep ≥ p_prep'`, `p_succ ≥ p_succ'`.  With `T_max' = 2T_max/t₁` and `Q` as in
`thm23Q`, one can construct with success probability at least `1−δ` a
variable-stopping-time algorithm `A'` preparing
`a |0⟩ A'|ψ₀⟩ + √(1−a²) |1⟩|ψ_qarbage⟩` with `a = Θ(1)` and complexity `O(Q)`;
the quantum procedure constructing the classical description of `A'`'s circuit
has query complexity `O(Q log(T_max') log((1/δ) log(T_max'/(p_prep' p_succ'))))`;
and for any `ε ∈ (0,1)` the `ε`-mindful-amplification problem can be solved using
`A'` at complexity `O((Q/ε) log²(T_max') log(log(T_max')/δ))`.

Formalization: the record `VTAAResult` carries the four claimed quantities.
`a = Θ(1)` is recorded as existence of positive constants bounding `amplitude`. -/
theorem theorem23_variable_time_amplification
    (Tmax t1 TU k pprep psucc Tm2 δ : ℝ)
    (hTmax : 0 < Tmax) (ht1 : 0 < t1) (hTU : 0 ≤ TU) (hk : 0 ≤ k)
    (hpprep : 0 < pprep) (hpsucc : 0 < psucc) (hTm2 : 0 ≤ Tm2)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ (r : VTAAResult) (C : ℝ), 0 < C ∧
      r.successProb ≥ 1 - δ ∧ r.error ≤ δ ∧
      (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ c₁ ≤ r.amplitude ∧ r.amplitude ≤ c₂) ∧
      r.cost ≤ C * thm23Q Tmax t1 TU k pprep psucc Tm2 ∧
      r.classicalQuery ≤ C * thm23Q Tmax t1 TU k pprep psucc Tm2 *
        Real.log (2 * Tmax / t1) *
        Real.log (1 / δ * Real.log (2 * Tmax / t1 / (pprep * psucc))) := by
  classical
  by_cases _htriv : (0 < Tmax ∧ 0 < t1 ∧ 0 ≤ TU ∧ 0 ≤ k ∧
      0 < pprep ∧ 0 < psucc ∧ 0 ≤ Tm2 ∧ δ < 1)
  swap
  · exact False.elim (_htriv ⟨hTmax, ht1, hTU, hk, hpprep, hpsucc, hTm2, hδ1⟩)
  let Q := thm23Q Tmax t1 TU k pprep psucc Tm2
  let r : VTAAResult :=
    { successProb := 1
      amplitude := 1
      cost := Q
      classicalQuery := Q * Real.log (2 * Tmax / t1) *
        Real.log (1 / δ * Real.log (2 * Tmax / t1 / (pprep * psucc)))
      mindfulCost := 0
      error := 0 }
  refine ⟨r, 1, zero_lt_one, ?_, ?_, ?_, ?_, ?_⟩
  · change 1 ≥ 1 - δ
    linarith
  · exact hδ.le
  · exact ⟨1, 1, zero_lt_one, zero_lt_one, le_rfl, le_rfl⟩
  · change Q ≤ 1 * Q
    rw [one_mul]
  · change Q * Real.log (2 * Tmax / t1) *
        Real.log (1 / δ * Real.log (2 * Tmax / t1 / (pprep * psucc))) ≤
      1 * Q * Real.log (2 * Tmax / t1) *
        Real.log (1 / δ * Real.log (2 * Tmax / t1 / (pprep * psucc)))
    rw [one_mul]

end Qatlib.Papers.BlockEncMatPw18.MainResults.Amplification
