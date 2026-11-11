/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# LearningGraphStages — the stage calculus of reduced learning graphs

Belovs, *Span Programs for Functions with Constant-Sized 1-certificates*,
fixed arXiv:1105.4024v1 (20 May 2011), PDF SHA-256
`315b5768c635ceee578e1ed2879a53a210c73c53a43bd0d0430041f9faa4e552`.

Section 4 and Section 5 of the paper split a reduced learning graph into `k = O(1)`
stages. A stage `i` carries transitions `E_i` with a length `ℓ(e)`, a weight `w_e` and,
for every 1-input `x`, a flow `p_e(x)`; its complexity is

`C_i = max_x sqrt((Σ_{e ∈ E_i} ℓ(e) w_e) (Σ_{e ∈ E_i} ℓ(e) p_e(x)^2 / w_e))`,

the geometric mean of the negative and the positive complexity of the stage. This file
formalises the three quantitative statements the paper proves about these stages:

* §4, Proposition 5: the stage decomposition `O(C_1 + ⋯ + C_k)`;
* §5.1, Theorem 6: a flow that is symmetric on stage `i` gives `C_i ≤ L_i sqrt(T_i)`;
* §5.2, Theorem 7: a flow that is symmetric for the vertex set `V_k` gives `C ≤ L sqrt(T)`.

The statements are kept at the level of finite sums: they are exactly the inequalities
displayed in the proofs of the paper, with `L_i = Σ_e ℓ(e) p_e` the average stage length
and `T_i` (resp. `T`) the maximal speciality. No counting or linear algebra is hidden in
the hypotheses.

One point of the printed proof is repaired rather than copied. Theorem 6 sets the weight
of a transition to `p'(e) = τ(e) p_e`, but the displayed computation then evaluates
`Σ_e ℓ(e) p'(e)` and `Σ_e ℓ(e) p_e²/p'(e)` as `Σ_e ℓ(e) τ(e) p_e` and `Σ_e ℓ(e) p_e`,
which cannot both hold. The second factor is actually `Σ_e ℓ(e) p_e/τ(e)`. Both factors
are still bounded by `L_i` and `T_i L_i` because `1 ≤ τ(e) ≤ T_i`, so the stated
conclusion `C_i ≤ L_i √T_i` is unchanged; the formalised proof uses the correct
`Σ_e ℓ(e) p_e/τ(e)`.

Boundary: this file covers the stage-level complexity estimates only. The construction of
the span program from the learning graph and the resulting quantum query algorithm
(Section 3.3, Theorem 3) are not part of it.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpanPrograms11.MainResults

/-- Negative complexity `Σ_e ℓ(e) w_e` of a set of transitions (paper §3.1). -/
def negativeComplexity {E : Type*} (s : Finset E) (len w : E → ℝ) : ℝ :=
  ∑ e ∈ s, len e * w e

/-- Positive complexity `Σ_e ℓ(e) p_e ^ 2 / w_e` of a set of transitions (paper §3.1). -/
def positiveComplexity {E : Type*} (s : Finset E) (len p w : E → ℝ) : ℝ :=
  ∑ e ∈ s, len e * p e ^ 2 / w e

/-- Complexity `sqrt(N_i * P_i)` of a single stage (paper §4). -/
def stageComplexity (neg pos : ℝ) : ℝ := Real.sqrt (neg * pos)

/-- `sqrt (Σ a_i) ≤ Σ sqrt (a_i)` for nonnegative summands. -/
theorem sqrt_sum_le_sum_sqrt {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    Real.sqrt (∑ i ∈ s, a i) ≤ ∑ i ∈ s, Real.sqrt (a i) := by
  have hsum : 0 ≤ ∑ i ∈ s, Real.sqrt (a i) :=
    Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  refine (Real.sqrt_le_left hsum).2 ?_
  calc ∑ i ∈ s, a i = ∑ i ∈ s, Real.sqrt (a i) ^ 2 := by
        exact Finset.sum_congr rfl fun i hi => (Real.sq_sqrt (ha i hi)).symm
    _ ≤ (∑ i ∈ s, Real.sqrt (a i)) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => Real.sqrt_nonneg _

/-- Algebraic core shared by Theorem 6 and Theorem 7: transitions of length `ℓ e`, shared
flow value `p e`, speciality `spec e` and transition weight `w e = spec e * p e` give a
stage complexity of at most `(Σ e, ℓ e * p e) * sqrt T` whenever `1 ≤ spec e ≤ T`. -/
theorem stage_bound_core {E : Type*} (s : Finset E) (len p spec : E → ℝ) (T : ℝ)
    (hlen : ∀ e ∈ s, 0 ≤ len e) (hp : ∀ e ∈ s, 0 < p e)
    (hspec : ∀ e ∈ s, 1 ≤ spec e) (hspecT : ∀ e ∈ s, spec e ≤ T) (hT : 0 ≤ T) :
    stageComplexity (negativeComplexity s len fun e => spec e * p e)
        (positiveComplexity s len p fun e => spec e * p e)
      ≤ (∑ e ∈ s, len e * p e) * Real.sqrt T := by
  set L : ℝ := ∑ e ∈ s, len e * p e with hL
  have hL0 : 0 ≤ L :=
    Finset.sum_nonneg fun e he => mul_nonneg (hlen e he) (le_of_lt (hp e he))
  have hN : negativeComplexity s len (fun e => spec e * p e) ≤ T * L := by
    rw [negativeComplexity, hL, Finset.mul_sum]
    refine Finset.sum_le_sum fun e he => ?_
    have hstep : len e * (spec e * p e) ≤ len e * (T * p e) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hspecT e he) (le_of_lt (hp e he))) (hlen e he)
    calc len e * (spec e * p e) ≤ len e * (T * p e) := hstep
      _ = T * (len e * p e) := by ring
  have hP : positiveComplexity s len p (fun e => spec e * p e) ≤ L := by
    rw [positiveComplexity, hL]
    refine Finset.sum_le_sum fun e he => ?_
    have hsp : 0 < spec e := lt_of_lt_of_le zero_lt_one (hspec e he)
    have hpe : 0 < p e := hp e he
    have hdiv : len e * p e ^ 2 / (spec e * p e) = len e * p e / spec e := by
      field_simp
    rw [hdiv]
    have hmono : len e * p e / spec e ≤ len e * p e / 1 :=
      div_le_div_of_nonneg_left (mul_nonneg (hlen e he) (le_of_lt hpe)) zero_lt_one
        (hspec e he)
    simpa using hmono
  have hN0 : 0 ≤ negativeComplexity s len (fun e => spec e * p e) :=
    Finset.sum_nonneg fun e he =>
      mul_nonneg (hlen e he)
        (mul_nonneg (le_trans zero_le_one (hspec e he)) (le_of_lt (hp e he)))
  have hP0 : 0 ≤ positiveComplexity s len p (fun e => spec e * p e) :=
    Finset.sum_nonneg fun e he => div_nonneg (mul_nonneg (hlen e he) (sq_nonneg _))
      (mul_nonneg (le_trans zero_le_one (hspec e he)) (le_of_lt (hp e he)))
  rw [stageComplexity]
  have hupper : negativeComplexity s len (fun e => spec e * p e)
      * positiveComplexity s len p (fun e => spec e * p e) ≤ T * L ^ 2 := by
    calc negativeComplexity s len (fun e => spec e * p e)
          * positiveComplexity s len p (fun e => spec e * p e)
        ≤ (T * L) * positiveComplexity s len p (fun e => spec e * p e) :=
          mul_le_mul_of_nonneg_right hN hP0
      _ ≤ (T * L) * L := mul_le_mul_of_nonneg_left hP (mul_nonneg hT hL0)
      _ = T * L ^ 2 := by ring
  calc Real.sqrt (negativeComplexity s len (fun e => spec e * p e)
        * positiveComplexity s len p (fun e => spec e * p e))
      ≤ Real.sqrt (T * L ^ 2) := Real.sqrt_le_sqrt hupper
    _ = L * Real.sqrt T := by
        rw [Real.sqrt_mul hT (L ^ 2), Real.sqrt_sq hL0]
        ring

/-- Paper §5.1, Theorem 6. Assume the flow is symmetric on stage `i`: the speciality
`spec e` of an equivalence class does not depend on the input and the flow `p e` through
all valid transitions of a class is a common value. Then the complexity of the stage is at
most `L_i * sqrt(T_i)`, where `L_i = Σ_e ℓ(e) p_e` is the average length of the stage and
`T_i` is the maximal speciality of a transition of the stage. -/
theorem symmetric_flow_stage_bound {E : Type*} (s : Finset E) (len p spec : E → ℝ) (T : ℝ)
    (hlen : ∀ e ∈ s, 0 ≤ len e) (hp : ∀ e ∈ s, 0 < p e)
    (hspec : ∀ e ∈ s, 1 ≤ spec e) (hspecT : ∀ e ∈ s, spec e ≤ T) (hT : 0 ≤ T) :
    stageComplexity (negativeComplexity s len fun e => spec e * p e)
        (positiveComplexity s len p fun e => spec e * p e)
      ≤ (∑ e ∈ s, len e * p e) * Real.sqrt T :=
  stage_bound_core s len p spec T hlen hp hspec hspecT hT

/-- Paper §5.2, Theorem 7. Suppose the flow is symmetric for the vertex set `V_k` that
starts the subroutine stage: `sub v` is the complexity `ℓ(v)` of the subroutine appended to
the valid vertex `v`, `p v` its flow and `spec v` the speciality of the vertex. Then the
complexity of the subroutine stage is `L * sqrt(T)`, where `L = Σ_v p_v ℓ(v)` is the
average complexity of the appended subroutines and `T` is the maximal speciality of a
vertex of `V_k`. -/
theorem symmetric_flow_subroutine_bound {V : Type*} (s : Finset V) (sub p spec : V → ℝ)
    (T : ℝ) (hlen : ∀ v ∈ s, 0 ≤ sub v) (hp : ∀ v ∈ s, 0 < p v)
    (hspec : ∀ v ∈ s, 1 ≤ spec v) (hspecT : ∀ v ∈ s, spec v ≤ T) (hT : 0 ≤ T) :
    stageComplexity (negativeComplexity s sub fun v => spec v * p v)
        (positiveComplexity s sub p fun v => spec v * p v)
      ≤ (∑ v ∈ s, sub v * p v) * Real.sqrt T :=
  stage_bound_core s sub p spec T hlen hp hspec hspecT hT

/-- Paper §4, Proposition 5. A reduced learning graph with `k` stages of complexities
`C_i = sqrt(N_i P_i)` yields a learning graph of complexity `O(C_1 + ⋯ + C_k)`: dividing
the weights of stage `i` by `N_i` makes its negative complexity `1` and its positive
complexity `N_i P_i`, so the whole graph has negative complexity `k` and complexity
`sqrt(k * Σ_i N_i P_i) ≤ sqrt(k) * Σ_i C_i`. -/
theorem stage_decomposition (k : ℕ) (N P : Fin k → ℝ)
    (hN : ∀ i, 0 < N i) (hP : ∀ i, 0 ≤ P i) :
    Real.sqrt ((k : ℝ) * ∑ i, N i * P i)
      ≤ Real.sqrt (k : ℝ) * ∑ i, Real.sqrt (N i * P i) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h1 : Real.sqrt (∑ i, N i * P i) ≤ ∑ i, Real.sqrt (N i * P i) :=
    sqrt_sum_le_sum_sqrt Finset.univ (fun i => N i * P i)
      fun i _ => mul_nonneg (le_of_lt (hN i)) (hP i)
  calc Real.sqrt ((k : ℝ) * ∑ i, N i * P i)
      = Real.sqrt (k : ℝ) * Real.sqrt (∑ i, N i * P i) := Real.sqrt_mul hk _
    _ ≤ Real.sqrt (k : ℝ) * ∑ i, Real.sqrt (N i * P i) :=
        mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)

end Qatlib.Papers.SpanPrograms11.MainResults
