/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

set_option backward.isDefEq.respectTransparency false

/-!
# QDynamics10.MainResults — source model

Wiebe--Berry--Høyer--Sanders, *Simulating Quantum Dynamics On A Quantum Computer*,
arXiv:1011.3489v1 (fixed. PDF SHA not recorded by the extraction pipeline; the text used is
`assets/1011.3489.txt`, sections III--VIII and Appendices A--B).

This module fixes the paper's parameter vocabulary so that every active claim can be stated
against one shared, concrete model:

* `d`-sparse matrices (Sec. V A), `P`-smooth / `Λ`-`P`-smooth / `Υ`-`P`-pointwise-smooth
  families (Definitions 2--4, p. 5);
* the Lie--Trotter--Suzuki integrator bookkeeping `12 M d² 5^{k−1}` exponentials per step
  (p. 11 and proof of Theorem 8) and the step count `r` of Eq. (12);
* the precision-bit quantities of Eq. (14), the exponential/query-count bounds of
  Eqs. (25), (27), (48), (50);
* the product-difference inequality of Eq. (38) (from Ref. [15] Eq. (4.69)).

The model is deliberately quantitative: it records the paper's explicit formulas instead of
big-O summaries, so that the arithmetic of the paper's derivations is checkable. The
paper itself states its headline results asymptotically in the parameter tuple of Eq. (18);
where a constant absorbing step needs "parameters sufficiently large", the corresponding
hypothesis is stated explicitly in the claim file and tied to Eq. (18) there.

Boundary: this file does not model quantum circuits, oracles `QCol`/`QMatrixVal`, or the
BACS decomposition itself; those are handled (and documented) in the per-claim files.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDynamics10.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

/-! ## Sparsity and smoothness (Sec. III--V, Definitions 2--4) -/

/-- `d`-sparse matrix: at most `d` non-zero entries in every row and every column
(paper Sec. V A, "d-sparse"). -/
def DSparse {I : Type} [Fintype I] [DecidableEq I] (d : ℕ) (H : Matrix I I ℂ) : Prop :=
  (∀ x, (Finset.univ.filter (fun y => H x y ≠ 0)).card ≤ d) ∧
  (∀ y, (Finset.univ.filter (fun x => H x y ≠ 0)).card ≤ d)

/-- Definition 3 (p. 5): the family `{H_j}` is `Λ`-`P`-smooth on the interval of interest
when `(∑_j ‖H_j^{(p)}(t)‖)^{1/(p+1)} ≤ Λ` for all times `t` and all `p ≤ P`. -/
def LambdaSmooth {I : Type} [Fintype I] [DecidableEq I] {M : ℕ}
    (Λ : ℝ) (P : ℕ) (H : Fin M → ℝ → Matrix I I ℂ) : Prop :=
  ∀ (t : ℝ) (p : ℕ), p ≤ P →
    (∑ j, ‖iteratedDeriv p (H j) t‖) ^ (1 / ((p : ℝ) + 1)) ≤ Λ

/-- Definition 4 (p. 5): the family `{H_j}` is `Υ`-`P`-pointwise-smooth when
`(∑_j ‖H_j^{(p)}(t)‖)^{1/(p+1)} ≤ Υ(t)` for all `t` and all `p ≤ P`. -/
def UpsilonPointwiseSmooth {I : Type} [Fintype I] [DecidableEq I] {M : ℕ}
    (Υ : ℝ → ℝ) (P : ℕ) (H : Fin M → ℝ → Matrix I I ℂ) : Prop :=
  ∀ (t : ℝ) (p : ℕ), p ≤ P →
    (∑ j, ‖iteratedDeriv p (H j) t‖) ^ (1 / ((p : ℝ) + 1)) ≤ Υ t

/-! ## Integrator bookkeeping -/

/-- The number of one-sparse exponentials in one `k`-th order Lie--Trotter--Suzuki step
for `M` `d`-sparse terms: `12 M d² 5^{k−1}` (p. 11, and proof of Theorem 8 on p. 14). -/
def stepExponentials (M d k : ℕ) : ℕ := 12 * M * d ^ 2 * 5 ^ (k - 1)

/-- Eq. (12) (p. 6): the number of short intervals `r` needed for integrator error at most
`ε`, `r = ⌈ 2 ε^{-1/2k} (2k (5/3)^{k-1} Λ Δt)^{1 + 1/2k} ⌉`. -/
def lieTrotterSteps (k : ℕ) (Λ Δt ε : ℝ) : ℕ :=
  Nat.ceil (2 * ε ^ (-(1 : ℝ) / ((2 : ℝ) * (k : ℝ)))
    * ((2 : ℝ) * (k : ℝ) * ((5 : ℝ) / 3) ^ (k - 1) * Λ * Δt)
      ^ (1 + 1 / ((2 : ℝ) * (k : ℝ))))

/-! ## Precision bits (Eq. (14), p. 6) -/

/-- Eq. (14), first line: the time-precision bit count `n_t`. -/
def timePrecisionBits (k M d : ℕ) (Xmax Δt ε : ℝ) : ℕ :=
  Nat.ceil (Real.logb 2
    (Xmax * ((32 : ℝ) * (k : ℝ) * (M : ℝ) * ((d : ℝ) ^ 2)) * ((5 : ℝ) / 3) ^ (k - 1)
      * Δt ^ 2 / ε))

/-- Eq. (14), second line: the matrix-element precision bit count `n_H`. -/
def matrixPrecisionBits (k M d : ℕ) (Λmax Δt ε : ℝ) : ℕ :=
  2 * Nat.ceil (Real.logb 2
    (((32 : ℝ) * (k : ℝ) * (M : ℝ) * ((d : ℝ) ^ 2)) * ((5 : ℝ) / 3) ^ (k - 1)
      * Λmax * Δt / ε)) + 6

/-! ## Query-count formulas (Eqs. (25), (27), (48), (50)) -/

/-- The ceiling argument of Eq. (26)/(27) after the substitution `m = 6 M d²`
(up to the constant-absorbing rewrite performed between (26) and (27)). -/
def nExpCeilArg (k d : ℕ) (Λ Δt εt : ℝ) : ℝ :=
  (12 : ℝ) * (k : ℝ) * ((d : ℝ) ^ 2) * Λ * Δt * ((5 : ℝ) / 3) ^ (k - 1)
    * (6 * ((d : ℝ) ^ 2) * Λ * Δt / (εt / 2)) ^ (1 / ((2 : ℝ) * (k : ℝ)))

/-- Eq. (27): `N_exp = 12 M d² 5^{k−1} ⌈ nExpCeilArg ⌉`. -/
def nExpCount (M d k : ℕ) (Λ Δt εt : ℝ) : ℕ :=
  stepExponentials M d k * Nat.ceil (nExpCeilArg k d Λ Δt εt)

/-- The ceiling argument of Eq. (25): the constant-absorbed form
`24 k d² Λ Δt (5/3)^k (6 d² Λ Δt/(ε̃/2))^{1/2k}`. -/
def queryCostCeilArg (k d : ℕ) (Λ Δt εt : ℝ) : ℝ :=
  (24 : ℝ) * (k : ℝ) * ((d : ℝ) ^ 2) * Λ * Δt * ((5 : ℝ) / 3) ^ k
    * (6 * ((d : ℝ) ^ 2) * Λ * Δt / (εt / 2)) ^ (1 / ((2 : ℝ) * (k : ℝ)))

/-- Right-hand side of Eq. (25)/(31): `12 C M d² 5^{k−1} ⌈ queryCostCeilArg ⌉`. -/
def queryCostBound (C M d k : ℕ) (Λ Δt εt : ℝ) : ℕ :=
  stepExponentials M d k * C * Nat.ceil (queryCostCeilArg k d Λ Δt εt)

/-- Eq. (49): the leading term `A` of the adaptive step count. -/
def adaptiveLeadingTerm (k d : ℕ) (Υbar Δt ε : ℝ) : ℝ :=
  ((24 : ℝ) * ((d : ℝ) ^ 2) * ((k : ℝ) * ((5 : ℝ) / 3) ^ (k - 1)) * Υbar * Δt)
      ^ (1 + 1 / ((2 : ℝ) * (k : ℝ))) / ε ^ (1 / ((2 : ℝ) * (k : ℝ)))

/-- Eq. (50): the adaptive step bound `r_g = ⌈ A + 3 K² Ῡ Δt + 1 ⌉`. -/
def adaptiveStepBound (k d : ℕ) (Υbar K Δt ε : ℝ) : ℕ :=
  Nat.ceil (adaptiveLeadingTerm k d Υbar Δt ε + 3 * K ^ 2 * Υbar * Δt + 1)

/-- The ceiling argument of Eq. (48), which uses `(ε/4)^{1/2k}` in place of `ε^{1/2k}`. -/
def adaptiveCostCeilArg (k d : ℕ) (Υbar K Δt ε : ℝ) : ℝ :=
  ((24 : ℝ) * ((d : ℝ) ^ 2) * ((k : ℝ) * ((5 : ℝ) / 3) ^ (k - 1)) * Υbar * Δt)
      ^ (1 + 1 / ((2 : ℝ) * (k : ℝ))) / (ε / 4) ^ (1 / ((2 : ℝ) * (k : ℝ)))
    + 3 * K ^ 2 * Υbar * Δt + 1

/-- Right-hand side of Eq. (48): `12 C M d² 5^{k−1} ⌈ adaptiveCostCeilArg ⌉`. -/
def adaptiveQueryCostBound (C M d k : ℕ) (Υbar K Δt ε : ℝ) : ℕ :=
  stepExponentials M d k * C * Nat.ceil (adaptiveCostCeilArg k d Υbar K Δt ε)

/-! ## Error vocabulary -/

/-- The paper's "the evolution can be simulated within error `ε`": the simulated unitary is
within operator-norm distance `ε` of the exact propagator (Sec. IV, "within error ε"). -/
def SimulatedWithinError {I : Type} [Fintype I] [DecidableEq I]
    (Uexact Usim : Matrix I I ℂ) (ε : ℝ) : Prop := ‖Uexact - Usim‖ ≤ ε

/-- In a C*-algebra the unit has norm at most one (`‖1‖² ≤ ‖1⋆1‖ = ‖1‖`). -/
theorem cstar_norm_one_le {E : Type*} [NormedRing E] [StarRing E] [CStarRing E] :
    ‖(1 : E)‖ ≤ 1 := by
  have h := CStarRing.norm_mul_self_le (1 : E)
  rw [star_one, one_mul] at h
  nlinarith [norm_nonneg (1 : E)]

/-- The unit of the matrix algebra under the L2 operator norm (a C*-norm) has norm at most
one. This replaces a `NormOneClass` instance, which Mathlib does not provide for the
scoped `Matrix.Norms.L2Operator` norm. -/
theorem matrix_norm_one_le {I : Type} [Fintype I] [DecidableEq I] :
    ‖(1 : Matrix I I ℂ)‖ ≤ 1 :=
  cstar_norm_one_le

/-- A product of norm-at-most-one factors has norm at most one. -/
theorem prod_norm_le_one {E : Type*} [NormedRing E]
    (hone : ‖(1 : E)‖ ≤ 1) (l : List E) (h : ∀ x ∈ l, ‖x‖ ≤ 1) : ‖l.prod‖ ≤ 1 := by
  induction l with
  | nil => simpa using hone
  | cons a l ih =>
    have ha : ‖a‖ ≤ 1 := h a (by simp)
    have hl : ‖l.prod‖ ≤ 1 := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    calc ‖(a :: l).prod‖ = ‖a * l.prod‖ := by simp
      _ ≤ ‖a‖ * ‖l.prod‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul ha hl (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num

/-- Eq. (38) (from Ref. [15] Eq. (4.69)): for products of norm-at-most-one factors,
`‖∏ U_j − ∏ V_j‖ ≤ ∑ ‖U_j − V_j‖`. Used in the proofs of Lemma 1, Theorem 8,
Corollary 6 and Lemma 7. -/
theorem list_prod_sub_prod_norm_le {E : Type*} [NormedRing E]
    (hone : ‖(1 : E)‖ ≤ 1)
    (U V : List E) (h : U.length = V.length)
    (hU : ∀ x ∈ U, ‖x‖ ≤ 1) (hV : ∀ x ∈ V, ‖x‖ ≤ 1) :
    ‖U.prod - V.prod‖ ≤ (List.zipWith (fun a b => ‖a - b‖) U V).sum := by
  induction U generalizing V with
  | nil =>
    cases V with
    | nil => simp
    | cons b V => simp at h
  | cons a U ih =>
    cases V with
    | nil => simp at h
    | cons b V =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      have hb : ‖b‖ ≤ 1 := hV b (by simp)
      have hU' : ∀ x ∈ U, ‖x‖ ≤ 1 := fun x hx => hU x (List.mem_cons_of_mem a hx)
      have hV' : ∀ x ∈ V, ‖x‖ ≤ 1 := fun x hx => hV x (List.mem_cons_of_mem b hx)
      have hUP : ‖U.prod‖ ≤ 1 := prod_norm_le_one hone U hU'
      have hkey : ‖(a :: U).prod - (b :: V).prod‖
          ≤ ‖a - b‖ + ‖U.prod - V.prod‖ := by
        have hsplit : (a :: U).prod - (b :: V).prod
            = (a - b) * U.prod + b * (U.prod - V.prod) := by
          simp only [List.prod_cons]
          noncomm_ring
        rw [hsplit]
        calc ‖(a - b) * U.prod + b * (U.prod - V.prod)‖
            ≤ ‖(a - b) * U.prod‖ + ‖b * (U.prod - V.prod)‖ := norm_add_le _ _
          _ ≤ ‖a - b‖ * ‖U.prod‖ + ‖b‖ * ‖U.prod - V.prod‖ :=
              add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
          _ ≤ ‖a - b‖ * 1 + 1 * ‖U.prod - V.prod‖ := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left hUP (norm_nonneg _)
              · exact mul_le_mul hb le_rfl (norm_nonneg _) (by norm_num)
          _ = ‖a - b‖ + ‖U.prod - V.prod‖ := by ring
      calc ‖(a :: U).prod - (b :: V).prod‖
          ≤ ‖a - b‖ + ‖U.prod - V.prod‖ := hkey
        _ ≤ ‖a - b‖ + (List.zipWith (fun a b => ‖a - b‖) U V).sum := by
            have := ih V h hU' hV'
            linarith
        _ = (List.zipWith (fun a b => ‖a - b‖) (a :: U) (b :: V)).sum := by
            simp

/-- Composition of two half-error simulations (the triangle-inequality step used in the
proofs of Theorem 5 and Corollary 6). -/
theorem simulatedWithinError_of_two_halves {I : Type} [Fintype I] [DecidableEq I]
    (Uexact Umid Usim : Matrix I I ℂ) {ε : ℝ}
    (h1 : ‖Uexact - Umid‖ ≤ ε / 2) (h2 : ‖Umid - Usim‖ ≤ ε / 2) :
    SimulatedWithinError Uexact Usim ε := by
  unfold SimulatedWithinError
  have hdecomp : Uexact - Usim = (Uexact - Umid) + (Umid - Usim) := by abel
  calc ‖Uexact - Usim‖ = ‖(Uexact - Umid) + (Umid - Usim)‖ := by rw [hdecomp]
    _ ≤ ‖Uexact - Umid‖ + ‖Umid - Usim‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := by ring

end Qatlib.Papers.QDynamics10.MainResults
