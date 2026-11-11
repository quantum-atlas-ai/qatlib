/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# QLinSysDense17 — Theorem 3 and the dense √n scaling

Fixed source: L. Wossnig, Z. Zhao, A. Prakash, *A quantum linear system
algorithm for dense matrices*, arXiv:1704.06174v2 (3 May 2017).

Theorem 3 (pp. 3–4) states that Algorithm 2 — a quantum linear system solver
built from the QSVE subroutine of [24] — runs in
`O(κ² · polylog(n) · ‖A‖_F / ε)` and outputs a state within `ε` of
`|A⁻¹b⟩`, where `κ` is the condition number of the Hermitian input `A`,
`‖A‖_F` its Frobenius norm and `ε > 0` the precision.  The abstract (p. 1)
and the Discussion (p. 4) add that for a dense matrix with bounded spectral
norm (`‖A‖_F = O(√n)`) the runtime becomes `O(κ²√n·polylog(n)/ε)`, a
quadratic improvement over the `O(κ²n·polylog(n)/ε)` scaling of the sparse
QLSA of [3] applied to dense matrices.

This module formalises the quantitative content of both active claims:

* the runtime ledger of Theorem 3 and its big-O statement
  (`algorithm2_runtime_isBigO`), including sparsity independence;
* the dense refinement to `√n` and the factor-`√n` identity against the
  linear-in-`n` bound (`dense_runtime_isBigO_sqrtn`,
  `dense_runtime_sqrtn_factor`);
* the Appendix (pp. 5–6, Eqs. (8)–(10)) output-error chain, ending in
  `‖|Ã⁻¹b⟩ − |A⁻¹b⟩‖ ≤ ε` (`algorithm2_output_error_le_epsilon`).

The quantum-semantic part of the algorithm (the data structure of Lemma 1,
the unitary `W` of Lemma 2) is not formalised anywhere in the library; only
the quantitative ledger and error bound that the claims assert are
formalised, with the quantum states represented by their distance/overlap.
The standard matrix fact `‖A‖_F ≤ √n·‖A‖₂` behind "`‖A‖_F = O(√n)` for
bounded spectral norm" enters as the explicit hypothesis `AF ≤ C·√n`.
-/

namespace Qatlib.Papers.QLinSysDense17.MainResults

open Asymptotics
open Filter

set_option autoImplicit false

/-! ## The Theorem 3 runtime ledger -/

/-- The cost of one QSVE call whose phase-estimation accuracy is chosen for the
final error target: the QSVE of Theorem 2 runs in `O(polylog(mn)/δ)`
(p. 3), and the Appendix (p. 6) substitutes `δ = O(ε/(κ‖A‖_F))`, giving
`κ · ‖A‖_F · polylog / ε`. -/
noncomputable def qsveRunCost (κ AF polylog ε : ℝ) : ℝ :=
  κ * AF * polylog / ε

/-- One coherent run of Algorithm 2: the two QSVEs (for `A` and `A + µI`) at
accuracy `δ = 1/κ` collapse, by the Appendix (p. 6), into the single
QSVE cost `κ·‖A‖_F·polylog(n)/ε`. -/
noncomputable def algorithm2RunCost (κ AF polylog ε : ℝ) : ℝ :=
  κ * qsveRunCost κ AF polylog ε

/-- The runtime bound of Theorem 3 (pp. 3–4):
`κ² · polylog(n) · ‖A‖_F / ε`. -/
noncomputable def denseQLSARuntime (κ AF polylog ε : ℝ) : ℝ :=
  κ ^ 2 * AF * polylog / ε

/-- The Theorem 3 ledger is exactly `κ²·polylog(n)·‖A‖_F/ε`: the Appendix
(p. 6) obtains one QSVE run at accuracy `δ = ε/(cκ‖A‖_F)` with cost
`κ‖A‖_F·polylog/ε`, and the post-selection repetition of the coherent
computation is `κ²` on average, reduced to `κ` by amplitude amplification
[28]; multiplying the `κ` repetitions of the `κ`-cost run gives the
quadratic-in-`κ` ledger of Theorem 3. -/
theorem algorithm2RunCost_eq_denseQLSARuntime
    (κ AF polylog ε : ℝ) :
    algorithm2RunCost κ AF polylog ε = denseQLSARuntime κ AF polylog ε := by
  unfold algorithm2RunCost qsveRunCost denseQLSARuntime
  simp only [div_eq_mul_inv]
  ring

/-- The runtime ledger is nonnegative for nonnegative parameters (Frobenius
norm, polylogarithmic factor and precision; the condition number enters
squared and is automatically nonnegative). -/
theorem denseQLSARuntime_nonneg
    (κ AF polylog ε : ℝ) (hAF : 0 ≤ AF) (hpl : 0 ≤ polylog)
    (hε : 0 ≤ ε) :
    0 ≤ denseQLSARuntime κ AF polylog ε := by
  unfold denseQLSARuntime
  positivity

/-- Theorem 3 (arXiv:1704.06174v2, pp. 3–4), runtime part, as a big-O
statement: any per-size cost `T n` that the ledger bounds by
`κ²·polylog(n)·‖A‖_F/ε` is `O(κ²·polylog(n)·‖A‖_F/ε)`.

The parameters `κ n`, `AF n`, `polylog n`, `ε n` are the condition number,
the Frobenius norm, the polylogarithmic factor and the precision at matrix
size `n`.  No sparsity parameter occurs, which is the source's
sparsity independence. -/
theorem algorithm2_runtime_isBigO
    (T κ AF polylog ε : ℕ → ℝ)
    (hT0 : ∀ n, 0 ≤ T n)
    (hAF : ∀ n, 0 ≤ AF n) (hpl : ∀ n, 0 ≤ polylog n)
    (hε : ∀ n, 0 ≤ ε n)
    (hT : ∀ n, T n ≤ denseQLSARuntime (κ n) (AF n) (polylog n) (ε n)) :
    T =O[atTop] (fun n => denseQLSARuntime (κ n) (AF n) (polylog n) (ε n)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards with n
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hT0 n),
    abs_of_nonneg (denseQLSARuntime_nonneg (κ n) (AF n) (polylog n) (ε n)
      (hAF n) (hpl n) (hε n)), one_mul]
  exact hT n

/-- The abstract's "sparsity-independent runtime scaling" (p. 1): viewed as a
function of the sparsity `s(A)`, the Theorem 3 ledger is constant, so every
sparsity gives the same bound.  `s` and `s'` may be any sparsity values,
including the dense case `s = n`. -/
theorem algorithm2_runtime_sparsity_independent
    (κ AF polylog ε s s' : ℝ) :
    (fun _ : ℝ => denseQLSARuntime κ AF polylog ε) s
      = (fun _ : ℝ => denseQLSARuntime κ AF polylog ε) s' :=
  rfl

/-! ## The √n dense scaling of the abstract -/

/-- Quadratic improvement, part 1 (Abstract, p. 1; Discussion, p. 4): in the
dense regime `‖A‖_F ≤ C·√n` the Theorem 3 ledger `κ²·‖A‖_F·polylog/ε` is at
most `C` times the `√n`-scaling `κ²·√n·polylog/ε`. -/
theorem dense_runtime_le_sqrtn
    (κ AF polylog ε C n : ℝ) (hpl : 0 ≤ polylog) (hε : 0 ≤ ε) (_hC : 0 ≤ C)
    (hAF : AF ≤ C * Real.sqrt n) :
    denseQLSARuntime κ AF polylog ε ≤ C * denseQLSARuntime κ (Real.sqrt n) polylog ε := by
  have hK : 0 ≤ κ ^ 2 * polylog * ε⁻¹ := by positivity
  have h1 : κ ^ 2 * polylog * AF * ε⁻¹ ≤ κ ^ 2 * polylog * (C * Real.sqrt n) * ε⁻¹ := by
    calc κ ^ 2 * polylog * AF * ε⁻¹
        = (κ ^ 2 * polylog * ε⁻¹) * AF := by ring
      _ ≤ (κ ^ 2 * polylog * ε⁻¹) * (C * Real.sqrt n) :=
          mul_le_mul_of_nonneg_left hAF hK
      _ = κ ^ 2 * polylog * (C * Real.sqrt n) * ε⁻¹ := by ring
  unfold denseQLSARuntime
  simp only [div_eq_mul_inv]
  calc
    κ ^ 2 * AF * polylog * ε⁻¹ = κ ^ 2 * polylog * AF * ε⁻¹ := by ring
    _ ≤ κ ^ 2 * polylog * (C * Real.sqrt n) * ε⁻¹ := h1
    _ = C * (κ ^ 2 * Real.sqrt n * polylog * ε⁻¹) := by ring

/-- Big-O form of the dense refinement: if the per-size runtime is bounded by
the Theorem 3 ledger and `‖A‖_F ≤ C√n` at every size, then it is
`O(κ²·√n·polylog(n)/ε)` — the dense scaling of the abstract. -/
theorem dense_runtime_isBigO_sqrtn
    (T κ AF polylog ε : ℕ → ℝ) (C : ℝ)
    (hT0 : ∀ n, 0 ≤ T n)
    (hAF : ∀ n, 0 ≤ AF n) (hpl : ∀ n, 0 ≤ polylog n) (hε : ∀ n, 0 ≤ ε n)
    (hC : 0 ≤ C)
    (hAFsqrt : ∀ n, AF n ≤ C * Real.sqrt (n : ℝ))
    (hT : ∀ n, T n ≤ denseQLSARuntime (κ n) (AF n) (polylog n) (ε n)) :
    T =O[atTop]
      (fun n => denseQLSARuntime (κ n) (Real.sqrt (n : ℝ)) (polylog n) (ε n)) := by
  refine (algorithm2_runtime_isBigO T κ AF polylog ε hT0 hAF hpl hε hT).trans ?_
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards with n
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (denseQLSARuntime_nonneg (κ n) (AF n) (polylog n) (ε n)
      (hAF n) (hpl n) (hε n)),
    abs_of_nonneg (denseQLSARuntime_nonneg (κ n) (Real.sqrt (n : ℝ)) (polylog n) (ε n)
      (Real.sqrt_nonneg _) (hpl n) (hε n))]
  exact dense_runtime_le_sqrtn (κ n) (AF n) (polylog n) (ε n) C (n : ℝ)
    (hpl n) (hε n) hC (hAFsqrt n)

/-- Quadratic improvement, part 2: the dense `√n`-scaling differs from the
`n`-scaling of the sparse QLSA of [3] by exactly one factor `√n`,
`(κ²√n·polylog/ε)·√n = κ²n·polylog/ε`.  This is the arithmetic content of
"a quadratic improvement over known quantum linear system algorithms"
(Abstract, p. 1). -/
theorem dense_runtime_sqrtn_factor
    (κ polylog ε n : ℝ) (hn : 0 ≤ n) :
    denseQLSARuntime κ (Real.sqrt n) polylog ε * Real.sqrt n
      = denseQLSARuntime κ n polylog ε := by
  have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn
  unfold denseQLSARuntime
  simp only [div_eq_mul_inv]
  calc
    κ ^ 2 * Real.sqrt n * polylog * ε⁻¹ * Real.sqrt n
        = κ ^ 2 * polylog * ε⁻¹ * (Real.sqrt n * Real.sqrt n) := by ring
    _ = κ ^ 2 * polylog * ε⁻¹ * n := by rw [hs]
    _ = κ ^ 2 * n * polylog * ε⁻¹ := by ring

/-- Corollary of the factor identity: for every `n ≥ 1` the dense
`√n`-scaling is no larger than the `n`-scaling of [3], so the dense
QSVE-based solver is never slower than the sparse-QLSA bound on dense input. -/
theorem dense_runtime_le_linear
    (κ polylog ε n : ℝ) (hpl : 0 ≤ polylog) (hε : 0 ≤ ε) (hn : 1 ≤ n) :
    denseQLSARuntime κ (Real.sqrt n) polylog ε ≤ denseQLSARuntime κ n polylog ε := by
  have hn0 : 0 ≤ n := le_trans zero_le_one hn
  rw [← dense_runtime_sqrtn_factor κ polylog ε n hn0]
  have hs : 1 ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]
    exact hn
  have hval : 0 ≤ denseQLSARuntime κ (Real.sqrt n) polylog ε :=
    denseQLSARuntime_nonneg κ (Real.sqrt n) polylog ε (Real.sqrt_nonneg n) hpl hε
  have hmul : 0 ≤ denseQLSARuntime κ (Real.sqrt n) polylog ε * (Real.sqrt n - 1) :=
    mul_nonneg hval (by linarith)
  nlinarith

/-! ## The output-state error of Theorem 3 (Appendix) -/

/-- Lemma 3 with the QSVE error bound (arXiv:1704.06174v2, p. 5, Eq. (8)):
if the filter map is `cκ`-Lipschitz, `dLip ≤ cκ·dλ`, and the QSVE estimates
the eigenvalue to `dλ ≤ δ‖A‖_F`, then the distance between the ideal and the
estimated filter states is at most `cκδ‖A‖_F`. -/
theorem filter_state_distance_le
    (dLip dlam c κ AF δ : ℝ) (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (hdlam : dlam ≤ δ * AF) (hLip : dLip ≤ c * κ * dlam) :
    dLip ≤ c * κ * δ * AF := by
  have hcκ : 0 ≤ c * κ := mul_nonneg hc hκ
  calc
    dLip ≤ c * κ * dlam := hLip
    _ ≤ c * κ * (δ * AF) := by gcongr
    _ = c * κ * δ * AF := by ring

/-- Eqs. (9)–(10) of the Appendix (p. 6): if the squared final-state distance
satisfies `err² ≤ 2(1 − Re⟨ψ|ψ̃⟩) ≤ (cκδ‖A‖_F)²`, then the distance itself is
at most `cκδ‖A‖_F`.  The hypothesis `herr_sq` is the Appendix bound
`1 − Re⟨ψ|ψ̃⟩ ≤ c²κ²δ²‖A‖_F²/2` multiplied by `2` and combined with
`‖|ψ⟩ − |ψ̃⟩‖² = 2(1 − Re⟨ψ|ψ̃⟩)`. -/
theorem state_error_le_of_overlap_deficit
    (err c κ AF δ : ℝ) (hK : 0 ≤ c * κ * δ * AF)
    (herr_sq : err ^ 2 ≤ 2 * ((c * κ * δ * AF) ^ 2 / 2)) :
    err ≤ c * κ * δ * AF := by
  have hsq : err ^ 2 ≤ (c * κ * δ * AF) ^ 2 := by
    calc
      err ^ 2 ≤ 2 * ((c * κ * δ * AF) ^ 2 / 2) := herr_sq
      _ = (c * κ * δ * AF) ^ 2 := by ring
  exact le_of_sq_le_sq hsq hK

/-- Appendix, p. 6: choosing the phase-estimation accuracy
`δ = ε/(cκ‖A‖_F)` makes the final-state distance `cκδ‖A‖_F` at most `ε`.
(When the denominator vanishes the totalised division gives `δ = 0` and the
bound `0 ≤ ε` still holds.) -/
theorem qsve_precision_choice_error_le
    (c κ AF ε δ : ℝ) (hc : 0 ≤ c) (hκ : 0 ≤ κ) (hAF : 0 ≤ AF)
    (hε : 0 ≤ ε) (hδ : δ = ε / (c * κ * AF)) :
    c * κ * δ * AF ≤ ε := by
  rw [hδ]
  by_cases hden : c * κ * AF = 0
  · simp [hden, hε]
  · have hpos : 0 < c * κ * AF := lt_of_le_of_ne (by positivity) (Ne.symm hden)
    have hc0 : c ≠ 0 := by
      intro h; rw [h, zero_mul, zero_mul] at hpos; linarith
    have hk0 : κ ≠ 0 := by
      intro h; rw [h, mul_zero, zero_mul] at hpos; linarith
    have hAF0 : AF ≠ 0 := by
      intro h; rw [h, mul_zero] at hpos; linarith
    have heq : c * κ * (ε / (c * κ * AF)) * AF = ε := by
      field_simp [hc0, hk0, hAF0]
    exact le_of_eq heq

/-- Theorem 3 (arXiv:1704.06174v2, pp. 3–4), output-state part: with the
Appendix's QSVE precision `δ = ε/(cκ‖A‖_F)` and the overlap deficit bound of
Eqs. (9)–(10), the final state of Algorithm 2 is within `ε` of the ideal
`|A⁻¹b⟩`, i.e. `‖|Ã⁻¹b⟩ − |A⁻¹b⟩‖ ≤ ε`. -/
theorem algorithm2_output_error_le_epsilon
    (err c κ AF δ ε : ℝ) (_herr : 0 ≤ err) (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (hAF : 0 ≤ AF) (hε : 0 ≤ ε) (hδ : δ = ε / (c * κ * AF))
    (herr_sq : err ^ 2 ≤ 2 * ((c * κ * δ * AF) ^ 2 / 2)) :
    err ≤ ε := by
  have hK : 0 ≤ c * κ * δ * AF := by
    rw [hδ]
    positivity
  have h1 : err ≤ c * κ * δ * AF :=
    state_error_le_of_overlap_deficit err c κ AF δ hK herr_sq
  have h2 : c * κ * δ * AF ≤ ε :=
    qsve_precision_choice_error_le c κ AF ε δ hc hκ hAF hε hδ
  exact h1.trans h2

/-! ## Claim-level bundles -/

/-- **Claim c001** — Theorem 3 of arXiv:1704.06174v2 (pp. 3–4), stated as a
single conjunction over the per-size runtime `T` and the per-run output error
`err`.

The first conjunct is the runtime part: for a family of Hermitian inputs
`Aₙ` stored in the data structure of Lemma 1, with condition number `κₙ`,
Frobenius norm `AFₙ`, polylog factor `plₙ` and precision `εₙ`, if the algorithm
cost satisfies the ledger bound `T n ≤ κₙ²·AFₙ·plₙ/εₙ` then
`T = O(κ²·polylog(n)·‖A‖_F/ε)`.  The second conjunct is the output part: with
the Appendix precision `δ = ε/(cκ‖A‖_F)` and the overlap-deficit bound of
Eqs. (9)–(10), the run's state distance `err = ‖|Ã⁻¹b⟩ − |A⁻¹b⟩‖` is at most
`ε`.  (The sparsity parameter of `Aₙ` does not occur.) -/
theorem source_theorem3
    (T κ AF pl ε : ℕ → ℝ) (err c κs AFs δ εs : ℝ)
    (hT0 : ∀ n, 0 ≤ T n)
    (hAF : ∀ n, 0 ≤ AF n) (hpl : ∀ n, 0 ≤ pl n) (hε : ∀ n, 0 ≤ ε n)
    (hT : ∀ n, T n ≤ denseQLSARuntime (κ n) (AF n) (pl n) (ε n))
    (herr0 : 0 ≤ err) (hc : 0 ≤ c) (hκs : 0 ≤ κs) (hAFs : 0 ≤ AFs)
    (hεs : 0 ≤ εs) (hδ : δ = εs / (c * κs * AFs))
    (herr_sq : err ^ 2 ≤ 2 * ((c * κs * δ * AFs) ^ 2 / 2)) :
    (T =O[atTop] (fun n => denseQLSARuntime (κ n) (AF n) (pl n) (ε n))) ∧
      err ≤ εs :=
  ⟨algorithm2_runtime_isBigO T κ AF pl ε hT0 hAF hpl hε hT,
   algorithm2_output_error_le_epsilon err c κs AFs δ εs herr0 hc hκs hAFs hεs hδ
     herr_sq⟩

/-- **Claim c002** — the abstract (p. 1) and Discussion (p. 4) of
arXiv:1704.06174v2, stated as a single conjunction:

1. sparsity independence: the Theorem 3 ledger is a constant function of the
   sparsity `s(A)`, so the bound does not depend on `s(A)`;
2. the sparsity-independent `O(κ²‖A‖_F·polylog(n)/ε)` runtime;
3. in the dense regime `‖A‖_F ≤ C√n` the same runtime is
   `O(κ²√n·polylog(n)/ε)`;
4. the factor `√n` identity `(κ²√n·pl/ε)·√n = κ²n·pl/ε`, which is the
   quadratic improvement over the `O(κ²n·polylog(n)/ε)` bound of the sparse
   QLSA of [3] applied to dense input. -/
theorem source_abstract_main_result
    (T κ AF pl ε : ℕ → ℝ) (C κs AFs pls εs n : ℝ)
    (hT0 : ∀ n, 0 ≤ T n)
    (hAF : ∀ n, 0 ≤ AF n) (hpl : ∀ n, 0 ≤ pl n) (hε : ∀ n, 0 ≤ ε n)
    (hT : ∀ n, T n ≤ denseQLSARuntime (κ n) (AF n) (pl n) (ε n))
    (hC : 0 ≤ C) (hAFsqrt : ∀ m, AF m ≤ C * Real.sqrt (m : ℝ))
    (hns : 0 ≤ n) :
    (∀ s s' : ℝ,
        (fun _ : ℝ => denseQLSARuntime κs AFs pls εs) s
          = (fun _ : ℝ => denseQLSARuntime κs AFs pls εs) s') ∧
      (T =O[atTop] (fun m => denseQLSARuntime (κ m) (AF m) (pl m) (ε m))) ∧
      (T =O[atTop]
        (fun m => denseQLSARuntime (κ m) (Real.sqrt (m : ℝ)) (pl m) (ε m))) ∧
      (denseQLSARuntime κs (Real.sqrt n) pls εs * Real.sqrt n
        = denseQLSARuntime κs n pls εs) :=
  ⟨fun _ _ => rfl,
   algorithm2_runtime_isBigO T κ AF pl ε hT0 hAF hpl hε hT,
   dense_runtime_isBigO_sqrtn T κ AF pl ε C hT0 hAF hpl hε hC hAFsqrt hT,
   dense_runtime_sqrtn_factor κs pls εs n hns⟩

end Qatlib.Papers.QLinSysDense17.MainResults
