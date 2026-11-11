/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Qatlib.Papers.GateEffSim12.MainResults.SourceModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# ErrorBounds — Theorems 5.4 and 5.5 of arXiv:1211.4637v2

Fixed paper version: arXiv:1211.4637v2 (5 April 2013), PDF SHA-256
`aef583fed3675ee75a251ed7438ab99cb4c16b34697dd8f4293f3d39d07d471d`.
Theorem 5.4 is Eq. (45) (p. 20), Theorem 5.5 is Eq. (63) (p. 24).

The paper's §5 error analysis is a step-by-step comparison of two runs of the
recursive measurement: the uncompressed run (`u`) and the compressed run (`c`).
There are three error sources, formalised here as follows.

* Truncation of the high-Hamming-weight part of the initial state, Eq. (54):
  the initial states of the two runs differ by at most `ε'` in trace distance.
* A per-step implementation error of the measurement operators, Eq. (38)–(39):
  each step differs by at most a factor `ε` times the size of the state it acts
  on.  In Theorem 5.4 this factor is the full trace norm (worst case `h ≤ k'`
  located ones, `k' log m` steps); in Theorem 5.5 the factor is the trace of the
  *continuing* component only, Eq. (64)–(65).
* Contraction: measurement (and the unitary post-processing) does not increase
  the trace norm, Eq. (62).

`runSeq` is the state sequence after `n` recursive-measurement steps; the main
lemma `runSeq_error_le` is the induction behind Eqs. (54)–(62), and Theorem 5.4
/ 5.5 are the two arithmetic corollaries (Eq. (45) and Eq. (63)).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.GateEffSim12.MainResults.SourceModel

namespace Qatlib.Papers.GateEffSim12.MainResults.ErrorBounds

/-! ## Step sequences -/

/-- The state after `n` steps of a recursive run whose `n`-th step is the
linear map `step n` and whose initial state is `init`.  This is the sequence
`ρ_{η,ℓ}` of Eq. (64) with the measurement record traced out. -/
def runSeq {D : ℕ} (step : ℕ → Operator D →ₗ[ℂ] Operator D) (init : Operator D) :
    ℕ → Operator D
  | 0 => init
  | n + 1 => step n (runSeq step init n)

/-- A stepwise run whose steps are contractions has trace norm at most `1` if
its initial state does; this is the trace-norm preservation used throughout
Eqs. (56)–(62) of §5. -/
theorem runSeq_traceNorm_le {D : ℕ} (step : ℕ → Operator D →ₗ[ℂ] Operator D)
    (hcontract : ∀ n X, Matrix.traceNorm (step n X) ≤ Matrix.traceNorm X)
    (init : Operator D) (hinit : Matrix.traceNorm init ≤ 1) (n : ℕ) :
    Matrix.traceNorm (runSeq step init n) ≤ 1 := by
  induction n with
  | zero => simpa [runSeq] using hinit
  | succ n ih =>
      exact le_trans (hcontract n _) ih

/-! ## The error-accumulation induction (Eqs. (54)–(62)) -/

/-- **Error accumulation for the recursive measurement** (Eqs. (54)–(62) of
arXiv:1211.4637v2, pp. 20–23).  Let `stepU`/`stepC` be the steps of the
uncompressed and compressed runs, both contracting the trace norm.  Suppose

* the initial states are within `ε'` in trace distance (the truncation error of
  Eq. (54)), and the compressed initial state is a state (`traceNorm ≤ 1`), and
* each step differs by at most `2ε` times the trace norm of a "charged"
  component `cont n X` (the continuing component of Eq. (64);

then after `n` steps the two states are within
`ε' + 2ε Σ_{i<n} traceNorm (cont i (runSeq stepC initC i))`
in trace distance.  Setting `cont := id` gives the worst-case charging of
Eq. (54)–(62); using the continuing component gives Theorem 5.5's improvement,
Eq. (65). -/
theorem runSeq_error_le {D : ℕ}
    (stepU stepC : ℕ → Operator D →ₗ[ℂ] Operator D)
    (cont : ℕ → Operator D → Operator D)
    (ε ε' : ℝ) (_hε : 0 ≤ ε)
    (hcontractU : ∀ n X, Matrix.traceNorm (stepU n X) ≤ Matrix.traceNorm X)
    (hcontractC : ∀ n X, Matrix.traceNorm (stepC n X) ≤ Matrix.traceNorm X)
    (initU initC : Operator D)
    (hinitC : Matrix.traceNorm initC ≤ 1)
    (htrunc : Matrix.traceNorm (initU - initC) ≤ ε')
    (hstep : ∀ n X, Matrix.traceNorm (stepU n X - stepC n X) ≤
      2 * ε * Matrix.traceNorm (cont n X))
    (n : ℕ) :
    Matrix.traceNorm (runSeq stepU initU n - runSeq stepC initC n) ≤
      ε' + 2 * ε * ∑ i ∈ Finset.range n,
        Matrix.traceNorm (cont i (runSeq stepC initC i)) := by
  induction n with
  | zero => simp [runSeq, htrunc]
  | succ n ih =>
      simp only [runSeq]
      -- Triangle inequality: split the difference of the two `(n+1)`-st states
      -- through the image of the compressed state under the uncompressed step.
      have htri :
          Matrix.traceNorm (stepU n (runSeq stepU initU n) - stepC n (runSeq stepC initC n)) ≤
            Matrix.traceNorm (stepU n (runSeq stepU initU n) - stepU n (runSeq stepC initC n)) +
              Matrix.traceNorm (stepU n (runSeq stepC initC n) - stepC n (runSeq stepC initC n)) := by
        have h := Matrix.traceNorm_add_le
          (stepU n (runSeq stepU initU n) - stepU n (runSeq stepC initC n))
          (stepU n (runSeq stepC initC n) - stepC n (runSeq stepC initC n))
        have heq :
            (stepU n (runSeq stepU initU n) - stepU n (runSeq stepC initC n)) +
                (stepU n (runSeq stepC initC n) - stepC n (runSeq stepC initC n)) =
              stepU n (runSeq stepU initU n) - stepC n (runSeq stepC initC n) := by
          abel
        rwa [heq] at h
      -- The first term is the propagated previous error (contraction).
      have h1 :
          Matrix.traceNorm (stepU n (runSeq stepU initU n) - stepU n (runSeq stepC initC n)) ≤
            Matrix.traceNorm (runSeq stepU initU n - runSeq stepC initC n) := by
        have heq :
            stepU n (runSeq stepU initU n) - stepU n (runSeq stepC initC n) =
              stepU n (runSeq stepU initU n - runSeq stepC initC n) := by
          rw [map_sub]
        rw [heq]
        exact hcontractU n _
      -- The second term is the local implementation error, charged to `cont`.
      have h2 :
          Matrix.traceNorm (stepU n (runSeq stepC initC n) - stepC n (runSeq stepC initC n)) ≤
            2 * ε * Matrix.traceNorm (cont n (runSeq stepC initC n)) :=
        hstep n _
      have hsum :
          Matrix.traceNorm (stepU n (runSeq stepU initU n) - stepC n (runSeq stepC initC n)) ≤
            (ε' + 2 * ε * ∑ i ∈ Finset.range n,
              Matrix.traceNorm (cont i (runSeq stepC initC i))) +
              2 * ε * Matrix.traceNorm (cont n (runSeq stepC initC n)) := by
        linarith [htri, h1, h2, ih]
      calc
        Matrix.traceNorm (stepU n (runSeq stepU initU n) - stepC n (runSeq stepC initC n))
            ≤ (ε' + 2 * ε * ∑ i ∈ Finset.range n,
                Matrix.traceNorm (cont i (runSeq stepC initC i))) +
                2 * ε * Matrix.traceNorm (cont n (runSeq stepC initC n)) := hsum
        _ = ε' + 2 * ε * ∑ i ∈ Finset.range (n + 1),
              Matrix.traceNorm (cont i (runSeq stepC initC i)) := by
            rw [Finset.sum_range_succ]
            ring

/-! ## Theorem 5.4 (Eq. (45), p. 20) -/

/-- **Theorem 5.4 (error bounds), Eq. (45) of arXiv:1211.4637v2, p. 20.**
The trace distance `D'_av` between the compressed and uncompressed measurement
schemes after `K` recursive-measurement steps is `O(ε' + ε k' log m)`.

Formal model: the two runs share the step-contraction property (measurement is
trace-norm non-increasing, Eq. (62)), the initial truncation error is `ε'`
(Eq. (54)), each step is off by at most `2ε` times the state's trace norm
(Eq. (38)–(39) with the worst-case charge), and the number `K` of steps is at
most `k' log m` (there are `≤ k'` located ones and `log m` levels of the
recursive split, §5.3).  The trace distance of the final states bounds the
paper's `D_av` through Eq. (46)–(49). -/
theorem theorem_5_4 {D : ℕ}
    (stepU stepC : ℕ → Operator D →ₗ[ℂ] Operator D)
    (ε ε' : ℝ) (hε : 0 ≤ ε) (hε' : 0 ≤ ε')
    (k' m K : ℕ) (hk' : 0 < k') (hm : 1 < m)
    (hcontractU : ∀ n X, Matrix.traceNorm (stepU n X) ≤ Matrix.traceNorm X)
    (hcontractC : ∀ n X, Matrix.traceNorm (stepC n X) ≤ Matrix.traceNorm X)
    (initU initC : Operator D)
    (hinitC : Matrix.traceNorm initC ≤ 1)
    (htrunc : Matrix.traceNorm (initU - initC) ≤ ε')
    (hstep : ∀ n X, Matrix.traceNorm (stepU n X - stepC n X) ≤
      2 * ε * Matrix.traceNorm X)
    (hK : (K : ℝ) ≤ (k' : ℝ) * Real.log m) :
    ∃ c : ℝ, 0 < c ∧
      Matrix.traceNorm (runSeq stepU initU K - runSeq stepC initC K) ≤
        c * (ε' + ε * (k' : ℝ) * Real.log m) := by
  -- Each compressed state stays a state, so the total charge is at most `K`.
  have hstate : ∀ i, Matrix.traceNorm (runSeq stepC initC i) ≤ 1 := fun i =>
    runSeq_traceNorm_le stepC hcontractC initC hinitC i
  have hsumK : (∑ i ∈ Finset.range K, Matrix.traceNorm (runSeq stepC initC i)) ≤ (K : ℝ) := by
    calc
      (∑ i ∈ Finset.range K, Matrix.traceNorm (runSeq stepC initC i)) ≤
          ∑ _i ∈ Finset.range K, (1 : ℝ) := Finset.sum_le_sum fun i _ => hstate i
      _ = (K : ℝ) := by simp
  have hacc := runSeq_error_le stepU stepC (fun _ X => X) ε ε' hε hcontractU hcontractC
    initU initC hinitC htrunc hstep K
  -- `hstep` with `cont = id` is syntactically the hypothesis of `hacc`.
  have hlogm : 0 < Real.log m := Real.log_pos (by exact_mod_cast hm)
  have hkm : 0 ≤ ε * ((k' : ℝ) * Real.log m) :=
    mul_nonneg hε (mul_nonneg (Nat.cast_nonneg k') (le_of_lt hlogm))
  refine ⟨4, by norm_num, ?_⟩
  have hstepK : (2 : ℝ) * ε * (K : ℝ) ≤ 2 * ε * ((k' : ℝ) * Real.log m) := by
    have h2ε : (0 : ℝ) ≤ 2 * ε := by linarith
    calc (2 : ℝ) * ε * (K : ℝ) = (2 * ε) * (K : ℝ) := by ring
      _ ≤ (2 * ε) * ((k' : ℝ) * Real.log m) :=
          mul_le_mul_of_nonneg_left hK h2ε
  have hmain : Matrix.traceNorm (runSeq stepU initU K - runSeq stepC initC K) ≤
      ε' + 2 * ε * ((k' : ℝ) * Real.log m) := by
    calc
      Matrix.traceNorm (runSeq stepU initU K - runSeq stepC initC K) ≤
          ε' + 2 * ε * ∑ i ∈ Finset.range K, Matrix.traceNorm (runSeq stepC initC i) := by
            simpa using hacc
      _ ≤ ε' + 2 * ε * (K : ℝ) := by
            have h2ε : (0 : ℝ) ≤ 2 * ε := by linarith
            nlinarith [mul_le_mul_of_nonneg_left hsumK h2ε]
      _ ≤ ε' + 2 * ε * ((k' : ℝ) * Real.log m) := by linarith [hstepK]
  nlinarith [hmain, hε', hkm]

/-! ## Theorem 5.5 (Eq. (63), p. 24) -/

/-- **Theorem 5.5 (improved error bounds), Eq. (63) of arXiv:1211.4637v2,
p. 24.**  Provided `ε = O(1/(k' log m))`, the error is `O(ε' + ε log m)`.

Formal model: as in Theorem 5.4, but the per-step error is charged only to the
*continuing* component `cont n X` (Eq. (64)–(65)), and the total continuing mass
is bounded by `1 + 4β²m` (Eq. (66): the expected number of further ones is at
most `4β²m = O(1)`).  With `β² m ≤ 1` (the paper's choice `β² ≈ 1/8m`) the mass
is at most `5`, giving `D_av ≤ c(ε' + ε log m)` since `log m ≥ 1/2` for `m ≥ 2`.
The hypothesis `ε (k' log m) ≤ 1` records the paper's `ε = O(1/(k' log m))`
assumption. -/
theorem theorem_5_5 {D : ℕ}
    (stepU stepC : ℕ → Operator D →ₗ[ℂ] Operator D)
    (cont : ℕ → Operator D → Operator D)
    (ε ε' β : ℝ) (hε : 0 ≤ ε) (hε' : 0 ≤ ε') (_hβ : 0 ≤ β)
    (k' m K : ℕ) (hk' : 0 < k') (hm : 2 ≤ m)
    (hβm : β ^ 2 * (m : ℝ) ≤ 1)
    (hcontractU : ∀ n X, Matrix.traceNorm (stepU n X) ≤ Matrix.traceNorm X)
    (hcontractC : ∀ n X, Matrix.traceNorm (stepC n X) ≤ Matrix.traceNorm X)
    (initU initC : Operator D)
    (hinitC : Matrix.traceNorm initC ≤ 1)
    (htrunc : Matrix.traceNorm (initU - initC) ≤ ε')
    (hstep : ∀ n X, Matrix.traceNorm (stepU n X - stepC n X) ≤
      2 * ε * Matrix.traceNorm (cont n X))
    (hmass : (∑ i ∈ Finset.range K,
        Matrix.traceNorm (cont i (runSeq stepC initC i))) ≤ 1 + 4 * β ^ 2 * (m : ℝ))
    (hεsmall : ε * ((k' : ℝ) * Real.log m) ≤ 1) :
    ∃ c : ℝ, 0 < c ∧
      Matrix.traceNorm (runSeq stepU initU K - runSeq stepC initC K) ≤
        c * (ε' + ε * Real.log m) := by
  have hacc := runSeq_error_le stepU stepC cont ε ε' hε hcontractU hcontractC
    initU initC hinitC htrunc hstep K
  -- `log m ≥ 1/2` for `m ≥ 2`.
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlogm : (1 : ℝ) / 2 ≤ Real.log m :=
    le_trans hlog2 (Real.log_le_log (by norm_num) (by exact_mod_cast hm))
  -- Total charge: `2ε * (1 + 4β²m) ≤ 10ε`.
  have hmass5 : (1 : ℝ) + 4 * β ^ 2 * (m : ℝ) ≤ 5 := by nlinarith [hβm]
  have hcharge : 2 * ε * (1 + 4 * β ^ 2 * (m : ℝ)) ≤ 10 * ε := by
    have h2ε : (0 : ℝ) ≤ 2 * ε := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hmass5 h2ε]
  have hmain : Matrix.traceNorm (runSeq stepU initU K - runSeq stepC initC K) ≤ ε' + 10 * ε := by
    have h2ε : (0 : ℝ) ≤ 2 * ε := by linarith
    have hsummass : 2 * ε * (∑ i ∈ Finset.range K,
        Matrix.traceNorm (cont i (runSeq stepC initC i))) ≤ 10 * ε := by
      calc 2 * ε * (∑ i ∈ Finset.range K,
              Matrix.traceNorm (cont i (runSeq stepC initC i)))
          ≤ 2 * ε * (1 + 4 * β ^ 2 * (m : ℝ)) :=
            mul_le_mul_of_nonneg_left hmass h2ε
        _ ≤ 10 * ε := hcharge
    linarith [hacc, hsummass]
  refine ⟨21, by norm_num, ?_⟩
  have hlogm_nonneg : 0 ≤ Real.log m := le_trans (by norm_num) hlogm
  have hεlogm : 10 * ε ≤ 20 * ε * Real.log m := by
    nlinarith [hε, hlogm, mul_nonneg hε (sub_nonneg.mpr hlogm)]
  nlinarith [hmain, hε', hεlogm, mul_nonneg hε hlogm_nonneg]

end Qatlib.Papers.GateEffSim12.MainResults.ErrorBounds
