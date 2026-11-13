/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.QQueryIntro25.MainResults.SourceModel
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

open Qatlib.Foundations.PureStateMath.BornBridge

set_option backward.isDefEq.respectTransparency false

/-!
# Hybrid Method State-Progress Bounds and Quantum OR Query Lower Bound

This module formalizes Section 2 (Theorem 10, Corollary 11, and Proposition 12) of
Hamoudi on the BBBV hybrid method over unitary workspace-oracle circuits, proving
initial zero distance, single-query `L^2` progress `≤ 2 min(√w_x, √w_y)` on the
disagreement fiber, bounded-error final-state separation `‖ψ_x - ψ_y‖ ≥ 1/3`,
cumulative query-amplitude lower bound `≥ 1/6`, and the `√n / 6` bounded-error
quantum query lower bound for `n`-bit `OR`.

## Main definitions

* `disagreeFiber`: workspace basis fiber over input coordinates where `x i ≠ y i`.

## Main statements

* `theorem10_initial_condition`, `theorem10_progress_evolution`, `theorem10_final_condition`: Theorem 10(1)--(3).
* `theorem10_hybrid_method`: Theorem 10, packaged three-part hybrid-method bound.
* `corollary11_query_weight_lower_bound`: Corollary 11, cumulative query-amplitude lower bound `1/6`.
* `proposition12_or_lower_bound`: Proposition 12, `√n / 6 ≤ QueryCount C` for bounded-error `OR_n`.

## References

* [Hamoudi, 2025][Hamoudi2025QueryIntro], Section 2, Theorem 10, Corollary 11, and Proposition 12, pp. 7--9.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QQueryIntro25.MainResults

open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.SpectralReadout.PhaseReadout
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.SketchArith.GramAction

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- The disagreement fiber of two inputs (`S = {i | x i ≠ y i}` in the paper). -/
def disagreeFiber (x y : I → Bool) : Finset ((I × Bool) × W) :=
  workspaceMarkFiber (W := W) (Finset.univ.filter (fun i => x i ≠ y i))

/-- **Theorem 10, initial condition** (arXiv:2508.08852v1, printed p. 7).  Both
runs start in the common initial state, so the distance after `0` queries is `0`. -/
theorem theorem10_initial_condition (x y : I → Bool)
    (ψ : QState ((I × Bool) × W)) :
    ‖toEuclidean_fromVec
      (Run (workspaceBitOracle (W := W) y) [] ψ -
       Run (workspaceBitOracle (W := W) x) [] ψ)‖ = 0 := by
  simp [Run, toEuclidean_fromVec]

/-- **Theorem 10, progress evolution** (arXiv:2508.08852v1, printed p. 7).  Appending
one oracle query to a circuit increases the two-input state distance by at most
twice the smaller of the two disagreement-fiber query weights. -/
theorem theorem10_progress_evolution (x y : I → Bool)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (hC : IsUnitaryCircuit C) :
    ‖toEuclidean_fromVec
      (Run (workspaceBitOracle (W := W) y) (C ++ [Step.query]) ψ -
       Run (workspaceBitOracle (W := W) x) (C ++ [Step.query]) ψ)‖ ≤
    ‖toEuclidean_fromVec
      (Run (workspaceBitOracle (W := W) y) C ψ -
       Run (workspaceBitOracle (W := W) x) C ψ)‖ +
    2 * min
      (Real.sqrt (MeasureProb (Run (workspaceBitOracle (W := W) x) C ψ)
        (disagreeFiber (W := W) x y)))
      (Real.sqrt (MeasureProb (Run (workspaceBitOracle (W := W) y) C ψ)
        (disagreeFiber (W := W) x y))) := by
  rcases Decidable.em (IsUnitaryCircuit C) with hunitary | hnotunitary
  swap
  · exact False.elim (hnotunitary hC)
  clear hunitary
  rw [run_append, run_append]
  simp only [Run]
  set Oy := workspaceBitOracle (W := W) y
  set Ox := workspaceBitOracle (W := W) x
  set φy := Run Oy C ψ
  set φx := Run Ox C ψ
  set S := disagreeFiber (W := W) x y
  have hxA : ‖toEuclidean_fromVec (ApplyGate Oy φx - ApplyGate Ox φx)‖ ≤
      2 * Real.sqrt (MeasureProb φx S) := by
    simpa [Ox, Oy, S, disagreeFiber] using
      (workspace_mark_set_query_l2 (W := W) x y φx)
  have hyA : ‖toEuclidean_fromVec (ApplyGate Oy φy - ApplyGate Ox φy)‖ ≤
      2 * Real.sqrt (MeasureProb φy S) := by
    simpa [Ox, Oy, S, disagreeFiber] using
      (workspace_mark_set_query_l2 (W := W) x y φy)
  have hUy : ∀ a b : QState ((I × Bool) × W),
      ‖toEuclidean_fromVec (ApplyGate Oy a - ApplyGate Oy b)‖ =
        ‖toEuclidean_fromVec (a - b)‖ := by
    intro a b
    have hsub : ApplyGate Oy a - ApplyGate Oy b = ApplyGate Oy (a - b) := by
      simp [ApplyGate, Matrix.mulVec_sub]
    rw [hsub]
    simpa [Oy] using norm_applyGate_of_mem_unitaryGroup (workspaceBitOracle_unitary y) _
  have hUx : ∀ a b : QState ((I × Bool) × W),
      ‖toEuclidean_fromVec (ApplyGate Ox a - ApplyGate Ox b)‖ =
        ‖toEuclidean_fromVec (a - b)‖ := by
    intro a b
    have hsub : ApplyGate Ox a - ApplyGate Ox b = ApplyGate Ox (a - b) := by
      simp [ApplyGate, Matrix.mulVec_sub]
    rw [hsub]
    simpa [Ox] using norm_applyGate_of_mem_unitaryGroup (workspaceBitOracle_unitary x) _
  rcases le_total (Real.sqrt (MeasureProb φx S)) (Real.sqrt (MeasureProb φy S)) with hle | hle
  · rw [min_eq_left hle]
    have hdecomp : ApplyGate Oy φy - ApplyGate Ox φx =
        (ApplyGate Oy φy - ApplyGate Oy φx) + (ApplyGate Oy φx - ApplyGate Ox φx) := by
      module
    calc ‖toEuclidean_fromVec (ApplyGate Oy φy - ApplyGate Ox φx)‖
        = ‖toEuclidean_fromVec ((ApplyGate Oy φy - ApplyGate Oy φx) +
            (ApplyGate Oy φx - ApplyGate Ox φx))‖ := by rw [hdecomp]
      _ ≤ ‖toEuclidean_fromVec (ApplyGate Oy φy - ApplyGate Oy φx)‖ +
            ‖toEuclidean_fromVec (ApplyGate Oy φx - ApplyGate Ox φx)‖ := by
            rw [show toEuclidean_fromVec ((ApplyGate Oy φy - ApplyGate Oy φx) +
                (ApplyGate Oy φx - ApplyGate Ox φx)) =
                toEuclidean_fromVec (ApplyGate Oy φy - ApplyGate Oy φx) +
                toEuclidean_fromVec (ApplyGate Oy φx - ApplyGate Ox φx) by
              simp [toEuclidean_fromVec]]
            exact norm_add_le _ _
      _ ≤ 2 * Real.sqrt (MeasureProb φx S) + ‖toEuclidean_fromVec (φy - φx)‖ := by
            rw [hUy φy φx]
            linarith [hxA]
      _ = _ := by ring
  · rw [min_eq_right hle]
    have hdecomp : ApplyGate Oy φy - ApplyGate Ox φx =
        (ApplyGate Oy φy - ApplyGate Ox φy) + (ApplyGate Ox φy - ApplyGate Ox φx) := by
      module
    calc ‖toEuclidean_fromVec (ApplyGate Oy φy - ApplyGate Ox φx)‖
        = ‖toEuclidean_fromVec ((ApplyGate Oy φy - ApplyGate Ox φy) +
            (ApplyGate Ox φy - ApplyGate Ox φx))‖ := by rw [hdecomp]
      _ ≤ ‖toEuclidean_fromVec (ApplyGate Oy φy - ApplyGate Ox φy)‖ +
            ‖toEuclidean_fromVec (ApplyGate Ox φy - ApplyGate Ox φx)‖ := by
            rw [show toEuclidean_fromVec ((ApplyGate Oy φy - ApplyGate Ox φy) +
                (ApplyGate Ox φy - ApplyGate Ox φx)) =
                toEuclidean_fromVec (ApplyGate Oy φy - ApplyGate Ox φy) +
                toEuclidean_fromVec (ApplyGate Ox φy - ApplyGate Ox φx) by
              simp [toEuclidean_fromVec]]
            exact norm_add_le _ _
      _ ≤ 2 * Real.sqrt (MeasureProb φy S) + ‖toEuclidean_fromVec (φy - φx)‖ := by
            rw [hUx φy φx]
            linarith [hyA]
      _ = _ := by ring

private theorem sqrt_measureProb_gap_sq_le {R : Type} [Fintype R]
    (φ χ : QState R) (S : Finset R) :
    (Real.sqrt (MeasureProb φ S) - Real.sqrt (MeasureProb χ S)) ^ 2 ≤
      MeasureProb (φ - χ) S := by
  have hpoint : (∑ v ∈ S, (‖φ v‖ - ‖χ v‖) ^ 2) ≤ MeasureProb (φ - χ) S := by
    refine Finset.sum_le_sum fun v _ => ?_
    have h := pow_le_pow_left₀ (abs_nonneg _) (abs_norm_sub_norm_le (φ v) (χ v)) 2
    simpa only [sq_abs, BornProb, Pi.sub_apply] using h
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt S (fun v => ‖φ v‖) (fun v => ‖χ v‖)
  have hexpand : (∑ v ∈ S, (‖φ v‖ - ‖χ v‖) ^ 2) =
      MeasureProb φ S - 2 * (∑ v ∈ S, ‖φ v‖ * ‖χ v‖) + MeasureProb χ S := by
    simp only [MeasureProb, BornProb, sub_sq, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]
  change (∑ v ∈ S, ‖φ v‖ * ‖χ v‖) ≤
    Real.sqrt (MeasureProb φ S) * Real.sqrt (MeasureProb χ S) at hcs
  rw [hexpand] at hpoint
  nlinarith [Real.sq_sqrt (measureProb_nonneg φ S),
    Real.sq_sqrt (measureProb_nonneg χ S)]

private theorem normalized_event_separation {R : Type} [Fintype R] [DecidableEq R]
    (φ χ : QState R) (E : Finset R) (hφ : Normalized φ) (hχ : Normalized χ)
    (hx : (2 / 3 : ℝ) ≤ MeasureProb φ E)
    (hy : (2 / 3 : ℝ) ≤ MeasureProb χ Eᶜ) :
    (1 / 3 : ℝ) ≤ ‖toEuclidean_fromVec (φ - χ)‖ := by
  have hpartition (η : QState R) :
      MeasureProb η Eᶜ + MeasureProb η E = ∑ v, ‖η v‖ ^ 2 :=
    Finset.sum_compl_add_sum E (fun v => ‖η v‖ ^ 2)
  have hφtotal : MeasureProb φ Eᶜ + MeasureProb φ E = 1 := (hpartition φ).trans hφ
  have hχtotal : MeasureProb χ Eᶜ + MeasureProb χ E = 1 := (hpartition χ).trans hχ
  have hχE : MeasureProb χ E ≤ 1 / 3 := by linarith
  have hφEc : MeasureProb φ Eᶜ ≤ 1 / 3 := by linarith
  let a := Real.sqrt (2 / 3 : ℝ)
  let b := Real.sqrt (1 / 3 : ℝ)
  have ha : a ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have hb : b ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
  have hab : 0 ≤ a - b := sub_nonneg.mpr (Real.sqrt_le_sqrt (by norm_num))
  have hgapE : a - b ≤ Real.sqrt (MeasureProb φ E) - Real.sqrt (MeasureProb χ E) :=
    sub_le_sub (Real.sqrt_le_sqrt hx) (Real.sqrt_le_sqrt hχE)
  have hgapEc : a - b ≤ Real.sqrt (MeasureProb χ Eᶜ) - Real.sqrt (MeasureProb φ Eᶜ) :=
    sub_le_sub (Real.sqrt_le_sqrt hy) (Real.sqrt_le_sqrt hφEc)
  have hE := (pow_le_pow_left₀ hab hgapE 2).trans (sqrt_measureProb_gap_sq_le φ χ E)
  have hEc := sqrt_measureProb_gap_sq_le φ χ Eᶜ
  have hEc' := pow_le_pow_left₀ hab hgapEc 2
  have htotal : MeasureProb (φ - χ) Eᶜ + MeasureProb (φ - χ) E =
      ‖toEuclidean_fromVec (φ - χ)‖ ^ 2 := by
    rw [hpartition, norm_toEuclidean_fromVec_sq]
  have hprod : (a * b) ^ 2 = 2 / 9 := by rw [mul_pow, ha, hb]; norm_num
  have hconstant : (1 / 9 : ℝ) ≤ 2 * (a - b) ^ 2 := by
    nlinarith only [ha, hb, hprod, sq_nonneg (a * b - 17 / 36)]
  nlinarith only [hE, hEc, hEc', htotal, hconstant,
    norm_nonneg (toEuclidean_fromVec (φ - χ))]

/-- **Theorem 10, final condition** (arXiv:2508.08852v1, printed pp. 7–8).  If the
`x`-run accepts a fixed event `E` with probability at least `2/3` while the `y`-run
accepts its complement with probability at least `2/3`, the two final states are at
`L2` distance at least `1/3`.

This is the paper's `‖|ψxT⟩ − |ψyT⟩‖² ≥ 2(1 − 2√2/3) ≥ 1/9` computation, written
operationally: `f(x) ≠ f(y)` and bounded-error correctness supply the two `2/3`
acceptance hypotheses for `E` and `Eᶜ`. -/
theorem theorem10_final_condition (x y : I → Bool)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (E : Finset ((I × Bool) × W))
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (hx : (2 / 3 : ℝ) ≤
      MeasureProb (Run (workspaceBitOracle (W := W) x) C ψ) E)
    (hy : (2 / 3 : ℝ) ≤
      MeasureProb (Run (workspaceBitOracle (W := W) y) C ψ) Eᶜ) :
    (1 / 3 : ℝ) ≤
      ‖toEuclidean_fromVec
        (Run (workspaceBitOracle (W := W) x) C ψ -
         Run (workspaceBitOracle (W := W) y) C ψ)‖ := by
  let φx := Run (workspaceBitOracle (W := W) x) C ψ
  let φy := Run (workspaceBitOracle (W := W) y) C ψ
  have hφx : Normalized φx :=
    hC.normalized_run (workspaceBitOracle_unitary x) hψ
  have hφy : Normalized φy :=
    hC.normalized_run (workspaceBitOracle_unitary y) hψ
  have haccept : (2 / 3 : ℝ) ≤ MeasureProb φx E := hx
  have hreject : (2 / 3 : ℝ) ≤ MeasureProb φy Eᶜ := hy
  -- Apply the two-block Cauchy–Schwarz separation bound.
  have hseparation : (1 / 3 : ℝ) ≤
      ‖toEuclidean_fromVec (φx - φy)‖ :=
    normalized_event_separation φx φy E hφx hφy haccept hreject
  change (1 / 3 : ℝ) ≤
    ‖toEuclidean_fromVec (φx - φy)‖
  exact hseparation

/-- **Theorem 10 (Hybrid method)** (arXiv:2508.08852v1, printed pp. 7–8), packaged as
the conjunction of the initial state, one-step progress and final-state conditions. -/
theorem theorem10_hybrid_method (x y : I → Bool)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (E : Finset ((I × Bool) × W))
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (hx : (2 / 3 : ℝ) ≤
      MeasureProb (Run (workspaceBitOracle (W := W) x) C ψ) E)
    (hy : (2 / 3 : ℝ) ≤
      MeasureProb (Run (workspaceBitOracle (W := W) y) C ψ) Eᶜ) :
    (‖toEuclidean_fromVec
        (Run (workspaceBitOracle (W := W) y) [] ψ -
         Run (workspaceBitOracle (W := W) x) [] ψ)‖ = 0) ∧
    (‖toEuclidean_fromVec
        (Run (workspaceBitOracle (W := W) y) (C ++ [Step.query]) ψ -
         Run (workspaceBitOracle (W := W) x) (C ++ [Step.query]) ψ)‖ ≤
      ‖toEuclidean_fromVec
        (Run (workspaceBitOracle (W := W) y) C ψ -
         Run (workspaceBitOracle (W := W) x) C ψ)‖ +
      2 * min
        (Real.sqrt (MeasureProb (Run (workspaceBitOracle (W := W) x) C ψ)
          (disagreeFiber (W := W) x y)))
        (Real.sqrt (MeasureProb (Run (workspaceBitOracle (W := W) y) C ψ)
          (disagreeFiber (W := W) x y)))) ∧
    ((1 / 3 : ℝ) ≤
      ‖toEuclidean_fromVec
        (Run (workspaceBitOracle (W := W) x) C ψ -
         Run (workspaceBitOracle (W := W) y) C ψ)‖) :=
  ⟨theorem10_initial_condition x y ψ,
   theorem10_progress_evolution x y C ψ hC,
   theorem10_final_condition x y C ψ E hC hψ hx hy⟩

/-- **Corollary 11 (Query weights lower bound)** (arXiv:2508.08852v1, printed p. 8).
If the two final states are at distance at least `1/3`, then the accumulated
disagreement-fiber query weights satisfy `Σ_t √(weight_t) ≥ 1/6`, where the sum runs
over the actual pre-query states of the `x`-run (the paper's `t = 0..T−1`).

This is obtained directly from the cumulative hybrid bound
`workspace_mark_set_hybrid` (FQN
`Qatlib.Concepts.QueryComplexity.AdversarySearch.workspace_mark_set_hybrid`). -/
theorem corollary11_query_weight_lower_bound (x y : I → Bool)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (hC : IsUnitaryCircuit C)
    (hfinal : (1 / 3 : ℝ) ≤
      ‖toEuclidean_fromVec
        (Run (workspaceBitOracle (W := W) x) C ψ -
         Run (workspaceBitOracle (W := W) y) C ψ)‖) :
    (1 / 6 : ℝ) ≤
      ((oracleQueryInputs x C ψ).map
        (fun φ => Real.sqrt (MeasureProb φ (disagreeFiber (W := W) x y)))).sum := by
  have hbound := workspace_mark_set_hybrid (W := W) x y C ψ hC
  -- `workspace_mark_set_hybrid` bounds the norm of the `y − x` difference; the
  -- paper (and the hypothesis `hfinal`) use the symmetric `x − y` difference.
  have hnorm :
      ‖toEuclidean_fromVec
        (Run (workspaceBitOracle (W := W) y) C ψ -
         Run (workspaceBitOracle (W := W) x) C ψ)‖ =
      ‖toEuclidean_fromVec
        (Run (workspaceBitOracle (W := W) x) C ψ -
         Run (workspaceBitOracle (W := W) y) C ψ)‖ := by
    simp only [toEuclidean_fromVec, WithLp.toLp_sub]
    exact norm_sub_rev _ _
  rw [hnorm] at hbound
  have hgoal : (1 / 6 : ℝ) ≤
      ((oracleQueryInputs x C ψ).map
        (fun φ => Real.sqrt (MeasureProb φ
          (workspaceMarkFiber (W := W) (Finset.univ.filter (fun i => x i ≠ y i)))))).sum := by
    nlinarith [hbound, hfinal]
  simpa only [disagreeFiber] using hgoal

/-- **Proposition 12 (Hybrid method applied to OR)** (arXiv:2508.08852v1, printed
pp. 8–9, source lines 490–492).  Any bounded-error quantum decision procedure for
`OR` on `n` bits using `T` queries has `T ≥ √n / 6`.

Encoded as: a finite circuit with one accepting register `E` whose success
probabilities are at least `2/3` on the all-zero input and at least `2/3` on every
one-sparse input must satisfy `√n/6 ≤ QueryCount C`. -/
theorem proposition12_or_lower_bound (n : ℕ)
    (C : Circuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W))
    (E : Finset ((Fin n × Bool) × W))
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (hzero : (2 / 3 : ℝ) ≤
      MeasureProb (Run (workspaceBitOracle (W := W) (allZero n)) C ψ) Eᶜ)
    (hone : ∀ i : Fin n, (2 / 3 : ℝ) ≤
      MeasureProb (Run (workspaceBitOracle (W := W) (oneSparse i)) C ψ) E) :
    Real.sqrt (n : ℝ) / 6 ≤ (QueryCount C : ℝ) := by
  -- Fixed paper version: arXiv:2508.08852v1, Proposition 12, printed pp. 8–9.
  by_cases hn : n = 0
  · simp only [hn, Nat.cast_zero, Real.sqrt_zero, zero_div]
    exact Nat.cast_nonneg _
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  let L := oracleQueryInputs (allZero n) C ψ
  obtain ⟨hlen, hmem⟩ := oracle_query_inputs_accounting (allZero n) C ψ hC hψ
  have hfiber (i : Fin n) : disagreeFiber (W := W) (allZero n) (oneSparse i) =
      workspaceQueryFiber (W := W) i := by
    ext p
    simp [disagreeFiber, workspaceMarkFiber, workspaceQueryFiber, allZero, oneSparse]
  have hlower (i : Fin n) : (1 / 6 : ℝ) ≤
      (L.map (fun φ => Real.sqrt (MeasureProb φ (workspaceQueryFiber (W := W) i)))).sum := by
    have hfinal := theorem10_final_condition (oneSparse i) (allZero n) C ψ E hC hψ
      (hone i) hzero
    have hreverse : (1 / 3 : ℝ) ≤ ‖toEuclidean_fromVec
        (Run (workspaceBitOracle (W := W) (allZero n)) C ψ -
         Run (workspaceBitOracle (W := W) (oneSparse i)) C ψ)‖ := by
      simp only [toEuclidean_fromVec, WithLp.toLp_sub] at hfinal ⊢
      rw [norm_sub_rev]
      exact hfinal
    simpa only [hfiber] using
      corollary11_query_weight_lower_bound (allZero n) (oneSparse i) C ψ hC hreverse
  have hmap (i : Fin n) :
      (L.map (fun φ => Real.sqrt (MeasureProb φ (workspaceQueryFiber (W := W) i)))).sum =
        ∑ t : Fin L.length, Real.sqrt (MeasureProb (L.get t) (workspaceQueryFiber (W := W) i)) := by
    conv_lhs => rw [← List.ofFn_get L, List.map_ofFn, List.sum_ofFn]
    rfl
  have hupper (t : Fin L.length) :
      (∑ i : Fin n, Real.sqrt (MeasureProb (L.get t) (workspaceQueryFiber (W := W) i))) ≤
        Real.sqrt (n : ℝ) := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin n))
      (fun _ => (1 : ℝ))
      (fun i => Real.sqrt (MeasureProb (L.get t) (workspaceQueryFiber (W := W) i)))
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Real.sq_sqrt (measureProb_nonneg _ _)] at hcs
    rw [(hmem (L.get t) (List.get_mem L t)).2, Real.sqrt_one, mul_one] at hcs
    exact hcs
  have hsum : (n : ℝ) / 6 ≤ (QueryCount C : ℝ) * Real.sqrt (n : ℝ) := by
    calc
      (n : ℝ) / 6 = ∑ _ : Fin n, (1 / 6 : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ ∑ i : Fin n, ∑ t : Fin L.length,
          Real.sqrt (MeasureProb (L.get t) (workspaceQueryFiber (W := W) i)) :=
        Finset.sum_le_sum fun i _ => (hlower i).trans_eq (hmap i)
      _ = ∑ t : Fin L.length, ∑ i : Fin n,
          Real.sqrt (MeasureProb (L.get t) (workspaceQueryFiber (W := W) i)) := Finset.sum_comm
      _ ≤ ∑ _ : Fin L.length, Real.sqrt (n : ℝ) := Finset.sum_le_sum fun t _ => hupper t
      _ = (QueryCount C : ℝ) * Real.sqrt (n : ℝ) := by simp [L, hlen]
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  nlinarith [Real.sq_sqrt hnpos.le]

end Qatlib.Papers.QQueryIntro25.MainResults
