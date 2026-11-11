/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorNormGibbs

/-!
# Executed words and application access counts

This module relates segmented product words to their lengths, label visits, and tariffs, and
records matched-order and family-word properties of recursive Suzuki words [Suzuki1990]. These
counts support commutator-scaled simulation estimates in the setting of [ChildsEtAl2021Trotter].

It also provides positive segment choices, access and cost-ledger witnesses, and
variation-of-constants identities for forced LCHS evolution. Explicit examples show that the
stated output checks allow success mass above one and a forced solution that vanishes.

## Main statements

* `segmentWord_length`: counts the executed segmented word.
* `recursive_suzuki_matched_order`: gives the matched order of a recursive Suzuki word.
* `lchs_forced_hasDerivAt`: gives the differential equation of the forced solution.
* `clause60_successMass_not_bounded`: exhibits output checks with success mass above one.
* `segmentLabelTariff_eq`: computes the segmented label tariff.

## References

* [Suzuki, 1990][Suzuki1990]
* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs

set_option autoImplicit false
set_option maxHeartbeats 400000

open Matrix Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
open scoped Classical BigOperators Matrix.Norms.L2Operator

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open scoped ComplexOrder

/-- A word with `r` segments has length `r * xs.length`. -/
theorem segmentWord_length {I : Type} [Fintype I] (xs : List (Matrix I I ℂ))
    (t : ℝ) (r : ℕ) : (segmentWord xs t r).length = r * xs.length := by
  simp [segmentWord]

/-- The number of visits to a family label is `r` times the number of positions carrying that
label. -/
theorem segmentLabelVisits_eq {I : Type} [Fintype I] {m : ℕ} (xs : List (Matrix I I ℂ))
    (lab : Fin xs.length → Fin m) (r : ℕ) (j : Fin m) :
    segmentLabelVisits xs lab r j =
      r * ((List.finRange xs.length).filter (fun i => lab i = j)).length := rfl

/-- Summing a function over the finite-range list equals its finite-type sum. -/
theorem list_sum_map_finRange {α : Type} [AddCommMonoid α] {n : ℕ} (f : Fin n → α) :
    ((List.finRange n).map f).sum = ∑ i : Fin n, f i := by
  rw [← List.ofFn_id, List.map_ofFn, List.sum_ofFn]
  simp

/-- The sum of label prices weighted by fiber cardinalities equals the sum of the prices over
all labelled positions. -/
theorem sum_price_mul_fiber_card {n m : ℕ} (price : Fin m → ℕ) (lab : Fin n → Fin m) :
    (∑ j : Fin m, price j * ((Finset.univ.filter (fun i : Fin n => lab i = j)).card : ℕ)) =
      ∑ i : Fin n, price (lab i) := by
  classical
  have h1 : (∑ j : Fin m, price j * ((Finset.univ.filter (fun i : Fin n => lab i = j)).card : ℕ))
      = ∑ j : Fin m, ∑ i ∈ Finset.univ.filter (fun i : Fin n => lab i = j), price j := by
    apply Finset.sum_congr rfl
    intro j _
    simp [Finset.sum_const, mul_comm]
  have h2 : (∑ j : Fin m, ∑ i ∈ Finset.univ.filter (fun i : Fin n => lab i = j), price j)
      = ∑ j : Fin m, ∑ i ∈ Finset.univ.filter (fun i : Fin n => lab i = j), price (lab i) := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i hi
    have hmem : lab i = j := by simpa using! hi
    rw [hmem]
  rw [h1, h2]
  exact Finset.sum_fiberwise_of_maps_to (fun (i : Fin n) (_ : i ∈ Finset.univ) =>
    Finset.mem_univ (lab i)) (fun i => price (lab i))

/-- The recursive Suzuki word at level `k` matches the sum generator through order `2 * (k +
1)`. -/
theorem recursive_suzuki_matched_order {D : ℕ} (hs : List (Operator D)) (k : ℕ) :
    IsMatchedOrder (recursiveSuzukiGenerators hs k) hs.sum (2 * (k + 1)) := by
  intro n hn
  exact recursive_suzuki_all_even_order_coefficients (Fin D) hs k n hn

/-- Every recursive Suzuki word possesses a representation as a scaled word over a finite
operator family. -/
theorem recursive_suzuki_family_word {D : ℕ} (hs : List (Operator D)) (k : ℕ) :
    ∃ (m : ℕ) (H : Fin m → Operator D)
      (lab : Fin (recursiveSuzukiGenerators hs k).length → Fin m)
      (c : Fin (recursiveSuzukiGenerators hs k).length → ℝ),
      IsFamilyWord H (recursiveSuzukiGenerators hs k) lab c := by
  refine ⟨(recursiveSuzukiGenerators hs k).length,
    (recursiveSuzukiGenerators hs k).get, id, fun _ => 1, ?_⟩
  intro i
  simp [one_smul]

/-- The selected TFIM segment count is a power of two. -/
theorem tfimSegmentChoice_eq_two_pow {D : ℕ} (A B : Operator D) (t ε : ℝ) :
    ∃ k : ℕ, tfimSegmentChoice A B t ε = 2 ^ k :=
  ⟨Nat.clog 2 (max 1 (Nat.ceil
      (max (4 * t * (‖A‖ + ‖B‖))
        (max (Real.sqrt (t ^ 3 * ‖pfComm A (pfComm A B)‖ / ε))
          (Real.sqrt (2 * t ^ 3 * ‖pfComm B (pfComm B A)‖ / (3 * ε))))))), rfl⟩

/-- The selected TFIM segment count is positive. -/
theorem tfimSegmentChoice_pos {D : ℕ} (A B : Operator D) (t ε : ℝ) :
    0 < tfimSegmentChoice A B t ε := by
  unfold tfimSegmentChoice nextPow2
  exact pow_pos two_pos _

/-- For positive tolerance, an FPRAS cost ledger and a soft factor at least one satisfy the
runtime assumption with a positive sample count. -/
theorem fpras_cost_ledger_witness (n r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (ledger : FprasCostLedger) (soft : ℝ),
      1 ≤ soft ∧ fprasRuntimeAssumption n r ε soft ledger.runtime ∧ 0 < ledger.samples := by
  refine ⟨⟨1, 0⟩, 1, le_rfl, ⟨le_rfl, hε, ?_⟩, by norm_num⟩
  have hn : 0 ≤ (n : ℝ) ^ 17 := by positivity
  have hr : 0 ≤ (r : ℝ) ^ 14 := by positivity
  have he : 0 < ε ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hε _
  have hprod : 0 ≤ (n : ℝ) ^ 17 * (r : ℝ) ^ 14 * ε ^ (-(2 : ℝ)) := by positivity
  simpa using! hprod

/-- The selected midpoint segment count is positive. -/
theorem midpointSegments_pos (L commMass T ε : ℝ) :
    0 < midpointSegments L commMass T ε := by
  unfold midpointSegments
  exact lt_of_lt_of_le zero_lt_one (le_max_left 1 _)

/-- Midpoint nodes possess a time-evaluation access record with `N` node queries and `N`
exponential macros. -/
theorem midpoint_timeEvalAccess_exists (T : ℝ) (N : ℕ) :
    ∃ access : TimeEvalAccess,
      access.nodes = midpointNodes T N ∧
      access.nodeQueries = N ∧
      access.exponentialMacros = N :=
  ⟨⟨midpointNodes T N, N, N⟩, rfl, rfl, rfl⟩

/-- For continuous generator and forcing, the forced solution factors into ordered evolution
times the initial state plus transported forcing. -/
theorem lchs_forced_factor {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (hA : Continuous A) (hb : Continuous b)
    (s : ℝ) (v : QState I) (t : ℝ) :
    orderedForcedSolution A b s v t =
      orderedEvolution A s t *ᵥ (v + ∫ u in s..t, orderedEvolution A u s *ᵥ b u) := by
  let L : QState I →L[ℝ] QState I :=
    ((Matrix.mulVecLin (orderedEvolution A s t)).restrictScalars ℝ).toContinuousLinearMap
  have hc : Continuous (fun u => orderedEvolution A u s) :=
    continuous_iff_continuousAt.mpr
      (fun u => (orderedEvolution_hasDerivAt_start A hA s u).continuousAt)
  have hi := ((hc.matrix_mulVec hb).intervalIntegrable (μ := MeasureTheory.volume) s t)
  have he (u : ℝ) : orderedEvolution A u t *ᵥ b u =
      L (orderedEvolution A u s *ᵥ b u) := by
    change _ = orderedEvolution A s t *ᵥ (orderedEvolution A u s *ᵥ b u)
    rw [Matrix.mulVec_mulVec, orderedEvolution_cocycle A hA u s t]
  unfold orderedForcedSolution
  rw [Matrix.mulVec_add]
  congr 1
  rw [intervalIntegral.integral_congr (fun u _ => he u), L.intervalIntegral_comp_comm hi]
  rfl

/-- The LCHS forced generator is continuous when both coefficient fields are continuous. -/
theorem lchsForcedGenerator_continuous {D : ℕ}
    (Lfield Hfield : ℝ → Matrix (Fin D) (Fin D) ℂ)
    (hL : Continuous Lfield) (hH : Continuous Hfield) :
    Continuous (lchsForcedGenerator Lfield Hfield) := by
  unfold lchsForcedGenerator
  fun_prop

/-- The forced LCHS solution satisfies the ordered variation-of-constants factorization from
time zero. -/
theorem lchs_forced_duhamel {D : ℕ}
    (Lfield Hfield : ℝ → Matrix (Fin D) (Fin D) ℂ)
    (b : ℝ → QState (Fin D)) (T : ℝ) (v : QState (Fin D))
    (hL : Continuous Lfield) (hH : Continuous Hfield) (hb : Continuous b) :
    orderedForcedSolution (lchsForcedGenerator Lfield Hfield) b 0 v T =
      orderedEvolution (lchsForcedGenerator Lfield Hfield) 0 T *ᵥ
        (v + ∫ u in 0..T,
          orderedEvolution (lchsForcedGenerator Lfield Hfield) u 0 *ᵥ b u) :=
  lchs_forced_factor (lchsForcedGenerator Lfield Hfield) b
    (lchsForcedGenerator_continuous Lfield Hfield hL hH) hb 0 v T

/-- The forced LCHS solution has derivative equal to minus the generator applied to the solution
plus the forcing. -/
theorem lchs_forced_hasDerivAt {D : ℕ}
    (Lfield Hfield : ℝ → Matrix (Fin D) (Fin D) ℂ)
    (b : ℝ → QState (Fin D)) (T : ℝ) (v : QState (Fin D))
    (hL : Continuous Lfield) (hH : Continuous Hfield) (hb : Continuous b) :
    HasDerivAt (orderedForcedSolution (lchsForcedGenerator Lfield Hfield) b 0 v)
      (-(lchsForcedGenerator Lfield Hfield T *ᵥ
          orderedForcedSolution (lchsForcedGenerator Lfield Hfield) b 0 v T) + b T) T :=
  orderedForcedSolution_hasDerivAt (lchsForcedGenerator Lfield Hfield) b
    (lchsForcedGenerator_continuous Lfield Hfield hL hH) hb 0 v T

/-- A positive success-mass lower bound and a real trace imply that the output trace is nonzero. -/
theorem lchs_output_trace_ne_zero {D : ℕ} (Mout : Operator D) (pSucc s : ℝ)
    (hp : 0 < pSucc) (hps : pSucc ≤ s) (hs : s = (Matrix.trace Mout).re)
    (him : (Matrix.trace Mout).im = 0) : Matrix.trace Mout ≠ 0 := by
  have hre : 0 < (Matrix.trace Mout).re := by nlinarith
  have hreal : Matrix.trace Mout = ((Matrix.trace Mout).re : ℂ) :=
    (Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr him)).symm
  rw [hreal]
  exact_mod_cast ne_of_gt hre

/-- Normalizing a positive semidefinite output with nonzero trace yields a density operator. -/
theorem lchs_output_density {D : ℕ} (Mout : Operator D) (hM : Mout.PosSemidef)
    (hne : Matrix.trace Mout ≠ 0) : IsDensityOperator (normalizedDensity Mout) :=
  normalizedDensity_isDensity Mout hM hne

/-- The exponential-access count equals the amplification rounds times the sum of homogeneous
and source labels. -/
theorem lchs_exponentialAccesses_eq (Λ : LchsAccessLedger) :
    Λ.exponentialAccesses =
      Λ.amplificationRounds * (Λ.homogeneousLabels + Λ.sourceLabels) := rfl

/-- An LCHS access ledger determines a time-evaluation record with the stated node-query and
exponential-macro counts. -/
theorem lchs_timeEvalAccess_exists (Λ : LchsAccessLedger) :
    ∃ access : TimeEvalAccess,
      access.nodeQueries = Λ.sourceLabels * Λ.amplificationRounds ∧
      access.exponentialMacros = Λ.exponentialAccesses :=
  ⟨⟨[], Λ.sourceLabels * Λ.amplificationRounds, Λ.exponentialAccesses⟩, rfl, rfl⟩

/-- There is positive semidefinite output data satisfying the stated positive success-mass
conditions whose success mass exceeds one. -/
theorem clause60_successMass_not_bounded :
    ∃ (D : ℕ) (Mout : Matrix (Fin D) (Fin D) ℂ) (chk : LchsOutputCheck) (pSucc : ℝ),
      0 < pSucc ∧
      pSucc ≤ chk.successMass ∧
      chk.successMass = (Matrix.trace Mout).re ∧
      (Matrix.trace Mout).im = 0 ∧
      Mout.PosSemidef ∧
      ¬(chk.successMass ≤ 1) := by
  refine ⟨1, 2, ⟨2, 0⟩, 1, by norm_num, by norm_num, ?_, ?_, ?_, by norm_num⟩
  · norm_num [Matrix.trace, Matrix.ofNat_apply]
  · norm_num [Matrix.trace, Matrix.ofNat_apply]
  · have h : (2 : Matrix (Fin 1) (Fin 1) ℂ) = ((2 : ℕ) : Matrix (Fin 1) (Fin 1) ℂ) := by
      norm_num
    rw [h]
    exact Matrix.PosSemidef.natCast 2

/-- Continuous LCHS coefficient and forcing fields can produce a zero forced solution at a
positive time, so the stated hypotheses do not imply positive output norm. -/
theorem clause60_forcedSolution_can_vanish :
    ∃ (D : ℕ) (Lfield Hfield : ℝ → Matrix (Fin D) (Fin D) ℂ)
        (b : ℝ → QState (Fin D)) (T : ℝ) (v : QState (Fin D)),
      Continuous Lfield ∧ Continuous Hfield ∧ Continuous b ∧ 0 < T ∧
      orderedForcedSolution (lchsForcedGenerator Lfield Hfield) b 0 v T = 0 ∧
      ¬(0 < ‖toEuclidean_fromVec
        (orderedForcedSolution (lchsForcedGenerator Lfield Hfield) b 0 v T)‖) := by
  refine ⟨1, fun _ => 0, fun _ => 0, fun _ => 0, 1, 0, continuous_const,
    continuous_const, continuous_const, by norm_num, ?_, ?_⟩
  · simp [orderedForcedSolution, Matrix.mulVec_zero]
  · have hz : orderedForcedSolution
        (lchsForcedGenerator (fun _ => (0 : Matrix (Fin 1) (Fin 1) ℂ))
          (fun _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)))
        (fun _ => (0 : QState (Fin 1))) 0 0 1 = 0 := by
      simp [orderedForcedSolution, Matrix.mulVec_zero]
    rw [hz]
    simp [toEuclidean_fromVec]
open scoped ComplexOrder
open Set
set_option warningAsError false
variable {I : Type} [Fintype I] [DecidableEq I]
variable {I : Type} [Fintype I]

/-- The length of a filtered finite-range list equals the cardinality of the corresponding
filtered finite set. -/
theorem length_filter_finRange {n : ℕ} (q : Fin n → Prop) [DecidablePred q] :
    ((List.finRange n).filter (fun i => q i)).length =
      (Finset.univ.filter (fun i => q i)).card := by
  classical
  have hn : ((List.finRange n).filter (fun i => q i)).Nodup :=
    (List.nodup_finRange n).filter _
  have hcard : ((List.finRange n).filter (fun i => q i)).toFinset.card =
      ((List.finRange n).filter (fun i => q i)).length :=
    List.toFinset_card_of_nodup hn
  have hset : ((List.finRange n).filter (fun i => q i)).toFinset =
      Finset.univ.filter (fun i => q i) := by
    ext x
    simp
  rw [← hcard, hset]

/-- The total segmented label tariff equals `r` times the sum of the prices of the original word
positions. -/
theorem segmentLabelTariff_eq {m : ℕ} (xs : List (Matrix I I ℂ))
    (lab : Fin xs.length → Fin m) (t : ℝ) (r : ℕ) (price : Fin m → ℕ) :
    segmentLabelTariff xs lab t r price =
      r * ((List.finRange xs.length).map (fun i => price (lab i))).sum := by
  classical
  have h1 : segmentLabelTariff xs lab t r price =
      ∑ j : Fin m, price j * segmentLabelVisits xs lab r j := by
    unfold segmentLabelTariff
    rw [list_sum_map_finRange]
  rw [h1]
  simp only [segmentLabelVisits]
  have hswap : ∀ j : Fin m,
      price j * (r * ((List.finRange xs.length).filter (fun i => lab i = j)).length) =
      r * (price j * ((List.finRange xs.length).filter (fun i => lab i = j)).length) := by
    intro j
    ring
  simp only [hswap]
  rw [← Finset.mul_sum]
  congr 1
  have h2 : (∑ j : Fin m,
        price j * ((List.finRange xs.length).filter (fun i => lab i = j)).length) =
      ∑ j : Fin m,
        price j * ((Finset.univ.filter (fun i : Fin xs.length => lab i = j)).card) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [length_filter_finRange]
  rw [h2, sum_price_mul_fiber_card price lab]
  exact (list_sum_map_finRange _).symm
end Qatlib.Concepts.TrotterFormula.GeneralOrder
