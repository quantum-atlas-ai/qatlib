/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Qatlib.Concepts.CoherentSim.TaylorEncoding.TaylorLCUProgram
import Qatlib.Concepts.CoherentSim.GeneralUnitary.GeneralUnitaryTaylorConsumers
import Qatlib.Concepts.CoherentSim.ResetDiscard.ObliviousAmplitudeAmplification
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding

/-!
# Taylor segments for amplified discard simulation

`taylorDiscardEquiv` groups the Taylor workspace into ancillary and data registers, exposing the
Taylor polynomial as a scale-two block encoding for segment size at most `log 2`. The module
also provides a source-form oblivious-amplification word and its substitution and repetition
costs for the Taylor method [BerryEtAl2015Taylor].

## Main statements

* `taylor_discard_block_encoding_ln2`: The relabeled Taylor-polynomial encoding.
* `taylor_ln2_matrix_remainder`: A factorial remainder bound.
* `source_discard_substituted_ledger`: Exact costs after substitution and repetition.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.CoherentSim.FactorialTaylor
open Qatlib.Concepts.CoherentSim.TaylorEncoding

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Matrix.Norms.L2Operator

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 800000

/-- The reassociation equivalence that groups the Taylor label, control bit, and address into
one ancillary register separate from the data register. -/
def taylorDiscardEquiv (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (K : ℕ) :
    TaylorWordLabel J K × (Bool × (J × I)) ≃ (TaylorWordLabel J K × (Bool × J)) × I where
  toFun y := ((y.1, (y.2.1, y.2.2.1)), y.2.2.2)
  invFun x := (x.1.1, (x.1.2.1, (x.1.2.2, x.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The inverse of `taylorDiscardEquiv` restores the nested Taylor-workspace register
arrangement. -/
private theorem taylorDiscardEquiv_symm (J I : Type) [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (K : ℕ)
    (y : (TaylorWordLabel J K × (Bool × J)) × I) :
    (taylorDiscardEquiv J I K).symm y = (y.1.1, (y.1.2.1, (y.1.2.2, y.2))) := rfl

/-- Relabeling a matrix commutes with forming its conjugate-transpose product. -/
private theorem relabelGate_conj_mul {H G : Type} [Fintype H] [DecidableEq H]
    [Fintype G] [DecidableEq G] (e : H ≃ G) (X : Matrix H H ℂ) :
    (relabelGate e X)ᴴ * relabelGate e X = relabelGate e (Xᴴ * X) := by
  have hstar : relabelGate e Xᴴ = (relabelGate e X)ᴴ := by
    ext a b
    simp [relabelGate, Matrix.reindex_apply, Matrix.conjTranspose_apply]
  have hmul : relabelGate e (Xᴴ * X) = relabelGate e Xᴴ * relabelGate e X := by
    ext a b
    simp only [relabelGate, Matrix.reindex_apply, Matrix.mul_apply, Matrix.submatrix_apply]
    rw [Equiv.sum_comp e.symm (fun j => Xᴴ (e.symm a) j * X j (e.symm b))]
  rw [← hstar, ← hmul]

/-- Relabeling the identity matrix gives the identity matrix. -/
private theorem relabelGate_one' {H G : Type} [Fintype H] [DecidableEq H]
    [Fintype G] [DecidableEq G] (e : H ≃ G) :
    relabelGate e (1 : Matrix H H ℂ) = 1 := by
  ext a b
  simp [relabelGate, Matrix.reindex_apply, Matrix.one_apply]

/-- The oblivious-amplification instruction word with a global minus sign, two projector
reflections, two forward queries, and one backward query. -/
noncomputable def sourceDiscardOAAWord {H : Type} [Fintype H] [DecidableEq H]
    (P : Matrix H H ℂ) : List (AdjointStep H) :=
  [.gate (-(1 : Matrix H H ℂ)), .forward, .gate (1 - 2 * P), .backward, .gate (1 - 2 * P),
    .forward]

/-- Compression by a delta-function frame extracts the matrix entries indexed by its defining
map. -/
private theorem compress_delta_frame {X : Type} [Fintype X] [DecidableEq X]
    {P : Type} [Fintype P] [DecidableEq P] (f : P → X)
    (A : Matrix X X ℂ) (p q : P) :
    compress (Matrix.of fun x i => if x = f i then (1 : ℂ) else 0) A
        (Matrix.of fun x i => if x = f i then (1 : ℂ) else 0) p q = A (f p) (f q) := by
  simp only [compress, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (f q)]
  · rw [if_pos rfl, mul_one]
    rw [Finset.sum_eq_single (f p)]
    · simp
    · intro x _ hx
      rw [if_neg hx]
      simp
    · intro h
      exact absurd (Finset.mem_univ (f p)) h
  · intro y _ hy
    rw [if_neg hy, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (f q)) h

/-- The range projector of a delta-function frame for an injective map is the diagonal indicator
of that map's image. -/
private theorem delta_rangeProjector_apply {X : Type} [Fintype X] [DecidableEq X]
    {P : Type} [Fintype P] [DecidableEq P] (f : P → X) (hf : Function.Injective f)
    (x y : X) :
    (rangeProjector (Matrix.of fun a p => if a = f p then (1 : ℂ) else 0)) x y
      = if x = y ∧ ∃ p, x = f p then 1 else 0 := by
  simp only [rangeProjector, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases hxy : x = y
  · subst y
    by_cases hx : ∃ p, x = f p
    · obtain ⟨p, hp⟩ := hx
      rw [if_pos ⟨rfl, ⟨p, hp⟩⟩, Finset.sum_eq_single p]
      · rw [hp]
        simp
      · intro q _ hq
        rw [if_neg (fun hc => hq (hf (hp.symm.trans hc)).symm)]
        simp
      · intro hnp
        exact absurd (Finset.mem_univ p) hnp
    · rw [if_neg (by intro hc; exact hx hc.2)]
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [if_neg (fun hc => hx ⟨q, hc⟩)]
      simp
  · rw [if_neg (by intro hc; exact hxy hc.1)]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hxk : x = f k
    · rw [if_pos hxk, if_neg (fun hc => hxy (hxk.trans hc.symm))]
      simp
    · rw [if_neg hxk]
      simp

/-- The selected corner after Taylor-register reassociation equals compression by the original
Taylor frame. -/
private theorem relabel_corner_eq_compress (J I : Type) [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (j₀ : J) (K : ℕ)
    (A : Matrix (TaylorWordLabel J K × (Bool × (J × I)))
      (TaylorWordLabel J K × (Bool × (J × I))) ℂ) :
    BlockCorner (relabelGate (taylorDiscardEquiv J I K) A)
        (taylorEmptyLabel J K, (false, j₀)) =
      compress (taylorFrame (I := I) j₀ K) A (taylorFrame (I := I) j₀ K) := by
  ext i i'
  simp only [taylorFrame]
  rw [compress_delta_frame (fun i : I => (taylorEmptyLabel J K, (false, (j₀, i)))) A i i']
  simp only [BlockCorner, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    taylorDiscardEquiv_symm]
  rfl

local instance (priority := 10000) instProdProdFast {α β γ : Type} [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] : DecidableEq ((α × β) × γ) :=
  @instDecidableEqProd (α × β) γ (@instDecidableEqProd α β _ _) _

set_option maxHeartbeats 2000000 in

/-- For unitary summands with coefficient mass times duration at most `log 2`, the relabeled
Taylor circuit is a scale-two block encoding of the truncated exponential polynomial. See
[BerryEtAl2015Taylor]. -/
theorem taylor_discard_block_encoding_ln2 (J I : Type) [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (h : J → ℝ) (U : J → Matrix I I ℂ) (j₀ : J) (τ : ℝ) (K : ℕ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) (hτ : (∑ j, |h j|) * |τ| ≤ Real.log 2) :
    IsBlockEncoding (relabelGate (taylorDiscardEquiv J I K)
        (evaluate (taylorQuery U K) (taylorLCUWord h j₀ τ K)))
      (taylorEmptyLabel J K, (false, j₀))
      (Polynomial.aeval (∑ j, (h j : ℂ) • U j) (exponentialTaylorPolynomial τ (K + 1))) 2 := by
  obtain ⟨_, hwf, _, _⟩ :=
    taylor_lcu_actual_prepare_select_and_counts_ln2 (I := I) h j₀ τ K hτ
  refine ⟨?_, by norm_num, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      relabelGate_conj_mul (taylorDiscardEquiv J I K)]
    rw [show (evaluate (taylorQuery U K) (taylorLCUWord h j₀ τ K))ᴴ *
        evaluate (taylorQuery U K) (taylorLCUWord h j₀ τ K) = 1 from by
      simpa [Matrix.star_eq_conjTranspose] using!
        (hwf.evaluate_unitary (taylorQuery_unitary U hU K)).1]
    exact relabelGate_one' (taylorDiscardEquiv J I K)
  · rw [relabel_corner_eq_compress J I j₀ K _,
      taylor_actual_lcu_corner_polynomial_ln2 h U j₀ τ K hU hτ]
    norm_num

/-- Reassociating the Taylor workspace sends the Taylor-frame range projector to the
corresponding ancillary fiber projector. -/
theorem relabel_rangeProjector_taylorFrame (J I : Type) [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (j₀ : J) (K : ℕ) :
    relabelGate (taylorDiscardEquiv J I K) (rangeProjector (taylorFrame (I := I) j₀ K))
      = FiberProjector (I := I) (taylorEmptyLabel J K, (false, j₀)) := by
  have hinj : Function.Injective
      (fun i : I => ((taylorEmptyLabel J K, (false, (j₀, i))) :
        TaylorWordLabel J K × (Bool × (J × I)))) := by
    intro a b hab
    exact congrArg (fun x => x.2.2.2) hab
  ext ⟨⟨wl, fl, j⟩, i⟩ ⟨⟨wl', fl', j'⟩, i'⟩
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    taylorDiscardEquiv_symm, FiberProjector, Matrix.of_apply, taylorFrame,
    delta_rangeProjector_apply _ hinj]
  have hiff : (((wl, fl, j) = (taylorEmptyLabel J K, (false, j₀)) ∧
        ((wl, fl, j), i) = ((wl', fl', j'), i')) ↔
      ((wl, (fl, (j, i))) = (wl', (fl', (j', i')))) ∧
      ∃ p : I, (wl, (fl, (j, i))) = (taylorEmptyLabel J K, (false, (j₀, p)))) := by
    simp only [Prod.mk.injEq]
    tauto
  by_cases h : ((wl, fl, j) = (taylorEmptyLabel J K, (false, j₀)) ∧
    ((wl, fl, j), i) = ((wl', fl', j'), i'))
  · rw [if_pos (hiff.mp h), if_pos h]
  · rw [if_neg (fun hc => h (hiff.mpr hc)), if_neg h]

/-- For unitary summands with coefficient mass times duration at most `log 2`, the truncated
matrix exponential has norm error at most `2 / (K + 1)!`. See [BerryEtAl2015Taylor]. -/
theorem taylor_ln2_matrix_remainder (J I : Type) [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (h : J → ℝ) (U : J → Matrix I I ℂ) (τ : ℝ) (K : ℕ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) (hτ : (∑ j, |h j|) * |τ| ≤ Real.log 2) :
    ‖Polynomial.aeval (∑ j, (h j : ℂ) • U j) (exponentialTaylorPolynomial τ (K + 1)) -
      hamiltonianEvolution (∑ j, (h j : ℂ) • U j) τ‖ ≤ 2 / ((K+1).factorial : ℝ) := by
  have hln2 : (Real.log 2 : ℝ) ≤ 1 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    exact (Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2).trans_eq (by rw [Real.log_exp])
  let H : Matrix I I ℂ := ∑ j, (h j : ℂ) • U j
  let X : Matrix I I ℂ := (-Complex.I * (τ : ℂ)) • H
  have hH : ‖H‖ ≤ ∑ j, |h j| := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (l2_norm_unitary_le_one (hU j))
  have hX : ‖X‖ ≤ Real.log 2 := by
    have hc : ‖-Complex.I * (τ : ℂ)‖ = |τ| := by
      simp [Complex.norm_real, Real.norm_eq_abs]
    calc ‖X‖ = |τ| * ‖H‖ := by rw [norm_smul, hc]
      _ ≤ |τ| * ∑ j, |h j| := mul_le_mul_of_nonneg_left hH (abs_nonneg _)
      _ ≤ Real.log 2 := by simpa [mul_comm] using! hτ
  let f : ℕ → Matrix I I ℂ := fun n => (n.factorial : ℂ)⁻¹ • X ^ n
  have hf : Summable f := NormedSpace.expSeries_summable' X
  have hfn : Summable fun n => ‖f n‖ := NormedSpace.norm_expSeries_summable' X
  have ht : ∑' n, f n = NormedSpace.exp X := (NormedSpace.exp_series_hasSum_exp' X).tsum_eq
  have htail : NormedSpace.exp X - ∑ n ∈ Finset.range (K + 1), f n =
      ∑' n, f (n + (K + 1)) := by
    have hs := hf.sum_add_tsum_nat_add (K + 1)
    rw [ht] at hs
    exact eq_sub_of_add_eq' hs |>.symm
  have hterm : ∀ n, 0 < n → ‖f n‖ ≤ (Real.log 2)^n/(n.factorial : ℝ) := by
    intro n hnpos
    calc ‖f n‖ = (n.factorial : ℝ)⁻¹ * ‖X ^ n‖ := by
          simp [f, norm_smul, norm_inv]
      _ ≤ (n.factorial : ℝ)⁻¹ * ‖X‖ ^ n :=
          mul_le_mul_of_nonneg_left (norm_pow_le' X hnpos) (by positivity)
      _ ≤ (n.factorial : ℝ)⁻¹ * (Real.log 2)^n := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_pow_left₀ (norm_nonneg X) hX n
      _ = (Real.log 2)^n/(n.factorial : ℝ) := by field_simp
  have hn : Summable fun n => ‖f (n + (K + 1))‖ := (summable_nat_add_iff _).2 hfn
  have htailScalar := factorial_taylor_tail_and_coherent_precision.1 (Real.log 2) K
    (Real.log_nonneg (by norm_num)) hln2
  have hg : Summable fun n => (Real.log 2)^(n+(K+1))/((n+(K+1)).factorial : ℝ) := by
    simpa [Nat.add_comm] using! htailScalar.1
  rw [aeval_exponentialTaylorPolynomial, norm_sub_rev]
  change ‖NormedSpace.exp X - ∑ n ∈ Finset.range (K + 1), f n‖ ≤ _
  rw [htail]
  calc ‖∑' n, f (n + (K + 1))‖ ≤ ∑' n, ‖f (n + (K + 1))‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n, (Real.log 2)^(n+(K+1))/((n+(K+1)).factorial : ℝ) :=
        hn.tsum_le_tsum (fun n => hterm _ (by omega)) hg
    _ ≤ 2*(Real.log 2)^(K+1)/((K+1).factorial : ℝ) := by
        simpa only [Nat.add_comm] using! htailScalar.2
    _ ≤ 2/((K+1).factorial : ℝ) := by
        have h1 : (Real.log 2)^(K+1) ≤ 1 := by
          have := pow_le_pow_left₀ (Real.log_nonneg (by norm_num)) hln2 (K+1)
          simpa using! this
        have h2 : (0:ℝ) < ((K+1).factorial : ℝ) := by positivity
        rw [div_le_div_iff_of_pos_right h2]
        nlinarith [h1]

/-- The source discard amplification word evaluates to oblivious amplitude amplification and
uses three queries and three gates. -/
theorem source_discard_oaa_semantics {H : Type} [Fintype H] [DecidableEq H]
    (O P : Matrix H H ℂ) :
    evaluate O (sourceDiscardOAAWord P) = ObliviousAmplitudeAmplification P O ∧
    adjointQueryCount (sourceDiscardOAAWord P) = 3 ∧
    adjointGateCount (sourceDiscardOAAWord P) = 3 := by
  refine ⟨?_, rfl, rfl⟩
  simp only [sourceDiscardOAAWord, evaluate, instructionMatrix, Matrix.mul_one]
  rw [ObliviousAmplitudeAmplification, Matrix.star_eq_conjTranspose]
  noncomm_ring

/-- The source discard amplification word is well formed when its reflection matrix is built
from a star projection. -/
theorem source_discard_oaa_wellFormed {H : Type} [Fintype H] [DecidableEq H]
    (P : Matrix H H ℂ) (hP : IsStarProjection P) :
    WellFormedAdjointCircuit (sourceDiscardOAAWord P) := by
  have hR : (1 - 2 * P) ∈ Matrix.unitaryGroup H ℂ := by
    rw [show 1 - 2 * P = 2 * (1 - P) - 1 by noncomm_ring]
    exact hP.one_sub.two_mul_sub_one_mem_unitary
  have hn : (-(1 : Matrix H H ℂ)) ∈ Matrix.unitaryGroup H ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    simp
  rw [sourceDiscardOAAWord]
  simp only [WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.forward_cons_iff,
    WellFormedAdjointCircuit.backward_cons_iff, WellFormedAdjointCircuit.nil, and_true]
  exact ⟨hn, hR, hR⟩

/-- Relabeling commutes with the oblivious amplitude amplification product. -/
theorem relabelGate_obliviousAmplitudeAmplification {H G : Type} [Fintype H]
    [DecidableEq H] [Fintype G] [DecidableEq G] (e : H ≃ G) (P W : Matrix H H ℂ) :
    relabelGate e (ObliviousAmplitudeAmplification P W) =
      ObliviousAmplitudeAmplification (relabelGate e P) (relabelGate e W) := by
  have heq : ∀ X : Matrix H H ℂ, relabelGate e X = Matrix.reindexAlgEquiv ℂ ℂ e X := fun _ => rfl
  have hstar : (Matrix.reindexAlgEquiv ℂ ℂ e W)ᴴ = Matrix.reindexAlgEquiv ℂ ℂ e Wᴴ := by
    ext a b
    simp [Matrix.reindexAlgEquiv_apply, Matrix.conjTranspose_apply]
  simp only [ObliviousAmplitudeAmplification, two_mul]
  simp only [heq, Matrix.star_eq_conjTranspose,
    map_neg, map_mul, hstar, map_sub, map_add, map_one]

/-- Substituting a well-formed body into the source amplification word preserves
well-formedness. Repeating it `r` times uses `3 * r` times the body's query count and `r *
(3 + 3 * adjointGateCount body)` gates. See [BerryEtAl2015Taylor]. -/
theorem source_discard_substituted_ledger {H : Type} [Fintype H] [DecidableEq H]
    (body : List (AdjointStep H)) (P : Matrix H H ℂ) (r : ℕ)
    (hbody : WellFormedAdjointCircuit body) (hP : IsStarProjection P) :
    WellFormedAdjointCircuit (substituteAdjointCircuit body (sourceDiscardOAAWord P)) ∧
    adjointQueryCount
        (repeatAdjointWord (substituteAdjointCircuit body (sourceDiscardOAAWord P)) r) =
      r * 3 * adjointQueryCount body ∧
    adjointGateCount
        (repeatAdjointWord (substituteAdjointCircuit body (sourceDiscardOAAWord P)) r) =
      r * (3 + 3 * adjointGateCount body) := by
  have hoaa := source_discard_oaa_semantics (1 : Matrix H H ℂ) P
  have hc := substitute_adjoint_evaluate_cost (1 : Matrix H H ℂ) body (sourceDiscardOAAWord P)
  have hr := repeat_adjoint_word_semantics_cost (1 : Matrix H H ℂ)
    (substituteAdjointCircuit body (sourceDiscardOAAWord P)) r
  refine ⟨hc.2.2.2 hbody (source_discard_oaa_wellFormed P hP), ?_, ?_⟩
  · rw [hr.2.1, hc.2.1, hoaa.2.1]
    ring
  · rw [hr.2.2.1, hc.2.2.1, hoaa.2.2, hoaa.2.1]

end Qatlib.Concepts.CoherentSim.ResetDiscard
