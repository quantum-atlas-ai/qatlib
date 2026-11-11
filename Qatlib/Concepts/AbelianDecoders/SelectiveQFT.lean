/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AbelianDecoders.FourierSupport.SparseFourierSupport
import Qatlib.Foundations.InstrumentCore.Measurement.Basic
import Qatlib.Foundations.BornMetrics.EventProbability

/-!
# Selective measurement followed by the quantum Fourier transform

This module applies sparse Fourier support results to a state conditioned on a
positive-probability measurement event. `selective_qft_circular_window_actual_readout` supplies
a positive readout window and the one-gate circuit ledger, while the joint-weight identity
relates normalized and unnormalized branches. For background, see [Cornwell2014].

## Main statements

* `selective_qft_circular_window_actual_readout`: For a normalized state and
  positive-probability selection, each cyclic Fourier window of the conditioned support length
  has positive readout probability; the QFT circuit uses one gate and no queries, and satisfies
  the joint-weight identity.
* `selective_qft_actual_support_product`: For a normalized state and positive-probability
  selection `S`, `N` is at most `S.card` times the support size after applying the QFT to the
  conditioned state.

## References

* [Cornwell, 2014][Cornwell2014]
* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.InstrumentCore.Measurement

open Qatlib.Concepts.AbelianDecoders.FourierSupport
open Qatlib.Foundations.BornMetrics.EventProbability

namespace Qatlib.Concepts.AbelianDecoders.SelectiveQFT

open Matrix
open scoped Classical

/-- Conditioning on a positive-probability event produces a nonzero state with positive support
size at most the cardinality of the selected set. -/
theorem selective_fourier_support {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : QState I) (S : Finset I) (hp : 0 < MeasureProb ψ S) :
    PostMeasure ψ S ≠ 0 ∧ 0 < (sparseFourierSupport (PostMeasure ψ S)).card ∧
      (sparseFourierSupport (PostMeasure ψ S)).card ≤ S.card := by
  have hn : PostMeasure ψ S ≠ 0 := by
    intro hz
    have h := normalized_postMeasure hp
    simp [Normalized, hz] at h
  refine ⟨hn, sparseFourierSupport_card_pos hn, Finset.card_le_card ?_⟩
  intro x hx
  by_contra hnot
  exact ((mem_sparseFourierSupport _ _).mp hx) (postMeasure_apply_of_not_mem ψ S hnot)

/-- For a positive-probability selection, the selection probability times the subsequent readout
weight after `U` equals the readout weight obtained from the unnormalized collapsed state. -/
theorem selective_gate_joint_weight {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : QState I) (S W : Finset I) (U : Matrix I I ℂ)
    (hp : 0 < MeasureProb ψ S) :
    MeasureProb ψ S * MeasureProb (ApplyGate U (PostMeasure ψ S)) W =
      MeasureProb (ApplyGate U (Collapse ψ S)) W := by
  have hstate : PostMeasure ψ S = (Real.sqrt (MeasureProb ψ S) : ℂ)⁻¹ • Collapse ψ S := rfl
  rw [hstate]
  change MeasureProb ψ S * MeasureProb
    (U *ᵥ ((Real.sqrt (MeasureProb ψ S) : ℂ)⁻¹ • Collapse ψ S)) W = _
  rw [Matrix.mulVec_smul, measureProb_smul]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hp.le]
  rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
  rfl

/-- For a normalized state and positive-probability selection, each cyclic Fourier window of the
conditioned support length has positive readout probability; the QFT circuit uses one gate
and no queries, and satisfies the joint-weight identity. -/
theorem selective_qft_circular_window_actual_readout :
    ∀ (N : ℕ) [NeZero N] (ψ : QState (ZMod N)) (S : Finset (ZMod N))
      (a : ZMod N), Normalized ψ → 0 < MeasureProb ψ S →
      let φ := PostMeasure ψ S
      let T := (Finset.univ.filter (fun x => φ x ≠ 0)).card
      let W := Finset.univ.filter (fun y : ZMod N =>
        ∃ t : Fin T, y = a + (t.val : ZMod N))
      let C : Circuit (ZMod N) := [.gate zmodQFTGate]
      0 < T ∧ T ≤ S.card ∧ IsUnitaryCircuit C ∧ QueryCount C = 0 ∧ GateCount C = 1 ∧
      0 < MeasureProb (Run (1 : Matrix (ZMod N) (ZMod N) ℂ) C φ) W ∧
      MeasureProb ψ S * MeasureProb (Run (1 : Matrix (ZMod N) (ZMod N) ℂ) C φ) W =
        MeasureProb (Run (1 : Matrix (ZMod N) (ZMod N) ℂ) C (Collapse ψ S)) W := by
  intro N _ ψ S a _hψ hp
  (try dsimp only)
  obtain ⟨hn, hT, hTS⟩ := selective_fourier_support ψ S hp
  refine ⟨hT, hTS, ?_, rfl, rfl, ?_, ?_⟩
  · simp [zmodQFTGate_unitary (NeZero.pos N)]
  · simp only [run_gate, run_nil, applyGate_zmodQFTGate]
    obtain ⟨t, ht⟩ := sparse_fourier_circular_window (PostMeasure ψ S) hn a
    apply Finset.sum_pos'
    · intro y _
      exact sq_nonneg _
    · refine ⟨a + (t.val : ZMod N), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨t, rfl⟩
      · exact sq_pos_of_pos (norm_pos_iff.mpr ht)
  · simp only [run_gate, run_nil]
    exact selective_gate_joint_weight ψ S _ zmodQFTGate hp

/-- For a normalized state and positive-probability selection `S`, `N` is at most `S.card` times
the support size after applying the QFT to the conditioned state. -/
theorem selective_qft_actual_support_product :
    ∀ (N : ℕ) [NeZero N] (ψ : QState (ZMod N)) (S : Finset (ZMod N)),
      Normalized ψ → 0 < MeasureProb ψ S →
      N ≤ S.card * (Finset.univ.filter (fun y =>
        Run (1 : Matrix (ZMod N) (ZMod N) ℂ)
          ([.gate zmodQFTGate] : Circuit (ZMod N)) (PostMeasure ψ S) y ≠ 0)).card := by
  intro N _ ψ S _hψ hp
  simp only [run_gate, run_nil, applyGate_zmodQFTGate]
  obtain ⟨hn, _, hTS⟩ := selective_fourier_support ψ S hp
  exact (sparse_fourier_support_product (PostMeasure ψ S) hn).trans
    (Nat.mul_le_mul_right _ hTS)

end Qatlib.Concepts.AbelianDecoders.SelectiveQFT
